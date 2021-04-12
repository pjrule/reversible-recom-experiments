using ArgParse
using Random
using LibPQ, Tables, JSON
using DataStructures
include("../202101/gerrychainjulia/src/GerryChain.jl")
using .GerryChain
using StatProfilerHTML
#using Profile

EXPECTED_COLUMNS = [
    "step", "non_adjacent", "no_split", "seam_length",
    "a_label", "b_label", "a_pop", "b_pop", "a_nodes", "b_nodes"
]
REASONS = ["non_adjacent", "no_split", "seam_length"]

function weight_score(graph::BaseGraph, partition::Partition)::Int
    partition.weight
end

function make_reasons_score(reason::String)::PlanScore
    function score(graph::BaseGraph, partition::Partition)::Int
        if isnothing(partition.chain_meta) || !haskey(partition.chain_meta, "reasons")
            return 0
        end
        return partition.chain_meta["reasons"][reason]
    end
    sanitized_reason = replace(replace(reason, "-" => "_"), " " => "_")
    return PlanScore("reasons_$(sanitized_reason)", score)
end


function parse_cli()
    s = ArgParseSettings()

    @add_arg_table s begin
        "--db"
            required = true
        "--db-batch-id"
            required = true
            arg_type = Int
        "--description"
        "--snapshot-interval"
            default = 0
            arg_type = Int
        "--record-cols"
            nargs = '*'
    end

    return parse_args(s)
end


function init_scores(
    conn,
    batch_id::Int,
    scores::Array{AbstractScore, 1})::Dict{String, Int}

    execute(conn, "BEGIN")
    for score in scores
        if score isa PlanScore
            score_type = "plan"
        else
            score_type = "district"
        end
        execute(
            conn,
            """INSERT INTO scores (batch_id, name, score_type) VALUES (\$1, \$2, \$3) 
            ON CONFLICT DO NOTHING""",
            (batch_id, score.name, score_type)
        )
    end
    execute(conn, "COMMIT")

    existing_scores = columntable(
        execute(conn, "SELECT id, name FROM scores WHERE batch_id = \$1", [batch_id])
    )
    return Dict(
        name => id
        for (name, id) in zip(existing_scores[:name], existing_scores[:id])
    )
end

function main(args)
    meta = JSON.parse(readline())
    graph_path = meta["graph_json"]
    pop_col = meta["pop_col"]
    num_steps = meta["num_steps"]
    rng_seed = meta["rng_seed"]

    batch_id = args["db-batch-id"]
    snapshot_interval = args["snapshot-interval"]
    
    # Generate scores (For scores worker).
    record_cols = args["record-cols"]
    scores = Array{AbstractScore, 1}()
    push!(scores, num_cut_edges("cut_edges"))
    push!(scores, PlanScore("weights", weight_score))
    for col in record_cols
        push!(scores, DistrictAggregate(col))
    end
    for reason in REASONS
        push!(scores, make_reasons_score(reason))
    end

    graph = BaseGraph(graph_path, pop_col)
    partition = Partition(graph, meta["assignment_col"])

    # Initialize the experiment in the database.
    conn = LibPQ.Connection(args["db"])
    println("Got connection: ", conn)
    res = execute(
        conn,
        "INSERT INTO chain_meta (batch_id, description, districts, steps, meta) VALUES (\$1, \$2, \$3, \$4, \$5) RETURNING id",
        [
            batch_id,
            get(args, "description", ""),
            partition.num_dists,
            num_steps,
            JSON.json(meta)
        ]
    )
    chain_id = Int(columntable(res)[:id][1])
    score_ids = init_scores(conn, batch_id, scores)
    println("score IDs: ", score_ids)

    # Insert the initial partition.
    step_values = score_initial_partition(graph, partition, scores)
    for (score, data) in step_values
        println("score: ", score, "\t", data)
        if data isa AbstractDict
            # TODO
        elseif data isa AbstractArray
            for (dist, val) in enumerate(data)
                #println("\tinserting: ", (chain_id, score_ids[score], 0, dist, val))
                execute(
                    conn,
                    """INSERT INTO district_scores (chain_id, score_id, step, district, score) 
                    VALUES (\$1, \$2, \$3, \$4, \$5)""",
                    (chain_id, score_ids[score], 0, dist, val)
                )
            end
        else
            #println("\tinserting: ", (chain_id, score_ids[score], 0, data))
            execute(
                conn,
                """INSERT INTO plan_scores (chain_id, score_id, step, score) 
                VALUES (\$1, \$2, \$3, \$4)""",
                (chain_id, score_ids[score], 0, data)
            )
            # plan_scores
        end
    end

    header = chomp(readline())
    columns = split(header, "\t")
    @assert Set(columns) == Set(EXPECTED_COLUMNS)

    @profilehtml for (idx, line) in enumerate(eachline())
        println(chomp(line))
        println(idx)
        execute(conn, "BEGIN")
        next = split(chomp(line), "\t")
        #if length(next) != length(EXPECTED_COLUMNS)
        row = Dict(columns[idx] => val for (idx, val) in enumerate(next))
        proposal = RecomProposal(
            parse(Int, row["a_label"]) + 1, parse(Int, row["b_label"]) + 1,
            parse(Int, row["a_pop"]), parse(Int, row["b_pop"]),
            BitSet([parse(Int, node) + 1
                    for node in split(row["a_nodes"][begin+1:end-1], ",")]),
            BitSet([parse(Int, node) + 1
                    for node in split(row["b_nodes"][begin+1:end-1], ",")])
        )

        step_values = score_partition_from_proposal(graph, partition, proposal, scores)
        district_delta = step_values["dists"]
        for (score, data) in step_values
            if score == "dists"
                continue
            end
            if data isa AbstractDict
                # TODO
            elseif data isa AbstractArray
                for (i, dist) in enumerate(district_delta)
                    execute(
                        conn,
                        """INSERT INTO district_scores (chain_id, score_id, step, district, score) 
                        VALUES (\$1, \$2, \$3, \$4, \$5)""",
                        (chain_id, score_ids[score], idx, dist, data[i])
                    )
                end
            else
                execute(
                    conn,
                    """INSERT INTO plan_scores (chain_id, score_id, step, score) 
                    VALUES (\$1, \$2, \$3, \$4)""",
                    (chain_id, score_ids[score], idx, data)
                )
            end
        end
        
        if snapshot_interval > 0 && idx % snapshot_interval == 0
            execute(
                conn,
                """INSERT INTO plan_snapshots (chain_id, step, assignment)
                VALUES (\$1, \$2, \$3)""",
                (chain_id, idx, partition.assignments)
            )
        end
        execute(conn, "COMMIT")

        update_partition!(partition, graph, proposal)
        reasons = Dict(reason => parse(Int, row[reason]) for reason in REASONS)
        partition.chain_meta = Dict("reasons" => reasons)
        partition.weight = sum(values(reasons)) + 1
    end
    println("here")
    close(conn)
    println("done for real")
end

main(parse_cli())
