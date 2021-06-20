using Random
using JSON
using DataStructures
include("./gerrychainjulia/src/GerryChain.jl")
using .GerryChain

EXPECTED_COLUMNS = [
    "step", "non_adjacent", "no_split", "seam_length",
    "a_label", "b_label", "a_pop", "b_pop", "a_nodes", "b_nodes"
]

function main()
    meta = JSON.parse(readline())
    graph_path = meta["graph_json"]
    pop_col = meta["pop_col"]
    num_steps = meta["num_steps"]
    rng_seed = meta["rng_seed"]
    
    # Generate scores (For scores worker).
    scores = Array{AbstractScore, 1}()  # ignoring weights for now

    graph = BaseGraph(graph_path, pop_col)
    partition = Partition(graph, meta["assignment_col"])
    step_values = score_initial_partition(graph, partition, scores)

    header = chomp(readline())
    columns = split(header, "\t")
    @assert Set(columns) == Set(EXPECTED_COLUMNS)

    label_flips = zeros(Int, graph.num_nodes)

    for (idx, line) in enumerate(eachline())
        next = split(chomp(line), "\t")
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
        old_assignments = copy(partition.assignments)
        update_partition!(partition, graph, proposal)
        for (idx, (before, after)) in enumerate(zip(old_assignments, partition.assignments))
            if before != after
                label_flips[idx] += 1
            end
        end
    end
    JSON.print(Dict("meta" => meta, "flips" => label_flips))
end

main()
