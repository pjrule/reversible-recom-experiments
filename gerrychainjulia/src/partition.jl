mutable struct Partition
    num_dists::Int
    num_cut_edges::Int
    assignments::Array{Int, 1}                  # of length(num_nodes)
    dist_populations::Array{Int, 1}             # of length(num_districts)
    cut_edges::Array{Int, 1}                    # of length(num_edges)
    dist_adj::SparseMatrixCSC{Int, Int}
    dist_nodes::Array{BitSet}
    parent::Union{Partition, Nothing}           # optional parent partition
    weight::Float64
    chain_meta::Union{Dict, Nothing}
end

"""
    Partition(graph::BaseGraph,
              assignment_col::AbstractString)::Partition

Partition represents a partition of the nodes of the graph.
It contains plan-specific information that will change each time we
change our plan.

*Arguments:*
- graph:          BaseGraph object that has the underlying network
                  structure of the plan.
- assignment_col: the key denoting the district assignment at the
                  node level
"""
function Partition(graph::BaseGraph,
                   assignment_col::AbstractString)::Partition
    populations =  graph.populations
    assignments = get_assignments(graph.attributes, assignment_col)
    num_districts = length(Set(assignments))

    # get cut_edges, district_adjacencies
    dist_adj, cut_edges = get_district_adj_and_cut_edges(graph, assignments, num_districts)
    num_cut_edges = sum(cut_edges)

    # get district populations
    dist_populations = get_district_populations(assignments, populations, graph.num_nodes, num_districts)

    # get district_nodes
    dist_nodes = get_district_nodes(assignments, graph.num_nodes, num_districts)

    # return Partition with no parent by default
    return Partition(num_districts, num_cut_edges, assignments, dist_populations, cut_edges,
                     dist_adj, dist_nodes, nothing, 1, nothing)
end

"""
    get_assignments(node_attributes::Array,
                    assignment_col::AbstractString)::Array{Int, 1}

Extracts the assignments for each node in a graph. First attempts
to parse the values of the assignments column as an Int; if it fails,
it assumes every unique string assignment corresponds to to a unique
district.
*Returns* an Int Array of length `length(node_attributes)`.
"""
function get_assignments(node_attributes::Array,
                         assignment_col::AbstractString)::Array{Int, 1}
    assignment_to_num = Dict{String, Int}() # map unique strings to integers
    raw_assignments = get_attribute_by_key(node_attributes, assignment_col)
    processed_assignments = zeros(length(raw_assignments))
    for (i, raw_value) in enumerate(raw_assignments)
        if raw_value isa Int
            processed_assignments[i] = raw_value
        elseif raw_value isa String
            try
                processed_assignments[i] = parse(Int, raw_assignment)
            catch exception # if the String could not be read as an int
                if !haskey(assignment_to_num, raw_value)
                    assignment_to_num[raw_value] = length(assignment_to_num) + 1
                end
                processed_assignments[i] = assignment_to_num[raw_value]
            end
        else
            message = """
                District assignments should be Ints or Strings; type
                $(typeof(raw_value)) was found instead.
            """
            throw(DomainError(raw_value, message))
        end
    end
    return processed_assignments
end

"""
    get_district_nodes(assignments::Array{Int, 1},
                       num_nodes::Int,
                       num_districts::Int)::Array{Set{Int}, 1}

*Returns* an Array of Sets `district_nodes` where the nodes of the i'th
district will be at `district_nodes[i]` as a Set.
"""
function get_district_nodes(assignments::Array{Int, 1},
                            num_nodes::Int,
                            num_districts::Int)::Array{Set{Int}, 1}
    district_nodes = [BitSet([]) for _ in 1:num_districts]
    for i in 1:num_nodes
        push!(district_nodes[assignments[i]], i)
    end
    return district_nodes
end

"""
    get_district_populations(assignments::Array{Int, 1},
                             populations::Array{Int, 1},
                             num_nodes::Int,
                             num_districts::Int)::Array{Int, 1}

*Returns* an Array of populations `dist_pops` where the population of
the i'th district is at `dist_pops[i]`.
"""
function get_district_populations(assignments::Array{Int, 1},
                                  populations::Array{Int, 1},
                                  num_nodes::Int,
                                  num_districts::Int)::Array{Int, 1}
    district_populations = zeros(Int, num_districts)
    for i in 1:num_nodes
        district_populations[assignments[i]] += populations[i]
    end
    return district_populations
end

"""
    get_district_adj_and_cut_edges(graph::BaseGraph,
                                   assignments::Array{Int, 1},
                                   num_districts::Int)

*Returns:*
- district\\_adj: a `num_districts` x `num_districts` matrix where the
                elements are the number of cut edges between the districts
- cut\\_edges:    an Array of size(num\\_edges) where i'th element is 1
                if edge `i` is a cut\\_edge, 0 otherwise
"""
function get_district_adj_and_cut_edges(graph::BaseGraph,
                                        assignments::Array{Int, 1},
                                        num_districts::Int)
    district_adj = zeros(Int, num_districts, num_districts)
    num_edges = ne(graph.simple_graph)
    cut_edges = zeros(Int, graph.num_edges)

    for edge in edges(graph.simple_graph)
        src_assignment = assignments[src(edge)]
        dst_assignment = assignments[dst(edge)]

        if src_assignment != dst_assignment
            # look up the index for this edge
            index = graph.adj_matrix[src(edge), dst(edge)]
            cut_edges[index] = 1

            district_adj[src_assignment, dst_assignment] += 1
            district_adj[dst_assignment, src_assignment] += 1
        end
    end
    return district_adj, cut_edges
end

"""
    sample_adjacent_districts_randomly(partition::Partition,
                                       rng::AbstractRNG)

Randomly sample two adjacent districts and return them.
"""
function district_pair_uniform(partition::Partition,
                                graph::BaseGraph,
                                rng::AbstractRNG)
    #println("uniform")
    while true
        D??? = rand(rng, 1:partition.num_dists)
        D??? = rand(rng, 1:partition.num_dists)
        if partition.dist_adj[D???, D???] != 0
            return D???, D???
        end
    end
end

function district_pair_cut_edges(partition::Partition,
                                 graph::BaseGraph,
                                 rng::AbstractRNG)
    #println("cut edges")
    edge = missing
    while ismissing(edge)
        proposed_edge = rand(rng, 1:graph.num_edges)
        if partition.cut_edges[proposed_edge] == 1
            edge = proposed_edge
        end
    end
    node_a = graph.edge_src[edge]
    node_b = graph.edge_dst[edge]
    return partition.assignments[node_a], partition.assignments[node_b]
end


function district_pair_random_nodes(partition::Partition,
                                    graph::BaseGraph,
                                    rng::AbstractRNG)
    #println("random nodes")
    while true
        node_a = rand(rng, 1:graph.num_nodes)
        node_b = rand(rng, graph.neighbors[node_a])
        dist_a = partition.assignments[node_a] 
        dist_b = partition.assignments[node_b]
        if dist_a != dist_b 
            return dist_a, dist_b
        end
    end
end


function district_pair_chen_style(partition::Partition,
                                  graph::BaseGraph,
                                  rng::AbstractRNG,
                                  county_col::String="COUNTY")
    #println("Chen-style")
    while true
        node_a = rand(rng, 1:graph.num_nodes)
        node_b = rand(rng, graph.neighbors[node_a])
        county_a = graph.attributes[node_a][county_col]
        county_b = graph.attributes[node_b][county_col]
        dist_a = partition.assignments[node_a] 
        dist_b = partition.assignments[node_b]
        if dist_a != dist_b && county_a == county_b
            return dist_a, dist_b
        end
    end
end

"""
    update_partition_adjacency!(partition::Partition,
                                graph::BaseGraph)

Updates the district adjacency matrix and cut edges
to reflect the partition's assignments for each node.
"""
function update_partition_adjacency!(partition::Partition,
                                     graph::BaseGraph)
    partition.dist_adj = spzeros(Int, partition.num_dists, partition.num_dists)
    partition.num_cut_edges = 0

    for i=1:graph.num_edges
        src_assignment = partition.assignments[graph.edge_src[i]]
        dst_assignment = partition.assignments[graph.edge_dst[i]]

        if src_assignment != dst_assignment
            partition.cut_edges[i] = 1
            partition.num_cut_edges += 1

            partition.dist_adj[src_assignment, dst_assignment] += 1
            partition.dist_adj[dst_assignment, src_assignment] += 1
        else
            partition.cut_edges[i] = 0
        end
    end
end

function update_partition_weight!(partition::Partition,
                                  weight::Float64)
    """Updates a partition's weight (1 by default)."""
    partition.weight = weight
end

