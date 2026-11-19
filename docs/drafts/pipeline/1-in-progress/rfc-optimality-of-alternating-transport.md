# Exact gain from two simultaneous transports

- **Stage** 1-in-progress
- **Question** Which new positives increase the number of edges, and can rearrangement of the same two sets of edges improve that gain?

For matchings \(A,B\), let \(W\) be the positives reached from an \(A\)-only positive by alternating an \(A\)-edge with an inverse \(B\)-edge. Put \(U=A_+\cap W\), \(N=A(U)\), and \(P=B_+\setminus W\). Every used edge from a reached source ends in \(N\). For a \(B\)-edge this follows from the predecessor of its reached source. Every unreached source of either matching belongs to \(P\), since all \(A\)-only sources start walks. Thus \(N\cup P\) covers every allowed edge.

Any joint matching retaining \(A_+\) and \(B_-\) matches all \(U\) into \(N\), so exhausts \(N\). It also covers \(B(P)\), disjoint from \(N\) by closure of the reached set. It therefore attains the cover size \(|U|+|P|\) and is maximum on the union of the two edge sets. Its gain over \(A\) equals the number of \(B\)-only positives outside \(W\). The formula identifies the exact additional endpoints for which a new arithmetic edge is needed to improve on the switch.
