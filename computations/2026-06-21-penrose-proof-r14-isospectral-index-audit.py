#!/usr/bin/env python3
"""Small-case NODE check: isospectral non-isomorphic graph drums.

Expected proof-route outcome: likely a dead end.  It tests whether the
isospectral/non-reconstruction phenomenon adds anything to Layer C beyond the
already clear point that a faithful index counts negative directions rather
than reconstructing all geometry.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations

import networkx as nx
import numpy as np


def graph_from_mask(n: int, mask: int) -> nx.Graph:
    g = nx.Graph()
    g.add_nodes_from(range(n))
    edges = list(combinations(range(n), 2))
    for bit, edge in enumerate(edges):
        if mask & (1 << bit):
            g.add_edge(*edge)
    return g


def laplacian_spectrum_key(g: nx.Graph) -> tuple[float, ...]:
    L = nx.laplacian_matrix(g).toarray().astype(float)
    vals = np.linalg.eigvalsh(L)
    return tuple(np.round(vals, 8))


def find_cospectral_pair(n: int = 5) -> tuple[nx.Graph, nx.Graph, tuple[float, ...]] | None:
    buckets: dict[tuple[float, ...], list[nx.Graph]] = defaultdict(list)
    edge_count = n * (n - 1) // 2
    for mask in range(1 << edge_count):
        g = graph_from_mask(n, mask)
        key = laplacian_spectrum_key(g)
        for h in buckets[key]:
            if not nx.is_isomorphic(g, h):
                return h, g, key
        buckets[key].append(g)
    return None


def inertia(vals: tuple[float, ...], tol: float = 1e-8) -> tuple[int, int, int]:
    arr = np.array(vals)
    return (
        int(np.sum(arr < -tol)),
        int(np.sum(np.abs(arr) <= tol)),
        int(np.sum(arr > tol)),
    )


def main() -> None:
    pair = find_cospectral_pair(5)
    if pair is None:
        pair = find_cospectral_pair(6)
    if pair is None:
        raise RuntimeError("no pair found")
    g, h, spectrum = pair
    print("NODE small case: Laplacian-cospectral non-isomorphic graphs")
    print(f"n={g.number_of_nodes()}")
    print(f"G_edges={sorted(g.edges())}")
    print(f"H_edges={sorted(h.edges())}")
    print(f"isomorphic={nx.is_isomorphic(g, h)}")
    print(f"laplacian_spectrum={spectrum}")
    print(f"same_edge_count={g.number_of_edges() == h.number_of_edges()}")
    print(f"zero_multiplicity={sum(abs(x) < 1e-8 for x in spectrum)}")

    shifted = tuple(x - 2.0 for x in spectrum)
    print()
    print("Proof-route audit toy: same full spectrum gives same shifted inertia")
    print(f"shifted_by_2_spectrum={shifted}")
    print(f"shifted_inertia_neg_zero_pos={inertia(shifted)}")
    print(
        "Interpretation: isospectral non-reconstruction is real, but for a pure "
        "negative-index target, the full spectrum already determines the index. "
        "This does not sharpen the source-built kappa_- route beyond the known "
        "boundary-domain/reconstruction distinction."
    )


if __name__ == "__main__":
    main()
