#!/usr/bin/env python3
import numpy as np


def trial(rng, n=80, domains=8):
    domain = np.repeat(np.arange(domains), n // domains)
    rng.shuffle(domain)
    imports = np.zeros((n, n), dtype=bool)
    semantic = np.zeros((n, n), dtype=bool)
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            # imports are deliberately sparse and mostly local
            if domain[i] == domain[j] and rng.random() < 0.025:
                imports[i, j] = True
            elif rng.random() < 0.002:
                imports[i, j] = True
            # semantic coupling is shared contract ownership, often cross-cutting
            if domain[i] == domain[j] and rng.random() < 0.18:
                semantic[i, j] = True
            elif (domain[i] + domain[j]) % domains in (0, 3) and rng.random() < 0.035:
                semantic[i, j] = True
    return imports, semantic


def closure_size(edges, seeds):
    n = edges.shape[0]
    seen = set(seeds)
    frontier = list(seeds)
    while frontier:
        i = frontier.pop()
        for j in np.flatnonzero(edges[i]):
            if int(j) not in seen:
                seen.add(int(j))
                frontier.append(int(j))
    return len(seen)


def main():
    rng = np.random.default_rng(20260621)
    print("NODE: semantic dependencies can dominate package imports")
    print("mutated_modules import_closure_q50 import_closure_q90 semantic_closure_q50 semantic_closure_q90 silent_semantic_ratio_q50")
    for seeds_count in [1, 2, 4, 8]:
        import_sizes = []
        semantic_sizes = []
        silent_ratios = []
        for _ in range(500):
            imports, semantic = trial(rng)
            seeds = rng.choice(imports.shape[0], size=seeds_count, replace=False).tolist()
            import_edges = imports
            combined_edges = imports | semantic
            imp = closure_size(import_edges, seeds)
            sem = closure_size(combined_edges, seeds)
            import_sizes.append(imp)
            semantic_sizes.append(sem)
            silent_ratios.append((sem - imp) / max(1, imp))
        print(
            f"{seeds_count:15d} {np.quantile(import_sizes,0.5):18.6f} {np.quantile(import_sizes,0.9):18.6f} "
            f"{np.quantile(semantic_sizes,0.5):21.6f} {np.quantile(semantic_sizes,0.9):21.6f} "
            f"{np.quantile(silent_ratios,0.5):25.6f}"
        )


if __name__ == "__main__":
    main()
