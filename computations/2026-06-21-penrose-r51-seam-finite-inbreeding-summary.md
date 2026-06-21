# R51 - finite-place inbreeding and seam firewall

Status: dead end / confirms existing seam-firewall no-go.

Random source chain:
- seed RandomNode: arrays and networks need Aldous-Hoover-style analogues, not ordinary sequence de Finetti alone
- broad topic RNG: 7, relational population genetics
- NODE RNG: 4, inbreeding changes expected genotype-pair distributions
- target-file RNG: 3, `docs/consolidated/01-landscape-and-weld-geometry.md`
- target-topic RNG: 10, seam-firewall
- scientific-method RNG: 23, classify boundary cases
- perturbation-method RNG: 15, strengthen

## Transfer

The NODE says that pair distributions change when finite actors share ancestry.
The target asks whether finite-place dependence can force archimedean
phase-weld positivity.

Finite-place inbreeding was modeled by assigning shared phase multipliers to
blocks of primes in a finite Euler log-derivative. Boundary cases ranged from
independent prime phases (`block=1`) to complete shared phase (`block=80`).

## Evidence

Script:

```text
computations/2026-06-21-penrose-r51-seam-finite-inbreeding.py
```

NODE validation:

```text
F=0.00: P(AA)=0.1225, P(AB)=0.4550, P(BB)=0.4225
F=1.00: P(AA)=0.3500, P(AB)=0.0000, P(BB)=0.6500
```

Finite-prime phase inbreeding boundary:

```text
block= 1, same_block_pairs=0.000, med_Delta(.3,.5,.7,1.2)=(-0.0091,-0.0659,-0.1556,-0.0496), center_excess=+0.0164
block= 2, same_block_pairs=0.013, med_Delta(.3,.5,.7,1.2)=(-0.0240,-0.0873,-0.1460,-0.0552), center_excess=-0.0023
block= 5, same_block_pairs=0.051, med_Delta(.3,.5,.7,1.2)=(-0.0282,-0.1033,-0.1853,-0.0444), center_excess=+0.0035
block=20, same_block_pairs=0.241, med_Delta(.3,.5,.7,1.2)=(-0.0413,-0.1420,-0.2027,-0.0601), center_excess=-0.0200
block=80, same_block_pairs=1.000, med_Delta(.3,.5,.7,1.2)=(-0.0308,-0.1345,-0.2218,-0.0642), center_excess=-0.0082
```

The strengthened boundary is `block=80`: complete finite-place phase sharing
still does not force a positive seam-centered signal.

## Verdict

Dead end for non-reducing count. This is a useful finite-control battery for
the seam firewall, but it confirms the existing theorem-shaped no-go: changing
finite-place pair distributions does not force archimedean positivity.
