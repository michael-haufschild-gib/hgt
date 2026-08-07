# Suzuki prime-seam parity-Hankel strong indefiniteness

- **ID:** `suzuki-prime-seam-parity-hankel-strong-indefiniteness`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / THEOREM (Lean) / FAILED MECHANISM CLASS
- **Scientific status:** `[PROVED HERE] [UNCONDITIONAL] [NO COMPUTATION]`
  `[DELTA-HANKEL ANCESTRY CLASSICAL] [CANDIDATE NEW SUZUKI APPLICATION]`
  `[NOT A SUZUKI NO-GO] [NOT AN RH PROOF]`
- **Statement:** As soon as the first prime seam is interior, Suzuki's literal parity-Hankel
  difference has both infinite positive and infinite negative index. Hence no one-sided
  finite-index comparison survives cofinally.

## Goal

The prime-free classification gives one positive exponential square minus infinitely many
negative squares. That raises a potentially constructive possibility: perhaps the full parity
difference has positive index at most one and therefore forces a one-sided min--max interlacing
law.

The prime atoms kill this possibility completely.

## Exact prime seam

Suzuki's positive-ray Weil kernel is

```text
K
 =K_reg(t)dt
  -sum_(n>=2) Lambda(n)n^(-1/2) delta_(log n),          (1)
```

so the parity Hankel form contains

```text
P_(a,n)(phi,psi)
 =-w_n integral phi(y)conj(psi(log n-y))dy,             (2)

w_n=Lambda(n)n^(-1/2)>0
```

whenever

```text
log n<2a.                                               (3)
```

For a prime `p`, `w_p=log(p)/sqrt(p)>0`. In particular, every aperture

```text
a>log(2)/2                                              (4)
```

contains the interior first-prime seam `x+y=log 2`.

## Swap-block signature

Fix one visible prime seam `L=log p`. Choose a small interval `I` on one side of `L/2` and let

```text
JI={L-x:x in I}.
```

Take `I` so that `I`, `JI` are disjoint and their relevant pairwise sum neighborhoods contain no
other visible prime-power seam. On

```text
L2(I) direct_sum L2(JI),
```

the `p`-atom is exactly

```text
-w_p J,
```

where `J(u,v)=(v,u)` is the reflection swap. Therefore

```text
atom(u,u) =-w_p||(u,u)||^2,
atom(u,-u)=+w_p||(u,-u)||^2.                            (5)
```

Each swap parity has infinite dimension.

## Regular perturbation cannot remove either sign

The regular kernel is continuous and bounded on the compact product of the chosen intervals.
Partition `I` into `m` disjoint subintervals of width `eta`, choose normalized bumps `u_j`, and
reflect them into `JI`.

For any vector in their `2m`-dimensional span,

```text
|H_reg(f,f)| <= M ||f||_1^2
              <= C_m M eta ||f||_2^2.                  (6)
```

Choose `eta` so small that

```text
C_m M eta < w_p.                                        (7)
```

All other atomic terms vanish by the seam-avoidance choice. Equations `(5)--(7)` imply:

```text
H_a(f,f)<0
```

on the `m`-dimensional reflected-even bump packet and

```text
H_a(f,f)>0
```

on the `m`-dimensional reflected-odd bump packet. Since `m` is arbitrary,

```text
ind_+(H_a)=infinity,
ind_-(H_a)=infinity                                    (8)
```

for every `a>log(2)/2`. Positive scaling preserves inertia, so

```text
ind_+(Q_even-Q_odd)=ind_-(Q_even-Q_odd)=infinity.        (9)
```

This proof works on the smooth test core and therefore requires no compact-operator or essential
spectrum hypothesis.

## Route-G consequence

The prime-free regular corner remains useful: it proves infinite negative index at every aperture.
Once the first prime seam appears, `(9)` sharpens the cofinal classification to strong
indefiniteness.

This kills all parity-interlacing transfers based on:

- finite rank or finite codimension;
- finitely many negative squares;
- finitely many positive squares;
- either orientation of a finite-index Pontryagin comparison;
- a one-sided codimension-one min--max order inferred from the archimedean corner.

It does not prove that the two full parity spectra fail every accidental interlacing relation, and
it does not touch the genuine two-angle meromorphic Livšic/Hermite--Biehler carrier. Route G
remains open.

## Positive survivor

Any viable parity theorem must use the arithmetic organization of all seam reflections, not an
order or inertia bound on their aggregate. The source-side options left are:

- a variation-diminishing or oscillation theorem for the full prime-seam reflection system;
- the exact parity credit/debt transport law already isolated in Route G;
- a source transform that diagonalizes or cancels the seam swaps before comparison;
- bypassing literal parity comparison through the two-angle meromorphic carrier.

## Novelty audit

Classical content:

- a Hankel delta kernel acts by reflection;
- its swap-even and swap-odd sectors have opposite signs;
- localized bumps suppress bounded regular kernels;
- a point-supported Hankel singularity is strongly indefinite.

Yafaev's 2013 analysis of Hankel kernels singular at a positive point already establishes the
generic two-sided spectral behavior, including delta-type reflection models. No new abstract
delta-Hankel spectral theorem is claimed.

Targeted primary-source audit:

- Suzuki 2026 gives the exact negative prime-power atoms in the restricted-Weil screw kernel but
  does not state their consequence `(8)`--`(9)` for the literal parity blocks.
- Yafaev 2013 treats the parent singular-Hankel class but not Suzuki's prime-power seam system,
  parity reduction, or the resulting obstruction to transferring boundary-angle interlacing.
- Corpus search found the exact finite-prime parity carrier and generic seam/Krein inertia laws,
  but no theorem deriving cofinal two-sided infinite inertia of Suzuki's literal parity
  difference from one visible prime seam.

Candidate novelty is restricted to the exact Suzuki synthesis:

```text
negative first-prime Hankel atom
  + parity sum-coordinate seam
  + reflected bump localization
  -> cofinal (infinity,infinity) inertia
  -> no finite-index parity comparison in either orientation.
```

External priority remains unverified.

## Formalization

File:

```text
formal/GaloisForLFunctions/RHTower/
  SuzukiPrimeSeamParityHankelStrongIndefiniteness.lean
```

Main declarations:

```text
primeSeamPacketNormSq
primeSeamAtomQuadratic
primeSeamEvenEmbedding
primeSeamOddEmbedding
primeSeamAtomQuadratic_even
primeSeamAtomQuadratic_odd
primeSeamPerturbedQuadratic_even_neg
primeSeamPerturbedQuadratic_odd_pos
suzukiPrimeSeamWeight
suzukiPrimeSeamWeight_prime_pos
suzukiPrimeSeam_midpoint_in_aperture
suzukiPrimeSeam_add_smallPerturbation_signedPackets
```

The formal theorem proves, for arbitrary packet dimension, that both signs survive every regular
quadratic perturbation bounded by a constant strictly below the exact prime seam weight.

Verification:

```text
lake env lean \
  GaloisForLFunctions/RHTower/SuzukiPrimeSeamParityHankelStrongIndefiniteness.lean
```

passed with no `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or computation.

## Status

`[FAILED-CLASS: ONE-SIDED FINITE-INDEX PARITY INTERLACING]`

Positive survivor: only a genuinely arithmetic infinite-seam oscillation/transport theorem, a
source transform, or the two-angle meromorphic carrier can compare the literal parity sectors.
