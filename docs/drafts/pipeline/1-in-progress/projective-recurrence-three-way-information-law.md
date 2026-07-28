# Projective recurrence three-way information law

- **ID:** `projective-recurrence-three-way-information-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / TARGET-VOLUME SHARPNESS / INTEGER PHASE ALLOCATION
- **Source:** hostile attack on the publication-ready projective recurrence manuscript
- **Statement:** Haar target information, the least spectrum-uniform recurrence deadline, and
  parallel-Gaussian rate--distortion have the same high-information law; the exact finite-resolution
  construction is a monotone integer phase-allocation problem whose inactive coordinates form a
  weight tail.

## Frontier

- `[CORPUS]` `universalWeightedFloquetFidelityRecurrenceTime_rateDistortionSandwich`
  traps the logarithm of the least universal Floquet deadline around the pivot water entropy with
  explicit additive costs.
- `[CORPUS]` `universalWeightedFloquetFidelityRecurrenceTime_rateDistortionNormalized`
  gives the corresponding constant-free relative law whenever the water entropy absorbs both
  carrier costs.
- `[CORPUS]`
  `measureReal_torusProjectiveWeightedCoherenceTarget_canonicalHaarWater_le`
  gives a pivot-resolved upper bound for the normalized-Haar target volume.
- `[CORPUS]` `isUniversalProjectiveWeightedCoherenceDeadline_of_selectedFeasible`
  gives a selected-support product deadline with tail loss `2 tau`.
- `[FORMALIZED]` `exists_weightedFloquetFidelity_recurrence_after` upgrades any
  universal near-hit deadline to a return after every prescribed delay `M`,
  by time `(M+1)T`.
- `[LITERATURE]` Gaussian reverse water filling and integer transform-code bit allocation are
  established parent optimization mechanisms. They are not novelty objects.
- `[LITERATURE]` shrinking-target laws for torus translations depend on Diophantine arithmetic;
  no finite-horizon linear lower law can hold uniformly for every fixed phase packet.

## Claim A — canonical water box

Fix `r >= 2`, positive weights `w_j` summing to one, and `0 < eta <= 1`. Let
`H_proj(w,eta)` be the pivot-minimized Gaussian water entropy and let

```text
mu_w(eta)=Haar{z in T^r : |sum_j w_j z_j| >= 1-eta}.
```

### Theorem A `[FORMALIZED]`

Writing `d=r-1`,

```text
(sqrt(2)/pi)^d exp(-H_proj(w,eta))
 <= mu_w(eta)
 <= B_H(w,eta)
 <= r exp{(pi/4)d-H_proj(w,eta)}.                         (A1)
```

Consequently,

```text
H_proj-(pi/4)d-log r
 <= -log mu_w
 <= H_proj+d log(pi/sqrt(2)).                             (A2)
```

Together with the existing recurrence sandwich,

```text
log T_w(eta)=H_proj(w,eta)+O(d),
-log mu_w(eta)=H_proj(w,eta)+O(d),                        (A3)
```

with all constants displayed in `(A1)`--`(A2)` and the existing deadline theorem. Whenever
`H_proj/d -> infinity`, both ratios to `H_proj` tend to one. Thus the Haar target information,
the worst-packet recurrence information, and Gaussian rate--distortion have one sharp
high-information law.

### Proof

Choose a pivot `k` attaining `H_proj` and a minimizing distortion allocation

```text
0 < D_j <= w_j,  sum_(j!=k) D_j <= eta,
H_proj=(1/2)sum_(j!=k) log(w_j/D_j).
```

Use projective coordinates `z_j/z_k=exp(i theta_j)`. The projective shear preserves product Haar.
On the box

```text
|theta_j| <= sqrt(2 D_j/w_j),  j!=k,
```

the real part after removing the pivot phase satisfies

```text
Re sum_j w_j z_j
 >= 1-sum_(j!=k) w_j theta_j^2/2
 >= 1-sum_(j!=k)D_j
 >= 1-eta.
```

Because `D_j<=w_j`, every radius is at most `sqrt(2)<pi`; its normalized-circle measure is
`sqrt(2D_j/w_j)/pi`. The product box therefore has measure

```text
product_(j!=k) sqrt(2D_j/w_j)/pi
=(sqrt(2)/pi)^d exp(-H_proj).
```

This proves the first inequality in `(A1)`. The middle inequality is the pivot-resolved corpus
theorem. The water identity `lambda_k eta<=d` and `H_proj<=H_k` give the final envelope.
Taking negative logarithms proves `(A2)`. Combining with the corpus deadline sandwich proves
`(A3)`.

### Hostile attack

1. **“This is an exact Haar quantile.”** False. It is a two-sided target-volume information law,
   not an equality for a finite-horizon hitting quantile.
2. **“This makes first `N` hits independent.”** False. No time independence is used or claimed.
3. **“The `O(d)` term disappeared.”** False. It becomes negligible only in the
   high-information regime. Finite-resolution integer rounding is handled separately below.
4. **“The result is a new Gaussian rate--distortion theorem.”** False. Novelty, if any, is the
   three-way quantum identification and its target-volume lower inclusion.

Verdict: `SURVIVES PRELIMINARY ATTACK`; exact theorem is formalized in
`ProjectiveWeightedTargetVolumeLower.lean`. Load-bearing declarations are
`canonicalEntropyFactor_le_volumeReal_coherenceTarget`,
`canonicalWaterEntropy_targetInformation_sandwich`,
`abs_targetInformation_sub_canonicalWaterEntropy_le`, and
`abs_targetInformation_div_canonicalWaterEntropy_sub_one_le`.

## Claim B — exact quantized phase allocation

For `q in N_{>=1}` put

```text
delta(1)=pi,
delta(q)=min(pi,2pi/q) for q>=2,
c(q)=1-cos(delta(q)).
```

For pivot `k`, define the exact integer allocation number

```text
C_k(w,eta)
 =min {product_(j!=k) q_j :
       q_j>=1, sum_(j!=k) w_j c(q_j)<=eta},               (B1)
C_Z(w,eta)=min_k C_k(w,eta).
```

### Conjecture B `[PAPER-PROVED] [REDISCOVERED] [NOT USED IN MANUSCRIPT]`

1. Every phase packet returns by clock `C_Z(w,eta)`.
2. A minimizing allocation exists.
3. No minimizer uses `q_j=2`.
4. After sorting `w_1>=...>=w_d`, some minimizer satisfies
   `q_1>=...>=q_d`; consequently the synchronized coordinates `q_j>=3` form a weight prefix and
   the discarded coordinates `q_j=1` form a weight tail.
5. The continuous high-resolution relaxation of `(B1)` is the existing reverse-water-filling
   program. The exact finite law is therefore integer phase allocation, not a dimension-free
   continuous surrogate.

### Proof

Partition coordinate `j` into `q_j` equal arcs. Among `product q_j+1` projective orbit points,
two occupy one product cell. Their difference gives a positive clock at most `product q_j` and a
centered phase error at most `delta(q_j)`. Therefore

```text
Re sum_j w_j z_j >= 1-sum_(j!=k)w_j c(q_j)>=1-eta.
```

Feasible allocations exist by taking all `q_j` sufficiently large. The positive integers are
well ordered, so the set of feasible products has a least element; only finitely many tuples have
that fixed product. Hence a minimizer exists.

Since `c(1)=c(2)=2`, replacing `q_j=2` by `1` preserves feasibility and strictly lowers the
product. Thus no minimizer uses two.

The function `c(q)` is nonincreasing. If `w_i>=w_j` but `q_i<q_j`, swap the two resolutions. The
product is unchanged and the defect changes by

```text
(w_i-w_j)(c(q_j)-c(q_i))<=0.
```

Repeated inversions yield a monotone minimizer. Because two is absent, the indices with
`q_j>=3` are a prefix.

### Hostile attack

1. **“This is novel integer bit allocation.”** `REDISCOVERED` as an optimization pattern. The
   positive survivor is its exact projective-recurrence interpretation and the identification of
   one-cell coordinates with physical worst-case tail loss.
2. **“The dimension cost is gone.”** False. It is represented exactly by the integer product.
   The valid statement is that ambient-support rounding is replaced by exact selected-support
   rounding.
3. **“Reverse water filling exactly solves `(B1)`.”** False at finite resolution. It solves the
   continuous high-resolution relaxation. The monotone prefix theorem is the exact selection law.

Verdict: optimization mechanism `REDISCOVERED`. Exact joint integer optimization remains
unformalized and is removed from the manuscript claim surface. The retained selected-support
construction is only a feasible recurrence certificate; it is not called a joint optimizer or
identified with the continuous water-active set.

## No-go boundary

`[FALSIFIED]` A finite-horizon lower bound proportional to `N mu_w(eta)` cannot be claimed for all
fixed spectra from Haar invariance alone. Return events are arithmetically correlated; commensurate
spectra can return at the first clock, and shrinking-target behavior of torus translations depends
on Diophantine type.

**Strongest positive survivor:** the two-sided one-step target-volume law `(A1)`, the exact
minimax information sandwich already in the corpus, the unconditional
post-delay recurrence theorem, and almost-everywhere/generic orbit laws only
after an explicit arithmetic audit.

## Gates

- [x] 0 → 1: exact statements, obstruction, corpus frontier, and paper proofs recorded
- [x] 1 → 2: Claim A priority and measure-theoretic proof dependencies audited
- [x] 2 → 3: Claim A exact Lean theorems and targeted foreground checks
- [x] 3 → 4: Claim A integrated into manuscript; Claim B excluded from its claim surface
- [ ] Final: axiom audit, module build, and hostile editorial re-audit
