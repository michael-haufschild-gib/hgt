# Hedenmalm--theta Möbius prime-cell wall freezing

- **ID:** P-G46
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + LEAN FORMALIZATION IN PROGRESS
- **Source:** P-G45 prime-cell thermal cascade; Route-P quantized harmonic escape and principal-class trichotomy
- **Statement:** Route P's persistent `1/p` escape is the frozen residue of the P-G45 thermal prime-cell peak when the two-sided aperture reaches its singular wall.

## Goal

Explain why every interior squarefree Möbius Euler cell returns to cold vacuum while Route P's
critical half-density retains the non-summable principal class `[1/p]`.  Required explanation must
be coefficient-exact and source-local, not an analogy between two limits.

## Gates

- [x] 0 → 1 in-progress: exact wall theorem, proof, cross-corpus coefficient weld
- [ ] 1 → 2 fully-proven: finalize after Lean source check
- [ ] 2 → 3 formalized: module, umbrella, build, lint, axiom audit green
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## P-G46 wall-freezing theorem `[PROVED HERE]`

P-G45 writes prime-cell defect odds as

\[
 W_{q,r}(T)=\frac{qT^{-r}(T-1)^2}{T(1+qT^{-r})^2}.
\tag{1}
\]

Interior two-sided apertures satisfy `r>1`.  Their unique peak obeys

\[
 T_{q,r}^*>\frac{r+1}{r-1}>\frac2{r-1}.
\tag{2}
\]

Hence the peak is forced to infinite thermal scale as `r→1+`.  At the wall `r=1`, `(1)` becomes

\[
 W_{q,1}(T)=q\left(\frac{T-1}{T+q}\right)^2.
\tag{3}
\]

The P-G45 balance collapses to

\[
 B_{q,1}(T)=2(1+q)>0,
\tag{4}
\]

so `W_{q,1}` is strictly increasing for every `T>1`.  Its cold limit is

\[
 \lim_{T\to\infty}W_{q,1}(T)=q.
\tag{5}
\]

Thus wall transition changes topology of thermal orbit:

- `r>1`: zero defect → unique finite peak → zero defect;
- `r=1`: zero defect → strict increase → frozen nonzero residue `q`.

## Exact Route-P coefficient weld

Set `q=1/p`, `T=p^d`, `d>0`.  Direct exponent algebra gives

\[
 W_{1/p,1}(p^d)
 =\frac{p^{-1}(1-p^{-d})^2}{(1+p^{-1-d})^2}
 =\frac{\operatorname{primeValuationHellingerGap}(-d,p)}
 {(1+p^{-1-d})^2}.
\tag{6}
\]

The denominator is a strictly positive projective normalization tending to one in prime scale.
Therefore the existing Route-P physical Hellinger gap is exactly the unprojectivized numerator of
the wall cell, and `(5)` specializes to

\[
 \lim_{T\to\infty}W_{1/p,1}(T)=\frac1p.
\tag{7}
\]

Equation `(7)` is the local source origin of P-G28's quantized harmonic escape and the
principal-class trichotomy: every nonneutral wall fibre retains `[1/p]`; neutral fibre is zero.

## Higher universal principle

Route P is a boundary-freezing transition of squarefree Bernoulli Julia geometry.

1. P-G45 interior primes form a transient ultraviolet-to-infrared peak cascade.
2. Critical half-density is singular aperture wall, not another interior fibre.
3. Approaching wall sends every turning point to infinity by `(2)`.
4. At wall, return branch disappears and each cell freezes at `1/p`.
5. Summing frozen residues creates harmonic obstruction; no finite or summable correction can
   remove it, matching existing principal-class no-gos.

This unifies P-G28, P-G37--P-G40, P-G44, and P-G45 in one source phase diagram.  Persistent
Route-P escape is not failure of cold vacuum law; it is noncommutation of cold limit with singular
aperture-wall limit.

## Hostile audit

- No RH conclusion: off-center wall fibres exhibit `(7)` unconditionally.
- No computation: all identities follow from real powers and rational differentiation.
- Not merely restating harmonic escape: `(2)--(6)` derive its `1/p` class from finite squarefree
  prime-cell Hellinger geometry and classify exact mechanism by which transient peaks freeze.
- This kills regular-interior continuation as producer.  Any bounded/continuous aperture
  deformation inherits peak escape and cannot make wall residue vanish.
- A successful source law must act singularly before wall specialization or couple the frozen
  cell to a Poisson/Gamma dual channel with an independently created opposite principal symbol.

## Lean certificate

Target module:

```text
formal/GaloisForLFunctions/RHTower/
  HedenmalmThetaMobiusPoleUnitPrimeCellWallFreezing.lean
```

Target declarations:

- `thermalBernoulliPeakBalance_one`;
- `thermalBernoulliMidpointDefectOdds_one`;
- `deriv_thermalBernoulliMidpointDefectOdds_one_pos`;
- `tendsto_thermalBernoulliMidpointDefectOdds_one_atTop`;
- `two_div_sub_one_lt_thermalBernoulliPeak`;
- `thermalBernoulliMidpointDefectOdds_prime_eq_hellingerGap`;
- `tendsto_thermalBernoulliMidpointDefectOdds_prime_wall_atTop`.

## Exact survivor

Search only for a pre-wall, nonseparable Euler--Gamma/Poisson coupling whose dual principal
symbol is `-1/p` on the same labelled cell and whose vanishing is a source identity rather than a
fibre-selected counterterm.  Existing fixed principal subtraction has opposite selector polarity;
the needed cancellation must be operator-valued and label-faithful before wall evaluation.

## Log

- 2026-08-12 — derived singular `r=1` phase, strict wall monotonicity, frozen residue, peak-escape
  lower bound, and exact Route-P Hellinger-gap weld; Lean module started.
