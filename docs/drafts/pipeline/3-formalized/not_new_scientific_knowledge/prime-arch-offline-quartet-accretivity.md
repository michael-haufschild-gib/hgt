# Prime--archimedean off-line quartet accretivity

- **ID:** `prime-arch-offline-quartet-accretivity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / TOP-DOWN HYPOTHESIS DISCHARGE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT AN RH PROOF]`
- **Lean files:**
  - `formal/GaloisForLFunctions/RHTower/XiEndpointOffLineQuartetHeightGap.lean`
  - `formal/GaloisForLFunctions/RHTower/PrimeArchOffLineQuartetAccretivity.lean`
  - `formal/GaloisForLFunctions/RHTower/PrimeArchExactOffLineQuartetAccretivity.lean`
  - `formal/GaloisForLFunctions/RHTower/PrimeArchOffLineQuartetKMSMaster.lean`
- **Statement:** The four distinct FE--Schwarz copies of every off-critical Xi zero contribute
  four equal nonnegative endpoint charges.  Consequently
  `4 <= c * (1 + (Im rho)^2)`, and every radius satisfying
  `c * ((R + 1/2)^2 + 1) < 4` is an unconditional accretive band for the continued
  prime--Gamma source.  The explicit bounds certify `R = 218/25`.  Positively, every such
  radius satisfies `R+1/2 < |Im rho|` for every off-line zero `rho`: the quartet mechanism
  creates a strict half-unit buffer but cannot make a self-excluding contradiction loop by itself.

## Result

For an off-line multiplicity copy `q`, let `J` be critical-line conjugation and `C` ordinary
conjugation.  The four copies

\[
q,\qquad Jq,\qquad Cq,\qquad JCq
\]

are distinct.  Their endpoint cross charges are equal and nonnegative.  Since their full sum is
the completed endpoint curvature `c`,

\[
4\,e(q)\le c.
\]

The pointwise estimate `1/(1+gamma^2) <= e(q)` gives the exact orbit law

\[
4\le c(1+\gamma^2).
\]

The unconditional source value `c < 2/43` then gives

\[
(\operatorname{Im}\rho)^2>85
\]

for every off-critical zero.  On-critical zeros have zero transverse spectral coordinate, so
their line-conjugate resolvent pair has the anti-Herglotz sign at every frequency without a height
estimate.  The exact orbit law handles all remaining atoms whenever

\[
c\bigl((R+1/2)^2+1\bigr)<4.
\]

The sharper certified bound `c < 93/2000` proves this strict inequality at `R=218/25`, so the full
continued source trace has nonpositive imaginary part on `|Re z| <= 218/25`.  Reflection removes negative
frequencies.  Thus RH is equivalent to completed
prime--Gamma accretivity only at positive heights above `218/25`; Gaussian-rational density reduces
that remaining obligation to countably many source values.

The same two strict inequalities expose the precise boundary of a contradiction proof.  If `rho`
is off line and `R` is any exact quartet-admissible radius, then

\[
c((R+1/2)^2+1)<4\le c(1+(\operatorname{Im}\rho)^2),
\]

and `c>0`, hence

\[
R+1/2<|\operatorname{Im}\rho|.
\]

This is the positive self-exclusion law: the source budget always leaves a half-unit separation
between the discharged band and every off-line orbit.  A closed contradiction chain therefore
needs a second mechanism that propagates accretivity across that buffer; iterating the same
endpoint quartet estimate cannot reach the zero that generated it.

## Proof

Let `J` denote critical-line conjugation and `C` ordinary conjugation on multiplicity copies.  If
`q` is off the critical line, then `q != Jq`; the nonzero ordinate of every nontrivial Xi zero also
gives `q != Cq`.  Applying the same two coordinate tests after either involution proves that

\[
\{q,Jq,Cq,JCq\}
\]

has four elements.  The explicit endpoint-charge formula

\[
e(\beta+i\gamma)=
\frac{\gamma^2+\beta(1-\beta)}
{(\beta^2+\gamma^2)((1-\beta)^2+\gamma^2)}
\]

is invariant under `beta -> 1-beta` and `gamma -> -gamma`.  Hence all four charges are equal.
Every endpoint charge is nonnegative, their sum over all multiplicity copies is `c`, and finite
subsum monotonicity yields `4 e(q) <= c`.  Combining this with

\[
\frac1{1+\gamma^2}\le e(q)
\]

first gives the exact relation

\[
4\le c(1+\gamma^2).
\]

The rational estimate `c<2/43` then gives

\[
\frac4{1+\gamma^2}<\frac2{43},
\]

so `gamma^2 > 85`.

For a centered spectral point `a` and upper-half-plane test point `z`, the imaginary part of the
line-conjugate resolvent pair has sign opposite to

\[
(\operatorname{Re}z-\operatorname{Re}a)^2
+(\operatorname{Im}z)^2-(\operatorname{Im}a)^2.
\]

If `a` is on the real axis this expression is strictly positive because `Im z > 0`.  Otherwise,
the exact orbit law, `|Im a| < 1/2`, `|Re z| <= R`, and
`c * ((R+1/2)^2+1) < 4` give `|Re z-Re a| > |Im a|`, so it is again strictly positive.
Absolute summability permits pairing
and summing the atoms.  The same height comparison excludes off-line poles in the upper half of
the band; on-line poles lie on its boundary.  This proves the full source sign on the band.

Taking `R=218/25`, applying the source reflection `z -> -conj z`, translating back by
`s=1/2+iz`, and using continuity plus density of `Q+iQ` proves the stated countable criterion.

## Open core

Prove the remaining positive-height completed prime--Gamma values are accretive.  The theorem
removes the entire interval from height zero through `218/25`, all negative heights, and all
irrational test points, but does not prove the surviving source sign.

## Gates

- [x] 0 -> 1 in-progress: four-orbit source relation and one-sided RH consequence identified
- [x] 1 -> 2 fully-proven: complete orbit, height, resolvent-sign, reflection, and density proof
- [x] 2 -> 3 formalized: placeholder-free Lean modules, axiom audit, lint, and umbrella build
- [ ] 3 -> 4 publication-ready: not proposed; this is an RH bridge theorem

## Lean certificate

Principal declarations:

```text
four_mul_xiEndpointCrossCharge_le_curvature_of_offLine
four_le_curvature_mul_one_add_im_sq_of_offLine
xiZeroCopy_offLine_eightyFive_lt_im_sq
xiOffLineQuartetAccretiveBand_add_half_lt_abs_im_of_offLine
not_xiOffLineQuartetAccretiveBand_at_abs_im_of_offLine
XiEndpointOffLineQuartetAccretiveBand
xiRelativeResolventTerm_lineConj_pair_im_nonpos_offLineOrbit
continuedPrimeArchPositiveFrequencyAbove_iff_riemannHypothesis_of_offLineQuartetBand
continuedPrimeArchSourceRelativeTrace_im_nonpos_eightySeven_tenths
continuedPrimeArchSourceRelativeTrace_im_nonpos_twoHundredEighteen_twentyFifths
completedPrimeGammaGaussianRatPositiveAboveEightySevenTenths_iff_riemannHypothesis
primeArchOffLineQuartetConnesBornWittenKMSMaster
```

The three modules and the `RHTower` umbrella compile.  Formal lint passes.  `#print axioms` on the
orbit bound, height theorem, countable RH criterion, and KMS master theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Exterior diagonal consequence

The paper theorem
`../../2-fully-proven/not_new_scientific_knowledge/xi-positive-paired-diagonal-sector-collapse.md`
uses the formalized inequality

```text
R+1/2 < |im(rho)|
```

for every off-line Xi zero at an exact quartet-admissible radius `R` to localize every possible
failure of RH inside the positive-frequency exterior source domain after FE--Schwarz reflection.
There the diagonal of the positive-paired reduced Cauchy kernel is the reciprocal-square sector
observable.  Its nonnegativity alone excludes the localized pole.  Hence the quartet band is not
only a central anti-Herglotz prefix: it also proves that exterior one-point diagonal passivity is a
complete RH criterion.  The composition is currently paper-level.
