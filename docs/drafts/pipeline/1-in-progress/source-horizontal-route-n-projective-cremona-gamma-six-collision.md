# Source-horizontal Route-N projective Cremona / Gamma-six collision

- **Stage:** 1 — in progress
- **Status:** `[LEAN-PROVED CORE] [UNCONDITIONAL] [NOT RH]`
- **Date:** 2026-08-12
- **Lean modules:**
  - `formal/GaloisForLFunctions/RHTower/SourceHorizontalRouteNProjectiveCremonaInvolution.lean`
  - `formal/GaloisForLFunctions/RHTower/SourceHorizontalRouteNDeningerGammaSixCurvatureCollision.lean`

## Mathematical delta

Let `C_p=p^-1` and let `T_(p,t)=p^(-1-2|t|)` be Route N's twisted squarefree parity odds.  The
two retained horizontal orientations are not independent formulas:

```text
inward  = T_(p,t),
outward = C_p^2/T_(p,t).
```

Thus reflection is the positive Cremona involution `x ↦ C²/x`.  It reverses the exact bounded
Julia/Cayley coordinate `(x-C)/(x+C)`, is realized by opposite weights on one residue projective
clock, and has fixed point exactly `t=0`.  Route-P Weyl adjunction preserves weight, so its equality
with functional-equation duality is equivalent to the same fixed-point equation.  This closes the
N/P/R scalar and projective identification without assuming transport equality.

At the ordered prime-labelled pair `(2,3)`, multiplication retains both labels and gives

```text
C_6       = C_2 C_3 = 1/6,
inward_6  = 6^(-1-2|t|),
outward_6 = 6^(-1+2|t|).
```

The normalized inward odds are exactly Deninger's mixed reflection--Wold curvature
`(1/6)^(2|t|)`; normalized outward odds are its reciprocal.  One Gamma-six Wold step therefore
scales the exact shell carrier by the normalized Route-N inward orientation.  The signed difference
is the already source-landed marked tame reader:

```text
outward_6 - inward_6
  = C_6 · deningerGammaSixExceptionalTameReader 2 ((1+|t|)/2).
```

This is coefficient faithful and zero exactly at `t=0`.

## Heavy-conjecture loop

1. **C15-A — residue Weyl transport flips projective weight.** Failed.  Existing Route-P fracture
   theorem proves Weyl adjunction preserves the weight and agrees with the negative-weight dual
   only at center.
2. **C15-B — orientations are related by a nonlinear source polarity.** Proved.  The unique
   positive critical-product reflection is `x ↦ C²/x`; it negates the Julia/Cayley coordinate and
   is involutive.
3. **C15-C — Route N and Route P/R use the same polarity.** Proved.  Inward/outward odds are the
   marked odds of the same projective carrier at weights `±|t| log p`; Route-P adjunction/duality
   collision and scalar-orientation collision are both equivalent to `t=0`.
4. **C15-D — Gamma-six shell anomaly is independent extra force.** Failed positively.  It is
   exactly the `(2,3)` Route-N curvature after critical normalization, so combining the two cannot
   create another equation.
5. **C15-E — send signed orientation directly to Hardy vacuum.** Failed sharply.  Depth zero of
   every source-curved Poisson character is `1`, hence its reflected difference is identically
   zero for every grade.  The strongest positive survivor is grade two, where the signed difference
   is exactly the marked Gamma-six tame/Calderón reader above.

## New universal principle

Horizontal reflection is not linear transport.  It is a birational polarity on the critical-odds
hyperbola.  Permutation, unitary/Weyl adjunction, positive-cone packet exchange, and functional
equation covariance can exchange its sheets but cannot identify them.  The corpus's repeated
`same carrier, wrong transport` failures are shadows of this linear-versus-Cremona mismatch.

The source side is now stronger than a scalar receiver: completed-exponent reflection supplies an
actual anti-birational involution, Gamma-six cyclic homology supplies the physical descent anomaly,
and Route N supplies its prime-labelled projective odds.  What remains is one independent relation
forcing the grade-two tame reader to land in a killed target class.  Ordinary Hardy vacuum cannot
be that target because its depth-zero character is identically orientation-blind.

## Exact remaining producer

Construct a source-derived, coefficient-faithful landing of the grade-two marked Gamma-six tame
reader—not depth-zero Poisson evaluation—into either:

1. a uniformly admitted fixed-source event relation consumed by adaptive contiguity; or
2. a target-side strict ideal/Calderón class annihilated before scalarization.

The landing must preserve ordered labels `(2,3)`, Xi multiplicity, and both anti-birational
orientations.  Reflection covariance, Wold stationarity, projective state equality, or cyclic
descent may not be assumed: each is already formally equivalent to neutrality.

## Verification

- [x] direct Lean check of both modules
- [ ] targeted final module build
- [ ] axiom audit
- [ ] scoped forbidden-token scan
- [ ] diff check

