# PW-B quadratic half-line receiver cone

- **ID:** PW-QHC
- **Stage:** 3-formalized
- **Type:** COMPLETE SEMIALGEBRAIC RECEIVER CLASSIFICATION
- **Parent:** PW-SM3 / PW-B
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekQuadraticHalfLineReceiverCone`
- **Frontier-map policy:** read only

## Result

For `P(x)=a x²+b x+c`, Lean proves that `P(x)>0` for every `x>1` exactly in
the union of four semialgebraic chambers:

1. `a>0`, `b≥-2a`, and `P(1)≥0`;
2. `a>0`, `b<-2a`, and `b²<4ac`;
3. `a=0`, `b>0`, and `P(1)≥0`;
4. `a=0`, `b=0`, and `c>0`.

Instantiating `(a,b,c)` with the three PW signed matrix moments
`(m₀,m₁,m₂)` defines the complete **uniform half-line receiver cone**.
Every actual Xi divisor satisfies `C(ρ)>1`.  Therefore, for every finite signed
matrix in this cone,

`CrossGradeEnergy(M,ρ)=0 ↔ Re(ρ)=1/2`,

and universal vanishing on Xi support is exactly RH.

This cone strictly concerns root exclusion on the full physical coordinate
half-line.  A matrix outside it may still avoid the actual (unknown) set of Xi
coordinates, but no source-independent half-line guarantee remains.

## Paper proof

Necessity of `a≥0` follows by dividing `P(x)` by `x²` along `x=n+1` and taking
the limit; when `a=0`, division by `x` similarly forces `b≥0`.  Positivity on
the open half-line forces `P(1)≥0` by the right-limit `x→1+`.

If `a>0` and the vertex lies at or left of one (`b≥-2a`),

`P(x)-P(1)=(x-1)(a(x+1)+b)>0`

for `x>1`, so `P(1)≥0` is necessary and sufficient.  If the vertex lies inside
the half-line (`b<-2a`), evaluation at `-b/(2a)` and

`4aP(x)=(2ax+b)²+(4ac-b²)`

show strict positivity is equivalent to `b²<4ac`.  The linear and constant
cases give chambers 3 and 4.  PW-SM3 then identifies `P` with the signed-matrix
residual polynomial.  Open-strip real part and nonzero Xi height give
`C(ρ)=1+Re(ρ)(1-Re(ρ))+Im(ρ)²>1`; the wall-union-root theorem reduces the
energy zero locus to the wall.

Dependency-closed; no analytic or asymptotic premise remains.

## Lean theorems

- `quadratic_leading_nonneg_of_pos_on_one`
- `quadratic_linear_nonneg_of_pos_on_one`
- `quadratic_boundary_nonneg_of_pos_on_one`
- `quadratic_pos_on_one_iff`
- `schwarzschildParikhWilczekSignedMatrixReceiverCone_iff`
- `schwarzschildParikhWilczekBorelSpectralCoordinate_gt_one`
- `schwarzschildParikhWilczekSignedMatrixResidualPolynomial_pos`
- `schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff_of_receiverCone`
- `riemannHypothesis_iff_schwarzschildParikhWilczekSignedMatrixCrossGradeEnergy_zero`

## Closed burden and positive survivor

PW-SM3 reduced every finite signed matrix to a quadratic root problem.  PW-QHC
now closes that problem uniformly: the exact acceptable moment set is four
explicit chambers.  Source construction no longer needs entrywise positivity;
it need only prove its three moments enter this larger cone.

**Positive survivor.** A finite signed PW source is a valid exact RH receiver
whenever its moment triple satisfies one of the four unconditional chambers.
Remaining producer burden is now precise: derive such a triple from literal
cross-shell/orbit dynamics without assuming zero placement.

## Novelty audit (through 2026-08-27)

Mandatory corpus search found a real-root discriminant lemma but no strict
quadratic half-line iff or PW moment-cone theorem.  Primary-source search covered
the original Parikh--Wilczek recoil law
([arXiv:hep-th/9907001](https://arxiv.org/abs/hep-th/9907001)), later tunneling
correlation analysis ([arXiv:1406.3635](https://arxiv.org/abs/1406.3635)), and
higher-curvature successive-emission analysis
([arXiv:1703.10760](https://arxiv.org/abs/1703.10760)).  No source found the
Borel three-moment reduction or its four-chamber half-line receiver cone.

Novelty priority remains provisional pending expert/database review; theorems
are unconditional and formally checked.

## Verification

- Direct `lake env lean` check: passed.
- Targeted module build: passed.
- Axiom audit: all nine exported theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Umbrella import: wired; full umbrella build intentionally not run.
