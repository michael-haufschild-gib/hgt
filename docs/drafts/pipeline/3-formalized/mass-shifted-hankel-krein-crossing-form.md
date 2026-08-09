# Mass-shifted Hankel Krein crossing form

- **ID:** `mass-shifted-hankel-krein-crossing-form`
- **Status:** Formalized in Lean 4
- **Route:** mass-shifted spectral face, §9.3 exact open core
- **Novelty:** `[NOVELTY UNVERIFIED]`

## Conjecture loop

### K1 — Source-conditioned extension is a Krein null-cone slope

Let `L_s` be the moment functional, `[p,q]_s=L_s(pq)`, and let `P` be the monic null
polynomial of a singular `(n+1)`-Hankel face.  Then

\[
 [P,P]_s=0,
 \qquad
 R_s(P)=[P,XP]_s.
\]

Thus the affine extension coordinate is the crossing form of multiplication by `X` on a
lightlike vector.  The missing source theorem is not ordinary positivity; it is positive Krein
type on the completed-Xi incidence cone.

**Paper proof.** Kernel incidence makes `P` orthogonal to every polynomial of degree at most `n`,
including itself.  The established shifted-square identity gives
`R_s(P)=L_s(X P^2)=[P,XP]_s` by commutativity.  No analytic or zero-location premise enters.

### K2 — Local sector geometry should orient the crossing

**Failed.** `mass-shifted-tied-power-sector-orientation-no-go` supplies two exact narrow-sector,
endpoint-radius, conjugation-stable tied-power sources with the same lightlike face and opposite
crossing slopes.  Krein null-cone orientation is extra global data.

### K3 — Completed-source incidence may orient the Krein slope

For shifted Xi moments, the same crossing form equals the monic remainder, the first-unseen
source/atomic tangent defect up to its universal factor, the forward-minus-backward Christoffel
port imbalance divided by four, and the projective prime--Gamma source imbalance.  Proving strict
positive Krein type only on actual completed-Xi null lines would close the first-crossing route.

This is current open core.  Required input must be global Euler--Gamma coherence; separate local
spectral, sector, and transport marginals are formally ruled out.

### K4 — A positive heat or Euler--Gamma carrier should orient the crossing

**Failed.** The corpus's strict von-Mangoldt--Gamma Hankel law occupies a different bivariate
Hausdorff row. Its raw source positivity does not pass through the factorial normalization used by
the shifted-Xi heat resolvent; `VonMangoldtGammaFactorialNormalizationNoGo` already proves failure
at the first raw trace block.

The stronger exact countermodel in
`mass-shifted-factorial-positive-carrier-orientation-no-go` has two strictly positive two-atom
carriers with the same factorially normalized singular face and opposite crossings `7/24` and
`-1/12`. Therefore even pointwise carrier positivity, by itself, cannot prove K3.

### K5 — Crossing is the first surviving factorial-Volterra rung

**Proved.** For

`F_r(t)=Σ_j c_j t^(r+j)/(r+j)!`,

kernel incidence annihilates the integrals of `F_0,...,F_n` against the Xi heat-resolvent carrier,
and

`[P_c,XP_c]_y = c_n⁻¹ ∫ F_(n+1)(t) exp(-yt) H_Xi(t) dt`.

This is the sharp positive survivor of K4. The missing source theorem must orient the first
non-annihilated Volterra rung conditional on the whole null flag and completed Euler--Gamma
incidence; neither raw carrier positivity nor an unrelated Krein Gram can do so.

### K6 — Completed-source scalar budgets may orient the rung

**Failed.** The multiplicity-three clouds in
`mass-shifted-tied-power-global-budget-orientation-no-go` satisfy simultaneously the strict
`85/84` sector, `2/41` radius, exact corpus zeroth-moment window, first-moment upper bound, global
orientation-energy cap, conjugation symmetry, tied-power transport, and one common positive
singular face. Their crossings still have opposite signs.

This kills a scalar-budget synthesis of K3. The global input must be mixed: it must couple the
Euler--Gamma source to the particular null polynomial or factorial-Volterra flag. Separate bounds
on source mass, first trace, and transverse energy cannot orient the affine extension class.

## Lean targets

- `formal/GaloisForLFunctions/HTGeometry/FiniteHankelBoundaryKreinCrossing.lean`
  proves `HTGeometry.finiteHankelBoundaryNullSelf_eq_zero`,
  `HTGeometry.finiteHankelBoundaryNullCrossingForm_eq_monicRemainder`, and
  `HTGeometry.finiteHankelBoundary_kreinCrossingClass`.
- `formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryKreinCrossing.lean`
  proves the shifted-Xi null, crossing, completed-source, projective-dominance, and first-crossing
  specializations, plus the exact factorial-Volterra null-flag/next-rung identity.
- `formal/GaloisForLFunctions/HTGeometry/FactorialPositiveCarrierOrientationNoGo.lean`
  proves that two strictly positive carriers can share one factorially normalized singular face
  while carrying opposite Krein orientations. All modules are wired into their theorem-area
  umbrellas.
- `formal/GaloisForLFunctions/HTGeometry/TiedPowerGlobalBudgetOrientationNoGo.lean`
  proves that exact central Xi scalar windows and orientation-energy budget remain compatible with
  opposite crossings on one endpoint-sized tied-power face.

## Status note

This closes K1, K5, and the exact reduction in K3, not the source sign. RH still requires proving
strict positive crossing type on every admissible completed-Xi singular null line. K2 and K4 prove
this cannot follow from isolated local marginals, exact transport, or positivity of a carrier before
factorial normalization. K6 further rules out repairing those failures by adjoining the known
central scalar moment and transverse-energy budgets.
