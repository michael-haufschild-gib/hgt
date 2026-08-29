# Theta cusp direct fixed-action C5 Jacobian ninth germ

- **ID:** TC-C5-JG9
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean 4)
- **Source:** Lean corpus modules `ThetaCuspFixedActionC5Jacobian`,
  `ThetaCuspFixedActionC5JacobianSeamOrientation`, and
  `PolynomialODEJetC5FixedActionSeamClosure`; formalized in
  `FixedActionC5JacobianGermClosure`, `FixedActionC5JacobianGermAnalyticClosure`, and
  `ThetaCuspFixedActionC5JacobianGermClosure`
- **Statement:** The division-free centre linearization of the literal direct fixed-action C5
  Jacobian has all jets below order nine equal to zero and ninth jet
  `20160 * thetaCuspC5FixedActionSeamLogValue > 0`.

## Goal

Supply first genuine analytic orientation datum for direct C5 transport along reflected-action
level sets. This is local input for direct-Jacobian orientation, then reflection/Ptolemy wall
control, arbitrary finite-packet positivity, CLG/TTF or Weil positivity, and the corpus RH
endpoint. Claim does not infer RH from a finite jet: global orientation and packet propagation
remain open.

## Gates

- [x] 0 → 1  in-progress: literal source, exact determinant attack, RH passport fixed
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open paper dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build`, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper and full novelty audit

## Exact statement

Put

`q(t) = 2(L(0)-L(t))`, `r(t)=exp(q(t))-1`,
`a=q'`, `b=q''`, `c=q'''`, `d=q''''`, `A=-L''(0)`, and `h=b-2A`.

Define the division-free partial numerators

```
N₁ = -(9/4)t r -(5/2)t² a r - 2t²a,
N₂ =  (5/4)t² r,
Nₑ = -(9/4)a r +(5/2)t(b-a²)r - 2ta²,
G  = N₁(ac-hb) + N₂(ad-hc) - hNₑ.
```

For every `t>0`, if `J(u,t)` is corpus definition
`thetaCuspReflectedActionC5FixedActionJacobian`, then

`G(t) = r(t)² * deriv (fun u => J(u,t)) 0`.

Moreover

`G⁽ⁿ⁾(0)=0` for `n<9`, and

`G⁽⁹⁾(0)=20160(A²D-5ABC+4B³-18A³C+36A²B²)>0`,

where `B=-L⁽⁴⁾(0)`, `C=-L⁽⁶⁾(0)`, and `D=-L⁽⁸⁾(0)`.
Consequently `G(t)>0`, hence `deriv (fun u => J(u,t)) 0>0`, on some punctured right
neighborhood of the self-dual displacement seam.

## Proof `[PROVED HERE]`

At `u=0`, reflection gives `qᵤ=aᵤ=bᵤ=0`. Differentiating
`J=Cᵤ qₜ-Cₜ qᵤ` once in `u` gives

`Jᵤ = a(Paction*h + P₁*c + P₂*d) - h(Pₑ + Paction*a + P₁*b + P₂*c)`.

The two `Paction*a*h` terms cancel identically. Multiplication by `r²` clears every reciprocal
radius and yields exactly displayed `G`.

For the jet calculation, use derivative jets, not normalized Taylor coefficients. Leibniz is
binomial convolution and `e=exp(q)` obeys `e⁽ⁿ⁺¹⁾=(e*a)⁽ⁿ⁾`. Reflection gives

`q₀=q₁=q₃=q₅=q₇=q₉=0`,
`q₂=2A`, `q₄=2B`, `q₆=2C`, `q₈=2D`.

Substitution into the three numerator products cancels every jet below nine. At order nine the
six surviving monomials have coefficients

`20160, -100800, 80640, -362880, 725760`,

which factor as `20160(A²D-5ABC+4B³-18A³C+36A²B²)`.
`thetaCuspC5FixedActionSeamLogValue_pos` proves the final factor positive for the literal theta
source. Smooth Taylor remainder then gives the punctured right-neighborhood sign.

## RH passport

`TC-C5-JG9`
→ global positivity of the same direct fixed-action centre Jacobian
→ transport from C5 reflection centres to the reflection-odd rank-four/Ptolemy wall
→ arbitrary finite packets and cofinal no-escape
→ CLG/TTF or Weil polarization nonnegativity
→ `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` or
`riemannHypothesis_iff_xiWeilPolarization_nonneg`
→ RH.

Exact next burden: replace local Taylor orientation by global `u>0,t>0` direct-Jacobian
orientation without assuming any RH-equivalent positivity premise.

## Lean realization

- `HTGeometry.c5FixedActionRegularizedCenterJet_elimination`: universal order-nine jet
  cancellation and exact coefficient.
- `RHTower.thetaCuspC5FixedActionJacobianCenterRegularizedGerm_eq`: equality to squared-radius
  regularization of actual direct C5 Jacobian centre derivative for every `t>0`.
- `RHTower.eventually_deriv_thetaCuspReflectedActionC5FixedActionJacobian_center_pos`: unconditional
  strict direct-J orientation on a punctured right seam neighbourhood.
- `RHTower.eventually_right_thetaCuspReflectedActionC5FixedActionJacobian_pos`: for every sufficiently
  small positive displacement, actual direct-J is strictly positive throughout a punctured right
  neighbourhood of the reflection centre.
- Direct Lean checks and targeted builds pass. Axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`; no added axioms.

## Novelty and hostile audit

- Corpus search found named direct Jacobian and source-positive seam invariant, but no Taylor-germ
  theorem identifying them.
- Exact web searches through 2026-08-29 found no matching fixed-action C5 Jacobian germ. Closest
  current result is Planat–Solé, *Second-Level Concavity of the Riemann Ξ Kernel*,
  arXiv:2608.19160, which concerns a different Laguerre/log-concavity expression and states no RH
  consequence.
- Reverse-orientation velocity minor does not kill this route: its term cancels from direct
  determinant linearization, and the surviving ninth jet is strictly positive.
- Verdict: `SURVIVES PRELIMINARY ATTACK`; publication novelty remains subject to expert review.

## Log

- 2026-08-29 — corpus-derived conjecture; determinant cancellation and complete paper proof.
- 2026-08-29 — formalized universal jet, analytic realization, actual Jacobian identity, and local
  strict direct-J orientation; wired HTGeometry and RHTower umbrellas.
- 2026-08-29 — transported positive centre derivative to an actual fibrewise direct-J chamber.
  Uniform two-variable control as `t → 0`, compact middle positivity, and first-atom tail remain.
