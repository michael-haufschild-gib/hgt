# Euler–Stokes rank-port inertia law

- **ID:** euler-stokes-rank-port-inertia
- **Stage:** 4-publication-ready
- **Type:** THEOREM — paper and Lean proofs complete; hostile audit passed
- **Manuscript:** `docs/drafts/manuscripts/euler-capacity-law/main.tex`
- **Prior local source:** `docs/drafts/manuscripts/stokes-cartan-lorentz-law/main.tex`; used only as
  the genus-zero one-port input
- **Statement:** Every geometric reading of a connected wild Stokes diagram determines a physical-rank covector lying in one dual Lorentz cone of its invariant Cartan form; after isolating that port, all local Stokes/Rees/corona energy is positive, while topology changes only the coefficient of the same rank-square defect.

## Goal

Find and prove a universal law whose genus-zero rooted-tree specialization is the Stokes–Cartan Lorentz-capacity theorem, and whose other shadows include reading invariance, Fourier/Harnad rank change, Rees monotonicity, corona reduction, vanishing-cycle positivity, and the higher-genus Euler correction. A publishable result must identify a genuinely geometric constraint beyond the classical Schur-complement/Haynsworth inertia formula.

## Gates

- [x] 0 → 1 in-progress: well-posed candidates, primary-source extraction plan, explicit falsifiers
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: unconditional Lean theorem(s), targeted `lake build` green, formal lint/axiom audit
- [x] 3 → 4 publication-ready: standalone paper plus hostile novelty and correctness review

## Candidate laws

Let `q` be the invariant Cartan/Tits form of a connected wild Stokes diagram and let `R_alpha` be the physical-rank functional in a geometric reading `alpha`.

1. **E1 — rank-cone law.** For every admissible basic reading `alpha`, `q` is positive definite on `ker R_alpha`. Equivalently, every `R_alpha` is a timelike dual covector for one Lorentz form and admits a reading-relative passive realization
   `q(x) = P_alpha(x) - lambda_alpha R_alpha(x)^2`, with `P_alpha > 0`.
2. **E2 — Euler alignment law.** On a genus-`g` curve with the same local formal type in reading `alpha`, the dimension form is
   `q_{g,alpha}(x) = q(x) - 2g R_alpha(x)^2`.
3. **E3 — universal one-time law.** E1 and E2 imply every connected admissible wild diagram in every genus has negative index at most one; Fourier/Harnad transforms move the rank covector inside the same dual time cone rather than creating a new negative direction.
4. **E3' — multiport fallback.** If E1 fails but the genus correction and genus-zero Stokes defect are independent, then
   `q_g = P - A^T Lambda_g A`
   with a canonical port space of dimension at most two, hence negative index at most two. This is mathematically weaker and publishable only if the port space has a new intrinsic microlocal interpretation.

## Abstract algebraic skeleton

For `P > 0`, a surjective port map `A : V -> W`, capacity `C_A = A P^{-1} A^T`, and symmetric defect `Lambda`, the constrained minimizer gives the exact splitting
`Q(x) = P(z) + w^T(C_A^{-1} - Lambda)w`, where `w=Ax` and `z` lies in `ker A`.
Thus all nonpositive inertia is exactly the inertia of the finite-dimensional capacity gap `C_A^{-1}-Lambda`. Series extension adds the same quadratic form to both inverse capacity and defect, leaving the gap invariant. This skeleton is classical linear algebra/network theory and is not itself the claimed novelty.

## Stronger survivor: Euler--capacity / one-port index law

**[PROVED HERE]**

The multiport fallback is unnecessary once global gluing is written on the compatible local lattice.  Let a connected genus-`g` curve have `m >= 1` marked points.  At point `a`, let `(V_a,Q_a,R_a)` be the marked one-pole Stokes quadratic space, including its ordinary type-`A` conjugacy legs.  The local one-defect theorem gives

`Q_a = P_a - lambda_a R_a^2`, with `P_a > 0`.

Write `c_a = R_a P_a^{-1} R_a^T` and `Omega_a = c_a^{-1}-lambda_a`.  The global numerical deformation lattice is the rank fibre product

`V_Sigma = { (x_a) : R_1(x_1)=...=R_m(x_m)=M }`.

Boalch's exact quasi-Hamiltonian dimension formula, compared with its `m` one-pole specializations, gives the fusion identity

`Q_Sigma = sum_a Q_a + 2(1-g-m) M^2`.

Centering every local summand at fixed common rank therefore yields the candidate headline theorem

`Q_Sigma(x) = sum_a P_a(z_a) + M^2 Omega_Sigma`,

where

`Omega_Sigma = sum_a Omega_a - 2(g+m-1)
             = chi(Sigma) + sum_a (Omega_a-2)
             = chi(Sigma) - sum_a delta_a`, where `delta_a=2-Omega_a`.

Consequences are exact: global nonpositive inertia is the sign of the single Euler--capacity scalar; negative index and nullity are at most one; inverse capacities add under fusion; each handle subtracts exactly `2` from the same common-rank gap; Rees refinements add only positive local conormal energy; corona/vanishing-cycle elimination is Schur reduction inside the positive spatial summands.  The old paper is precisely `g=0,m=1`.

This is a polarized quadratic-form refinement of the known scalar rigidity-index formulas.  Hiroe proved, under multiplicity-free or regular-semisimple hypotheses plus spectral-curve regularity assumptions, that the rigidity index of one connection equals the Euler characteristic of the normalization of its irregular spectral curve.  That theorem does not state inertia, a capacity gap, positivity on every rank kernel, fusion additivity of inverse capacities, or the marked-lattice quadratic refinement above.  These distinctions are load-bearing for novelty.

## Falsifiers

- A realized wild diagram and admissible reading with a nonzero `x in ker R_alpha` and `q(x) <= 0` kills E1.
- A realized higher-genus dimension form with two independent negative directions kills E3.
- A primary dimension formula whose handle contribution is not exactly `2g (physical rank)^2` kills E2 as stated.
- A Fourier/Harnad orbit containing rank covectors in opposite dual time cones, or a spacelike rank covector, kills the rank-cone formulation.
- If the strongest survivor is only the abstract Schur-complement identity, the route fails novelty.
- A mismatch between the quasi-Hamiltonian global dimension polynomial and `sum_a Q_a + 2(1-g-m)M^2` kills the Euler--capacity theorem.
- Failure of the local one-pole factorization after including a legal formal-monodromy marking kills the claimed arbitrary-marking scope.

## Attack

1. Extract exact rank and dimension formulas from Douçot's genus-zero diagram paper and Boalch's general-genus quasi-Hamiltonian construction.
2. Translate every admissible reading's rank into a covector on the fixed diagram lattice.
3. Use the already-proved genus-zero Lorentz law to reduce E1 to the sharp dual inequality `R_alpha^T C^{-1} R_alpha < 0` (with the appropriate nonsingular convention), or directly to positivity on `ker R_alpha` in affine boundary cases.
4. Enumerate/falsify small realized diagrams and all known basic-representation rank formulas before attempting a general proof.
5. Seek a microlocal proof: physical rank as intersection with a polarization/fiber class; positivity on its kernel from compactly supported vanishing-cycle energy; Fourier/Harnad action as a positive-cone isometry.

## Theatre checks

- Do not rename Haynsworth inertia additivity as a new theorem.
- Do not infer E1 from one preferred reading; quantify over and verify all admissible readings.
- Do not call formalization of the abstract skeleton evidence for the geometric conjecture.
- Do not claim universality beyond the precisely realized class proved from primary geometric input.
- Treat failed searches as evidence only, never proof of novelty.

## No-go closure

If E1/E2/E3 fail, prove and formalize the sharp strongest survivor: exact port dimension, classification of offending rank covectors, or a necessary-and-sufficient capacity inequality. Record an explicit realized counterexample and its geometric source.

## Log

- 2026-08-03 — promoted to in-progress after the genus-zero Lorentz-capacity paper was completed; current paper reclassified as the `dim W = 1`, genus-zero evidence case.
- 2026-08-03 — extracted Doucot's exact generic and nongeneric rank covectors from the enriched tree.  For the realized twisted triangle with edges `(6,3,4)`, both the one-pole rank `(3,2,3)` and Fourier rank `(2,1,4)` are dual-timelike (`R^T C^{-1}R=-245/86` and `-104/129` respectively), while an arbitrary positive coordinate covector is not (`e_1^T C^{-1}e_1=5/258`); physical ranks are genuinely constrained, so positivity is not a vacuous consequence of coefficient signs.
- 2026-08-03 — extracted Boalch's general-genus fusion construction and dimension formula.  Each handle contributes exactly `2 rank^2`; comparison with one-pole atoms yields the Euler--capacity formula above.  Literature searches found the scalar rigidity-index/Euler-characteristic theorem (Hiroe 2019) but no Cartan-inertia, capacity, effective-resistance, or rank-polarization theorem.
- 2026-08-03 — proved exact fusion identity and Euler-minus-capacity-defect law on paper. Added
  unit-rank variational characterization, physical-rank dual-timelike corollary, handle monotonicity,
  and connected-sum sewing. Recast prior genus-zero results as the `g=0,m=1` shadow.
- 2026-08-03 — formalized the dependent physical-rank fibre product, global quadratic form,
  Euler--capacity completion, `sigNeg <= 1`, exact Lorentz index, affine null ray, capacity-ray
  minimization, and genus-step law in `StokesEulerFusionCapacity.lean`; direct Lean check green.
- 2026-08-03 — closed full-marking composition in
  `StokesEulerFusionTypeALegs.lean`: dependent type-A increment spaces, compatible rank fibre
  product, exact positive-plus-one-rank form, and arbitrary-genus `sigNeg <= 1`; targeted build and
  axiom audit green.
