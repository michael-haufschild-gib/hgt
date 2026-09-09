# Actual unipotent blocks reduced to original current periods

Status: dependency-closed paper proof and complete Lean audit passed.
RH remains open.
Frontier map is read-only.

## Exact source result

Put n=N+1, let F be the complete original congruence Maass source, D=||F||²,
and m its full finite-group mean. For a positive regulator e, put r=√(D+e²).
Define the original horizontal current density

    H_e = (pairEnergy₁ + phaseCurrent₁² + e² directionalEnergy₁) / r³.

At height y>0 define full one-period integrals

    R_e(y)=∫₀¹ 1/r(x+iy) dx,
    E_e(y)=∫₀¹ H_e(x+iy) dx,
    C_e(y)=R_e(y) E_e(y).

Every component, pair current, total phase current and regulator-gradient
term is retained. For z in the upper half-plane write y'=Im(S⁻¹z). Then

    D(z) ≤ |Deck N| |m(z)|²
      + (4/3) N(2N+1) (D(z)+e²) [C_e(Im z)+C_e(y')].

In particular, whenever D(z)>0, m(z)=0 and e²≤D(z),

    1 ≤ (8/3) N(2N+1) [C_e(Im z)+C_e(y')].

These statements make no assumption about the original common-zero locus.
They require no uniform bound on R_e, nor any spectral-gap hypothesis.

## Dependency-closed proof

1. The actual upper integer matrix U₊(j) is T^j. Direct matrix algebra gives
   U₋(j)=S U₊(−j) S⁻¹. Augmented normalized components (e,F)/r transform by
   the original finite quotient permutation, which fixes the added coordinate.
   Simultaneously transforming two endpoints therefore preserves their
   complete squared chord. Each lower chord is exactly an upper chord at S⁻¹z.

2. Original density and regulated radius are invariant under integral modular
   action. Multiplying the augmented chord by r(z)² reconstructs the literal
   original displacement energy exactly. The added coordinate cancels from
   the endpoint difference. This identity holds at common zeros.

3. Existing source C² regularity supplies every FTC and integrability input.
   Weighted Cauchy gives the exact retained cost for each signed horizontal
   path: squared augmented chord ≤ (∫1/r)(∫H_e). The original pair/phase
   identity proves H_e=directionalRemainder₁/r, including the e² gradient term.
   Inversion supplies the signed horizontal path for each lower motion.

4. Sum these costs over every j in ℤ/nℤ using the actual integer j.val and
   normalization 1/(2n). This defines blockPathCost K_e(z). The previous
   complete finite-group comparison and exact block energy give

       centered variance ≤ 16 r(z)² K_e(z),
       D(z) ≤ |Deck N||m(z)|² + 16 r(z)² K_e(z).

5. T has identity complex differential. Literal modular derivative transport
   permutes all source coordinates and preserves horizontal derivative
   energy, pair/phase contributions and regulated radius. Thus both 1/r and
   H_e have period one. Their integral over any period has the same value,
   independent of the starting point. Over signed integer length j, each
   integral is multiplied by j. Their product is exactly j² C_e(y).

6. Consequently

       K_e(z)=M_N [C_e(Im z)+C_e(Im(S⁻¹z))],
       M_N=(2n)⁻¹ Σ_{j=0}^{n−1} j²=N(2N+1)/12.

   The squared-sum formula is proved by induction and ring algebra. There
   is no numerical experiment, external certificate or computational oracle.
   Substitution proves the full density estimate. If e²≤D and D>0, then
   D/(D+e²)≥1/2, giving the stated lower requirement on the two period costs.

## What this changes and what remains

The complete block comparison is now connected to literal original currents
through actual paths; no missing differential or endpoint identification is
hidden inside a receiver premise. The cost is exactly reduced to two heights.
The finite-group coefficient 16 remains uniform, while this specific
geometric comparison carries N(2N+1)/12. The formula does not assert that
optimal constants or actual source costs diverge as the source/level varies.

The resistance factors remain source-dependent and can deteriorate during
regulator removal. A lower bound on their products with line integrals does
not by itself give a lower bound on unweighted quotient-area current mass.
The invariant mean, original nodal residual, full phase/pair currents and
measure must survive that next step. The quarter inequality and independent
full-Xi spectral occurrence are both still open. No route is retired here.

## Corpus discovery

Broad OR searches, uncapped per module and with full result retrieval:

- Horocycle/unipotent/matrix coefficient/spectral gap/uncertainty: 764 rows,
  258 modules, `/tmp/sqb16_horocycle_broad.json`.
- Translation difference/derivative energy/path energy/Poincare inequality/
  uncertainty principle: 118 rows, 46 modules, `/tmp/sqb16_energy_broad.json`.
- Poincare/transport/coarea/capacity/oscillation: 12,339 rows, 2,711 modules,
  `/tmp/sqb16_transport_broad.json`.
- Mautner/complementary/principalSeries/property tau/property T/Kloosterman/
  Kuznetsov: 1,999 rows, 640 modules, `/tmp/sqb16_representation_broad.json`.

Counts describe discovery metadata, not proof inspections. Inspected sources
included actual Maass Fourier modes, cyclic automorphic representation,
weighted chord/resistance estimates, source/current transport and pair/phase
identities. Mathlib's periodic interval-integral laws supply exact signed
period scaling. No new representation-theoretic exclusion was inferred from
search matches or from the existing algebraic cyclic representation.

## Lean and audit

`GaloisForLFunctions/RHTower/SelbergMaassUnipotentPaths.lean` contains 43 public
definitions/theorems in namespace
`GaloisForLFunctions.RHTower.SelbergMaassUnipotentPaths`.

Main results: `displacementEnergy_eq_radius_sq_mul_augmented_chord`,
`blockEnergy_le_radius_sq_mul_pathCost`, `pathEnergy_eq_current_integral`,
`horizontalCost_integer`, `parameterMoment_eq`,
`blockPathCost_eq_two_periods`, `density_le_mean_add_two_periods`,
`two_period_cost_lower_of_mean_zero`.

Complete `/tmp/sqb16_paths.lean` scratch and final source checks passed
without warnings. Sole-target final build passed; preflight and final build
logs identify only the new leaf as compiled. No full or umbrella build ran.
Existing cached EvenL2LogUnitary informational output was replayed.
All 43 declarations have checked axiom inventories containing only
`propext`, `Classical.choice`, and `Quot.sound`. All 43 are indexed exactly
once, and the module is imported once in the RHTower umbrella. Repository
formal lint passed with existing large-file warnings. No owned Lean/Lake
process remains. No frontier-map edits were made; peer work was preserved.

Logs: `/tmp/sqb16_paths_scratch.log`, `/tmp/sqb16_paths_source.log`,
`/tmp/sqb16_paths_preflight.log`, `/tmp/sqb16_paths_build.log`,
`/tmp/sqb16_axioms.lean`, `/tmp/sqb16_axioms.log`,
`/tmp/sqb16_audit_names.txt`, `/tmp/sqb16_index.log`, `/tmp/sqb16_lint.log`.
