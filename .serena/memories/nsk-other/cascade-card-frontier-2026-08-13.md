# universal-first-order-entire-cascade-unit-cost — Lean frontier (2026-08-13 evening)

Card target: transcendental entire f_1..f_n, each P_k(z,f_k,f_k')=0 ⇒ ord_DA(f_n∘…∘f_1) = n.
Assembly point: CascadeExactOrderUnconditional.exactDifferentialOrder_entireCascade_of_elimination_pos
— only `helim` (order-m DA relation ⇒ nonzero polynomial state relation) remains, for the general
algebraic first-order law. Closed instances: exp tower, poly-coeff, linear, rational
(RatCascadeOrder.exactDifferentialOrder_ratCascade).

## ITEM 2 CLOSED 2026-08-13 (this session), card log part 13 appended
New modules (umbrella-wired, built, axiom-clean):
- IntegralGeneratorDerivationClearing.lean — aeval_derivative_mul_deriv_mem_adjoin (clearing at an
  abstract generator; generalizes AdjoinRootDerivationIntegral).
- PlaceDerivationValuationDrop.lean — valuation_mul_fun_le_exp_of_mem_pow /
  valuation_mul_fun_algebraMap_le / valuation_mul_fun_le / valuation_fun_le_of_not_mem_pow
  (+ Derivation wrappers valuation_mul_deriv_le, valuation_deriv_le_of_not_mem_pow).
  IMPORTANT LEAN LESSON: statements are in PLAIN-FUNCTION form (D : K → K with hadd/hmul
  hypotheses) — stating over `Derivation A K K` made every concrete application defeq-identify two
  transitive instance paths (CommSemiring.toSemiring∘Semifield vs DivisionSemiring.toSemiring∘…)
  through the FractionRing/OreLocalization tower → whnf timeout even at 8M heartbeats. Plain
  functions remove the seam. Diagnose such cases with a partial-application probe
  (`have h := lemma arg1 arg2`) + `set_option pp.explicit true` + `set_option diagnostics true`.
- AlgebraicCascadeDifferentDrop.lean — exists_monogenic_clearing (closure monogenic + q'(α) ≠ 0 +
  clearing at every place), capstones exists_pos_valuation_algLaw_uDeriv_le (∀ Q ∃ e ≥ 1 drop ≤ e)
  and valuation_algLaw_uDeriv_le_of_normalizedFactor (drop ≤ KD ramification multiplicity e — tame
  bound). Also: charZero_residueField_topInt (+ quotient-form alias instance — TC needed both),
  module_finite_algCascadeInt (IsIntegralClosure.finite), isTorsionFree
  (Module.isTorsionFree_iff_algebraMap_injective), maxExt ≠ ⊥, FiniteDimensional residue quotient
  (Module.Finite.of_surjective mkQ + of_restrictScalars_finite).
  File uses set_option maxHeartbeats/synthInstance.maxHeartbeats 1000000 file-wide (phase 2).

## REMAINING: item 3 only (then assembly)
1. Restate the peel (terminal-linear Bell induction: TerminalPowerCascadeInduction,
   ColumnPencilDeterminant, PeelStep/Invariant/LimitVector/Induction family) over the extended
   place datum, using the drop bound at ramified places (one u-degree per differentiation).
2. Reduction I analytic selection: which place the cascade follows — Wiman layer exists
   (WimanPlaceRoot.exists_radius_wiman_place, TopSymbolWimanPlace.exists_radius_norm_topSymbol_le,
   WimanValironSelection/SmallDefect/..., EliminationOrderDescent GradedAlong charts,
   TranscendentalEntireOrderOne for Strelitz ρ>0 input).
3. Produce general helim; assemble exactDifferentialOrder_entireCascade (no elimination
   hypothesis); wire; build; axiom-audit; fix stale card notes (gate box ~line 465 'observability
   on a general cascade', superseded Lean-status block); promote card to stage 3
   (git mv to 3-formalized/new_scientific_knowledge/other/).
Template for the peel: RatCascadeLaw/RatCascadeOrder (cleared-model route,
not_differentiallyAlgebraicOfOrder_of_clearedModel) — the general case cannot clear to polynomials,
so the elimination must run through the valuation flag (nested order X_n >> … >> X_1 >> z), Bell
identities J_r(X_r) = ±X_r^(r-1) J_{r-1}(A) (derivationIterateOutputJacobian_det*), and the
nonzero nested initial coefficient (card Reduction III §Bell).

## Process notes
Other agents build/commit concurrently (my new modules got committed + umbrella-wired by them).
Machine often saturated (18+ lean processes) — one own process, expect slow elaboration.

## Item 3 decomposition (designed 2026-08-13, after reading CommonClearedJets.lean)
Engine (rational case): CommonClearedJets.not_differentiallyAlgebraicOfOrder_of_clearedModel takes
(δ, δp, Dtot) cleared law both analytic (evalAt along cascade) and model-side, nonvanishing witness
hind, and **hindep : AlgebraicIndependent ℂ (z, δ^0(X_N), …, δ^m(X_N)) in CascadeField** ⇒
¬DA of order m. Rational case discharged hindep via output-determinant
(algebraicIndependent_cons_of_output, RatAffineFam.output_det_ne_zero).
General algebraic case sub-items:
(3a) Extension transfer layer: generalize ClearedJets/CommonClearedJets from CascadeField to
     AlgCascadeField p — the analytic evaluation of extension elements along the cascade branch
     (root p ↦ deriv of the state; well-defined since P(z,F_k,F_k')≡0). Work in cleared/polynomial
     form as the rational case does (never evaluate at denominator zeros). AdjoinRoot elements =
     polynomials in root of degree < deg p over CascadeField; evaluation = evalAt on coefficients +
     branch value at the root.
(3b) hindep over the extension: AlgebraicIndependent ℂ (z, jets of fx N under algLaw p (uDeriv-style
     law)) — via the valuation flag (nested order X_n ≫ … ≫ X_1 ≫ z), Bell induction
     (derivationIterateOutputJacobian_det*, TerminalPowerCascadeInduction), and the item-2 drop
     bound (AlgebraicCascadeDifferentDrop capstones) controlling that differentiation costs ≤ one
     u-degree at each (possibly ramified) place. Nested initial coefficient nonzero = card
     Reduction III §Bell argument.
(3c) Reduction I: analytic selection of the place/branch the cascade follows (Wiman layer:
     exists_radius_wiman_place etc.) — enters as the hlawA analog: the cleared law holds
     analytically along the selected branch, and the branch has the positive Wiman charge q>0
     (Strelitz ρ>0, TranscendentalEntireOrderOne) that Reduction II/III need for nonzero exponents.
Then: general helim ⇒ exactDifferentialOrder_entireCascade via
exactDifferentialOrder_entireCascade_of_elimination_pos; wire, build, axiom-audit, fix stale card
notes, promote card.

## Key finding (end of 2026-08-13 session): 3b engine already generic
TerminalPowerCascadeInduction is stated over ANY `R` [CommRing R] [Algebra ℂ R] — capstone
`algebraicIndependent_cascadeOutput_of_power`: triangularity (coordinate derivation P_k kills all
jets of lower outputs) + power diagonal (Y_{k+1} = C_k X_k^{q_k}, q_k ≠ 0) ⇒ the output jets are
algebraically independent. It applies verbatim on AlgCascadeField. So 3b reduces to:
(A) the graded/initial-coefficient layer at the composite valuation flag — extract initials, prove
    the Bell steps act on initials as the model says, and use item-2 drop bounds to show lower
    terms cannot cancel the nested leading coefficient (card Reduction III's exact argument);
(B) nonzero exponents q_k from the Wiman charge (Reduction I/II analytic supply, mostly built);
(C) 3a extension transfer mirroring ClearedJets/CommonClearedJets with the branch relation
    P(z, F_k, F_k') ≡ 0 replacing rational clearing (engine consumes:
    hindep over the extension + cleared law along the analytic branch).
Next session: read PeelStep/PeelInvariant/PeelLimitVector/PeelInduction + EliminationOrderDescent
(GradedAlong charts) and design module (A) — likely `AlgebraicCascadeInitialFlag.lean`.

## Item 3 module plan (after reading PeelInvariant/PeelEntry, 2026-08-13 late)
Rational peel architecture to mirror: logJetJacobian = jetOrbitMatrix of border row (logBorder =
logFactor Q_l'/Q_l up to level, 0 above); invariants PeelHyp/BorderShape (leading term = log factor,
corrections TopDegLE ≤ −3); det_jetOrbitMatrix_ne_zero_of_peelHyp → logJetJacobian_det_ne_zero →
output_det_ne_zero → algebraicIndependent_cons_of_output → cleared-model engine.
General analog (planned modules):
A1 PlaceGrading.lean — PlaceDegLE Q γ f := v_Q f ≤ γ (γ : ℤᵐ⁰) on AlgCascadeField; mul/add/inv
   lemmas; derivation-drop lemma = item-2 capstones; PlaceFree (v = 1).
A2 AlgebraicBorderShape.lean — border rows at the composite flag: leading initial
   in_(X_{k-1})A_k^0 = c_k A_{k-1}^0 X_{k-1}^{q_{k-1}} (q from ramification/Wiman), corrections of
   strictly smaller place-valuation; the Bell step preserves the shape (uses generic
   TerminalPowerCascadeInduction Jacobian identities + item-2 drop).
A3 AlgebraicPeelInduction.lean — flag induction, nested initial coefficient nonzero, determinant
   nonzero, algebraic independence of extension jets (feeds hindep).
A4 Wiman supply — Reduction I/II: exists_radius_wiman_place ⇒ branch initial exponent q = ρ > 0
   (TranscendentalEntireOrderOne for Strelitz), per layer.
A5 Extension transfer (3a: ClearedJets analog with branch relation P(z,F,F')≡0) + general helim +
   exactDifferentialOrder_entireCascade assembly.

## A1 DONE (2026-08-13, same session): PlaceGrading.lean
Wired, built, axiom-clean. Vocabulary: PlaceDegLE v γ f (v_Q f ≤ γ, γ : ℤᵐ⁰), PlaceFree v f
(v_Q f = 1); closure lemmas add/sub/neg/mul/pow/mono/div_placeFree; PlaceDegLE.fun_deriv =
item-2 drop in grading form; valuation_add_of_lt (leading-term visibility, via mathlib
Valuation.map_add_eq_of_lt_left).
## A2 design decisions (made, not yet implemented)
- One simple extension suffices for the whole cascade branch data: char 0 ⇒ primitive element for
  the compositum of all layers' branches; AlgCascadeField p model is adequate; flag = family of
  places (Q_m over topInt m's maximal ideal) in the SAME field, ramifications e_m.
- Avoid iterated residue fields: mirror rational BorderShape — f = leadingTerm + r with
  v_{Q_m}(r) < v_{Q_m}(leadingTerm), leadingTerm an explicit product c·A⁰·(coordinate power);
  visibility through Bell steps via valuation_add_of_lt; derivation costs via PlaceDegLE.fun_deriv
  with e_m from valuation_algLaw_uDeriv_le_of_normalizedFactor.
- Next concrete step: A2 AlgebraicBorderShape.lean — define the border-row predicate at one place,
  prove the one-step Bell reduction preserves it (leading term transforms by the model law,
  corrections stay strictly smaller), then A3 flag induction feeding
  TerminalPowerCascadeInduction.algebraicIndependent_cascadeOutput_of_power.

## A2/A3 architecture resolved (end of session)
No lexicographic composite valuation and no iterated residue fields needed: mirror the PEEL —
one place per level. At level r, at place Q_r (over coordinate r's degree at infinity):
entries of the output-jet Jacobian J_r have border shape at Q_r; the Bell row-reduction
(exact generic identities derivationIterateOutputJacobian_det*) gives
det J_r = ±(unit·X_r-power)·det J_{r−1}(next-level outputs) + correction of strictly smaller
Q_r-valuation; valuation_add_of_lt makes det J_r ≠ 0 descend from det J_{r−1} ≠ 0.
So A2 = per-level border-shape predicate + one-step statement (PeelStep skeleton with
TopDegLE→PlaceDegLE swap, derivation cost from PlaceDegLE.fun_deriv with e_r =
KD multiplicity via valuation_algLaw_uDeriv_le_of_normalizedFactor);
A3 = induction down the levels (PeelInduction skeleton) ending at the one-variable base
(∂(c A₁ X₁^{q₁})/∂X₁ ≠ 0). Then hindep for the engine, then A4 (Wiman q_r > 0 supply) and A5
(extension ClearedJets transfer + assembly).
