# universal-first-order-entire-cascade-unit-cost — Lean frontier (2026-08-13, session 2 state)

Card target: transcendental entire f_1..f_n, each P_k(z,f_k,f_k')=0 ⇒ ord_DA(f_n∘…∘f_1) = n.
Assembly point: CascadeExactOrderUnconditional.exactDifferentialOrder_entireCascade_of_elimination_pos
— only `helim` (order-m relation ⇒ polynomial state relation) remains for the general algebraic case.
Closed instances: exp tower, poly-coeff, linear, rational (RatCascadeOrder.exactDifferentialOrder_ratCascade).

## NEW THIS SESSION (2026-08-13), both `lake env lean`-clean, NOT yet umbrella-wired:
1. `HTGeometry/IntegralGeneratorDerivationClearing.lean` —
   `aeval_derivative_mul_deriv_mem_adjoin`: for S ⊆ K subring D-stable, L a K-algebra, D' extending D,
   α ∈ L with annihilator q (coeffs in S): q'(α)·D'f ∈ adjoin S {α} for f ∈ adjoin S {α}.
   Also `aeval_mem_adjoin_singleton`, `algebraMap_subring_apply`. (Generalizes
   AdjoinRootDerivationIntegral from AdjoinRoot.root to any generator — needed for the monogenic
   generator of the full integral closure.)
2. `HTGeometry/PlaceDerivationValuationDrop.lean` —
   `valuation_mul_deriv_le_exp_of_mem_pow` (ideal-power induction via Submodule.mul_induction_on),
   `valuation_mul_deriv_algebraMap_le`, `valuation_mul_deriv_le` (fraction field:
   v(c·Df) ≤ v(f)·exp 1), `valuation_deriv_le_of_not_mem_pow` (c ∉ Qᵉ ⇒ v(Df) ≤ v(f)·exp e).
   Abstract over any Dedekind R, fraction field K, HeightOneSpectrum v, Derivation A K K.
   ℤᵐ⁰ uses WithZero.exp; `ring` DOES NOT work in ℤᵐ⁰ — use mul_comm/mul_left_comm/mul_assoc rewrites;
   Submodule.mul_induction_on cannot be used with `induction … using` (use refine).
   push_neg deprecated → `push Not`.

## NEXT: N3 `AlgebraicCascadeDifferentDrop.lean` (designed, not yet written)
For Q : HeightOneSpectrum (algCascadeInt m p):
(a) ∃ e ≥ 1: ∀ f, v_Q(algLaw p (uDeriv m) f) ≤ v_Q(f)·exp e — via monogenic generator α of the
    closure (DedekindOrderMonogenic.exists_adjoin_eq_top_of_dedekind_finite), clearing constant
    c_B := aeval α (derivative (minpoly (topInt m) α)), N1 discharge of N2's hclear, e := mult+1.
(b) For Q over maximalIdeal (topInt m) with KD multiplicity e: same bound with THE ramification e —
    via KummerDedekindDifferentOrder.not_mem_pow_aeval_derivative (c_B ∉ Q^e).
Discharge chain for hclear: hgen_B (adjoin (topInt m) {α} = ⊤ in B) → map through
IsScalarTower.toAlgHom (topInt m) B (AlgCascadeField p) (AlgHom.map_adjoin) → N1 with
q̄ := (minpoly (topInt m) α).map (inclusion), coeff ∈ topInt via coeff_map; hqα via
aeval_map_algebraMap + aeval_algHom_apply + minpoly.aeval; c ≠ 0 via
minpoly.isIntegrallyClosed_eq_field_fractions + separable derivative nonzero (char 0).
Instances needed (some may need manual derivation): Module.Finite (topInt m) (algCascadeInt m p)
(IsIntegralClosure.finite), CharZero (ResidueField (topInt m)) (integers are units in topInt: nonzero
constants; write manual instance), Module.IsTorsionFree via Module.isTorsionFree_iff_algebraMap_injective
(injectivity proof pattern inside AlgebraicCascadePlace), FiniteDimensional (ResidueField)
(B ⧸ maxExt) from Module.Finite (Module.Finite.quotient?), maxExt ≠ ⊥ (image of nonzero u ≠ 0),
IsIntegrallyClosed (topInt m) (DVR→UFD→integrally closed — instance search may be SLOW/need
maxHeartbeats; AlgebraicCascadePlace needed synthInstance.maxHeartbeats 1000000 for IsDomain).
Then also record v_Q(algebraMap u) = exp(−e_ram) for the peel's bookkeeping (u = 1/X_m uniformizer
of topInt; topInt_maximalIdeal facts in TopDegreeValuationRing).

After N3: item 3 = restate the peel (Bell induction, TerminalPowerCascadeInduction line) over the
place datum + Reduction I (WimanPlaceRoot.exists_radius_wiman_place, TopSymbolWimanPlace,
EliminationOrderDescent GradedAlong charts) to produce general helim, then assemble
exactDifferentialOrder_entireCascade, wire everything into HTGeometry umbrella, build, axiom-audit,
update stale card notes (gate ~line 465, superseded Lean-status block), promote card.

## Machine/process notes
2026-08-13: ~18 concurrent lean processes from other agents; even `import Mathlib` scratch can
exceed 600s under load. One own process at a time; kill detached PIDs (pkill -f <file>) before
starting the next.
