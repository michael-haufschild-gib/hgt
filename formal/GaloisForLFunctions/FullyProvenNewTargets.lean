/-
# `2-fully-proven/new` Lean targets, excluding the hRigid path

Door grade: BRIDGE / formal ledger.  This file adds no mathematical shortcut: it
collects the Lean proof objects currently serving the cards in
`docs/drafts/pipeline/2-fully-proven/new`, with the hRigid branch deliberately
left out because that path is owned by the parallel agent.

The rule here is strict.  A declaration below is either:
* a theorem wrapper around an existing proof object, or
* a target `Prop` whose proof is supplied immediately by an existing theorem.

For cards whose paper statement is wider than the present Lean theorem, the
wrapper name says which branch is proved.
-/
import GaloisForLFunctions.Hurwitz.N2Final
import GaloisForLFunctions.Hurwitz.AllNQuadFilt
import GaloisForLFunctions.U0.U0CardTheorems
import GaloisForLFunctions.Bottcher.AlgIndep
import GaloisForLFunctions.Bottcher.CoverMonodromy
import GaloisForLFunctions.Bottcher.DyadicMonodromy
import GaloisForLFunctions.Bottcher.MonodromyMultiplier
import GaloisForLFunctions.Bottcher.Q62DeepDataAssembly
import GaloisForLFunctions.Bottcher.HDiscLoopDeck

noncomputable section

open Complex Filter Topology MeasureTheory Metric Polynomial
open HurwitzN2Tail U0MeroCarrier U0KummerRepick Bottcher

namespace FullyProvenNewTargets

/-! ## Hurwitz cards -/

/-- Generic Lean target for
`hurwitz-quadratic-n2-density-shadow.md`.

This is the currently formalized branch of the paper card: it assumes
`s ∉ ℤ` and `2s ∉ ℤ`.  The half-integer branch of the paper statement is not
claimed here. -/
def HurwitzN2DensityShadowGenericTarget (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, (k : ℂ) ≠ s) →
  (∀ k : ℤ, (k : ℂ) ≠ 2 * s) →
  ∀ (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ)
      (N : ℕ),
    (∀ n, N ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z) *
          ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) *
            (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0

/-- Formal wrapper for the generic branch of
`hurwitz-quadratic-n2-density-shadow.md`. -/
theorem hurwitz_quadratic_n2_density_shadow_generic (s : ℂ) :
    HurwitzN2DensityShadowGenericTarget s := by
  intro hs1 hsZ h2sZ q l cc N hrel
  exact HurwitzN2Final.hurwitz_n2_unconditional
    (s := s) (N := N) hs1 hsZ h2sZ q l cc hrel

/-- Formalized all-`N` quadratic-block target for
`hurwitz-quadratic-all-n-tail-independence.md`.

This records the current Lean-proved spine: every quadratic weight coefficient
`A_w` vanishes for the genuine factored relation.  The final rational-tail
independence / linear-constant descent advertised by the paper card remains a
separate target, not hidden here. -/
def HurwitzAllNQuadraticBlockGenericTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, (k : ℂ) ≠ s) →
  (∀ k : ℤ, (k : ℂ) ≠ 2 * s) →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) (M : ℕ),
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    ∀ w, w ≤ 2 * N → HurwitzAllNQuadFilt.AqN q w = 0

/-- Formal wrapper for the all-`N` quadratic-block spine. -/
theorem hurwitz_quadratic_allN_tail_independence_quadratic_block (N : ℕ) (s : ℂ) :
    HurwitzAllNQuadraticBlockGenericTarget N s := by
  intro hs1 hs h2s q l cc M hrel
  exact HurwitzAllNQuadFilt.allN_quad_vanish_genuine
    (N := N) (s := s) (M := M) hs1 hs h2s q l cc hrel

/-! ## `u₀ ⟂ φ_b` cards -/

/-- Shared carrier target for the three u0-phi cards.

The only extra input is the explicit `PhibKummerInputs` provider; no axiom or
placeholder is introduced. -/
def U0PhiIndependenceCarrierTarget {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b) : Prop :=
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  NoRelation (RatFunc ℂ) (phiMero b hU_esc)
    (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext))

/-- Formal wrapper for `u0-phi-independence.md` (connected branch), conditional
on the explicit Kummer-input provider. -/
theorem u0_phi_independence_connected_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hKummer : U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_connected hUo hUc hUne hUinf hU_ext hU_esc hKummer

/-- Formal wrapper for `u0-phi-independence-disconnected.md`, conditional on
the explicit Kummer-input provider. -/
theorem u0_phi_independence_disconnected_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hKummer : U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_disconnected hUo hUc hUne hUinf hU_ext hU_esc hKummer

/-- Formal wrapper for `u0-phi-independence-all-parameters.md`, conditional on
the explicit Kummer-input provider. -/
theorem u0_phi_independence_all_parameters_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hKummer : U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_all_parameters hUo hUc hUne hUinf hU_ext hU_esc
    hKummer

/-! ## Böttcher monodromy cards, non-hRigid side -/

/-- Algebraic target for
`not-new-but-required/unbounded-one-coordinate-monodromy-obstruction.md`. -/
def UnboundedOneCoordinateMonodromyTarget
    {K M : Type*} [Field K] [Field M] [Algebra K M] (F G : M) : Prop :=
  Transcendental K G →
  F ≠ 0 →
  (∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
    d < m ∧ orderOf ζ = m ∧ σ G = G ∧ σ ζ = ζ ∧ σ F = ζ * F) →
  ∀ P : Polynomial (Polynomial K),
    (P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0 →
    P = 0

/-- Formal wrapper for the unbounded one-coordinate monodromy obstruction. -/
theorem unbounded_one_coordinate_monodromy_obstruction_card
    {K M : Type*} [Field K] [Field M] [Algebra K M] (F G : M) :
    UnboundedOneCoordinateMonodromyTarget (K := K) (M := M) F G := by
  intro hG hF mono P hrel
  exact Bottcher.algIndep_of_unbounded_monodromy (K := K) (M := M) F G hG hF mono P hrel

/-- Order-only target for
`not-new-but-required/bottcher-dyadic-monodromy-finite-type-absence.md`. -/
def BottcherDyadicUnboundedOrderTarget : Prop :=
  ∀ d : ℕ, ∃ ζ : ℂ, d < orderOf ζ

/-- Formal wrapper: dyadic multipliers have unbounded order. -/
theorem bottcher_dyadic_monodromy_finite_type_absence_order :
    BottcherDyadicUnboundedOrderTarget :=
  Bottcher.exists_complex_orderOf_gt

/-- Carrier-level Prüfer order target in the cover-germ ring. -/
def BottcherCoverGermDyadicOrderTarget : Prop :=
  ∀ (c₁ c₂ : ℂ) (n m d : ℕ),
    ∃ (k : ℕ) (ζ : ℂ), ζ ^ (2 ^ k) = 1 ∧ ζ ≠ 0 ∧
      orderOf ((ζ : Bottcher.coverGerm c₁ c₂ n m)) = 2 ^ k ∧ d < 2 ^ k

/-- Formal wrapper: dyadic order tower transferred to the cover-germ carrier. -/
theorem bottcher_exact_pruefer_coverGerm_order :
    BottcherCoverGermDyadicOrderTarget := by
  intro c₁ c₂ n m d
  exact Bottcher.exists_dyadic_order_gt_coverGerm c₁ c₂ n m d

/-- Formal `monoF` coordinate datum from exact Prüfer monodromy on the
cover-germ carrier. -/
theorem bottcher_exact_pruefer_coverGerm_monoF
    (c₁ c₂ : ℂ) (m d : ℕ) :
    ∃ (k : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ k) = 1),
      d < orderOf ((ζ : Bottcher.coverGerm c₁ c₂ k m)) ∧
      Bottcher.deckGermEquiv hζ hpow (Bottcher.zGerm : Bottcher.coverGerm c₁ c₂ k m)
        = Bottcher.zGerm ∧
      Bottcher.deckGermEquiv hζ hpow (Bottcher.v2Germ : Bottcher.coverGerm c₁ c₂ k m)
        = Bottcher.v2Germ ∧
      Bottcher.deckGermEquiv hζ hpow ((ζ : Bottcher.coverGerm c₁ c₂ k m))
        = (ζ : Bottcher.coverGerm c₁ c₂ k m) ∧
      Bottcher.deckGermEquiv hζ hpow (Bottcher.v1Germ : Bottcher.coverGerm c₁ c₂ k m)
        = (ζ : Bottcher.coverGerm c₁ c₂ k m) * Bottcher.v1Germ :=
  Bottcher.coverGerm_monoF_datum c₁ c₂ m d

/-- Formal `monoG` coordinate datum from exact Prüfer monodromy on the
cover-germ carrier. -/
theorem bottcher_exact_pruefer_coverGerm_monoG
    (c₁ c₂ : ℂ) (n d : ℕ) :
    ∃ (k : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ k) = 1),
      d < orderOf ((ζ : Bottcher.coverGerm c₁ c₂ n k)) ∧
      Bottcher.deckGermEquiv₂ hζ hpow (Bottcher.zGerm : Bottcher.coverGerm c₁ c₂ n k)
        = Bottcher.zGerm ∧
      Bottcher.deckGermEquiv₂ hζ hpow (Bottcher.v1Germ : Bottcher.coverGerm c₁ c₂ n k)
        = Bottcher.v1Germ ∧
      Bottcher.deckGermEquiv₂ hζ hpow ((ζ : Bottcher.coverGerm c₁ c₂ n k))
        = (ζ : Bottcher.coverGerm c₁ c₂ n k) ∧
      Bottcher.deckGermEquiv₂ hζ hpow (Bottcher.v2Germ : Bottcher.coverGerm c₁ c₂ n k)
        = (ζ : Bottcher.coverGerm c₁ c₂ n k) * Bottcher.v2Germ :=
  Bottcher.coverGerm_monoG_datum c₁ c₂ n d

/-- Period-to-order target for the Böttcher exact-monodromy pipeline. -/
def BottcherPeriodMultiplierOrderTarget : Prop :=
  ∀ (μ : Measure ℂ), IsFiniteMeasure μ →
  ∀ {c : ℂ} {R : ℝ} (n : ℕ), 0 ≤ R → μ (sphere c R) = 0 →
    Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap c R) θ • (circleMap c R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod μ) →
    (μ (ball c R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹ →
    orderOf (Complex.exp (∮ z in C(c, R), ∫ ζ, (z - ζ)⁻¹ ∂μ)) = 2 ^ n

/-- Formal wrapper: period `2πi / 2^n` gives multiplier order `2^n`. -/
theorem bottcher_exact_pruefer_period_multiplier_order :
    BottcherPeriodMultiplierOrderTarget := by
  intro μ hfinite c R n h0 hsphere hint hmass
  letI : IsFiniteMeasure μ := hfinite
  exact Bottcher.multiplier_orderOf_of_mass μ n h0 hsphere hint hmass

/-! ## q62 both-disconnected / hDisc branch -/

/-- The non-hRigid hDisc tower target used by
`q62-both-disconnected.md` and the disconnected branch of
`q62-bottcher-independence-n2-all-parameters.md`. -/
def Q62HDiscFixedInverseTowerTarget (c₁ c₂ : ℂ) : Prop :=
  (∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
    (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
    ∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
        n = d + 1 ∧
        max 2 ‖c₁‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ n d R' hR'pos) ∧
  (∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₂ : ℂ → ℂ),
    (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
    ∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
        n = d + 1 ∧
        max 2 ‖c₂‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ n d R' hR'pos)

/-- Formal wrapper for the completed hDisc loop/deck tower, excluding the hRigid branch. -/
theorem q62_both_disconnected_hdisc_fixed_inverse_towers (c₁ c₂ : ℂ) :
    Q62HDiscFixedInverseTowerTarget c₁ c₂ :=
  Bottcher.exteriorAnnulus_loop_and_uniform_hliftFG_towers_with_fixed_inverse c₁ c₂

/-- Existing hDisc deep-data close for q62; exposed as a Lean object so the card
mapping has a stable name without importing the hRigid path. -/
def q62_both_disconnected_deep_data_escape_formal_proof :=
  @Bottcher.q62_disconnected_of_deepData_escape

/-- Existing additive loop/deck close for q62 both-disconnected; exposed for the
same card mapping. -/
def q62_both_disconnected_additive_loop_deck_formal_proof :=
  @Bottcher.q62_independence_disconnected_of_dyadic_additive_loop_and_two_zfixing_decks

/-- Existing vertical-strip loop/deck close for q62 both-disconnected; exposed for
the same card mapping. -/
def q62_both_disconnected_vertical_strip_loop_deck_formal_proof :=
  @Bottcher.q62_independence_disconnected_of_dyadic_verticalStrip_loop_and_two_zfixing_decks

end FullyProvenNewTargets
