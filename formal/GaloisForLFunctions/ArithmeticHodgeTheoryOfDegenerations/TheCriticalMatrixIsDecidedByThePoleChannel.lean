import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PrimitiveCriticalThresholdEqualsWindowThreshold

/-!
# The critical matrix is decided by the pole channel

At critical overlap `1 ≤ c`, `c⁸ ≤ R log N`, the complete Weil energy on `ℝ^N` splits along the
polar conductor line `L = conductorSubspace 1 N` and its orthogonal complement, the primitive
hyperplane. Call **pole channel at ratio `R`** (`EventuallyPoleChannelPos`) eventual positivity of
the energy on every vector `x + w` with `0 ≠ x ∈ L` and `w ⊥ L`.

* `posDef_iff_primitive_and_poleChannel`: for any function on a finite-dimensional inner-product
  space and any subspace `L`, positivity off `0` is positivity on `Lᗮ` plus positivity on
  `(L ∖ 0) + Lᗮ`.
* `eventuallyCriticalPosDef_iff_poleChannel_of_lt_iInf_windowThreshold`: below the window threshold
  `W = ⨅_{A ≥ 0} windowThreshold A` the primitive hyperplane is eventually positive
  (`R_pole = W`), so the complete matrix at ratio `R` is positive iff its pole channel is.
* `criticalPositivityThreshold_eq_iInf_windowThreshold_iff_poleChannel`: the whole-space threshold
  `R_c(ζ)` equals `W` (the open question whether the pole direction lowers the threshold) iff the
  pole channel is eventually positive at every ratio below `W`.

Together with `W = ⊤ ⟺ RH` (`highConductorCriticalThreshold_eq_top_iff_riemannHypothesis`), the
critical ratio problem is the window problem plus one channel.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology RHTower Zeta23
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory BezoutValuationIncidence
  SpacingScaleHarmonicAnalysis

/-- **Positivity splits along a subspace.** On a finite-dimensional inner-product space, a
function is positive off `0` iff it is positive on `Lᗮ ∖ 0` and on every `x + w` with
`0 ≠ x ∈ L`, `w ∈ Lᗮ`. -/
theorem posDef_iff_primitive_and_poleChannel {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℝ V) (E : V → ℝ) :
    (∀ z : V, z ≠ 0 → 0 < E z) ↔
      (∀ w ∈ Lᗮ, w ≠ 0 → 0 < E w) ∧ ∀ x ∈ L, x ≠ 0 → ∀ w ∈ Lᗮ, 0 < E (x + w) := by
  constructor
  · intro h
    refine ⟨fun w _ hw => h w hw, fun x hx hx0 w hw => h _ fun h0 => hx0 ?_⟩
    have horth : ⟪x, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hx hw
    have hsq : ‖x + w‖ ^ 2 = ‖x‖ ^ 2 + ‖w‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
        horth, real_inner_comm x w, horth, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring
    rw [h0, norm_zero] at hsq
    have : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖w‖, sq_nonneg ‖x‖]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  · rintro ⟨hw, hx⟩ z hz
    obtain ⟨x, hxL, w, hwL, rfl⟩ := L.exists_add_mem_mem_orthogonal z
    by_cases hx0 : x = 0
    · subst hx0
      rw [zero_add] at hz ⊢
      exact hw w hwL hz
    · exact hx x hxL hx0 w hwL

/-- **The pole channel at ratio `R`**: eventual positivity of the complete energy on every
`x + w` with `0 ≠ x` in the polar conductor line and `w` primitive. -/
def EventuallyPoleChannelPos (R : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R * Real.log (N : ℝ) →
    ∀ x ∈ conductorSubspace 1 N, x ≠ 0 → ∀ w ∈ (conductorSubspace 1 N)ᗮ,
      0 < completeWeilEnergy tiltedUnitSpline c N (x + w)

/-- **The complete matrix is the primitive hyperplane plus the pole channel.** -/
theorem eventuallyCriticalPosDef_iff (R : ℝ) :
    EventuallyCriticalPosDef R ↔ EventuallyPoleOrthogonalPosDef R ∧ EventuallyPoleChannelPos R := by
  constructor
  · intro h
    refine ⟨eventuallyPoleOrthogonalPosDef_of_posDef h, ?_⟩
    filter_upwards [h] with N hN c hc1 hc8
    exact ((posDef_iff_primitive_and_poleChannel _ _).mp fun z hz => hN hc1 hc8 hz).2
  · rintro ⟨hP, hC⟩
    filter_upwards [hP, hC] with N hPN hCN c hc1 hc8 z hz
    exact (posDef_iff_primitive_and_poleChannel (conductorSubspace 1 N)
      (completeWeilEnergy tiltedUnitSpline c N)).mpr
      ⟨fun w hw hw0 => hPN hc1 hc8 hw hw0, hCN hc1 hc8⟩ z hz

/-- **Below the window threshold the pole channel decides.** -/
theorem eventuallyCriticalPosDef_iff_poleChannel_of_lt_iInf_windowThreshold {R : ℝ} (hR : 0 < R)
    (hlt : (R : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) :
    EventuallyCriticalPosDef R ↔ EventuallyPoleChannelPos R := by
  rw [eventuallyCriticalPosDef_iff]
  exact and_iff_right (eventuallyPoleOrthogonalPosDef_of_lt_iInf_windowThreshold hR hlt)

/-- **The whole-space threshold is the window threshold iff the pole channel pays below it.** -/
theorem criticalPositivityThreshold_eq_iInf_windowThreshold_iff_poleChannel :
    criticalPositivityThreshold = ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A ↔
      ∀ R : ℝ, 0 < R → (R : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A →
        EventuallyPoleChannelPos R := by
  set W : EReal := ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A with hW
  have hle : criticalPositivityThreshold ≤ W :=
    criticalPositivityThreshold_le_poleOrthogonalCriticalThreshold.trans
      poleOrthogonalCriticalThreshold_eq_iInf_windowThreshold.le
  constructor
  · intro heq R hR hRW
    have hRc : (R : EReal) < criticalPositivityThreshold := heq ▸ hRW
    obtain ⟨_, ⟨r, ⟨hr0, hr⟩, rfl⟩, hRr⟩ := lt_sSup_iff.mp hRc
    have hRr' : R ≤ r := (EReal.coe_lt_coe_iff.mp hRr).le
    exact (eventuallyCriticalPosDef_iff_poleChannel_of_lt_iInf_windowThreshold hR hRW).mp
      (eventuallyCriticalPosDef_antitone hRr' hr)
  · intro hC
    refine le_antisymm hle (le_of_forall_lt fun a ha => ?_)
    have hpos := criticalPositivityThreshold_pos
    rcases le_or_gt a 0 with ha0 | ha0
    · exact ha0.trans_lt hpos
    · obtain ⟨R, haR, hRW⟩ := EReal.lt_iff_exists_real_btwn.mp ha
      have hR : 0 < R := EReal.coe_pos.mp (ha0.trans haR)
      have hmem : (R : EReal) ≤ criticalPositivityThreshold :=
        le_sSup ⟨R, ⟨hR, (eventuallyCriticalPosDef_iff_poleChannel_of_lt_iInf_windowThreshold hR
          hRW).mpr (hC R hR hRW)⟩, rfl⟩
      exact haR.trans_le hmem

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
