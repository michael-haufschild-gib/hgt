import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.TemperedConfigurationsWithAFiniteOffLineLayerHaveCriticalStates
import GaloisForLFunctions.RHTower.BeurlingOverRegularIntegersOffLineZeros
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerTwins

/-!
# The off-line layers of the Beurling and twin models carry critical states

The quartet `{ρ, ρ̄, 1 − ρ̄, 1 − ρ}` of a point of the strip is the smallest configuration closed under
conjugation and the functional equation. Off the critical line it carries a confined critical state
(`quartet_criticalState`), by the existence theorem for tempered configurations with a finite
off-line layer.

* **Over-regular Beurling system** (`overRegular_quartet_criticalState`). The zeta function of the
  over-regular Beurling integers with `μ = 2/5, ν = 1/10, γ = 1` (nonnegative prime density) vanishes at
  `3/5 + i`; it has no functional equation, and the symmetrization of its off-line zero carries a
  critical state.
* **Explicit form** (`quartet_criticalState_explicit`). A quartet state is a finite exponential
  polynomial: it lies in the span of the vectors `e^{(z+8)u}cos(Im z·u)`, `e^{(z+8)u}sin(Im z·u)` at the
  shifted points of the quartet. The over-regular Beurling zeta vanishes in the strip exactly at
  `3/5 ± i` (`overRegularZeta_eq_zero_iff`, `overRegular_criticalState_explicit`).
* **Positive Euler twins** (`positiveTwin_quartet_criticalState`, `positiveTwin_criticalState_explicit`). For every `σ ∈ (½, 1)` a positive
  multiplicative Euler twin of degree one vanishes at a point of `Re s = σ`, and its quartet carries a
  critical state.
-/

noncomputable section
open MeasureTheory Set Complex Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ModelStates
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

/-- The quartet `{ρ, ρ̄, 1 − ρ̄, 1 − ρ}` as a zero configuration with unit multiplicities. -/
def quartetConfig (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) : ZeroConfig where
  carrier := {ρ, conj ρ, 1 - conj ρ, 1 - ρ}
  mult _ := 1
  one_le_mult _ _ := le_rfl
  strip := by
    rintro z (rfl | rfl | rfl | rfl)
    · exact ⟨h0, h1⟩
    · rw [Complex.conj_re]; exact ⟨h0, h1⟩
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; constructor <;> linarith
    · simp only [Complex.sub_re, Complex.one_re]; constructor <;> linarith
  reflect_mem := by
    rintro z (rfl | rfl | rfl | rfl) <;> simp [reflect]
  mult_reflect _ _ := rfl
  finite_window _ _ :=
    ((((Set.finite_singleton _).insert _).insert _).insert _).subset inter_subset_left

theorem quartetConfig_finite (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    (quartetConfig ρ h0 h1).carrier.Finite :=
  (((Set.finite_singleton _).insert _).insert _).insert _

theorem temperedConfig_quartet (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    TemperedConfig (quartetConfig ρ h0 h1) := by
  haveI := (quartetConfig_finite ρ h0 h1).to_subtype
  exact Summable.of_finite

theorem conj_quartet (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    ∀ z ∈ (quartetConfig ρ h0 h1).carrier,
      conj z ∈ (quartetConfig ρ h0 h1).carrier ∧
        (quartetConfig ρ h0 h1).mult (conj z) = (quartetConfig ρ h0 h1).mult z := by
  rintro z (rfl | rfl | rfl | rfl) <;> refine ⟨?_, rfl⟩ <;> simp [quartetConfig]

/-- **The quartet of an off-line point carries a confined critical state.** -/
theorem quartet_criticalState {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) (hre : ρ.re ≠ 1 / 2) :
    ∃ hfin : (offLineSet (quartetConfig ρ h0 h1)).Finite, ∃ (a : ℝ) (F : ConfSpace), 0 < a ∧
      (configEnergy hfin).Admissible F ∧ ‖F‖ = 1 ∧ (configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
      ∀ G : ConfSpace, (configEnergy hfin).Admissible G →
        0 ≤ (configEnergy hfin).energy G + a * ‖G‖ ^ 2 := by
  have hfin : (offLineSet (quartetConfig ρ h0 h1)).Finite :=
    (quartetConfig_finite ρ h0 h1).subset fun z hz => hz.1
  exact ⟨hfin, exists_configCriticalState (temperedConfig_quartet ρ h0 h1) hfin
    (conj_quartet ρ h0 h1) (show ρ ∈ (quartetConfig ρ h0 h1).carrier from Or.inl rfl) hre⟩

/-- **The over-regular Beurling model.** Its zeta function vanishes at `3/5 + i`, and the quartet of
this zero carries a confined critical state. -/
theorem overRegular_quartet_criticalState :
    RHTower.BeurlingOverRegularIntegers.overRegularZeta (2 / 5) (1 / 10) 1 ((3 / 5 : ℝ) + I) = 0 ∧
      ∃ (h0 : 0 ≤ (((3 / 5 : ℝ) : ℂ) + I).re) (h1 : (((3 / 5 : ℝ) : ℂ) + I).re ≤ 1)
        (hfin : (offLineSet (quartetConfig _ h0 h1)).Finite) (a : ℝ) (F : ConfSpace), 0 < a ∧
        (configEnergy hfin).Admissible F ∧ ‖F‖ = 1 ∧
        (configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
        ∀ G : ConfSpace, (configEnergy hfin).Admissible G →
          0 ≤ (configEnergy hfin).energy G + a * ‖G‖ ^ 2 := by
  have hz : RHTower.BeurlingOverRegularIntegers.overRegularZeta (2 / 5) (1 / 10) 1
      ((3 / 5 : ℝ) + I) = 0 := by
    have h := RHTower.BeurlingOverRegularIntegers.overRegularZeta_eq_zero (2 / 5) (1 / 10) 1
    norm_num at h ⊢
    exact h
  have hre : (((3 / 5 : ℝ) : ℂ) + I).re = 3 / 5 := by simp
  have h0 : 0 ≤ (((3 / 5 : ℝ) : ℂ) + I).re := by rw [hre]; norm_num
  have h1 : (((3 / 5 : ℝ) : ℂ) + I).re ≤ 1 := by rw [hre]; norm_num
  obtain ⟨hfin, rest⟩ := quartet_criticalState h0 h1 (by rw [hre]; norm_num)
  exact ⟨hz, h0, h1, hfin, rest⟩

/-- **The positive Euler twins.** For every `σ ∈ (½, 1)` there is a positive multiplicative Euler
twin vanishing at a point of `Re s = σ` whose quartet carries a confined critical state. -/
theorem positiveTwin_quartet_criticalState (N : ℕ) {σ : ℝ} (hσ0 : 1 / 2 < σ) (hσ1 : σ < 1) :
    ∃ (F : RHTower.ExtendedSelbergClass) (s : ℂ), F.coeff.IsMultiplicative ∧ F.coeff 1 = 1 ∧
      (∀ n : ℕ, n ≠ 0 → (F.coeff n).im = 0 ∧ 1 ≤ (F.coeff n).re) ∧ s.re = σ ∧ F s = 0 ∧
      ∃ (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (hfin : (offLineSet (quartetConfig s h0 h1)).Finite)
        (a : ℝ) (G : ConfSpace), 0 < a ∧ (configEnergy hfin).Admissible G ∧ ‖G‖ = 1 ∧
        (configEnergy hfin).energy G + a * ‖G‖ ^ 2 = 0 ∧
        ∀ H : ConfSpace, (configEnergy hfin).Admissible H →
          0 ≤ (configEnergy hfin).energy H + a * ‖H‖ ^ 2 := by
  obtain ⟨F, -, hmul, h1F, ⟨C, hC⟩, -, ⟨s, hs, hFs⟩, -, -⟩ :=
    GaloisForLFunctions.SelbergClass.PositiveFiniteEuler.exists_positive_multiplicative_euler_twin_at
      N σ hσ0 hσ1
  have h0 : 0 ≤ s.re := by rw [hs]; linarith
  have h1 : s.re ≤ 1 := by rw [hs]; linarith
  obtain ⟨hfin, rest⟩ := quartet_criticalState h0 h1 (by rw [hs]; linarith)
  exact ⟨F, s, hmul, h1F, fun n hn => ⟨(hC n hn).1, (hC n hn).2.1⟩, hs, hFs, h0, h1, hfin, rest⟩

/-! ### Explicit states -/

theorem finite_onLineIdx_quartet (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    Finite (OnLineIdx (quartetConfig ρ h0 h1)) := by
  haveI := (quartetConfig_finite ρ h0 h1).to_subtype
  unfold OnLineIdx
  infer_instance

/-- **The quartet state is an exponential polynomial.** The critical state of an off-line quartet lies
in the span of the finitely many vectors `e^{(z+8)u} cos(Im z · u)`, `e^{(z+8)u} sin(Im z · u)` at the
points `z = ±(ρ' − ½)` of the quartet: by the Euler–Lagrange equation it is the combination of these
vectors with its own zero coordinates as coefficients, divided by the critical ratio. -/
theorem quartet_criticalState_explicit {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) (hre : ρ.re ≠ 1 / 2) :
    ∃ hfin : (offLineSet (quartetConfig ρ h0 h1)).Finite, ∃ (a : ℝ) (F : ConfSpace), 0 < a ∧
      ‖F‖ = 1 ∧ (configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
      (∀ G : ConfSpace, 0 ≤ (configEnergy hfin).energy G + a * ‖G‖ ^ 2) ∧
      F ∈ Submodule.span ℝ (Set.range (configEnergy hfin).a ∪ Set.range (configEnergy hfin).b ∪
        Set.range (configEnergy hfin).p ∪ Set.range (configEnergy hfin).q) := by
  obtain ⟨hfin, a, F, ha, -, hF1, hEq, hmin⟩ := quartet_criticalState h0 h1 hre
  haveI := finite_onLineIdx_quartet ρ h0 h1
  have hadm : ∀ G : ConfSpace, (configEnergy hfin).Admissible G := fun G => Summable.of_finite
  refine ⟨hfin, a, F, ha, hF1, hEq, fun G => hmin G (hadm G), ?_⟩
  exact (configEnergy hfin).mem_span_of_groundState (lam := -a) (by linarith) (by linarith)
    (fun G hG => by have := hmin G hG; linarith)

/-- **The zeros of the over-regular Beurling zeta in the strip** are exactly `3/5 ± i` (the pole
`s = 1` excluded). -/
theorem overRegularZeta_eq_zero_iff {s : ℂ} (h0 : 0 ≤ s.re) (hs1 : s ≠ 1) :
    RHTower.BeurlingOverRegularIntegers.overRegularZeta (2 / 5) (1 / 10) 1 s = 0 ↔
      s = ((3 / 5 : ℝ) : ℂ) + I ∨ s = ((3 / 5 : ℝ) : ℂ) - I := by
  unfold RHTower.BeurlingOverRegularIntegers.overRegularZeta
  have hd1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hre_pos : ∀ c : ℝ, 0 < c → s + (c : ℂ) ≠ 0 := fun c hc h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hd2 : s + ((3 * (2 / 5 : ℝ) - 1 - 1 / 10 : ℝ) : ℂ) ≠ 0 := hre_pos _ (by norm_num)
  have hd3 : s + ((3 * (2 / 5 : ℝ) - 1 + 1 / 10 : ℝ) : ℂ) ≠ 0 := hre_pos _ (by norm_num)
  have hn3 : s + ((4 * (2 / 5 : ℝ) - 1 : ℝ) : ℂ) ≠ 0 := hre_pos _ (by norm_num)
  push_cast at hd2 hd3 hn3 ⊢
  rw [div_eq_zero_iff, or_iff_left (mul_ne_zero (mul_ne_zero hd1 hd2) hd3), mul_eq_zero,
    or_iff_left hn3]
  constructor
  · intro h
    have h' : (s - (1 - 2 / 5) - I) * (s - (1 - 2 / 5) + I) = 0 := by
      rw [← h]; ring_nf; rw [I_sq]; ring
    rcases mul_eq_zero.mp h' with h2 | h2
    · left; linear_combination h2
    · right; linear_combination h2
  · rintro (h | h) <;> rw [h] <;> ring_nf <;> rw [I_sq] <;> ring

/-- **The Beurling model, explicitly.** The over-regular Beurling zeta vanishes in the strip exactly at
`3/5 ± i`; the configuration of these zeros and their functional-equation mirrors `2/5 ± i` carries a
critical state, an exponential polynomial at the shifted zeros. -/
theorem overRegular_criticalState_explicit :
    (∀ s : ℂ, 0 ≤ s.re → s ≠ 1 →
      (RHTower.BeurlingOverRegularIntegers.overRegularZeta (2 / 5) (1 / 10) 1 s = 0 ↔
        s = ((3 / 5 : ℝ) : ℂ) + I ∨ s = ((3 / 5 : ℝ) : ℂ) - I)) ∧
      ∃ (h0 : 0 ≤ (((3 / 5 : ℝ) : ℂ) + I).re) (h1 : (((3 / 5 : ℝ) : ℂ) + I).re ≤ 1)
        (hfin : (offLineSet (quartetConfig _ h0 h1)).Finite) (a : ℝ) (F : ConfSpace), 0 < a ∧
        ‖F‖ = 1 ∧ (configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
        (∀ G : ConfSpace, 0 ≤ (configEnergy hfin).energy G + a * ‖G‖ ^ 2) ∧
        F ∈ Submodule.span ℝ (Set.range (configEnergy hfin).a ∪ Set.range (configEnergy hfin).b ∪
          Set.range (configEnergy hfin).p ∪ Set.range (configEnergy hfin).q) := by
  have hre : (((3 / 5 : ℝ) : ℂ) + I).re = 3 / 5 := by simp
  have h0 : 0 ≤ (((3 / 5 : ℝ) : ℂ) + I).re := by rw [hre]; norm_num
  have h1 : (((3 / 5 : ℝ) : ℂ) + I).re ≤ 1 := by rw [hre]; norm_num
  obtain ⟨hfin, rest⟩ := quartet_criticalState_explicit h0 h1 (by rw [hre]; norm_num)
  exact ⟨fun s hs hs1 => overRegularZeta_eq_zero_iff hs hs1, h0, h1, hfin, rest⟩

/-- **The positive twins, explicitly.** For `σ ∈ (½, 1)` the quartet of a zero of a positive Euler twin
on `Re s = σ` carries a critical state that is an exponential polynomial at the shifted zeros. -/
theorem positiveTwin_criticalState_explicit (N : ℕ) {σ : ℝ} (hσ0 : 1 / 2 < σ) (hσ1 : σ < 1) :
    ∃ (F : RHTower.ExtendedSelbergClass) (s : ℂ), F.coeff.IsMultiplicative ∧ F.coeff 1 = 1 ∧
      s.re = σ ∧ F s = 0 ∧
      ∃ (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (hfin : (offLineSet (quartetConfig s h0 h1)).Finite)
        (a : ℝ) (G : ConfSpace), 0 < a ∧ ‖G‖ = 1 ∧ (configEnergy hfin).energy G + a * ‖G‖ ^ 2 = 0 ∧
        (∀ H : ConfSpace, 0 ≤ (configEnergy hfin).energy H + a * ‖H‖ ^ 2) ∧
        G ∈ Submodule.span ℝ (Set.range (configEnergy hfin).a ∪ Set.range (configEnergy hfin).b ∪
          Set.range (configEnergy hfin).p ∪ Set.range (configEnergy hfin).q) := by
  obtain ⟨F, -, hmul, h1F, -, -, ⟨s, hs, hFs⟩, -, -⟩ :=
    GaloisForLFunctions.SelbergClass.PositiveFiniteEuler.exists_positive_multiplicative_euler_twin_at
      N σ hσ0 hσ1
  have h0 : 0 ≤ s.re := by rw [hs]; linarith
  have h1 : s.re ≤ 1 := by rw [hs]; linarith
  obtain ⟨hfin, rest⟩ := quartet_criticalState_explicit h0 h1 (by rw [hs]; linarith)
  exact ⟨F, s, hmul, h1F, hs, hFs, h0, h1, hfin, rest⟩

#print axioms overRegular_quartet_criticalState
#print axioms positiveTwin_quartet_criticalState
#print axioms overRegular_criticalState_explicit
#print axioms positiveTwin_criticalState_explicit

end GaloisForLFunctions.ExclusionOfTheCriticalState.ModelStates
