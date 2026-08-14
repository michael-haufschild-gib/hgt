import GaloisForLFunctions.RHTower.GateWordFirstHit

/-!
# Zero-fugacity recovery of gate-word complexity

The discounted first-hit mass of a gate language is squeezed between the discount raised to the
minimal hitting length and the same power of the discount divided by the alphabet size.  Taking
logarithms and letting the discount vanish therefore recovers the minimal hitting length exactly:
the tropical limit of the first-hit free energy is word complexity.

The same sandwich absorbs a union over all targets reachable within a fixed length: the indicator
of the reachable event is dominated by a fixed multiple of the first-hit mass, so the measure of
that event is controlled by a single first-hit moment.
-/

open scoped ENNReal Topology
open MeasureTheory Filter

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section MinimalWord

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] {X : Type*}

/-- A reachable target is reached by a word of minimal length. -/
theorem exists_minimal_hitting_word (act : Γ → X → X) (χ : X) (A : Set X)
    (h : ∃ w : List Γ, wordEval act w χ ∈ A) :
    ∃ w₀ : List Γ, wordEval act w₀ χ ∈ A ∧
      ∀ w : List Γ, wordEval act w χ ∈ A → w₀.length ≤ w.length := by
  classical
  obtain ⟨v, hv⟩ := h
  have hex : ∃ n : ℕ, ∃ w : List Γ, w.length = n ∧ wordEval act w χ ∈ A := ⟨v.length, v, rfl, hv⟩
  obtain ⟨w₀, hw₀len, hw₀⟩ := Nat.find_spec hex
  refine ⟨w₀, hw₀, fun w hw => ?_⟩
  rw [hw₀len]
  exact Nat.find_le ⟨w, rfl, hw⟩

end MinimalWord

section TropicalRecovery

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] {X : Type*}

/-- The real-valued discounted first-hit mass at a real discount. -/
noncomputable def firstHitMassReal (act : Γ → X → X) (χ : X) (A : Set X) (t : ℝ) : ℝ :=
  (firstHitMass act χ A (ENNReal.ofReal t)).toReal

theorem firstHitMass_le_one (act : Γ → X → X) (χ : X) (A : Set X) {a : ℝ≥0∞} (ha : a ≤ 1) :
    firstHitMass act χ A a ≤ 1 := by
  simpa using firstHitMass_le_pow act χ A ha (c := 0) (fun w _ => Nat.zero_le _)

theorem firstHitMass_ne_top (act : Γ → X → X) (χ : X) (A : Set X) {a : ℝ≥0∞} (ha : a ≤ 1) :
    firstHitMass act χ A a ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (firstHitMass_le_one act χ A ha)

/-- **Real complexity sandwich.**  At a discount in the unit interval the real first-hit mass is
squeezed between the two powers of the minimal hitting length. -/
theorem firstHitMassReal_sandwich (act : Γ → X → X) (χ : X) (A : Set X) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {w₀ : List Γ} (hw₀ : wordEval act w₀ χ ∈ A)
    (hmin : ∀ w : List Γ, wordEval act w χ ∈ A → w₀.length ≤ w.length) :
    (t / Fintype.card Γ) ^ w₀.length ≤ firstHitMassReal act χ A t ∧
      firstHitMassReal act χ A t ≤ t ^ w₀.length := by
  have hM : (0 : ℝ) < Fintype.card Γ := by
    exact_mod_cast Fintype.card_pos (α := Γ)
  have haE : ENNReal.ofReal t ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ht1.le
  have hFtop : firstHitMass act χ A (ENNReal.ofReal t) ≠ ⊤ := firstHitMass_ne_top act χ A haE
  have hlow := pow_le_firstHitMass act χ A (ENNReal.ofReal t) hw₀ hmin
  have hhigh := firstHitMass_le_pow act χ A haE (c := w₀.length)
    (fun w hw => hmin w hw.1)
  have hdivtop : (ENNReal.ofReal t / (Fintype.card Γ : ℝ≥0∞)) ^ w₀.length ≠ ⊤ := by
    refine ENNReal.pow_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top ?_)
    simp
  have hlowreal : ((ENNReal.ofReal t / (Fintype.card Γ : ℝ≥0∞)) ^ w₀.length).toReal =
      (t / Fintype.card Γ) ^ w₀.length := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofReal ht0.le,
      ENNReal.toReal_natCast]
  have hhighreal : ((ENNReal.ofReal t) ^ w₀.length).toReal = t ^ w₀.length := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal ht0.le]
  constructor
  · rw [← hlowreal, firstHitMassReal]
    exact (ENNReal.toReal_le_toReal hdivtop hFtop).mpr hlow
  · rw [← hhighreal, firstHitMassReal]
    exact (ENNReal.toReal_le_toReal hFtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mpr hhigh

theorem firstHitMassReal_pos (act : Γ → X → X) (χ : X) (A : Set X) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {w₀ : List Γ} (hw₀ : wordEval act w₀ χ ∈ A)
    (hmin : ∀ w : List Γ, wordEval act w χ ∈ A → w₀.length ≤ w.length) :
    0 < firstHitMassReal act χ A t := by
  have hM : (0 : ℝ) < Fintype.card Γ := by
    exact_mod_cast Fintype.card_pos (α := Γ)
  refine lt_of_lt_of_le ?_ (firstHitMassReal_sandwich act χ A ht0 ht1 hw₀ hmin).1
  exact pow_pos (div_pos ht0 hM) _

/-- **Exact zero-fugacity exponent.**  The minimal hitting length is the tropical limit of the
first-hit surprisal as the discount vanishes. -/
theorem tendsto_neg_log_firstHitMassReal (act : Γ → X → X) (χ : X) (A : Set X)
    {w₀ : List Γ} (hw₀ : wordEval act w₀ χ ∈ A)
    (hmin : ∀ w : List Γ, wordEval act w χ ∈ A → w₀.length ≤ w.length) :
    Filter.Tendsto
      (fun t : ℝ => -Real.log (firstHitMassReal act χ A t) / Real.log (1 / t))
      (𝓝[>] (0 : ℝ)) (𝓝 (w₀.length : ℝ)) := by
  have hM : (0 : ℝ) < Fintype.card Γ := by
    exact_mod_cast Fintype.card_pos (α := Γ)
  have hlogtop : Filter.Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] (0 : ℝ)) Filter.atTop := by
    have hb : Filter.Tendsto Real.log (𝓝[>] (0 : ℝ)) Filter.atBot := Real.tendsto_log_nhdsGT_zero
    have := Filter.tendsto_neg_atTop_iff.mpr hb
    refine this.congr fun t => ?_
    rw [one_div, Real.log_inv]
  have hupper : Filter.Tendsto
      (fun t : ℝ => (w₀.length : ℝ) +
        (w₀.length : ℝ) * Real.log (Fintype.card Γ) / Real.log (1 / t))
      (𝓝[>] (0 : ℝ)) (𝓝 (w₀.length : ℝ)) := by
    have hzero := Filter.Tendsto.const_add ((w₀.length : ℝ))
      (Filter.Tendsto.div_atTop
        (tendsto_const_nhds (x := (w₀.length : ℝ) * Real.log (Fintype.card Γ))
          (f := 𝓝[>] (0 : ℝ))) hlogtop)
    simpa using hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hL : 0 < Real.log (1 / t) := by
      rw [one_div]
      exact Real.log_pos (one_lt_inv_iff₀.mpr ⟨ht0, ht1⟩)
    have hF := firstHitMassReal_sandwich act χ A ht0 ht1 hw₀ hmin
    have hFpos := firstHitMassReal_pos act χ A ht0 ht1 hw₀ hmin
    have hlog : Real.log (firstHitMassReal act χ A t) ≤ (w₀.length : ℝ) * Real.log t := by
      refine le_trans (Real.log_le_log hFpos hF.2) (le_of_eq ?_)
      rw [Real.log_pow]
    have hkey : (w₀.length : ℝ) * Real.log (1 / t) ≤ -Real.log (firstHitMassReal act χ A t) := by
      rw [one_div, Real.log_inv]
      linarith
    rw [le_div_iff₀ hL]
    exact hkey
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hL : 0 < Real.log (1 / t) := by
      rw [one_div]
      exact Real.log_pos (one_lt_inv_iff₀.mpr ⟨ht0, ht1⟩)
    have hF := firstHitMassReal_sandwich act χ A ht0 ht1 hw₀ hmin
    have hFpos := firstHitMassReal_pos act χ A ht0 ht1 hw₀ hmin
    have hlowpos : (0 : ℝ) < (t / Fintype.card Γ) ^ w₀.length := pow_pos (div_pos ht0 hM) _
    have hlog : (w₀.length : ℝ) * (Real.log t - Real.log (Fintype.card Γ)) ≤
        Real.log (firstHitMassReal act χ A t) := by
      refine le_trans (le_of_eq ?_) (Real.log_le_log hlowpos hF.1)
      rw [Real.log_pow, Real.log_div ht0.ne' hM.ne']
    have hkey : -Real.log (firstHitMassReal act χ A t) ≤
        (w₀.length : ℝ) * Real.log (1 / t) +
          (w₀.length : ℝ) * Real.log (Fintype.card Γ) := by
      rw [one_div, Real.log_inv]
      nlinarith [hlog]
    rw [div_le_iff₀ hL, add_mul, div_mul_cancel₀ _ hL.ne']
    calc -Real.log (firstHitMassReal act χ A t)
        ≤ (w₀.length : ℝ) * Real.log (1 / t) +
          (w₀.length : ℝ) * Real.log (Fintype.card Γ) := hkey
      _ = (w₀.length : ℝ) * Real.log (1 / t) +
          (w₀.length : ℝ) * Real.log (Fintype.card Γ) := rfl

end TropicalRecovery

section CompleteUnion

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] {X : Type*}

/-- The event that some target in a family is reachable within a fixed synthesis length. -/
def reachableWithin (act : Γ → X → X) (χ : X) {Ω ι : Type*} (A : ι → Set X) (V : Ω → ι)
    (s : ℕ) : Set Ω :=
  {ω : Ω | ∃ w : List Γ, w.length ≤ s ∧ wordEval act w χ ∈ A (V ω)}

/-- The indicator of the reachable event is dominated by a fixed multiple of the first-hit mass. -/
theorem indicator_reachableWithin_le (act : Γ → X → X) (χ : X) {Ω ι : Type*} (A : ι → Set X)
    (V : Ω → ι) {a : ℝ≥0∞} (ha0 : a ≠ 0) (ha1 : a ≤ 1) (s : ℕ) (ω : Ω) :
    Set.indicator (reachableWithin act χ A V s) 1 ω ≤
      ((Fintype.card Γ : ℝ≥0∞) / a) ^ s * firstHitMass act χ (A (V ω)) a := by
  classical
  have hMne : (Fintype.card Γ : ℝ≥0∞) ≠ 0 := by simp
  have hMtop : (Fintype.card Γ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  by_cases hω : ω ∈ reachableWithin act χ A V s
  · obtain ⟨v, hvlen, hv⟩ := id hω
    obtain ⟨w₀, hw₀, hmin⟩ := exists_minimal_hitting_word act χ (A (V ω)) ⟨v, hv⟩
    have hlen : w₀.length ≤ s := le_trans (hmin v hv) hvlen
    have hMone : (1 : ℝ≥0∞) ≤ (Fintype.card Γ : ℝ≥0∞) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := Γ))
    have haM : a / (Fintype.card Γ : ℝ≥0∞) ≤ 1 :=
      ENNReal.div_le_of_le_mul (by simpa using le_trans ha1 hMone)
    have hstep : (a / (Fintype.card Γ : ℝ≥0∞)) ^ s ≤ firstHitMass act χ (A (V ω)) a :=
      le_trans (pow_le_pow_right_of_le_one' haM hlen)
        (pow_le_firstHitMass act χ (A (V ω)) a hw₀ hmin)
    have hcancel : ((Fintype.card Γ : ℝ≥0∞) / a) ^ s * (a / (Fintype.card Γ : ℝ≥0∞)) ^ s = 1 := by
      have h1 : ((Fintype.card Γ : ℝ≥0∞) / a) * (a / (Fintype.card Γ : ℝ≥0∞)) = 1 := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc a⁻¹ a,
          ENNReal.inv_mul_cancel ha0 hatop, one_mul, ENNReal.mul_inv_cancel hMne hMtop]
      rw [← mul_pow, h1, one_pow]
    rw [Set.indicator_of_mem hω]
    show (1 : ℝ≥0∞) ≤ _
    calc (1 : ℝ≥0∞)
        = ((Fintype.card Γ : ℝ≥0∞) / a) ^ s * (a / (Fintype.card Γ : ℝ≥0∞)) ^ s := hcancel.symm
      _ ≤ ((Fintype.card Γ : ℝ≥0∞) / a) ^ s * firstHitMass act χ (A (V ω)) a :=
          mul_le_mul_right hstep _
  · rw [Set.indicator_of_notMem hω]
    exact bot_le

/-- **First-hit complete-union bound.**  The measure of the event that a random target is reachable
within a fixed synthesis length is controlled by a single first-hit moment. -/
theorem measure_reachableWithin_le_lintegral (act : Γ → X → X) (χ : X) {Ω ι : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (A : ι → Set X) (V : Ω → ι) (R : Set Ω)
    {a : ℝ≥0∞} (ha0 : a ≠ 0) (ha1 : a ≤ 1) (s : ℕ)
    (hE : MeasurableSet (reachableWithin act χ A V s)) :
    μ (reachableWithin act χ A V s ∩ R) ≤
      ((Fintype.card Γ : ℝ≥0∞) / a) ^ s * ∫⁻ ω in R, firstHitMass act χ (A (V ω)) a ∂μ := by
  have hconst : ((Fintype.card Γ : ℝ≥0∞) / a) ^ s ≠ ⊤ :=
    ENNReal.pow_ne_top (by simp [ENNReal.div_eq_top, ha0])
  calc μ (reachableWithin act χ A V s ∩ R)
      = (μ.restrict R) (reachableWithin act χ A V s) := (Measure.restrict_apply hE).symm
    _ = ∫⁻ ω in R, Set.indicator (reachableWithin act χ A V s) 1 ω ∂μ :=
        (lintegral_indicator_one hE).symm
    _ ≤ ∫⁻ ω in R, ((Fintype.card Γ : ℝ≥0∞) / a) ^ s * firstHitMass act χ (A (V ω)) a ∂μ :=
        lintegral_mono fun ω => indicator_reachableWithin_le act χ A V ha0 ha1 s ω
    _ = ((Fintype.card Γ : ℝ≥0∞) / a) ^ s * ∫⁻ ω in R, firstHitMass act χ (A (V ω)) a ∂μ :=
        lintegral_const_mul' _ _ hconst

end CompleteUnion

end GaloisForLFunctions.RHTower
