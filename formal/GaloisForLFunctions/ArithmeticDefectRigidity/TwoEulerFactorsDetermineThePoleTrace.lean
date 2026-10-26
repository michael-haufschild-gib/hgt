import GaloisForLFunctions.ArithmeticDefectRigidity.OnePrimeEulerLawsLeavePeriodicGhosts
import GaloisForLFunctions.ArithmeticDefectRigidity.TheEtaRenormalizationIsPoleFree
import GaloisForLFunctions.ArithmeticDefectRigidity.CofactorEigenstatesSplitOverTranslatedZeros

/-!
# Two Euler factors determine the pole trace

For `0 < ε < 1/2` and `α = 1 − ε`, the Euler-factor law at `p` asks that `w − p^α D_p w` have finite
pronic energy, `D_p w(n) = w(⌊n/p⌋)`. It is trace-free and defined on every row.

* `exists_pronicEnergy_sub_pole_ne_top`: if `w(0) = 0` and the laws at `2` and `3` hold, then
  `w − c n^α` has finite pronic energy for a constant `c`, unique by
  `eq_of_pronicEnergy_sub_pole_ne_top`; conversely every law holds then
  (`pronicEnergy_eulerLaw_ne_top`).
* `one_euler_factor_leaves_a_ghost`: one law is not enough. The dyadic ghost
  `n^α cos(2π log₂ n)` passes the law at `2`, yet differs from every `c n^α` by infinite energy.
* `cofactor_two_euler_laws_iff`: for the total cofactor sum `S_ε v(n) = Σ_{j≤n} j^{-ε} v(⌊n/j⌋)`,
  the alternating (eta) law and the `3`-adic law together are equivalent to the renormalized
  inversion law `S_ε v − c n^α` admitted.

The log-scale profile `g(u) = e^{-u/2} w(⌊e^u⌋)` turns pronic energy into `∫ g²`
(`lintegral_logProfile_sq`) and the law at `p` into `g − p^{1/2−ε} g(· − log p) ∈ L²`
(`lawDefect_logProfile`); the two-law theorem on the line then applies with the incommensurable
periods `log 2`, `log 3`.
-/

open MeasureTheory Filter Topology Set Finset
open GaloisForLFunctions.BezoutValuationIncidence (pronicNorm pronicNorm_nonneg pronicNorm_sq
  pronicNorm_add_le)
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-! ### Pronic energy on the log scale -/

/-- The full-horizon pronic energy `Σ_{n≥1} v(n)²/(n(n+1))`. -/
def pronicEnergy (v : ℕ → ℝ) : ENNReal :=
  ∑' n : ℕ, ENNReal.ofReal (v (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))

/-- The log-scale profile `g(u) = e^{-u/2} v(⌊e^u⌋)`. -/
def logProfile (v : ℕ → ℝ) (u : ℝ) : ℝ := Real.exp (-(u / 2)) * v ⌊Real.exp u⌋₊

theorem measurable_logProfile (v : ℕ → ℝ) : Measurable (logProfile v) :=
  (Real.measurable_exp.comp (measurable_id.div_const 2).neg).mul
    (measurable_from_nat.comp (Nat.measurable_floor.comp Real.measurable_exp))

theorem lintegral_Ico_exp_neg {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ u in Ico a b, ENNReal.ofReal (Real.exp (-u)) =
      ENNReal.ofReal (Real.exp (-a) - Real.exp (-b)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_comp_neg (fun x => Real.exp x),
      integral_exp]
  · exact ((Real.continuous_exp.comp continuous_neg).integrableOn_Icc).mono_set Ico_subset_Icc_self
  · exact Eventually.of_forall fun u => (Real.exp_pos _).le

theorem mem_Ico_log_iff {u : ℝ} (n : ℕ) :
    u ∈ Ico (Real.log ((n : ℝ) + 1)) (Real.log ((n : ℝ) + 2)) ↔ ⌊Real.exp u⌋₊ = n + 1 := by
  rw [Set.mem_Ico, Real.log_le_iff_le_exp (by positivity), Real.lt_log_iff_exp_lt (by positivity),
    Nat.floor_eq_iff (Real.exp_pos u).le]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- **The pronic energy is the log-scale `L²` energy.** -/
theorem lintegral_logProfile_sq {v : ℕ → ℝ} (hv0 : v 0 = 0) :
    ∫⁻ u, ENNReal.ofReal (logProfile v u ^ 2) = pronicEnergy v := by
  have hpt : ∀ u : ℝ, ENNReal.ofReal (logProfile v u ^ 2) = ∑' n : ℕ,
      (Ico (Real.log ((n : ℝ) + 1)) (Real.log ((n : ℝ) + 2))).indicator
        (fun u => ENNReal.ofReal (Real.exp (-u)) * ENNReal.ofReal (v (n + 1) ^ 2)) u := by
    intro u
    have hsq : logProfile v u ^ 2 = Real.exp (-u) * v ⌊Real.exp u⌋₊ ^ 2 := by
      rw [logProfile, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [hsq, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rcases Nat.eq_zero_or_pos ⌊Real.exp u⌋₊ with h0 | hpos
    · rw [h0, hv0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero,
        mul_zero]
      symm
      refine ENNReal.tsum_eq_zero.mpr fun n => indicator_of_notMem ?_ _
      rw [mem_Ico_log_iff, h0]
      omega
    · obtain ⟨k, hk⟩ : ∃ k, ⌊Real.exp u⌋₊ = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [tsum_eq_single k fun n hn => indicator_of_notMem (by rw [mem_Ico_log_iff, hk]; omega) _,
        indicator_of_mem ((mem_Ico_log_iff k).mpr hk), hk]
  have hme : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-u)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)
  have hm : ∀ n : ℕ, Measurable fun u => (Ico (Real.log ((n : ℝ) + 1))
      (Real.log ((n : ℝ) + 2))).indicator
        (fun u => ENNReal.ofReal (Real.exp (-u)) * ENNReal.ofReal (v (n + 1) ^ 2)) u :=
    fun n => (hme.mul_const _).indicator measurableSet_Ico
  simp_rw [hpt]
  rw [lintegral_tsum fun n => (hm n).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_indicator measurableSet_Ico, lintegral_mul_const _ hme,
    lintegral_Ico_exp_neg (Real.log_le_log (by positivity) (by linarith)),
    Real.exp_neg, Real.exp_neg, Real.exp_log (by positivity), Real.exp_log (by positivity),
    ← ENNReal.ofReal_mul (by
      rw [sub_nonneg]; exact inv_anti₀ (by positivity) (by linarith)), mul_comm]
  congr 1
  field_simp
  ring

/-- Finite pronic energy is the same as uniformly bounded pronic norms. -/
theorem pronicEnergy_ne_top_iff (v : ℕ → ℝ) :
    pronicEnergy v ≠ ⊤ ↔ ∃ B : ℝ, ∀ T : ℕ, pronicNorm T v ≤ B := by
  have hnn : ∀ n : ℕ, 0 ≤ v (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := fun n => by positivity
  have hsq : ∀ T : ℕ, pronicNorm T v ^ 2 =
      ∑ n ∈ range T, v (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro T
    rw [pronicNorm_sq]
    refine (sum_nbij' (fun n => n - 1) (fun n => n + 1) ?_ ?_ ?_ ?_ ?_)
    · intro n hn; simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢; omega
    · intro n hn; simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢; omega
    · intro n hn; simp only [Finset.mem_Icc] at hn; omega
    · intro n _; omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      have h1 : n - 1 + 1 = n := by omega
      rw [h1]
      congr 1
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]; ring
  constructor
  · intro h
    have hsum : Summable fun n : ℕ => v (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      refine (ENNReal.summable_toReal h).congr fun n => ?_
      rw [ENNReal.toReal_ofReal (hnn n)]
    refine ⟨Real.sqrt (∑' n, v (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))), fun T => ?_⟩
    rw [← Real.sqrt_sq (pronicNorm_nonneg T v), hsq]
    exact Real.sqrt_le_sqrt (hsum.sum_le_tsum _ fun n _ => hnn n)
  · rintro ⟨B, hB⟩
    have hsum : Summable fun n : ℕ => v (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      refine summable_of_sum_range_le hnn (c := B ^ 2) fun T => ?_
      rw [← hsq]
      exact pow_le_pow_left₀ (pronicNorm_nonneg T v) (hB T) 2
    rw [pronicEnergy, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
    exact ENNReal.ofReal_ne_top

/-! ### The Euler-factor law on the log scale -/

/-- The Euler-factor defect `w − p^a D_p w`. -/
def eulerLaw (p : ℕ) (a : ℝ) (w : ℕ → ℝ) (n : ℕ) : ℝ := w n - (p : ℝ) ^ a * w (n / p)

/-- **The law at `p` is the one-prime law with period `log p`.** -/
theorem lawDefect_logProfile {p : ℕ} (hp : 0 < p) (κ : ℝ) (w : ℕ → ℝ) (u : ℝ) :
    lawDefect κ (Real.log p) (logProfile w) u = logProfile (eulerLaw p (κ + 1 / 2) w) u := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hfl : ⌊Real.exp (u - Real.log p)⌋₊ = ⌊Real.exp u⌋₊ / p := by
    rw [Real.exp_sub, Real.exp_log hp0, Nat.floor_div_natCast]
  have hexp : Real.exp (κ * Real.log p) * Real.exp (-((u - Real.log p) / 2)) =
      (p : ℝ) ^ (κ + 1 / 2) * Real.exp (-(u / 2)) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos hp0, ← Real.exp_add]
    ring_nf
  rw [lawDefect, logProfile, logProfile, hfl, ← mul_assoc, hexp, logProfile, eulerLaw]
  ring

theorem eulerLaw_zero {p : ℕ} (a : ℝ) {w : ℕ → ℝ} (hw0 : w 0 = 0) : eulerLaw p a w 0 = 0 := by
  simp [eulerLaw, hw0]

theorem addOrderOf_log_two_in_log_three :
    addOrderOf ((Real.log 2 : ℝ) : AddCircle (Real.log 3)) = 0 := by
  rw [addOrderOf_eq_zero_iff']
  intro n hn h
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  rw [zsmul_eq_mul, nsmul_eq_mul] at hm
  have h0 := int_eq_zero_of_two_zpow_eq_three_zpow (a := n) (b := m) (by push_cast; linarith)
  omega

theorem addOrderOf_log_three_in_log_two :
    addOrderOf ((Real.log 3 : ℝ) : AddCircle (Real.log 2)) = 0 := by
  rw [addOrderOf_eq_zero_iff']
  intro n hn h
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  rw [zsmul_eq_mul, nsmul_eq_mul] at hm
  have h0 := int_eq_zero_of_two_zpow_eq_three_zpow (a := m) (b := n) (by push_cast; linarith)
  rw [h0, Int.cast_zero, zero_mul] at hm
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have : (n : ℝ) = 0 := by nlinarith
  exact absurd (by exact_mod_cast this : n = 0) (by omega)

/-! ### The pole power on the log scale -/

/-- `0 ≤ x^α − ⌊x⌋^α ≤ 1` for `x ≥ 1`, `0 < α ≤ 1`. -/
theorem rpow_sub_floor_rpow_mem {α x : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hx : 1 ≤ x) :
    0 ≤ x ^ α - (⌊x⌋₊ : ℝ) ^ α ∧ x ^ α - (⌊x⌋₊ : ℝ) ^ α ≤ 1 := by
  have hx0 : 0 ≤ x := by linarith
  have hm : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hm1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  refine ⟨sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg _) hm hα.le), ?_⟩
  have hsub := Real.rpow_add_le_add_rpow (Nat.cast_nonneg ⌊x⌋₊) (sub_nonneg.mpr hm) hα.le hα1
  rw [add_sub_cancel] at hsub
  have hone : (x - ⌊x⌋₊) ^ α ≤ 1 := Real.rpow_le_one (sub_nonneg.mpr hm) (by linarith) hα.le
  linarith

/-- The log profile of the pole power is `c e^{κu}` up to an error of energy `≤ c² e^{-u}`. -/
theorem logProfile_sub_pole_sq_le {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 2) (w : ℕ → ℝ) (c : ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    ENNReal.ofReal (logProfile (fun n => w n - c * (n : ℝ) ^ (κ + 1 / 2)) u ^ 2) ≤
      2 * ENNReal.ofReal ((logProfile w u - c * Real.exp (κ * u)) ^ 2) +
        2 * ENNReal.ofReal (c ^ 2 * Real.exp (-u)) := by
  have hx : 1 ≤ Real.exp u := Real.one_le_exp hu
  obtain ⟨hD0, hD1⟩ := rpow_sub_floor_rpow_mem (α := κ + 1 / 2) (by positivity) (by linarith) hx
  set D := Real.exp u ^ (κ + 1 / 2) - (⌊Real.exp u⌋₊ : ℝ) ^ (κ + 1 / 2)
  have hexpκ : Real.exp (κ * u) = Real.exp (-(u / 2)) * Real.exp u ^ (κ + 1 / 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, ← Real.exp_add]; ring_nf
  have hid : logProfile (fun n => w n - c * (n : ℝ) ^ (κ + 1 / 2)) u =
      (logProfile w u - c * Real.exp (κ * u)) - (-(c * Real.exp (-(u / 2)) * D)) := by
    rw [logProfile, logProfile, hexpκ]; ring
  rw [hid]
  refine (ofReal_sq_sub_le _ _).trans (add_le_add le_rfl ?_)
  gcongr
  have he : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by rw [← Real.exp_nat_mul]; ring_nf
  rw [neg_sq, mul_pow, mul_pow, he]
  have hD2 : D ^ 2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_right (by positivity) hD2

theorem lintegral_Ici_exp_neg_ne_top :
    ∫⁻ u in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-u)) ≠ ⊤ := by
  have h : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [neg_mul, one_mul] using exp_neg_integrableOn_Ioi 0 one_pos
  exact (Integrable.lintegral_lt_top h).ne

/-! ### Two Euler factors -/

/-- **Two Euler factors determine the pole.** For `0 < ε < 1/2`, `α = 1 − ε`, a row with `w(0) = 0`
whose Euler-factor laws at `2` and `3` have finite pronic energy is `c n^α` modulo finite energy. -/
theorem exists_pronicEnergy_sub_pole_ne_top {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) {w : ℕ → ℝ}
    (hw0 : w 0 = 0) (h2 : pronicEnergy (eulerLaw 2 (1 - ε) w) ≠ ⊤)
    (h3 : pronicEnergy (eulerLaw 3 (1 - ε) w) ≠ ⊤) :
    ∃ c : ℝ, pronicEnergy (fun n => w n - c * (n : ℝ) ^ (1 - ε)) ≠ ⊤ := by
  set κ : ℝ := 1 / 2 - ε with hκdef
  have hκ0 : 0 < κ := by rw [hκdef]; linarith
  have hκ1 : κ ≤ 1 / 2 := by rw [hκdef]; linarith
  have hα : κ + 1 / 2 = 1 - ε := by rw [hκdef]; ring
  have hlaw : ∀ p : ℕ, 0 < p → pronicEnergy (eulerLaw p (1 - ε) w) ≠ ⊤ →
      ∫⁻ u, ENNReal.ofReal (lawDefect κ (Real.log p) (logProfile w) u ^ 2) ≠ ⊤ := by
    intro p hp h
    have hfun : (fun u => ENNReal.ofReal (lawDefect κ (Real.log p) (logProfile w) u ^ 2)) =
        fun u => ENNReal.ofReal (logProfile (eulerLaw p (1 - ε) w) u ^ 2) := by
      funext u; rw [lawDefect_logProfile hp, hα]
    rw [hfun, lintegral_logProfile_sq (eulerLaw_zero _ hw0)]
    exact h
  have h2' := hlaw 2 (by norm_num) h2
  have h3' := hlaw 3 (by norm_num) h3
  rw [Nat.cast_ofNat] at h2' h3'
  obtain ⟨c, hc⟩ := exists_lintegral_sub_const_mul_exp_ne_top hκ0
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (Real.log_pos (by norm_num : (1 : ℝ) < 3))
    addOrderOf_log_two_in_log_three addOrderOf_log_three_in_log_two (measurable_logProfile w)
    h2' h3'
  refine ⟨c, ?_⟩
  have hrow0 : (fun n : ℕ => w n - c * (n : ℝ) ^ (1 - ε)) 0 = 0 := by
    simp [hw0, Real.zero_rpow (by linarith : (1 : ℝ) - ε ≠ 0)]
  rw [← lintegral_logProfile_sq hrow0]
  have hbound : ∀ u : ℝ, ENNReal.ofReal (logProfile (fun n => w n - c * (n : ℝ) ^ (1 - ε)) u ^ 2) ≤
      2 * ENNReal.ofReal ((logProfile w u - c * Real.exp (κ * u)) ^ 2) +
        2 * (Ici (0 : ℝ)).indicator (fun u => ENNReal.ofReal (c ^ 2 * Real.exp (-u))) u := by
    intro u
    rcases lt_or_ge u 0 with hu | hu
    · have hfl : ⌊Real.exp u⌋₊ = 0 :=
        Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr hu)
      have h0 : logProfile (fun n => w n - c * (n : ℝ) ^ (1 - ε)) u = 0 := by
        rw [logProfile, hfl]
        simp [hw0, Real.zero_rpow (by linarith : (1 : ℝ) - ε ≠ 0)]
      rw [h0]
      simp
    · rw [indicator_of_mem (Set.mem_Ici.mpr hu), ← hα]
      exact logProfile_sub_pole_sq_le hκ0 hκ1 w c hu
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hbound)
  have hmA : Measurable fun u => 2 * ENNReal.ofReal ((logProfile w u - c * Real.exp (κ * u)) ^ 2) :=
    ((ENNReal.measurable_ofReal.comp (((measurable_logProfile w).sub
      (measurable_const.mul (Real.measurable_exp.comp (measurable_id.const_mul κ)))).pow_const 2))).const_mul 2
  rw [lintegral_add_left hmA, lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by norm_num), lintegral_indicator measurableSet_Ici]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hc,
    ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) ?_⟩
  have hme : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-u)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)
  simp_rw [ENNReal.ofReal_mul (sq_nonneg c)]
  rw [lintegral_const_mul _ hme]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top lintegral_Ici_exp_neg_ne_top

/-! ### Uniqueness and the converse -/

theorem pronicEnergy_add_le (a b : ℕ → ℝ) :
    pronicEnergy (fun n => a n + b n) ≤ 2 * pronicEnergy a + 2 * pronicEnergy b := by
  rw [pronicEnergy, pronicEnergy, pronicEnergy, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun n => ?_
  have hq : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have h := ofReal_sq_sub_le (a (n + 1) / Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)))
    (-(b (n + 1) / Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2))))
  have hs : Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) ^ 2 = ((n : ℝ) + 1) * ((n : ℝ) + 2) :=
    Real.sq_sqrt hq.le
  rw [sub_neg_eq_add, ← add_div, div_pow, div_pow, neg_sq, div_pow, hs] at h
  exact h

theorem pronicEnergy_neg (b : ℕ → ℝ) : pronicEnergy (fun n => -b n) = pronicEnergy b := by
  simp only [pronicEnergy, neg_sq]

/-- **The pole coefficient is unique.** -/
theorem eq_of_pronicEnergy_sub_pole_ne_top {ε : ℝ} (hε : ε < 1 / 2) {w : ℕ → ℝ}
    {c c' : ℝ} (h : pronicEnergy (fun n => w n - c * (n : ℝ) ^ (1 - ε)) ≠ ⊤)
    (h' : pronicEnergy (fun n => w n - c' * (n : ℝ) ^ (1 - ε)) ≠ ⊤) : c = c' := by
  by_contra hne
  have hd : pronicEnergy (fun n => (c' - c) * (n : ℝ) ^ (1 - ε)) ≠ ⊤ := by
    have hle := pronicEnergy_add_le (fun n => w n - c * (n : ℝ) ^ (1 - ε))
      (fun n => -(w n - c' * (n : ℝ) ^ (1 - ε)))
    rw [pronicEnergy_neg] at hle
    have hfun : (fun n : ℕ => (w n - c * (n : ℝ) ^ (1 - ε)) + -(w n - c' * (n : ℝ) ^ (1 - ε))) =
        fun n : ℕ => (c' - c) * (n : ℝ) ^ (1 - ε) := funext fun n => by ring
    rw [hfun] at hle
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) h,
      ENNReal.mul_ne_top (by norm_num) h'⟩) hle
  have hnn : ∀ n : ℕ, 0 ≤ ((c' - c) * (((n + 1 : ℕ) : ℝ)) ^ (1 - ε)) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) := fun n => by positivity
  have hsum : Summable fun n : ℕ => ((c' - c) * (((n + 1 : ℕ) : ℝ)) ^ (1 - ε)) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    refine (ENNReal.summable_toReal hd).congr fun n => ?_
    rw [ENNReal.toReal_ofReal (hnn n)]
  have hpos : 0 < (c' - c) ^ 2 := by
    have : c' - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    positivity
  have hlow : ∀ n : ℕ, (c' - c) ^ 2 / 2 * (1 / ((n : ℝ) + 1)) ≤
      ((c' - c) * (((n + 1 : ℕ) : ℝ)) ^ (1 - ε)) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hpow : (((n + 1 : ℕ) : ℝ) ^ (1 - ε)) ^ 2 =
        ((n : ℝ) + 1) ^ (2 : ℕ) * ((n : ℝ) + 1) ^ (-(2 * ε)) := by
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast ((n : ℝ) + 1) 2,
        ← Real.rpow_add (by positivity)]
      norm_num; ring_nf
    have hexp : ((n : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1) ^ (-(2 * ε)) := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hq : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≤ 2 * ((n : ℝ) + 1) ^ 2 := by nlinarith
    have hA := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) (-(2 * ε))
    rw [mul_pow, hpow]
    calc (c' - c) ^ 2 / 2 * (1 / ((n : ℝ) + 1)) = (c' - c) ^ 2 / 2 * ((n : ℝ) + 1)⁻¹ := by
          rw [one_div]
      _ ≤ (c' - c) ^ 2 / 2 * ((n : ℝ) + 1) ^ (-(2 * ε)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (c' - c) ^ 2 * (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * ε))) /
            (2 * ((n : ℝ) + 1) ^ 2) := by field_simp
      _ ≤ (c' - c) ^ 2 * (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ (-(2 * ε))) /
            (((n : ℝ) + 1) * ((n : ℝ) + 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hq
  have hharm : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    have := (hsum.of_nonneg_of_le (fun n => by positivity) hlow).mul_left (2 / (c' - c) ^ 2)
    refine this.congr fun n => ?_
    field_simp
  have : Summable fun n : ℕ => 1 / (n : ℝ) := by
    refine (summable_nat_add_iff 1).mp (hharm.congr fun n => ?_)
    push_cast; ring
  exact Real.not_summable_one_div_natCast this

/-- Rows bounded by `K` have pronic norm at most `K`. -/
theorem pronicNorm_le_of_abs_le {v : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hv : ∀ n, |v n| ≤ K) (T : ℕ) :
    pronicNorm T v ≤ K := by
  rw [← Real.sqrt_sq (pronicNorm_nonneg T v), pronicNorm_sq, ← Real.sqrt_sq hK]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ n ∈ Icc 1 T, v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
      ≤ ∑ n ∈ Icc 1 T, K ^ 2 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
        refine sum_le_sum fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        rw [show 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) by
          field_simp; ring, mul_one_div]
        have hv2 : v n ^ 2 ≤ K ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hv n) 2
        exact div_le_div_of_nonneg_right hv2 (by positivity)
    _ = K ^ 2 * (1 - 1 / ((T : ℝ) + 1)) := by rw [← mul_sum, sum_Icc_one_div_sub_one_div_succ]
    _ ≤ K ^ 2 := by
        have : 0 ≤ 1 / ((T : ℝ) + 1) := by positivity
        nlinarith [sq_nonneg K]

/-- The pole power passes every Euler law: `0 ≤ n^α − p^α⌊n/p⌋^α ≤ p^α`. -/
theorem abs_pole_eulerLaw_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    |(n : ℝ) ^ α - (p : ℝ) ^ α * ((n / p : ℕ) : ℝ) ^ α| ≤ (p : ℝ) ^ α := by
  have hmul : (p : ℝ) ^ α * ((n / p : ℕ) : ℝ) ^ α = ((p * (n / p) : ℕ) : ℝ) ^ α := by
    push_cast; rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  rw [hmul]
  have hle : ((p * (n / p) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mul_div_le n p
  have hlt : n < p * (n / p + 1) := Nat.lt_mul_div_succ n (by omega)
  have hgap : (n : ℝ) - ((p * (n / p) : ℕ) : ℝ) ≤ p := by
    have : (n : ℝ) < ((p * (n / p + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at this ⊢; linarith
  have hmono := Real.rpow_le_rpow (Nat.cast_nonneg _) hle hα.le
  have hsub := Real.rpow_add_le_add_rpow (Nat.cast_nonneg (p * (n / p))) (sub_nonneg.mpr hle)
    hα.le hα1
  rw [add_sub_cancel] at hsub
  have hgapα : ((n : ℝ) - ((p * (n / p) : ℕ) : ℝ)) ^ α ≤ (p : ℝ) ^ α :=
    Real.rpow_le_rpow (sub_nonneg.mpr hle) hgap hα.le
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  linarith

/-- **Converse.** If `w − c n^α` has finite pronic energy, every Euler law of `w` does. -/
theorem pronicEnergy_eulerLaw_ne_top {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) {w : ℕ → ℝ}
    (hw0 : w 0 = 0) {c : ℝ} (h : pronicEnergy (fun n => w n - c * (n : ℝ) ^ (1 - ε)) ≠ ⊤)
    {p : ℕ} (hp : 1 ≤ p) : pronicEnergy (eulerLaw p (1 - ε) w) ≠ ⊤ := by
  set u : ℕ → ℝ := fun n => w n - c * (n : ℝ) ^ (1 - ε) with hu
  have hu0 : u 0 = 0 := by simp [hu, hw0, Real.zero_rpow (by linarith : (1 : ℝ) - ε ≠ 0)]
  obtain ⟨B, hB⟩ := (pronicEnergy_ne_top_iff u).mp h
  have hP : 0 ≤ (p : ℝ) ^ (1 - ε) := by positivity
  set K := |c| * (p : ℝ) ^ (1 - ε)
  rw [pronicEnergy_ne_top_iff]
  refine ⟨B + (p : ℝ) ^ (1 - ε) * (Real.sqrt (2 / (p : ℝ)) * B) + K, fun T => ?_⟩
  have hrow : eulerLaw p (1 - ε) w = fun n => (u n + (p : ℝ) ^ (1 - ε) * (-(rowDilate p u n))) +
      c * ((n : ℝ) ^ (1 - ε) - (p : ℝ) ^ (1 - ε) * ((n / p : ℕ) : ℝ) ^ (1 - ε)) := by
    funext n; simp only [eulerLaw, hu, rowDilate]; ring
  rw [hrow]
  have h1 := pronicNorm_add_le T (fun n => u n + (p : ℝ) ^ (1 - ε) * (-(rowDilate p u n)))
    (fun n => c * ((n : ℝ) ^ (1 - ε) - (p : ℝ) ^ (1 - ε) * ((n / p : ℕ) : ℝ) ^ (1 - ε)))
  have h2 := pronicNorm_add_le T u (fun n => (p : ℝ) ^ (1 - ε) * (-(rowDilate p u n)))
  have h3 : pronicNorm T (fun n => (p : ℝ) ^ (1 - ε) * (-(rowDilate p u n))) =
      (p : ℝ) ^ (1 - ε) * pronicNorm T (rowDilate p u) := by
    rw [pronicNorm_const_mul hP, pronicNorm_neg]
  have h4 := pronicNorm_rowDilate_le hp T u hu0
  have h5 : pronicNorm T (fun n => c * ((n : ℝ) ^ (1 - ε) -
      (p : ℝ) ^ (1 - ε) * ((n / p : ℕ) : ℝ) ^ (1 - ε))) ≤ K :=
    pronicNorm_le_of_abs_le (by positivity) (fun n => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_pole_eulerLaw_le (by linarith) (by linarith) hp n)
        (abs_nonneg c)) T
  have h6 : (p : ℝ) ^ (1 - ε) * pronicNorm T (rowDilate p u) ≤
      (p : ℝ) ^ (1 - ε) * (Real.sqrt (2 / (p : ℝ)) * B) :=
    mul_le_mul_of_nonneg_left (h4.trans (mul_le_mul_of_nonneg_left (hB T) (Real.sqrt_nonneg _))) hP
  linarith [hB T]

/-! ### The cofactor sum -/

/-- **The two eta laws are the renormalized inversion law.** For any row `v`, the alternating
cofactor sum and the `3`-adic Euler law of the total cofactor sum have finite pronic energy iff
`S_ε v − c n^{1−ε}` does for some `c`. -/
theorem cofactor_two_euler_laws_iff {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) (v : ℕ → ℝ) :
    (pronicEnergy (etaCofactorSum ε v) ≠ ⊤ ∧
        pronicEnergy (eulerLaw 3 (1 - ε) (totalCofactorSum ε v)) ≠ ⊤) ↔
      ∃ c : ℝ, pronicEnergy (fun n => totalCofactorSum ε v n - c * (n : ℝ) ^ (1 - ε)) ≠ ⊤ := by
  have heta : etaCofactorSum ε v = eulerLaw 2 (1 - ε) (totalCofactorSum ε v) := by
    funext n; rw [etaCofactorSum_eq, eulerLaw]; norm_num
  rw [heta]
  constructor
  · rintro ⟨h2, h3⟩
    exact exists_pronicEnergy_sub_pole_ne_top hε0 hε (totalCofactorSum_zero ε v) h2 h3
  · rintro ⟨c, hc⟩
    exact ⟨pronicEnergy_eulerLaw_ne_top hε0 hε (totalCofactorSum_zero ε v) hc (by norm_num),
      pronicEnergy_eulerLaw_ne_top hε0 hε (totalCofactorSum_zero ε v) hc (by norm_num)⟩

/-! ### One Euler factor is not enough -/

/-- The dyadic phase `θ(x) = 2π log x / log 2`, which advances by `2π` when `x` doubles. -/
def dyadicPhase (x : ℝ) : ℝ := 2 * Real.pi * Real.log x / Real.log 2

/-- The `2`-adic ghost `n^α cos(2π log₂ n)`. -/
def dyadicGhost (α : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ α * Real.cos (dyadicPhase n)

theorem dyadicPhase_two_mul {x : ℝ} (hx : 0 < x) :
    dyadicPhase (2 * x) = dyadicPhase x + 2 * Real.pi := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [dyadicPhase, dyadicPhase, Real.log_mul (by norm_num) hx.ne']
  field_simp
  ring

/-- `|θ(x) − θ(m)| ≤ 2π (x − m)/(m log 2)` for `0 < m ≤ x`. -/
theorem abs_dyadicPhase_sub_le {m x : ℝ} (hm : 0 < m) (hmx : m ≤ x) :
    |dyadicPhase x - dyadicPhase m| ≤ 2 * Real.pi / Real.log 2 * ((x - m) / m) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log x - Real.log m ≤ (x - m) / m := by
    rw [← Real.log_div (by linarith) hm.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < x) hm)
    have he : x / m - 1 = (x - m) / m := by field_simp
    linarith
  have hlog0 : 0 ≤ Real.log x - Real.log m := sub_nonneg.mpr (Real.log_le_log hm hmx)
  rw [dyadicPhase, dyadicPhase, ← sub_div, ← mul_sub, abs_div, abs_of_pos hl2, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_nonneg hlog0]
  rw [div_le_iff₀ hl2]
  calc 2 * Real.pi * (Real.log x - Real.log m) ≤ 2 * Real.pi * ((x - m) / m) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 * Real.pi / Real.log 2 * ((x - m) / m) * Real.log 2 := by field_simp

/-- The step `|x^α cos θ(x) − m^α cos θ(m)| ≤ 1 + 2π/log 2` for `1 ≤ m ≤ x ≤ m + 1`. -/
theorem abs_ghost_step_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {m x : ℝ} (hm : 1 ≤ m)
    (hmx : m ≤ x) (hx : x ≤ m + 1) :
    |x ^ α * Real.cos (dyadicPhase x) - m ^ α * Real.cos (dyadicPhase m)| ≤
      1 + 2 * Real.pi / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm0 : 0 < m := by linarith
  have hpow : x ^ α - m ^ α ≤ 1 ∧ 0 ≤ x ^ α - m ^ α := by
    have hsub := Real.rpow_add_le_add_rpow hm0.le (sub_nonneg.mpr hmx) hα.le hα1
    rw [add_sub_cancel] at hsub
    have hone : (x - m) ^ α ≤ 1 := Real.rpow_le_one (sub_nonneg.mpr hmx) (by linarith) hα.le
    exact ⟨by linarith, sub_nonneg.mpr (Real.rpow_le_rpow hm0.le hmx hα.le)⟩
  have hmα : m ^ α ≤ m := by
    calc m ^ α ≤ m ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm hα1
      _ = m := Real.rpow_one m
  have hcos := Real.abs_cos_sub_cos_le (dyadicPhase x) (dyadicPhase m)
  have hph := abs_dyadicPhase_sub_le hm0 hmx
  have hsplit : x ^ α * Real.cos (dyadicPhase x) - m ^ α * Real.cos (dyadicPhase m) =
      (x ^ α - m ^ α) * Real.cos (dyadicPhase x) +
        m ^ α * (Real.cos (dyadicPhase x) - Real.cos (dyadicPhase m)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg hpow.2]
    exact (mul_le_of_le_one_right hpow.2 (Real.abs_cos_le_one _)).trans hpow.1
  · rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hm0.le α)]
    calc m ^ α * |Real.cos (dyadicPhase x) - Real.cos (dyadicPhase m)|
        ≤ m * (2 * Real.pi / Real.log 2 * ((x - m) / m)) :=
          mul_le_mul hmα (hcos.trans hph) (abs_nonneg _) hm0.le
      _ = 2 * Real.pi / Real.log 2 * (x - m) := by field_simp
      _ ≤ 2 * Real.pi / Real.log 2 * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * Real.pi / Real.log 2 := mul_one _

/-- **The ghost passes the law at `2`.** Its defect is bounded. -/
theorem abs_eulerLaw_two_dyadicGhost_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    |eulerLaw 2 α (dyadicGhost α) n| ≤ 1 + 2 * Real.pi / Real.log 2 := by
  have hK : 0 ≤ 1 + 2 * Real.pi / Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hg0 : dyadicGhost α 0 = 0 := by simp [dyadicGhost, Real.zero_rpow hα.ne']
  rcases Nat.eq_zero_or_pos (n / 2) with hm | hm
  · rw [eulerLaw, hm, hg0, mul_zero, sub_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hg0, abs_zero]; exact hK
    · have hn1 : n = 1 := by omega
      subst hn1
      simp only [dyadicGhost, Nat.cast_one, Real.one_rpow, one_mul, dyadicPhase, Real.log_one,
        mul_zero, zero_div, Real.cos_zero, abs_one]
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have : 0 ≤ 2 * Real.pi / Real.log 2 := by positivity
      linarith
  · have hm0 : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hm
    have hdbl : ((2 : ℕ) : ℝ) ^ α * dyadicGhost α (n / 2) =
        ((2 * (n / 2) : ℕ) : ℝ) ^ α * Real.cos (dyadicPhase ((2 * (n / 2) : ℕ) : ℝ)) := by
      rw [dyadicGhost]
      push_cast
      rw [dyadicPhase_two_mul hm0, Real.cos_add_two_pi, Real.mul_rpow (by norm_num) hm0.le]
      ring
    rw [eulerLaw, hdbl, dyadicGhost]
    have hle : ((2 * (n / 2) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mul_div_le n 2
    have hle1 : (n : ℝ) ≤ ((2 * (n / 2) : ℕ) : ℝ) + 1 := by
      have : n ≤ 2 * (n / 2) + 1 := by omega
      exact_mod_cast this
    have h1 : (1 : ℝ) ≤ ((2 * (n / 2) : ℕ) : ℝ) := by
      have : 1 ≤ 2 * (n / 2) := by omega
      exact_mod_cast this
    exact abs_ghost_step_le hα hα1 h1 hle hle1

theorem pronicEnergy_ne_top_of_abs_le {v : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hv : ∀ n, |v n| ≤ K) :
    pronicEnergy v ≠ ⊤ :=
  (pronicEnergy_ne_top_iff v).mpr ⟨K, pronicNorm_le_of_abs_le hK hv⟩

/-- On the log scale the ghost minus `c n^α` is `e^{κu}(cos(2πu/log 2) − c)` up to `O(e^{-u/2})`. -/
theorem abs_logProfile_ghost_sub_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (c : ℝ) {u : ℝ}
    (hu : 0 ≤ u) :
    |Real.exp ((α - 1 / 2) * u) * (Real.cos (2 * Real.pi * u / Real.log 2) - c) -
      logProfile (fun n => dyadicGhost α n - c * (n : ℝ) ^ α) u| ≤
      (1 + |c| + 2 * Real.pi / Real.log 2) * Real.exp (-(u / 2)) := by
  set x := Real.exp u with hxdef
  have hx : 1 ≤ x := Real.one_le_exp hu
  set m : ℝ := (⌊x⌋₊ : ℝ) with hmdef
  have hm1 : 1 ≤ m := by
    rw [hmdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Nat.floor_eq_zero]; linarith)
  have hmx : m ≤ x := Nat.floor_le (by linarith)
  have hxm : x ≤ m + 1 := (Nat.lt_floor_add_one x).le
  have hphase : dyadicPhase x = 2 * Real.pi * u / Real.log 2 := by
    rw [dyadicPhase, hxdef, Real.log_exp]
  have hexp : Real.exp ((α - 1 / 2) * u) = Real.exp (-(u / 2)) * x ^ α := by
    rw [hxdef, Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, ← Real.exp_add]; ring_nf
  have hstep := abs_ghost_step_le hα hα1 hm1 hmx hxm
  obtain ⟨hD0, hD1⟩ := rpow_sub_floor_rpow_mem hα hα1 hx
  have hid : Real.exp ((α - 1 / 2) * u) * (Real.cos (2 * Real.pi * u / Real.log 2) - c) -
      logProfile (fun n => dyadicGhost α n - c * (n : ℝ) ^ α) u =
      Real.exp (-(u / 2)) * ((x ^ α * Real.cos (dyadicPhase x) - m ^ α * Real.cos (dyadicPhase m)) -
        c * (x ^ α - m ^ α)) := by
    rw [hexp, logProfile, dyadicGhost, hphase]
    ring
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hD0]
  have : |c| * (x ^ α - m ^ α) ≤ |c| := mul_le_of_le_one_right (abs_nonneg c) hD1
  linarith

theorem lintegral_Ioi_exp_neg_ne_top :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-u)) ≠ ⊤ := by
  have h : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa only [neg_mul, one_mul] using exp_neg_integrableOn_Ioi 0 one_pos
  exact (Integrable.lintegral_lt_top h).ne

/-- **The ghost is not the pole modulo finite energy.** -/
theorem pronicEnergy_dyadicGhost_sub_pole_eq_top {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) (c : ℝ) :
    pronicEnergy (fun n => dyadicGhost (1 - ε) n - c * (n : ℝ) ^ (1 - ε)) = ⊤ := by
  by_contra hfin
  have hα : (0 : ℝ) < 1 - ε := by linarith
  have hα1 : 1 - ε ≤ 1 := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  haveI : Fact (0 < Real.log 2) := ⟨hl2⟩
  set L := logProfile (fun n => dyadicGhost (1 - ε) n - c * (n : ℝ) ^ (1 - ε)) with hLdef
  have hrow0 : (fun n : ℕ => dyadicGhost (1 - ε) n - c * (n : ℝ) ^ (1 - ε)) 0 = 0 := by
    simp [dyadicGhost, Real.zero_rpow hα.ne']
  have hL : ∫⁻ u, ENNReal.ofReal (L u ^ 2) ≠ ⊤ := by
    rw [hLdef, lintegral_logProfile_sq hrow0]; exact hfin
  set P : ℝ → ℝ := fun u => Real.cos (2 * Real.pi * u / Real.log 2) - c with hPdef
  have hPc : Continuous P :=
    (Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const _)).sub
      continuous_const
  have hPper : ∀ u, P (u + Real.log 2) = P u := by
    intro u
    simp only [hPdef]
    rw [show 2 * Real.pi * (u + Real.log 2) / Real.log 2 =
      2 * Real.pi * u / Real.log 2 + 2 * Real.pi by field_simp, Real.cos_add_two_pi]
  set K := 1 + |c| + 2 * Real.pi / Real.log 2
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ENNReal.ofReal (P u ^ 2) ≤
      2 * ENNReal.ofReal (L u ^ 2) + 2 * ENNReal.ofReal (K ^ 2 * Real.exp (-u)) := by
    intro u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have herr := abs_logProfile_ghost_sub_le hα hα1 c hu0
    set E := Real.exp ((1 - ε - 1 / 2) * u)
    have he : 1 ≤ E := Real.one_le_exp (mul_nonneg (by linarith) hu0)
    have h1 : P u ^ 2 ≤ (E * P u) ^ 2 := by
      rw [mul_pow]; nlinarith [sq_nonneg (P u), one_le_pow₀ (n := 2) he]
    have h2 : (E * P u - L u) ^ 2 ≤ K ^ 2 * Real.exp (-u) := by
      have hsq : (K * Real.exp (-(u / 2))) ^ 2 = K ^ 2 * Real.exp (-u) := by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
      rw [← hsq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) herr 2
    calc ENNReal.ofReal (P u ^ 2) ≤ ENNReal.ofReal ((L u - (-(E * P u - L u))) ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show L u - (-(E * P u - L u)) = E * P u by ring]; exact h1
      _ ≤ 2 * ENNReal.ofReal (L u ^ 2) + 2 * ENNReal.ofReal ((-(E * P u - L u)) ^ 2) :=
          ofReal_sq_sub_le _ _
      _ ≤ 2 * ENNReal.ofReal (L u ^ 2) + 2 * ENNReal.ofReal (K ^ 2 * Real.exp (-u)) := by
          gcongr
          rw [neg_sq]; exact h2
  have hPfin : ∫⁻ u in Ioi 0, ENNReal.ofReal (P u ^ 2) ≠ ⊤ := by
    have hmL : Measurable fun u => 2 * ENNReal.ofReal (L u ^ 2) :=
      (ENNReal.measurable_ofReal.comp ((measurable_logProfile _).pow_const 2)).const_mul 2
    have hme : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-u)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)
    refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_Ioi hpt)
    rw [lintegral_add_left hmL, lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤)
      (ne_top_of_le_ne_top hL (setLIntegral_le_lintegral _ _)),
      ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) ?_⟩
    simp_rw [ENNReal.ofReal_mul (sq_nonneg K)]
    rw [lintegral_const_mul _ hme]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top lintegral_Ioi_exp_neg_ne_top
  have hzero := ae_eq_zero_of_periodic hPc.measurable (Eventually.of_forall hPper) hPfin
  have hP0 : P = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq volume hPc continuous_const).mp hzero
  have ha := congrFun hP0 0
  have hb := congrFun hP0 (Real.log 2 / 2)
  simp only [hPdef] at ha hb
  rw [mul_zero, zero_div, Real.cos_zero] at ha
  rw [show 2 * Real.pi * (Real.log 2 / 2) / Real.log 2 = Real.pi by field_simp, Real.cos_pi] at hb
  linarith

/-- **One Euler factor does not determine the pole.** For `0 < ε < 1/2` the dyadic ghost
`n^{1−ε} cos(2π log₂ n)` passes the law at `2`, but `ghost − c n^{1−ε}` has infinite pronic energy
for every `c`. -/
theorem one_euler_factor_leaves_a_ghost {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    pronicEnergy (eulerLaw 2 (1 - ε) (dyadicGhost (1 - ε))) ≠ ⊤ ∧
      ∀ c : ℝ, pronicEnergy (fun n => dyadicGhost (1 - ε) n - c * (n : ℝ) ^ (1 - ε)) = ⊤ := by
  refine ⟨pronicEnergy_ne_top_of_abs_le ?_ (abs_eulerLaw_two_dyadicGhost_le (by linarith)
    (by linarith)), pronicEnergy_dyadicGhost_sub_pole_eq_top hε0 hε⟩
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

end GaloisForLFunctions.ArithmeticDefectRigidity
