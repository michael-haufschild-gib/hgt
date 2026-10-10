import GaloisForLFunctions.HTGeometry.ToeplitzGeometricTotalPositivity
import GaloisForLFunctions.HTGeometry.EvenEntireSquareLift
import GaloisForLFunctions.HTGeometry.StripRelationPropagation

/-!
# Total positivity of the reciprocal of an even function

For a function `u` analytic and nonvanishing at `0` let `β_m(u)` be the coefficient of `σ^{2m}` in
`1/u(σ)`.  Call `u` *even-reciprocally PF* (`EvenRecipPF`) when `1/u` has vanishing odd and
nonnegative even derivatives at `0` and `(β_m)` is `PF_k` for every `k`.

* `EvenRecipPF.mul`: closed under products, since `1/(uv) = (1/u)(1/v)` and even coefficients
  convolve.
* `EvenRecipPF.one_sub_sq_div`: the factor `1 − σ²/a`, `a > 0`, whose reciprocal has the
  geometric coefficients `a^{−m}` (`PFSeq.geometric`).
* `EvenRecipPF.of_tendstoLocallyUniformlyOn`: closed under locally uniform limits on a disk
  about `0` where the limit does not vanish.
* `iteratedDeriv_comp_sq`: the coefficients of `g` at `0` are the even coefficients of `g(σ²)`.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder Nat NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coefficients from a scalar power series: `f^{(n)}(0) = n! c_n`. -/
theorem iteratedDeriv_eq_of_hasFPowerSeriesAt {f : ℂ → ℂ} {c : ℕ → ℂ}
    (h : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0) (n : ℕ) :
    iteratedDeriv n f 0 = (n ! : ℂ) * c n := by
  have h1 := h.analyticAt.hasFPowerSeriesAt
  have heq := congrFun (FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (h1.eq_formalMultilinearSeries h)) n
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [← heq]
  field_simp

/-- Substituting `σ²` into a scalar power series. -/
theorem hasFPowerSeriesAt_comp_sq {g : ℂ → ℂ} {b : ℕ → ℂ}
    (h : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ b) 0) :
    HasFPowerSeriesAt (fun σ => g (σ ^ 2))
      (FormalMultilinearSeries.ofScalars ℂ (fun m => if Even m then b (m / 2) else 0)) 0 := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨ρ, hρ0, hρr, hρ1⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ENNReal.ofReal ρ < r ∧ ρ ≤ 1 := by
    obtain ⟨ρ', _, hρ'pos, hρ'r⟩ := ENNReal.lt_iff_exists_real_btwn.mp hr.r_pos
    exact ⟨min ρ' 1, lt_min (ENNReal.ofReal_pos.mp hρ'pos) one_pos,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_left _ _)) hρ'r, min_le_right _ _⟩
  refine ⟨ENNReal.ofReal ρ, ?_, by simpa using hρ0, ?_⟩
  · -- radius bound
    refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    have htρ : (t : ℝ) < ρ := by
      have := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp ht
      simpa using this
    refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
    have htr : ((t : ℝ≥0) : ℝ≥0∞) < (FormalMultilinearSeries.ofScalars ℂ b).radius :=
      lt_of_lt_of_le (ht.trans hρr) hr.r_le
    have hsum := FormalMultilinearSeries.summable_norm_mul_pow _ htr
    have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
    have hzero : ∀ m ∉ Set.range (fun k : ℕ => 2 * k),
        ‖FormalMultilinearSeries.ofScalars ℂ (fun m => if Even m then b (m / 2) else 0) m‖ *
          (t : ℝ) ^ m = 0 := by
      intro m hm
      have hodd : ¬ Even m := fun he => hm (by
        obtain ⟨k, hk⟩ := he
        exact ⟨k, show 2 * k = m by omega⟩)
      rw [FormalMultilinearSeries.ofScalars_norm, if_neg hodd, norm_zero, zero_mul]
    rw [← hinj.summable_iff hzero]
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg t.coe_nonneg _)) (fun k => ?_) hsum
    simp only [Function.comp_apply, FormalMultilinearSeries.ofScalars_norm]
    rw [if_pos (even_two_mul k), show 2 * k / 2 = k by omega, pow_mul]
    have ht1 : (t : ℝ) ≤ 1 := le_trans htρ.le hρ1
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (by nlinarith [t.coe_nonneg]) k) (norm_nonneg _)
  · intro y hy
    have hyρ : ‖y‖ < ρ := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hy
      exact (ENNReal.ofReal_lt_ofReal_iff hρ0).mp hy
    have hy2 : y ^ 2 ∈ Metric.eball (0 : ℂ) r := by
      have hlt : ‖y ^ 2‖ < ρ := by
        rw [norm_pow]
        nlinarith [norm_nonneg y]
      have : ENNReal.ofReal ‖y ^ 2‖ < r := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hlt.le) hρr
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
      exact this
    have h2 := hr.hasSum hy2
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at h2 ⊢
    have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
    have hzero : ∀ m ∉ Set.range (fun k : ℕ => 2 * k),
        (if Even m then b (m / 2) else 0) * y ^ m = 0 := by
      intro m hm
      have hodd : ¬ Even m := fun he => hm (by
        obtain ⟨k, hk⟩ := he
        exact ⟨k, show 2 * k = m by omega⟩)
      rw [if_neg hodd, zero_mul]
    rw [← hinj.hasSum_iff hzero]
    refine h2.congr_fun fun k => ?_
    simp only [Function.comp_apply, if_pos (even_two_mul k), show 2 * k / 2 = k by omega,
      pow_mul]

/-- **The coefficients of `g` are the even coefficients of `g(σ²)`.** -/
theorem iteratedDeriv_comp_sq {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    ((((2 * n) ! : ℕ) : ℂ))⁻¹ * iteratedDeriv (2 * n) (fun σ => g (σ ^ 2)) 0 =
      ((n ! : ℂ))⁻¹ * iteratedDeriv n g 0 := by
  have h := hasFPowerSeriesAt_comp_sq hg.hasFPowerSeriesAt
  rw [iteratedDeriv_eq_of_hasFPowerSeriesAt h, if_pos (even_two_mul n),
    show 2 * n / 2 = n by omega]
  have h1 : (((2 * n) ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

theorem iteratedDeriv_comp_sq_odd {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    iteratedDeriv (2 * n + 1) (fun σ => g (σ ^ 2)) 0 = 0 := by
  have h := hasFPowerSeriesAt_comp_sq hg.hasFPowerSeriesAt
  rw [iteratedDeriv_eq_of_hasFPowerSeriesAt h, if_neg (Nat.not_even_two_mul_add_one n), mul_zero]

/-- Splitting a sum over `0, …, 2k` into even terms when the odd terms vanish. -/
theorem sum_range_two_mul_add_one_eq_sum_even {k : ℕ} (F : ℕ → ℂ) (hF : ∀ j, F (2 * j + 1) = 0) :
    ∑ i ∈ Finset.range (2 * k + 1), F i = ∑ j ∈ Finset.range (k + 1), F (2 * j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, hF k, add_zero, Finset.sum_range_succ (n := k + 1),
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring]

/-- Even-order normalized Leibniz rule for functions analytic at `0`. -/
theorem factorial_inv_mul_iteratedDeriv_mul_even_of_analyticAt {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfo : ∀ k : ℕ, iteratedDeriv (2 * k + 1) f 0 = 0) (k : ℕ) :
    (((2 * k).factorial : ℂ))⁻¹ * iteratedDeriv (2 * k) (f * g) 0 =
      ∑ j ∈ Finset.range (k + 1),
        ((((2 * j).factorial : ℂ))⁻¹ * iteratedDeriv (2 * j) f 0) *
          ((((2 * (k - j)).factorial : ℂ))⁻¹ * iteratedDeriv (2 * (k - j)) g 0) := by
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range (2 * k + 1),
      (((2 * k).factorial : ℂ))⁻¹ *
          (((2 * k).choose i : ℂ) * iteratedDeriv i f 0 * iteratedDeriv (2 * k - i) g 0) =
        (((i.factorial : ℂ))⁻¹ * iteratedDeriv i f 0) *
          ((((2 * k - i).factorial : ℂ))⁻¹ * iteratedDeriv (2 * k - i) g 0) := by
    intro i hi
    have hik : i ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hfac : ((2 * k).choose i : ℂ) * (i.factorial : ℂ) * ((2 * k - i).factorial : ℂ) =
        ((2 * k).factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
    have h1 : ((2 * k).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h2 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h3 : ((2 * k - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    field_simp
    linear_combination (iteratedDeriv i f 0 * iteratedDeriv (2 * k - i) g 0) * hfac
  rw [Finset.sum_congr rfl hterm]
  have hsplit := sum_range_two_mul_add_one_eq_sum_even (k := k)
  refine (hsplit _ fun j => by rw [hfo j]; simp).trans ?_
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show 2 * k - 2 * j = 2 * (k - j) by omega]

theorem iteratedDeriv_mul_odd_eq_zero_of_analyticAt {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (hfo : ∀ k : ℕ, iteratedDeriv (2 * k + 1) f 0 = 0)
    (hgo : ∀ k : ℕ, iteratedDeriv (2 * k + 1) g 0 = 0) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (f * g) 0 = 0 := by
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hik : i ≤ 2 * k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
  · rw [show 2 * k + 1 - 2 * j = 2 * (k - j) + 1 by omega, hgo, mul_zero]
  · rw [hfo, mul_zero, zero_mul]

/-- The even reciprocal coefficients `β_m(u)`. -/
def evenRecipCoeff (u : ℂ → ℂ) (m : ℕ) : ℝ :=
  ((((2 * m).factorial : ℂ))⁻¹ * iteratedDeriv (2 * m) (fun σ => (u σ)⁻¹) 0).re

/-- Even-reciprocal total positivity. -/
structure EvenRecipPF (u : ℂ → ℂ) : Prop where
  analyticAt : AnalyticAt ℂ u 0
  ne_zero : u 0 ≠ 0
  odd : ∀ m, iteratedDeriv (2 * m + 1) (fun σ => (u σ)⁻¹) 0 = 0
  nonneg : ∀ m, 0 ≤ iteratedDeriv (2 * m) (fun σ => (u σ)⁻¹) 0
  pf : ∀ k, PFSeq k (evenRecipCoeff u)

theorem EvenRecipPF.analyticAt_inv {u : ℂ → ℂ} (hu : EvenRecipPF u) :
    AnalyticAt ℂ (fun σ => (u σ)⁻¹) 0 := hu.analyticAt.inv hu.ne_zero

theorem EvenRecipPF.coeff_real {u : ℂ → ℂ} (hu : EvenRecipPF u) (m : ℕ) :
    ((((2 * m).factorial : ℂ))⁻¹ * iteratedDeriv (2 * m) (fun σ => (u σ)⁻¹) 0) =
      ((evenRecipCoeff u m : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [evenRecipCoeff]
  · simp only [Complex.ofReal_im]
    rw [Complex.mul_im, (Complex.nonneg_iff.mp (hu.nonneg m)).2.symm, mul_zero, zero_add]
    rw [show (((2 * m).factorial : ℂ))⁻¹ = ((((2 * m).factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl,
      Complex.ofReal_im, zero_mul]

/-- **Products.** -/
theorem EvenRecipPF.mul {u v : ℂ → ℂ} (hu : EvenRecipPF u) (hv : EvenRecipPF v) :
    EvenRecipPF (u * v) := by
  have hinv : (fun σ => ((u * v) σ)⁻¹) = (fun σ => (u σ)⁻¹) * fun σ => (v σ)⁻¹ := by
    funext σ
    simp only [Pi.mul_apply, mul_inv]
  have hcoeff : evenRecipCoeff (u * v) = cauchyConv (evenRecipCoeff u) (evenRecipCoeff v) := by
    funext k
    unfold evenRecipCoeff cauchyConv
    rw [hinv, factorial_inv_mul_iteratedDeriv_mul_even_of_analyticAt hu.analyticAt_inv
      hv.analyticAt_inv hu.odd, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu.coeff_real, hv.coeff_real, ← Complex.ofReal_mul, Complex.ofReal_re]
    rfl
  refine ⟨hu.analyticAt.mul hv.analyticAt, mul_ne_zero hu.ne_zero hv.ne_zero, fun m => ?_,
    fun m => ?_, fun k => ?_⟩
  · rw [hinv]
    exact iteratedDeriv_mul_odd_eq_zero_of_analyticAt hu.analyticAt_inv hv.analyticAt_inv
      hu.odd hv.odd m
  · have h := factorial_inv_mul_iteratedDeriv_mul_even_of_analyticAt hu.analyticAt_inv
      hv.analyticAt_inv hu.odd m
    rw [← hinv] at h
    have hfac : (0 : ℂ) < (((2 * m).factorial : ℂ)) := by
      exact_mod_cast Nat.factorial_pos _
    have hsum : 0 ≤ ∑ j ∈ Finset.range (m + 1),
        ((((2 * j).factorial : ℂ))⁻¹ * iteratedDeriv (2 * j) (fun σ => (u σ)⁻¹) 0) *
          ((((2 * (m - j)).factorial : ℂ))⁻¹ *
            iteratedDeriv (2 * (m - j)) (fun σ => (v σ)⁻¹) 0) := by
      refine Finset.sum_nonneg fun j _ => ?_
      rw [hu.coeff_real, hv.coeff_real]
      refine mul_nonneg (Complex.zero_le_real.mpr ?_) (Complex.zero_le_real.mpr ?_)
      · have := hu.pf 1 1 le_rfl (fun _ => 0) (fun _ => j) (Subsingleton.strictMono _)
          (Subsingleton.strictMono _)
        simpa [toeplitzMinor, Matrix.det_unique, zext_natCast] using this
      · have := hv.pf 1 1 le_rfl (fun _ => 0) (fun _ => m - j) (Subsingleton.strictMono _)
          (Subsingleton.strictMono _)
        simpa [toeplitzMinor, Matrix.det_unique, zext_natCast] using this
    rw [← h] at hsum
    have hf0 : (0 : ℂ) ≤ (((2 * m).factorial : ℂ)) := Nat.cast_nonneg _
    have hne : (((2 * m).factorial : ℂ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have := mul_nonneg hf0 hsum
    rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this
  · rw [hcoeff]
    exact (hu.pf k).conv (hv.pf k)

/-- The constant `1`. -/
theorem EvenRecipPF.one : EvenRecipPF (fun _ => 1) := by
  have hinv : (fun σ : ℂ => ((fun _ : ℂ => (1 : ℂ)) σ)⁻¹) = fun _ => (1 : ℂ) := by
    funext σ
    simp
  refine ⟨analyticAt_const, one_ne_zero, fun m => ?_, fun m => ?_, fun k => ?_⟩
  · rw [hinv, iteratedDeriv_const]
    simp
  · rw [hinv, iteratedDeriv_const]
    split_ifs <;> simp
  · have hc : evenRecipCoeff (fun _ => 1) = twoTermSeq 1 0 := by
      funext m
      unfold evenRecipCoeff twoTermSeq
      rw [hinv, iteratedDeriv_const]
      rcases m with _ | _ | m <;> simp
    rw [hc]
    exact PFSeq.twoTerm zero_le_one le_rfl k

/-- The geometric power series of `(1 − z/a)⁻¹`. -/
theorem hasFPowerSeriesAt_inv_one_sub_div {a : ℝ} (ha : 0 < a) :
    HasFPowerSeriesAt (fun z : ℂ => (1 - z / a)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => ((a⁻¹ : ℝ) : ℂ) ^ k)) 0 := by
  refine ⟨ENNReal.ofReal a, ?_, by simpa using ha, ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    have hta : (t : ℝ) < a := by
      have := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp ht
      simpa using this
    refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
    have hq : (t : ℝ) / a < 1 := by rw [div_lt_one ha]; exact hta
    refine (summable_geometric_of_lt_one (by positivity) hq).congr fun k => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha), div_eq_inv_mul, mul_pow]
  · intro y hy
    have hya : ‖y‖ < a := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hy
      exact (ENNReal.ofReal_lt_ofReal_iff ha).mp hy
    have hq : ‖y / (a : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, div_lt_one ha]
      exact hya
    have h := hasSum_geometric_of_norm_lt_one hq
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
    refine h.congr_fun fun k => ?_
    push_cast
    rw [div_eq_mul_inv, mul_pow, mul_comm]

/-- **The factor `1 − σ²/a`, `a > 0`.** -/
theorem EvenRecipPF.one_sub_sq_div {a : ℝ} (ha : 0 < a) :
    EvenRecipPF (fun σ : ℂ => 1 - σ ^ 2 / a) := by
  set g : ℂ → ℂ := fun z => (1 - z / a)⁻¹ with hg
  have hgan : AnalyticAt ℂ g 0 := (hasFPowerSeriesAt_inv_one_sub_div ha).analyticAt
  have hinv : (fun σ : ℂ => ((fun σ : ℂ => 1 - σ ^ 2 / (a : ℂ)) σ)⁻¹) = fun σ => g (σ ^ 2) := rfl
  have hcoef : ∀ m, ((((2 * m) ! : ℕ) : ℂ))⁻¹ *
      iteratedDeriv (2 * m) (fun σ : ℂ => ((fun σ : ℂ => 1 - σ ^ 2 / (a : ℂ)) σ)⁻¹) 0 =
        (((a⁻¹ ^ m : ℝ)) : ℂ) := by
    intro m
    rw [hinv, iteratedDeriv_comp_sq hgan, iteratedDeriv_eq_of_hasFPowerSeriesAt
      (hasFPowerSeriesAt_inv_one_sub_div ha)]
    have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
    push_cast
    field_simp
  refine ⟨by fun_prop, by simp, fun m => ?_, fun m => ?_, fun k => ?_⟩
  · rw [hinv]
    exact iteratedDeriv_comp_sq_odd hgan m
  · have h := hcoef m
    have hfac : ((((2 * m) ! : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hD : iteratedDeriv (2 * m) (fun σ : ℂ => ((fun σ : ℂ => 1 - σ ^ 2 / (a : ℂ)) σ)⁻¹) 0 =
        ((((2 * m) ! : ℕ) : ℂ)) * (((a⁻¹ ^ m : ℝ)) : ℂ) := by
      rw [← h]
      field_simp
    rw [hD]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.mpr (by positivity))
  · have hc : evenRecipCoeff (fun σ : ℂ => 1 - σ ^ 2 / (a : ℂ)) = fun m => a⁻¹ ^ m := by
      funext m
      unfold evenRecipCoeff
      rw [show ((2 * m).factorial : ℂ) = (((2 * m) ! : ℕ) : ℂ) from rfl, hcoef m,
        Complex.ofReal_re]
    rw [hc]
    exact PFSeq.geometric (inv_nonneg.mpr ha.le) k

/-- **Limits.**  If `u_i → u` locally uniformly on an open disk `B ∋ 0`, all nonvanishing and
holomorphic on `B`, and each `u_i` is even-reciprocally PF, so is `u`. -/
theorem EvenRecipPF.of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : ι → ℂ → ℂ} {u : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hU : ∀ i, EvenRecipPF (U i))
    (hUd : ∀ i, DifferentiableOn ℂ (U i) (ball 0 r)) (hUne : ∀ i, ∀ σ ∈ ball (0 : ℂ) r, U i σ ≠ 0)
    (hud : DifferentiableOn ℂ u (ball 0 r)) (hune : ∀ σ ∈ ball (0 : ℂ) r, u σ ≠ 0)
    (h : TendstoLocallyUniformlyOn U u l (ball 0 r)) : EvenRecipPF u := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hinv : TendstoLocallyUniformlyOn (fun i σ => (U i σ)⁻¹) (fun σ => (u σ)⁻¹) l
      (ball 0 r) := h.inv₀ hud.continuousOn hune
  have hinvd : ∀ᶠ i in l, DifferentiableOn ℂ (fun σ => (U i σ)⁻¹) (ball 0 r) :=
    Eventually.of_forall fun i => (hUd i).inv fun σ hσ => hUne i σ hσ
  have hd : ∀ n, Tendsto (fun i => iteratedDeriv n (fun σ => (U i σ)⁻¹) 0) l
      (𝓝 (iteratedDeriv n (fun σ => (u σ)⁻¹) 0)) := fun n =>
    ((tendstoLocallyUniformlyOn_iteratedDeriv isOpen_ball hinv hinvd n).1.tendsto_at h0)
  have huan : AnalyticAt ℂ u 0 := hud.analyticAt (isOpen_ball.mem_nhds h0)
  refine ⟨huan, hune 0 h0, fun m => ?_, fun m => ?_, fun k => ?_⟩
  · have h1 : Tendsto (fun i => iteratedDeriv (2 * m + 1) (fun σ => (U i σ)⁻¹) 0) l (𝓝 0) := by
      simp only [fun i => (hU i).odd m]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hd (2 * m + 1)) h1
  · have hcl : IsClosed {z : ℂ | 0 ≤ z} := by
      have : {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0} := by
        ext z
        simp [Complex.nonneg_iff, eq_comm]
      rw [this]
      exact (isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_eq Complex.continuous_im continuous_const)
    exact hcl.mem_of_tendsto (hd (2 * m)) (Eventually.of_forall fun i => (hU i).nonneg m)
  · refine PFSeq.of_tendsto (l := l) (fun i => (hU i).pf k) fun n => ?_
    unfold evenRecipCoeff
    exact (Complex.continuous_re.tendsto _).comp ((hd (2 * n)).const_mul _)

end

end GaloisForLFunctions.HTGeometry
