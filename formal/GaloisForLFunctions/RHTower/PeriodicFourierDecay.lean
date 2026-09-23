import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries

/-!
# Fourier coefficient decay of a periodic `C²` function

Mathlib has the `L²` theory of Fourier series on `AddCircle` and the integration-by-parts recurrence
`fourierCoeffOn_of_hasDerivAt`, but not the classical consequence that a periodic `C²` function has
absolutely convergent Fourier series.  That is what this module supplies.

* `norm_fourierCoeffOn_le` — the trivial bound: a uniformly bounded integrand has uniformly bounded
  Fourier coefficients.
* `fourierCoeffOn_of_periodic` — the recurrence with the boundary term deleted, which is where
  periodicity is used.
* `norm_fourierCoeffOn_of_periodic` — each integration by parts gains a factor `(b-a)/(2π|n|)`.
* `norm_fourierCoeffOn_le_of_periodic_two` — two integrations by parts give `O(n^{-2})`.
* `summable_fourierCoeffOn_of_periodic_two` — hence the coefficients are absolutely summable.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral Set Filter Topology

/-! ## The two elementary bounds -/

theorem norm_two_pi_I_mul_intCast (n : ℤ) :
    ‖-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)‖ = 2 * Real.pi * |(n : ℝ)| := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
  have h2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
  have hpi : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hn : ‖((n : ℤ) : ℂ)‖ = |(n : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h2, hpi, hn]

theorem norm_fourierCoeffOn_le {a b : ℝ} (hab : a < b) {g : ℝ → ℂ} {C : ℝ}
    (hbnd : ∀ x, ‖g x‖ ≤ C) (n : ℤ) : ‖fourierCoeffOn hab g n‖ ≤ C := by
  haveI := Fact.mk (by linarith : 0 < b - a)
  have hba : (0 : ℝ) < b - a := by linarith
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have hb : ‖∫ x in a..b, fourier (-n) ((x : ℝ) : AddCircle (b - a)) • g x‖ ≤ C * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
    rw [norm_smul]
    have h1 : ‖(fourier (-n)) ((x : ℝ) : AddCircle (b - a))‖ ≤ 1 := by
      have h := ContinuousMap.norm_coe_le_norm
        (fourier (-n) : C(AddCircle (b - a), ℂ)) ((x : ℝ) : AddCircle (b - a))
      rwa [fourier_norm] at h
    calc ‖(fourier (-n)) ((x : ℝ) : AddCircle (b - a))‖ * ‖g x‖
        ≤ 1 * ‖g x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖g x‖ := one_mul _
      _ ≤ C := hbnd x
  have hnorm : ‖(1 / (b - a) : ℝ)‖ = 1 / (b - a) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]
  calc 1 / (b - a) * ‖∫ x in a..b, fourier (-n) ((x : ℝ) : AddCircle (b - a)) • g x‖
      ≤ 1 / (b - a) * (C * |b - a|) := by
        exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by
        rw [abs_of_pos hba]
        field_simp

/-! ## The gain from one integration by parts -/

theorem fourierCoeffOn_of_periodic {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) (hf' : IntervalIntegrable f' volume a b)
    (hper : f b = f a) :
    fourierCoeffOn hab f n
      = (1 / (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)))
        * (-(((b - a : ℝ)) : ℂ) * fourierCoeffOn hab f' n) := by
  rw [fourierCoeffOn_of_hasDerivAt hab hn hf hf', hper, sub_self, mul_zero, zero_sub]
  push_cast
  ring

theorem norm_fourierCoeffOn_of_periodic {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) (hf' : IntervalIntegrable f' volume a b)
    (hper : f b = f a) :
    ‖fourierCoeffOn hab f n‖
      = ((b - a) / (2 * Real.pi * |(n : ℝ)|)) * ‖fourierCoeffOn hab f' n‖ := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hnabs : (0 : ℝ) < |(n : ℝ)| := by
    have : ((n : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hn
    exact abs_pos.mpr this
  rw [fourierCoeffOn_of_periodic hab hn hf hf' hper, norm_mul, norm_mul, norm_div, norm_one,
    norm_two_pi_I_mul_intCast, norm_neg]
  have hcast : ‖(((b - a : ℝ)) : ℂ)‖ = b - a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hba]
  rw [hcast]
  field_simp

/-! ## The decay -/

/-- **Two integrations by parts give `O(n^{-2})` decay.**  Only the periodicity of `f` and of `f'`,
and a uniform bound on `f''`, are used. -/
theorem norm_fourierCoeffOn_le_of_periodic_two {a b : ℝ} (hab : a < b) {f f' f'' : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ uIcc a b, HasDerivAt f' (f'' x) x)
    (hf'i : IntervalIntegrable f' volume a b) (hf''i : IntervalIntegrable f'' volume a b)
    (hf''b : ∀ x, ‖f'' x‖ ≤ C) (hper : f b = f a) (hper' : f' b = f' a) {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn hab f n‖ ≤ ((b - a) / (2 * Real.pi)) ^ (2 : ℕ) * C * (1 / (n : ℝ) ^ (2 : ℕ)) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hnabs : (0 : ℝ) < |(n : ℝ)| := by
    have : ((n : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hn
    exact abs_pos.mpr this
  have hstep1 := norm_fourierCoeffOn_of_periodic hab hn hf hf'i hper
  have hstep2 := norm_fourierCoeffOn_of_periodic hab hn hf' hf''i hper'
  have hbnd := norm_fourierCoeffOn_le hab hf''b n
  have hC : (0 : ℝ) ≤ C := le_trans (norm_nonneg (f'' a)) (hf''b a)
  have hcoef : (0 : ℝ) < (b - a) / (2 * Real.pi * |(n : ℝ)|) := by
    have := Real.pi_pos
    positivity
  have hchain : ‖fourierCoeffOn hab f n‖
      = ((b - a) / (2 * Real.pi * |(n : ℝ)|)) ^ (2 : ℕ) * ‖fourierCoeffOn hab f'' n‖ := by
    rw [hstep1, hstep2]
    ring
  have hsq : ((b - a) / (2 * Real.pi * |(n : ℝ)|)) ^ (2 : ℕ)
      = ((b - a) / (2 * Real.pi)) ^ (2 : ℕ) * (1 / (n : ℝ) ^ (2 : ℕ)) := by
    have hn2 : |(n : ℝ)| ^ (2 : ℕ) = (n : ℝ) ^ (2 : ℕ) := sq_abs _
    have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
    have hnne : |(n : ℝ)| ≠ 0 := ne_of_gt hnabs
    field_simp
    rw [hn2]
  rw [hchain, hsq]
  have hnn : (0 : ℝ) ≤ ((b - a) / (2 * Real.pi)) ^ (2 : ℕ) * (1 / (n : ℝ) ^ (2 : ℕ)) := by
    have := Real.pi_pos
    positivity
  calc ((b - a) / (2 * Real.pi)) ^ (2 : ℕ) * (1 / (n : ℝ) ^ (2 : ℕ)) * ‖fourierCoeffOn hab f'' n‖
      ≤ ((b - a) / (2 * Real.pi)) ^ (2 : ℕ) * (1 / (n : ℝ) ^ (2 : ℕ)) * C :=
        mul_le_mul_of_nonneg_left hbnd hnn
    _ = ((b - a) / (2 * Real.pi)) ^ (2 : ℕ) * C * (1 / (n : ℝ) ^ (2 : ℕ)) := by ring

/-- **The Fourier coefficients of a periodic `C²` function are absolutely summable.**  This is the
input that mathlib's `hasSum_fourier_series_of_summable` needs in order to convert the `L²` theory into
pointwise summation. -/
theorem summable_fourierCoeffOn_of_periodic_two {a b : ℝ} (hab : a < b) {f f' f'' : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ uIcc a b, HasDerivAt f' (f'' x) x)
    (hf'i : IntervalIntegrable f' volume a b) (hf''i : IntervalIntegrable f'' volume a b)
    (hf''b : ∀ x, ‖f'' x‖ ≤ C) (hper : f b = f a) (hper' : f' b = f' a) :
    Summable (fun n : ℤ => fourierCoeffOn hab f n) := by
  have hbase : Summable fun n : ℤ => 1 / (n : ℝ) ^ (2 : ℕ) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℤ => ((b - a) / (2 * Real.pi)) ^ (2 : ℕ) * C * (1 / (n : ℝ) ^ (2 : ℕ)))
    (hbase.mul_left _) ?_
  have hcof : ({(0 : ℤ)}ᶜ : Set ℤ) ∈ Filter.cofinite := by
    rw [Filter.mem_cofinite, compl_compl]
    exact Set.finite_singleton 0
  filter_upwards [hcof] with n hn
  exact norm_fourierCoeffOn_le_of_periodic_two hab hf hf' hf'i hf''i hf''b hper hper'
    (by simpa using hn)

/-! ## Pointwise Fourier summation -/

/-- **Pointwise Fourier inversion for a periodic `C²` function.**  Mathlib's
`hasSum_fourier_series_of_summable` gives summation in the sup norm once the coefficients are
absolutely summable; combined with the decay above this is the classical pointwise statement. -/
theorem hasSum_fourier_of_periodic_two {a b : ℝ} (hab : a < b) {f f' f'' : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ uIcc a b, HasDerivAt f' (f'' x) x)
    (hf'i : IntervalIntegrable f' volume a b) (hf''i : IntervalIntegrable f'' volume a b)
    (hf''b : ∀ x, ‖f'' x‖ ≤ C) (hper : f b = f a) (hper' : f' b = f' a) {x : ℝ}
    (hx : x ∈ Ioc a b) :
    HasSum (fun n : ℤ =>
      fourierCoeffOn hab f n * fourier n ((x : ℝ) : AddCircle (b - a))) (f x) := by
  haveI := Fact.mk (by linarith : 0 < b - a)
  have hab' : a + (b - a) = b := by ring
  have hcontOn : ContinuousOn f (Icc a (a + (b - a))) := by
    rw [hab']
    intro y hy
    exact ((hf y (by rwa [uIcc_of_le hab.le])).continuousAt).continuousWithinAt
  have hfa : f a = f (a + (b - a)) := by rw [hab']; exact hper.symm
  have hcont : Continuous (AddCircle.liftIoc (b - a) a f) :=
    AddCircle.liftIoc_continuous hfa hcontOn
  let F : C(AddCircle (b - a), ℂ) := ⟨AddCircle.liftIoc (b - a) a f, hcont⟩
  have hsummable : Summable (fun n : ℤ => fourierCoeff (F : AddCircle (b - a) → ℂ) n) :=
    summable_fourierCoeffOn_of_periodic_two hab hf hf' hf'i hf''i hf''b hper hper'
  have heval := has_pointwise_sum_fourier_series_of_summable hsummable
    ((x : ℝ) : AddCircle (b - a))
  have hFx : F ((x : ℝ) : AddCircle (b - a)) = f x :=
    AddCircle.liftIoc_coe_apply (by rwa [hab'])
  rw [hFx] at heval
  refine heval.congr_fun fun n => ?_
  rw [smul_eq_mul]
  rfl

end GaloisForLFunctions.RHTower

end
