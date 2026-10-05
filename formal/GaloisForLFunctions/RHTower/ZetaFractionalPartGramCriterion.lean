import GaloisForLFunctions.RHTower.ZetaCriticalLineWeightedSecondMoment

/-!
# A fractional-part Gram criterion for the Riemann hypothesis

Let `A(m, n) = ∫_0^∞ {x/m}{x/n} dx/x²`.  For a real Dirichlet polynomial
`M(s) = Σ_{n ∈ S} a_n n^{-s}`, the function `F(y) = Σ_n a_n {1/(ny)}` has Mellin transform
`-ζ(s) M(s)/s` on `0 < Re s < 1`, so Plancherel on `Re s = ½` gives

`(1/2π) ∫ |ζ(½+it) M(½+it)|² dt/(¼ + t²) = Σ_{m,n} a_m a_n A(m, n)`.

The mollified Balazard–Saias–Yor inequality then yields, for every real `a`,

`(Σ_n a_n/n)² ≤ Σ_{m,n} a_m a_n A(m, n)`,

and the Riemann hypothesis follows if the ratio of the two sides can be made arbitrarily close to
`1`.  The case `S = {1}` is `A(1,1) = log 2π - γ`.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-- The fractional-part Gram entry `A(m, n) = ∫_0^∞ {x/m}{x/n} dx/x²`. -/
def fractGram (m n : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), Int.fract (x / m) * Int.fract (x / n) / x ^ 2

/-- `φ_n(u) = e^{-u/2} {e^u/n}`. -/
def fractLogPullDilate (n : ℕ) (u : ℝ) : ℂ :=
  ((Real.exp (-(u / 2)) * Int.fract (Real.exp u / n) : ℝ) : ℂ)

theorem fract_div_natCast_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    Int.fract (x / n) ≤ x := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : x / n ≤ x := div_le_self hx hn1
  have h2 := Int.floor_nonneg.mpr (div_nonneg hx (by positivity : (0 : ℝ) ≤ n))
  have h3 : (0 : ℝ) ≤ (⌊x / n⌋ : ℝ) := by exact_mod_cast h2
  unfold Int.fract
  linarith

theorem norm_fractLogPullDilate (n : ℕ) (u : ℝ) :
    ‖fractLogPullDilate n u‖ = Real.exp (-(u / 2)) * Int.fract (Real.exp u / n) := by
  rw [fractLogPullDilate, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _))]

theorem norm_fractLogPullDilate_le {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    ‖fractLogPullDilate n u‖ ≤ Real.exp (-(1 / 2) * |u|) := by
  rw [norm_fractLogPullDilate]
  have h1 := (Int.fract_lt_one (Real.exp u / n)).le
  have h2 := fract_div_natCast_le hn (Real.exp_pos u).le
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    calc Real.exp (-(u / 2)) * Int.fract (Real.exp u / n) ≤ Real.exp (-(u / 2)) * 1 :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (-(1 / 2) * u) := by ring_nf
  · rw [abs_of_neg hu]
    calc Real.exp (-(u / 2)) * Int.fract (Real.exp u / n)
        ≤ Real.exp (-(u / 2)) * Real.exp u := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Real.exp (-(1 / 2) * -u) := by rw [← Real.exp_add]; ring_nf

theorem measurable_fractLogPullDilate (n : ℕ) : Measurable (fractLogPullDilate n) :=
  Complex.measurable_ofReal.comp
    ((Real.measurable_exp.comp (measurable_id.div_const 2).neg).mul
      (measurable_fract.comp (Real.measurable_exp.div_const _)))

theorem integrable_exp_neg_half_mul_abs :
    Integrable (fun u : ℝ => Real.exp (-(1 / 2) * |u|)) :=
  (HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (r := 1 / 2) (by norm_num)).congr
    (Filter.Eventually.of_forall fun u => by simp)

theorem integrable_fractLogPullDilate {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fractLogPullDilate n) :=
  Integrable.mono' integrable_exp_neg_half_mul_abs
    (measurable_fractLogPullDilate n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => norm_fractLogPullDilate_le hn u)

/-- The Mellin transform of `y ↦ {1/(ny)}` is `n^{-s} (-ζ(s)/s)` on `0 < Re s < 1`. -/
theorem mellin_fract_inv_natCast_mul {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1) :
    mellin (fun y : ℝ => ((Int.fract ((n * y)⁻¹) : ℝ) : ℂ)) s
      = (n : ℂ) ^ (-s) * (-(riemannZeta s / s)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mellin_comp_mul_left (fun y : ℝ => ((Int.fract y⁻¹ : ℝ) : ℂ)) s hn0
  rw [h, smul_eq_mul, Complex.ofReal_natCast]
  congr 1
  have hm := mellin_comp_inv (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) s
  rw [hm, mellin, ← integral_Ioi_zero_fract_cpow h0 h1]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [smul_eq_mul]
  rw [show (-s - 1 : ℂ) = -(s + 1) by ring, mul_comm]

/-- **The Fourier transform of `φ_n` on the critical line.** -/
theorem fourier_fractLogPullDilate {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    𝓕 (fractLogPullDilate n) (t / (2 * π))
      = (n : ℂ) ^ (-(1 / 2 + t * I)) * (-(riemannZeta (1 / 2 + t * I) / (1 / 2 + t * I))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set s : ℂ := 1 / 2 + t * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have him : s.im = t := by simp [hs]
  have h := mellin_eq_fourier (fun y : ℝ => ((Int.fract ((n * y)⁻¹) : ℝ) : ℂ)) (s := s)
  rw [hre, him] at h
  have hfun : (fun u : ℝ => Real.exp (-(1 / 2) * u) • ((Int.fract ((n * Real.exp (-u))⁻¹) : ℝ) : ℂ))
      = fractLogPullDilate n := by
    funext u
    rw [fractLogPullDilate, Complex.real_smul, mul_inv, ← Real.exp_neg, neg_neg,
      show ((n : ℝ))⁻¹ * Real.exp u = Real.exp u / n by ring]
    push_cast
    ring_nf
  rw [hfun] at h
  rw [← h, mellin_fract_inv_natCast_mul hn (by rw [hre]; norm_num) (by rw [hre]; norm_num)]

/-- The real Dirichlet polynomial `M(s) = Σ_{n ∈ S} a_n n^{-s}`. -/
def realDirichletPoly (S : Finset ℕ) (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, (a n : ℂ) * (n : ℂ) ^ (-s)

/-- The pulled-back sawtooth combination `Φ(u) = Σ_n a_n φ_n(u)`. -/
def fractGramPull (S : Finset ℕ) (a : ℕ → ℝ) (u : ℝ) : ℂ :=
  ∑ n ∈ S, (a n : ℂ) * fractLogPullDilate n u

theorem integrable_fractGramPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    Integrable (fractGramPull S a) := by
  unfold fractGramPull
  exact integrable_finsetSum _ fun n hn => (integrable_fractLogPullDilate (hS n hn)).const_mul _

theorem fourier_fractGramPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) (t : ℝ) :
    𝓕 (fractGramPull S a) (t / (2 * π))
      = -(riemannZeta (1 / 2 + t * I) * realDirichletPoly S a (1 / 2 + t * I)
          / (1 / 2 + t * I)) := by
  have hlin : ∀ ξ : ℝ, 𝓕 (fractGramPull S a) ξ
      = ∑ n ∈ S, (a n : ℂ) * 𝓕 (fractLogPullDilate n) ξ := by
    intro ξ
    rw [Real.fourier_real_eq]
    unfold fractGramPull
    simp_rw [Finset.smul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [Real.fourier_real_eq, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    · intro n hn
      have hi := (integrable_fractLogPullDilate (hS n hn)).const_mul (a n : ℂ)
      refine Integrable.mono' hi.norm ?_ (Filter.Eventually.of_forall fun v => ?_)
      · exact ((Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable).smul
          hi.aestronglyMeasurable
      · rw [Circle.norm_smul]
  rw [hlin, Finset.sum_congr rfl fun n hn => by rw [fourier_fractLogPullDilate (hS n hn)]]
  unfold realDirichletPoly
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring


theorem fractGramPull_eq_ofReal (S : Finset ℕ) (a : ℕ → ℝ) (u : ℝ) :
    fractGramPull S a u
      = ((∑ n ∈ S, a n * (Real.exp (-(u / 2)) * Int.fract (Real.exp u / n)) : ℝ) : ℂ) := by
  unfold fractGramPull fractLogPullDilate
  push_cast
  rfl

theorem norm_fractGramPull_le {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) (u : ℝ) :
    ‖fractGramPull S a u‖ ≤ (∑ n ∈ S, |a n|) * Real.exp (-(1 / 2) * |u|) := by
  unfold fractGramPull
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_fractLogPullDilate_le (hS n hn) u) (abs_nonneg _)

theorem memLp_two_fractGramPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    MemLp (fractGramPull S a) 2 := by
  have hmeas := (integrable_fractGramPull hS a).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  set C : ℝ := ∑ n ∈ S, |a n| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun n _ => abs_nonneg _
  refine Integrable.mono' (integrable_exp_neg_half_mul_abs.const_mul (C ^ 2))
    (hmeas.norm.pow 2) (Filter.Eventually.of_forall fun u => ?_)
  have h1 := norm_fractGramPull_le hS a u
  have h2 : Real.exp (-(1 / 2) * |u|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := abs_nonneg u; nlinarith)
  have h3 : 0 ≤ Real.exp (-(1 / 2) * |u|) := (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖fractGramPull S a u‖ ^ 2 ≤ (C * Real.exp (-(1 / 2) * |u|)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = C ^ 2 * (Real.exp (-(1 / 2) * |u|) * Real.exp (-(1 / 2) * |u|)) := by ring
    _ ≤ C ^ 2 * (Real.exp (-(1 / 2) * |u|) * 1) := by gcongr
    _ = C ^ 2 * Real.exp (-(1 / 2) * |u|) := by ring

/-- `∫ φ_m φ_n = A(m, n)`. -/
theorem integral_fractLogPullDilate_mul (m n : ℕ) :
    ∫ u : ℝ, (Real.exp (-(u / 2)) * Int.fract (Real.exp u / m))
        * (Real.exp (-(u / 2)) * Int.fract (Real.exp u / n)) = fractGram m n := by
  have h1 : ∫ u : ℝ, (Real.exp (-(u / 2)) * Int.fract (Real.exp u / m))
        * (Real.exp (-(u / 2)) * Int.fract (Real.exp u / n))
      = ∫ u : ℝ, Real.exp u * (Int.fract (Real.exp (-u) / m) * Int.fract (Real.exp (-u) / n)) := by
    rw [← integral_neg_eq_self (fun u : ℝ => (Real.exp (-(u / 2)) * Int.fract (Real.exp u / m))
        * (Real.exp (-(u / 2)) * Int.fract (Real.exp u / n))) volume]
    congr 1
    funext u
    have he : Real.exp (-(-u / 2)) * Real.exp (-(-u / 2)) = Real.exp u := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (-(-u / 2)) * Int.fract (Real.exp (-u) / m)
          * (Real.exp (-(-u / 2)) * Int.fract (Real.exp (-u) / n))
        = (Real.exp (-(-u / 2)) * Real.exp (-(-u / 2)))
          * (Int.fract (Real.exp (-u) / m) * Int.fract (Real.exp (-u) / n)) := by ring
      _ = _ := by rw [he]
  rw [h1, ← GaloisForLFunctions.HTGeometry.integral_Ioi_comp_neg_log_div, fractGram]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  rw [neg_neg, Real.exp_log hx0, Real.exp_neg, Real.exp_log hx0]
  field_simp

theorem integrable_fractLogPullDilate_mul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Integrable (fun u : ℝ => (Real.exp (-(u / 2)) * Int.fract (Real.exp u / m))
        * (Real.exp (-(u / 2)) * Int.fract (Real.exp u / n))) := by
  have hb : ∀ k : ℕ, 1 ≤ k → ∀ u : ℝ,
      |Real.exp (-(u / 2)) * Int.fract (Real.exp u / k)| ≤ Real.exp (-(1 / 2) * |u|) := by
    intro k hk u
    have := norm_fractLogPullDilate_le hk u
    rwa [norm_fractLogPullDilate, ← abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (Int.fract_nonneg _))] at this
  refine Integrable.mono' integrable_exp_neg_half_mul_abs ?_
    (Filter.Eventually.of_forall fun u => ?_)
  · exact (((Real.measurable_exp.comp (measurable_id.div_const 2).neg).mul
      (measurable_fract.comp (Real.measurable_exp.div_const _))).mul
      ((Real.measurable_exp.comp (measurable_id.div_const 2).neg).mul
      (measurable_fract.comp (Real.measurable_exp.div_const _)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    have h1 := hb m hm u
    have h2 := hb n hn u
    have h3 : Real.exp (-(1 / 2) * |u|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := abs_nonneg u; nlinarith)
    calc |Real.exp (-(u / 2)) * Int.fract (Real.exp u / m)|
          * |Real.exp (-(u / 2)) * Int.fract (Real.exp u / n)|
        ≤ Real.exp (-(1 / 2) * |u|) * 1 :=
          mul_le_mul h1 (h2.trans h3) (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-(1 / 2) * |u|) := mul_one _

/-- **`∫ |Φ|² = Σ_{m,n} a_m a_n A(m, n)`.** -/
theorem integral_norm_sq_fractGramPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    ∫ u : ℝ, ‖fractGramPull S a u‖ ^ 2
      = ∑ m ∈ S, ∑ n ∈ S, a m * a n * fractGram m n := by
  have hpt : ∀ u : ℝ, ‖fractGramPull S a u‖ ^ 2
      = ∑ m ∈ S, ∑ n ∈ S, a m * a n * ((Real.exp (-(u / 2)) * Int.fract (Real.exp u / m))
          * (Real.exp (-(u / 2)) * Int.fract (Real.exp u / n))) := by
    intro u
    rw [fractGramPull_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq,
      Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m hm => integrable_finsetSum _ fun n hn =>
    (integrable_fractLogPullDilate_mul (hS m hm) (hS n hn)).const_mul _]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_finsetSum _ fun n hn =>
    (integrable_fractLogPullDilate_mul (hS m hm) (hS n hn)).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_fractLogPullDilate_mul]

/-- **The mollified mean square as a fractional-part Gram form.**
`(1/2π) ∫ |ζ(½+it) M(½+it)|² dt/(¼ + t²) = Σ_{m,n} a_m a_n A(m, n)`. -/
theorem integrable_and_meanSquare_eq_fractGram {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n)
    (a : ℕ → ℝ) :
    Integrable (fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)
        * realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) ∧
      (2 * π)⁻¹ * ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I)
          * realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)
        = ∑ m ∈ S, ∑ n ∈ S, a m * a n * fractGram m n := by
  have hπ : 0 < 2 * π := by positivity
  have hP := GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier
    (integrable_fractGramPull hS a) (memLp_two_fractGramPull hS a)
  rw [integral_norm_sq_fractGramPull hS a] at hP
  have hFint : Integrable (fun ξ : ℝ => ‖𝓕 (fractGramPull S a) ξ‖ ^ 2) := by
    by_cases h0 : ∑ m ∈ S, ∑ n ∈ S, a m * a n * fractGram m n = 0
    · have hz : ∫ u : ℝ, ‖fractGramPull S a u‖ ^ 2 = 0 := by
        rw [integral_norm_sq_fractGramPull hS a, h0]
      have hae : fractGramPull S a =ᵐ[volume] 0 := by
        have hnn : 0 ≤ᵐ[volume] fun u => ‖fractGramPull S a u‖ ^ 2 :=
          Filter.Eventually.of_forall fun u => by positivity
        have hi : Integrable (fun u => ‖fractGramPull S a u‖ ^ 2) := by
          rw [← memLp_two_iff_integrable_sq_norm
            (integrable_fractGramPull hS a).aestronglyMeasurable]
          exact memLp_two_fractGramPull hS a
        have := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hz
        exact this.mono fun u hu => by
          simpa using hu
      have hF0 : ∀ ξ, 𝓕 (fractGramPull S a) ξ = 0 := by
        intro ξ
        rw [Real.fourier_real_eq]
        have h0' : (fun v : ℝ => Real.fourierChar (-(v * ξ)) • fractGramPull S a v)
            =ᵐ[volume] fun _ => (0 : ℂ) := hae.mono fun u hu => by simp [hu]
        rw [integral_congr_ae h0', integral_zero]
      simp_rw [hF0]
      simp
    · by_contra hni
      rw [integral_undef hni] at hP
      exact h0 hP.symm
  have hpt : ∀ t : ℝ, ‖riemannZeta (1 / 2 + t * I) * realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2
      / (1 / 4 + t ^ 2) = ‖𝓕 (fractGramPull S a) (t / (2 * π))‖ ^ 2 := by
    intro t
    rw [fourier_fractGramPull hS, norm_neg, norm_div, div_pow, norm_half_add_mul_I,
      Real.sq_sqrt (by positivity)]
  simp_rw [hpt]
  refine ⟨hFint.comp_div hπ.ne', ?_⟩
  rw [Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 (fractGramPull S a) ξ‖ ^ 2) (2 * π), hP,
    abs_of_pos hπ, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul]

theorem realDirichletPoly_one (S : Finset ℕ) (a : ℕ → ℝ) :
    realDirichletPoly S a 1 = ((∑ n ∈ S, a n / n : ℝ) : ℂ) := by
  unfold realDirichletPoly
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.cpow_neg_one, div_eq_mul_inv]

theorem differentiable_realDirichletPoly {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    Differentiable ℂ (realDirichletPoly S a) := by
  intro s
  unfold realDirichletPoly
  refine DifferentiableAt.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by have := hS n hn; exact_mod_cast (by omega : n ≠ 0)
  exact (differentiableAt_const _).mul
    ((differentiableAt_id.neg).const_cpow (Or.inl hn0))

theorem norm_realDirichletPoly_le {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : ‖realDirichletPoly S a s‖ ≤ ∑ n ∈ S, |a n| := by
  unfold realDirichletPoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hS n hn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast_cpow_of_pos (by have := hS n hn; omega)]
  have : (n : ℝ) ^ (-s).re ≤ 1 := by
    rw [Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  calc |a n| * (n : ℝ) ^ (-s).re ≤ |a n| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |a n| := mul_one _

/-- **The fractional-part Gram lower bound.**  `(Σ a_n/n)² ≤ Σ_{m,n} a_m a_n A(m, n)` for every
real `a` on a finite set of positive integers. -/
theorem sq_sum_div_le_fractGram_form {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    (∑ n ∈ S, a n / n) ^ 2 ≤ ∑ m ∈ S, ∑ n ∈ S, a m * a n * fractGram m n := by
  obtain ⟨hint, hval⟩ := integrable_and_meanSquare_eq_fractGram hS a
  rw [← hval]
  by_cases h1 : ∑ n ∈ S, a n / n = 0
  · rw [h1, sq, mul_zero]
    have : 0 ≤ ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I)
        * realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2) :=
      integral_nonneg fun t => by positivity
    exact mul_nonneg (by positivity) this
  have hM1 : realDirichletPoly S a 1 ≠ 0 := by
    rw [realDirichletPoly_one]; exact_mod_cast h1
  have hmain := sum_log_le_half_log_meanSquare_zeta_mul (differentiable_realDirichletPoly hS a)
    ⟨_, fun s hs => norm_realDirichletPoly_le hS a hs⟩ hM1 hint (Z := ∅) (by simp)
  rw [Finset.sum_empty] at hmain
  have hcpos := mul_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹) (integral_sq_criticalLine_pos
    (F := fun t : ℝ => riemannZeta (1 / 2 + t * I) * realDirichletPoly S a (1 / 2 + t * I))
    (ae_riemannZeta_mul_ne_zero (differentiable_realDirichletPoly hS a) hM1) hint)
  have hM1p : 0 < ‖realDirichletPoly S a 1‖ := norm_pos_iff.mpr hM1
  have hlog : Real.log (‖realDirichletPoly S a 1‖ ^ 2) ≤ Real.log ((2 * π)⁻¹ * ∫ t : ℝ,
      ‖riemannZeta (1 / 2 + t * I) * realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2
        / (1 / 4 + t ^ 2)) := by
    rw [Real.log_pow]; push_cast; linarith
  have := (Real.log_le_log_iff (by positivity) hcpos).mp hlog
  rw [realDirichletPoly_one, Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
  exact this

/-- **A fractional-part Gram criterion for the Riemann hypothesis.**  If for every `ε > 0` there is
a real `a` on a finite set of positive integers with `Σ a_n/n ≠ 0` and
`Σ_{m,n} a_m a_n A(m, n) ≤ (1 + ε)(Σ a_n/n)²`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_fractGram_form
    (h : ∀ ε : ℝ, 0 < ε → ∃ (S : Finset ℕ) (a : ℕ → ℝ), (∀ n ∈ S, 1 ≤ n) ∧
      ∑ n ∈ S, a n / n ≠ 0 ∧
      ∑ m ∈ S, ∑ n ∈ S, a m * a n * fractGram m n ≤ (1 + ε) * (∑ n ∈ S, a n / n) ^ 2) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_mollified_meanSquare_le fun ε hε => ?_
  obtain ⟨S, a, hS, h1, hle⟩ := h ε hε
  obtain ⟨hint, hval⟩ := integrable_and_meanSquare_eq_fractGram hS a
  refine ⟨realDirichletPoly S a, differentiable_realDirichletPoly hS a,
    ⟨_, fun s hs => norm_realDirichletPoly_le hS a hs⟩,
    by rw [realDirichletPoly_one]; exact_mod_cast h1, hint, ?_⟩
  rw [hval, realDirichletPoly_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact hle

end

end RHTower
