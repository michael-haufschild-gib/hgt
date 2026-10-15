import GaloisForLFunctions.RHTower.EvenSectorStripPositivity
import GaloisForLFunctions.HTGeometry.WaveTraceSpectrum
import GaloisForLFunctions.HTGeometry.BochnerPositiveDefiniteReal

/-!
# The cosine-shifted spectral measures of the even sector

Let `lam` be Weil-positive on even tests with `|lam(n)| ≤ C_g √n (1 + log n)`.  Put
`ρ(z) = (z² + 2)^{1/2}` (principal branch; holomorphic on `|Im z| < √2`, real and `≥ √2` on `ℝ`,
even, and `|Im ρ(z)| ≤ |Im z|`).

For an even strip function `Φ` the function `y ↦ φ_Φ(y) = L(cos(y ρ) Φ Φ^#)` is continuous and
positive definite (`positiveDefinite_cosineShift`).  Indeed
`Σ c_i c_j cos((y_i − y_j) ρ) Φ Φ^# = A A^# + B B^#` with `A = Σ c_i cos(y_i ρ) Φ` and
`B = Σ c_i sin(y_i ρ) Φ`, two even strip functions on `|Im z| ≤ 5/4`, on which `L` is nonnegative
(`evenWeilDensity_specSq_nonneg`).  By Bochner, `φ_Φ` is the characteristic function of a finite
positive measure `ν_Φ` on the `ρ`-line (`exists_cosineShift_measure`).

Formally `ν_Φ = |Φ(√(ρ² − 2))|² μ` for the spectral measure `μ` of the even Weil functional in the
shifted variable `ρ² = r² + 2`.  On the real line `ρ ≥ √2`.  The segment `|ρ| < √2` carries the
imaginary frequencies `r = i√(2 − ρ²)`.  The shift turns the cosine-type (even) spectral problem
into an ordinary positive-definite one.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral

/-! ## The shifted spectral variable `ρ(z) = (z² + 2)^{1/2}` -/

/-- `ρ(z) = (z² + 2)^{1/2}` on the principal branch. -/
def rhoC (z : ℂ) : ℂ := (z ^ 2 + 2) ^ (1 / 2 : ℂ)

theorem rhoC_sq (z : ℂ) : rhoC z ^ 2 = z ^ 2 + 2 := by
  unfold rhoC
  rw [one_div]
  exact Complex.cpow_ofNat_inv_pow (z ^ 2 + 2) 2

theorem rhoC_neg (z : ℂ) : rhoC (-z) = rhoC z := by
  unfold rhoC; rw [neg_sq]

theorem rhoC_ofReal (r : ℝ) : rhoC r = ((Real.sqrt (r ^ 2 + 2) : ℝ) : ℂ) := by
  unfold rhoC
  rw [show (r : ℂ) ^ 2 + 2 = ((r ^ 2 + 2 : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), Real.sqrt_eq_rpow]

theorem sq_add_two_mem_slitPlane {z : ℂ} (hz : |z.im| < Real.sqrt 2) :
    z ^ 2 + 2 ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  have hre : (z ^ 2 + 2).re = z.re ^ 2 - z.im ^ 2 + 2 := by simp [sq]
  have him : (z ^ 2 + 2).im = 2 * z.re * z.im := by simp [sq]; ring
  have hy2 : z.im ^ 2 < 2 := by
    have h0 : 0 ≤ |z.im| := abs_nonneg _
    have := mul_self_lt_mul_self h0 hz
    rw [Real.mul_self_sqrt (by norm_num), ← sq, sq_abs] at this
    exact this
  by_cases h : z.re * z.im = 0
  · left
    rw [hre]
    rcases mul_eq_zero.mp h with h0 | h0
    · rw [h0]; nlinarith
    · rw [h0]; nlinarith [sq_nonneg z.re]
  · right
    rw [him]
    intro h2
    apply h
    linarith

theorem differentiableAt_rhoC {z : ℂ} (hz : |z.im| < Real.sqrt 2) : DifferentiableAt ℂ rhoC z :=
  ((differentiableAt_id.pow 2).add_const 2).cpow_const (sq_add_two_mem_slitPlane hz)

theorem rhoC_conj {z : ℂ} (hz : |z.im| < Real.sqrt 2) : rhoC (conj z) = conj (rhoC z) := by
  unfold rhoC
  have hmem := sq_add_two_mem_slitPlane hz
  have harg : (conj (z ^ 2 + 2)).arg ≠ Real.pi := by
    rw [Complex.arg_conj]
    have := Complex.mem_slitPlane_iff_arg.mp hmem
    split_ifs with h
    · exact absurd h this.1
    · intro h2
      have : (z ^ 2 + 2).arg = -Real.pi := by linarith
      have hgt := Complex.neg_pi_lt_arg (z ^ 2 + 2)
      linarith
  have h := Complex.cpow_conj (conj (z ^ 2 + 2)) (1 / 2) harg
  rw [Complex.conj_conj] at h
  have e : conj (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [e] at h
  rw [show conj z ^ 2 + 2 = conj (z ^ 2 + 2) by rw [map_add, map_pow, map_ofNat]]
  exact h

theorem abs_im_rhoC_le (z : ℂ) : |(rhoC z).im| ≤ |z.im| := by
  set w := rhoC z
  have hw2 : w ^ 2 = z ^ 2 + 2 := rhoC_sq z
  have hre : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [sq]
  have hn : ‖w ^ 2‖ = w.re ^ 2 + w.im ^ 2 := by
    rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]; ring
  have hz2 : ‖z ^ 2 + 2‖ ≤ z.re ^ 2 + z.im ^ 2 + 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith
  have hzre : (z ^ 2 + 2).re = z.re ^ 2 - z.im ^ 2 + 2 := by simp [sq]
  rw [hw2] at hre hn
  have : w.im ^ 2 ≤ z.im ^ 2 := by nlinarith
  exact sq_le_sq.mp this


/-! ## Good spectral densities -/

/-- A spectral density holomorphic and exponentially decaying on `|Im z| ≤ 5/4`, even, and real on
the real line. -/
structure GoodDensity (K : ℂ → ℂ) : Prop where
  strip : ∃ ε C : ℝ, 0 < ε ∧ StripDecay K (5 / 4) ε C
  even : ∀ z, K (-z) = K z
  real : ∀ r : ℝ, (K r).im = 0

theorem GoodDensity.continuous_ofReal {K : ℂ → ℂ} (hK : GoodDensity K) :
    Continuous fun r : ℝ => K r := by
  obtain ⟨ε, C, -, hs⟩ := hK.strip
  exact continuous_ofReal_comp_of_stripDecay hs (by norm_num)

theorem GoodDensity.norm_le {K : ℂ → ℂ} (hK : GoodDensity K) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ r : ℝ, ‖K r‖ ≤ C * Real.exp (-(ε * |r|)) := by
  obtain ⟨ε, C, hε, hs⟩ := hK.strip
  refine ⟨ε, C, hε, hs.const_nonneg (by norm_num), fun r => ?_⟩
  have := hs.bound r (by simp; norm_num)
  simpa using this

theorem GoodDensity.integrable_mul {K : ℂ → ℂ} (hK : GoodDensity K) {P : ℝ → ℝ}
    (hP : Continuous P) {M : ℝ} (hPb : ∀ r, |P r| ≤ M * (1 + |r|)) :
    Integrable fun r : ℝ => (K r).re * P r := by
  obtain ⟨ε, C, hε, hC, hb⟩ := hK.norm_le
  have hM : 0 ≤ M := by
    have := (abs_nonneg _).trans (hPb 0); simpa using this
  have hmaj : Integrable fun r : ℝ => C * M * ((1 + |r|) * Real.exp (-(ε * |r|))) := by
    have h1 : Integrable fun r : ℝ => Real.exp (-(ε * |r|)) := integrable_exp_neg_rate_abs hε
    have h2 : Integrable fun r : ℝ => |r| * Real.exp (-(ε * |r|)) := by
      refine (integrable_exp_neg_rate_abs (half_pos hε)).const_mul (2 / ε) |>.mono' ?_
        (Filter.Eventually.of_forall fun r => ?_)
      · exact ((continuous_abs.mul (by fun_prop : Continuous fun r : ℝ =>
          Real.exp (-(ε * |r|))))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_exp_neg_le hε
    refine ((h1.add h2).const_mul (C * M)).congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.add_apply]
    ring
  refine hmaj.mono' ((Complex.continuous_re.comp hK.continuous_ofReal).mul
    hP).aestronglyMeasurable (Filter.Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |(K r).re| * |P r| ≤ (C * Real.exp (-(ε * |r|))) * (M * (1 + |r|)) :=
        mul_le_mul ((Complex.abs_re_le_norm _).trans (hb r)) (hPb r) (abs_nonneg _)
          (by positivity)
    _ = C * M * ((1 + |r|) * Real.exp (-(ε * |r|))) := by ring

theorem GoodDensity.integrable_gammaBracket {K : ℂ → ℂ} (hK : GoodDensity K) :
    Integrable fun r : ℝ => (K r).re * EF.gammaBracket r := by
  refine hK.integrable_mul WeilHerglotz.continuous_gammaBracket (M := |gammaLogConst| + 2)
    fun r => ?_
  have := abs_abs_gammaBracket_le_linear r
  rwa [abs_abs] at this

theorem GoodDensity.integrable_cos {K : ℂ → ℂ} (hK : GoodDensity K) (x : ℝ) :
    Integrable fun r : ℝ => (K r).re * Real.cos (r * x) :=
  hK.integrable_mul (by fun_prop) (M := 1) fun r => by
    have := Real.abs_cos_le_one (r * x)
    nlinarith [abs_nonneg r]

/-- `(1/π) ∫ Re K(r) cos(rx) dr = 2 Re F̌K(x)`. -/
theorem GoodDensity.integral_cos_eq {K : ℂ → ℂ} (hK : GoodDensity K) (x : ℝ) :
    1 / Real.pi * ∫ r : ℝ, (K r).re * Real.cos (r * x) = 2 * (stripInvFT K x).re := by
  obtain ⟨ε, C, hε, hs⟩ := hK.strip
  have hint : Integrable fun r : ℝ => K r * cexp (-(I * r * x)) := by
    refine Integrable.mono' (g := fun r : ℝ => ‖K r‖) ?_ ?_ ?_
    · obtain ⟨ε', C', hε', hC', hb'⟩ := hK.norm_le
      exact ((integrable_exp_neg_rate_abs hε').const_mul C').mono'
        hK.continuous_ofReal.norm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun r => by rw [Real.norm_eq_abs, abs_norm]; exact hb' r)
    · exact (hK.continuous_ofReal.mul (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun r => by
        rw [norm_mul, norm_cexp_neg_I_real, mul_one]
  unfold stripInvFT
  have e1 : ((1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, K r * cexp (-(I * r * x))).re =
      1 / (2 * Real.pi) * ∫ r : ℝ, (K r * cexp (-(I * r * x))).re := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
    congr 1
    exact (integral_re hint).symm
  rw [e1]
  have e2 : ∀ r : ℝ, (K r * cexp (-(I * r * x))).re = (K r).re * Real.cos (r * x) := fun r => by
    have hi := hK.real r
    rw [Complex.mul_re, hi, zero_mul, sub_zero]
    congr 1
    rw [show -(I * (r : ℂ) * x) = ((-(r * x) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  simp_rw [e2]
  ring


/-! ## Linearity of the even functional on good densities -/

theorem growthConst_nonneg {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) : 0 ≤ Cg := by
  have h := (abs_nonneg (lam 2)).trans (hg 2 le_rfl)
  have hp : 0 < Real.sqrt (2 : ℕ) * (1 + Real.log (2 : ℕ)) := by
    have : 0 ≤ Real.log (2 : ℕ) := Real.log_natCast_nonneg 2
    positivity
  by_contra hneg
  push Not at hneg
  have : Cg * Real.sqrt (2 : ℕ) * (1 + Real.log (2 : ℕ)) < 0 := by
    rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg hp
  linarith

theorem abs_weight_le {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) (n : ℕ) :
    |(if 2 ≤ n then lam n / Real.sqrt n else 0)| ≤ Cg * (1 + Real.log n) := by
  have hCg := growthConst_nonneg hg
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  split_ifs with hn
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    have := hg n hn
    nlinarith
  · rw [abs_zero]; positivity

theorem GoodDensity.abs_prime_le {K : ℂ → ℂ} (hK : GoodDensity K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n →
      |1 / Real.pi * ∫ r : ℝ, (K r).re * Real.cos (r * Real.log n)| ≤
        D * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨ε, C, hε, hs⟩ := hK.strip
  have hC := hs.const_nonneg (by norm_num)
  set D₀ := C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi) with hD₀
  have hD₀0 : 0 ≤ D₀ := by
    have : 0 ≤ ∫ r : ℝ, Real.exp (-(ε * |r|)) := integral_nonneg fun _ => (Real.exp_pos _).le
    positivity
  refine ⟨2 * D₀, by positivity, fun n hn => ?_⟩
  rw [hK.integral_cos_eq]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := norm_stripInvFT_le (by norm_num) hε hs (Real.log n)
  have hexp : Real.exp (-(5 / 4 * |Real.log n|)) = (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
    rw [abs_of_nonneg (Real.log_natCast_nonneg n), Real.rpow_def_of_pos hn0]; ring_nf
  rw [hexp] at hb
  rw [abs_mul, abs_two]
  have := (Complex.abs_re_le_norm (stripInvFT K (Real.log n))).trans hb
  linarith

theorem GoodDensity.summable_prime {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {K : ℂ → ℂ}
    (hK : GoodDensity K) :
    Summable fun n : ℕ => (if 2 ≤ n then lam n / Real.sqrt n else 0) *
      (1 / Real.pi * ∫ r : ℝ, (K r).re * Real.cos (r * Real.log n)) := by
  obtain ⟨D, hD, hb⟩ := hK.abs_prime_le
  have hCg := growthConst_nonneg hg
  refine Summable.of_norm_bounded
    ((summable_one_add_log_mul_rpow (b₁ := 5 / 4) (by norm_num)).mul_left (Cg * D)) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero,
      ↓reduceIte, abs_zero, zero_mul]
    have h0 : (0 : ℝ) ^ (-(5 / 4 : ℝ)) = 0 := Real.zero_rpow (by norm_num)
    simp [h0]
  calc |(if 2 ≤ n then lam n / Real.sqrt n else 0)| *
        |1 / Real.pi * ∫ r : ℝ, (K r).re * Real.cos (r * Real.log n)|
      ≤ (Cg * (1 + Real.log n)) * (D * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
        mul_le_mul (abs_weight_le hg n) (hb n hn) (abs_nonneg _)
          (by have := Real.log_natCast_nonneg n; positivity)
    _ = Cg * D * ((1 + Real.log n) * (n : ℝ) ^ (-(5 / 4 : ℝ))) := by ring

theorem GoodDensity.sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) {K : ι → ℂ → ℂ}
    (hK : ∀ i ∈ s, GoodDensity (K i)) : GoodDensity fun z => ∑ i ∈ s, (a i : ℂ) * K i z := by
  classical
  refine ⟨?_, fun z => ?_, fun r => ?_⟩
  · induction s using Finset.induction_on with
    | empty => exact ⟨1, 0, one_pos, fun z _ => by simp, fun z _ => by simp⟩
    | insert j s hj ih =>
      obtain ⟨ε₁, C₁, hε₁, h₁⟩ := ih fun i hi => hK i (Finset.mem_insert_of_mem hi)
      obtain ⟨ε₂, C₂, hε₂, h₂⟩ := (hK j (Finset.mem_insert_self j s)).strip
      have hC₁ := h₁.const_nonneg (by norm_num)
      have hC₂ := h₂.const_nonneg (by norm_num)
      refine ⟨min ε₁ ε₂, |a j| * C₂ + C₁, lt_min hε₁ hε₂, fun z hz => ?_, fun z hz => ?_⟩
      · simp only [Finset.sum_insert hj]
        exact ((differentiableAt_const _).mul (h₂.diff z hz)).add
          (h₁.diff z hz)
      · simp only [Finset.sum_insert hj]
        have he : ∀ ε, min ε₁ ε₂ ≤ ε → Real.exp (-(ε * |z.re|)) ≤
            Real.exp (-(min ε₁ ε₂ * |z.re|)) := fun ε hε =>
          Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.re])
        calc ‖(a j : ℂ) * K j z + ∑ i ∈ s, (a i : ℂ) * K i z‖
            ≤ |a j| * ‖K j z‖ + ‖∑ i ∈ s, (a i : ℂ) * K i z‖ := by
              refine (norm_add_le _ _).trans ?_
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ |a j| * (C₂ * Real.exp (-(min ε₁ ε₂ * |z.re|))) +
              C₁ * Real.exp (-(min ε₁ ε₂ * |z.re|)) := by
              gcongr
              · exact (h₂.bound z hz).trans (mul_le_mul_of_nonneg_left (he ε₂ (min_le_right _ _))
                  hC₂)
              · exact (h₁.bound z hz).trans (mul_le_mul_of_nonneg_left (he ε₁ (min_le_left _ _))
                  hC₁)
          _ = (|a j| * C₂ + C₁) * Real.exp (-(min ε₁ ε₂ * |z.re|)) := by ring
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [(hK i hi).even]
  · rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Complex.im_ofReal_mul, (hK i hi).real, mul_zero]

/-- **Linearity.** -/
theorem evenWeilDensity_sum {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) {K : ι → ℂ → ℂ} (hK : ∀ i ∈ s, GoodDensity (K i)) :
    evenWeilDensity lam (fun z => ∑ i ∈ s, (a i : ℂ) * K i z) =
      ∑ i ∈ s, a i * evenWeilDensity lam (K i) := by
  unfold evenWeilDensity
  have hp : ((∑ i ∈ s, (a i : ℂ) * K i (I / 2)) + ∑ i ∈ s, (a i : ℂ) * K i (-I / 2)).re =
      ∑ i ∈ s, a i * (K i (I / 2) + K i (-I / 2)).re := by
    rw [← Finset.sum_add_distrib, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add, Complex.re_ofReal_mul]
  have ha : (∫ r : ℝ, (∑ i ∈ s, (a i : ℂ) * K i r).re * EF.gammaBracket r) =
      ∑ i ∈ s, a i * ∫ r : ℝ, (K i r).re * EF.gammaBracket r := by
    have e : (fun r : ℝ => (∑ i ∈ s, (a i : ℂ) * K i r).re * EF.gammaBracket r) =
        fun r : ℝ => ∑ i ∈ s, a i * ((K i r).re * EF.gammaBracket r) := by
      funext r
      rw [Complex.re_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_ofReal_mul]; ring
    rw [e, integral_finsetSum _ fun i hi => ((hK i hi).integrable_gammaBracket.const_mul (a i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  have hc : ∀ n : ℕ, (1 / Real.pi * ∫ r : ℝ, (∑ i ∈ s, (a i : ℂ) * K i r).re *
      Real.cos (r * Real.log n)) =
      ∑ i ∈ s, a i * (1 / Real.pi * ∫ r : ℝ, (K i r).re * Real.cos (r * Real.log n)) := by
    intro n
    have e : (fun r : ℝ => (∑ i ∈ s, (a i : ℂ) * K i r).re * Real.cos (r * Real.log n)) =
        fun r : ℝ => ∑ i ∈ s, a i * ((K i r).re * Real.cos (r * Real.log n)) := by
      funext r
      rw [Complex.re_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_ofReal_mul]; ring
    rw [e, integral_finsetSum _ fun i hi => (((hK i hi).integrable_cos _).const_mul (a i)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]; ring
  have ht : (∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
      (1 / Real.pi * ∫ r : ℝ, (∑ i ∈ s, (a i : ℂ) * K i r).re * Real.cos (r * Real.log n))) =
      ∑ i ∈ s, a i * ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
        (1 / Real.pi * ∫ r : ℝ, (K i r).re * Real.cos (r * Real.log n)) := by
    have hm : ∀ n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
        ∑ i ∈ s, a i * (1 / Real.pi * ∫ r : ℝ, (K i r).re * Real.cos (r * Real.log n)) =
        ∑ i ∈ s, a i * ((if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ, (K i r).re * Real.cos (r * Real.log n))) := by
      intro n
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp_rw [hc, hm]
    rw [Summable.tsum_finsetSum fun i hi => ((hK i hi).summable_prime hg).mul_left (a i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tsum_mul_left]
  rw [hp, ha, ht, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring


theorem evenWeilDensity_congr {lam : ℕ → ℝ} {K₁ K₂ : ℂ → ℂ} (h1 : K₁ (I / 2) = K₂ (I / 2))
    (h2 : K₁ (-I / 2) = K₂ (-I / 2)) (hr : ∀ r : ℝ, K₁ r = K₂ r) :
    evenWeilDensity lam K₁ = evenWeilDensity lam K₂ := by
  unfold evenWeilDensity
  rw [h1, h2]
  simp_rw [hr]

/-! ## Even strip functions and their cosine shifts -/

/-- An even strip function on `|Im z| ≤ 5/4`, real on the real line. -/
structure EvenStrip (Φ : ℂ → ℂ) : Prop where
  strip : ∃ ε C : ℝ, 0 < ε ∧ StripDecay Φ (5 / 4) ε C
  even : ∀ z, Φ (-z) = Φ z
  real : ∀ r : ℝ, (Φ r).im = 0

theorem EvenStrip.sym {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) (r : ℝ) : Φ (-(r : ℂ)) = conj (Φ r) := by
  rw [hΦ.even, Complex.conj_eq_iff_im.mpr (hΦ.real r)]

theorem abs_im_lt_sqrt_two {z : ℂ} (hz : |z.im| ≤ 5 / 4) : |z.im| < Real.sqrt 2 := by
  have : (5 / 4 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

theorem differentiableAt_specSq {Φ : ℂ → ℂ} {b ε C : ℝ} (hΦ : StripDecay Φ b ε C) {z : ℂ}
    (hz : |z.im| ≤ b) : DifferentiableAt ℂ (specSq Φ) z := by
  have h1 : DifferentiableAt ℂ Φ z := hΦ.diff z hz
  have h2 : DifferentiableAt ℂ Φ (conj z) := hΦ.diff (conj z) (by simpa using hz)
  have h3 := h2.conj_conj
  rw [Complex.conj_conj] at h3
  exact h1.mul h3

theorem norm_specSq_le {Φ : ℂ → ℂ} {b ε C : ℝ} (hΦ : StripDecay Φ b ε C) {z : ℂ}
    (hz : |z.im| ≤ b) :
    ‖specSq Φ z‖ ≤ C ^ 2 * Real.exp (-(2 * ε * |z.re|)) := by
  unfold specSq
  rw [norm_mul, Complex.norm_conj]
  have h1 := hΦ.bound z hz
  have h2 := hΦ.bound (conj z) (by simpa using hz)
  rw [Complex.conj_re] at h2
  calc ‖Φ z‖ * ‖Φ (conj z)‖ ≤ (C * Real.exp (-(ε * |z.re|))) * (C * Real.exp (-(ε * |z.re|))) :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = C ^ 2 * Real.exp (-(2 * ε * |z.re|)) := by
        rw [show C ^ 2 * Real.exp (-(2 * ε * |z.re|)) =
          C * C * (Real.exp (-(ε * |z.re|)) * Real.exp (-(ε * |z.re|))) by
            rw [← Real.exp_add]; ring_nf]
        ring

theorem specSq_neg_of_even {Φ : ℂ → ℂ} (heven : ∀ z, Φ (-z) = Φ z) (z : ℂ) :
    specSq Φ (-z) = specSq Φ z := by
  unfold specSq; rw [heven, map_neg, heven]

theorem specSq_im_ofReal {Φ : ℂ → ℂ} (r : ℝ) : (specSq Φ r).im = 0 := by
  unfold specSq
  rw [Complex.conj_ofReal, Complex.mul_conj, Complex.ofReal_im]

/-- The cosine shift `cos(y ρ(z)) Φ(z) Φ^#(z)`. -/
def rhoCosShift (y : ℝ) (Φ : ℂ → ℂ) (z : ℂ) : ℂ := Complex.cos (y * rhoC z) * specSq Φ z

theorem norm_cos_mul_rhoC_le (y : ℝ) {z : ℂ} :
    ‖Complex.cos (y * rhoC z)‖ ≤ Real.exp (|y| * |z.im|) := by
  refine (GaloisForLFunctions.HTGeometry.norm_ccos_le_exp_abs_im _).trans
    (Real.exp_le_exp.mpr ?_)
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_im_rhoC_le z) (abs_nonneg y)

theorem norm_sin_mul_rhoC_le (y : ℝ) {z : ℂ} :
    ‖Complex.sin (y * rhoC z)‖ ≤ Real.exp (|y| * |z.im|) := by
  refine (GaloisForLFunctions.HTGeometry.norm_csin_le_exp_abs_im _).trans
    (Real.exp_le_exp.mpr ?_)
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_im_rhoC_le z) (abs_nonneg y)

theorem cos_mul_rhoC_ofReal_im (y r : ℝ) : (Complex.cos (y * rhoC r)).im = 0 := by
  rw [rhoC_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.ofReal_im]

theorem sin_mul_rhoC_ofReal_im (y r : ℝ) : (Complex.sin (y * rhoC r)).im = 0 := by
  rw [rhoC_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.ofReal_im]

theorem goodDensity_cosShift (y : ℝ) {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) :
    GoodDensity (rhoCosShift y Φ) := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  refine ⟨⟨2 * ε, Real.exp (|y| * (5 / 4)) * C ^ 2, by positivity, fun z hz => ?_,
    fun z hz => ?_⟩, fun z => ?_, fun r => ?_⟩
  · exact ((differentiableAt_rhoC (abs_im_lt_sqrt_two hz)).const_mul (y : ℂ)).ccos.mul
      (differentiableAt_specSq hs hz)
  · unfold rhoCosShift
    rw [norm_mul]
    have h1 : ‖Complex.cos (y * rhoC z)‖ ≤ Real.exp (|y| * (5 / 4)) :=
      (norm_cos_mul_rhoC_le y).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hz (abs_nonneg y)))
    calc ‖Complex.cos (y * rhoC z)‖ * ‖specSq Φ z‖
        ≤ Real.exp (|y| * (5 / 4)) * (C ^ 2 * Real.exp (-(2 * ε * |z.re|))) :=
          mul_le_mul h1 (norm_specSq_le hs hz) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · unfold rhoCosShift; rw [rhoC_neg, specSq_neg_of_even hΦ.even]
  · unfold rhoCosShift
    rw [Complex.mul_im, cos_mul_rhoC_ofReal_im, specSq_im_ofReal]
    ring

theorem goodDensity_specSq {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) : GoodDensity (specSq Φ) := by
  have h := goodDensity_cosShift 0 hΦ
  have e : rhoCosShift 0 Φ = specSq Φ := by
    funext z; unfold rhoCosShift; simp
  rwa [e] at h

/-- The cosine-shift function `φ_Φ(y) = L(cos(y ρ) Φ Φ^#)`. -/
def cosineShiftFn (lam : ℕ → ℝ) (Φ : ℂ → ℂ) (y : ℝ) : ℝ := evenWeilDensity lam (rhoCosShift y Φ)


/-! ## Positive definiteness of the cosine-shift function -/

theorem evenWeilDensity_add {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {K₁ K₂ : ℂ → ℂ}
    (h₁ : GoodDensity K₁) (h₂ : GoodDensity K₂) :
    evenWeilDensity lam (fun z => K₁ z + K₂ z) =
      evenWeilDensity lam K₁ + evenWeilDensity lam K₂ := by
  have h := evenWeilDensity_sum hg (Finset.univ : Finset (Fin 2)) (fun _ => 1) (K := ![K₁, K₂])
    (fun i _ => by fin_cases i <;> simpa)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_one,
    one_mul] at h
  exact h

/-- `Σ c_i cos(t_i ρ) Φ`. -/
def cosComb {N : ℕ} (t c : Fin N → ℝ) (Φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i, (c i : ℂ) * Complex.cos (t i * rhoC z) * Φ z

/-- `Σ c_i sin(t_i ρ) Φ`. -/
def sinComb {N : ℕ} (t c : Fin N → ℝ) (Φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i, (c i : ℂ) * Complex.sin (t i * rhoC z) * Φ z

theorem stripDecay_trigComb {N : ℕ} (t c : Fin N → ℝ) {Φ : ℂ → ℂ} {ε C : ℝ}
    (hs : StripDecay Φ (5 / 4) ε C) (T : ℂ → ℂ) (hT : ∀ y : ℝ, ∀ z : ℂ, |z.im| ≤ 5 / 4 →
      DifferentiableAt ℂ (fun w => T (y * rhoC w)) z ∧
        ‖T (y * rhoC z)‖ ≤ Real.exp (|y| * (5 / 4))) :
    StripDecay (fun z => ∑ i, (c i : ℂ) * T (t i * rhoC z) * Φ z) (5 / 4) ε
      ((∑ i, |c i| * Real.exp (|t i| * (5 / 4))) * C) := by
  have hC := hs.const_nonneg (by norm_num)
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact DifferentiableAt.fun_sum fun i _ =>
      ((differentiableAt_const _).mul (hT (t i) z hz).1).mul (hs.diff z hz)
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := (hT (t i) z hz).2
    have h2 := hs.bound z hz
    calc |c i| * ‖T (t i * rhoC z)‖ * ‖Φ z‖
        ≤ |c i| * Real.exp (|t i| * (5 / 4)) * (C * Real.exp (-(ε * |z.re|))) := by
          gcongr
      _ = |c i| * Real.exp (|t i| * (5 / 4)) * C * Real.exp (-(ε * |z.re|)) := by ring

theorem evenStrip_cosComb {N : ℕ} (t c : Fin N → ℝ) {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) :
    EvenStrip (cosComb t c Φ) := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  refine ⟨⟨ε, _, hε, stripDecay_trigComb t c hs Complex.cos fun y z hz =>
    ⟨((differentiableAt_rhoC (abs_im_lt_sqrt_two hz)).const_mul (y : ℂ)).ccos,
      (norm_cos_mul_rhoC_le y).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hz (abs_nonneg y)))⟩⟩, fun z => ?_, fun r => ?_⟩
  · unfold cosComb; simp only [rhoC_neg, hΦ.even]
  · unfold cosComb
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Complex.mul_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      cos_mul_rhoC_ofReal_im, hΦ.real]
    ring

theorem evenStrip_sinComb {N : ℕ} (t c : Fin N → ℝ) {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) :
    EvenStrip (sinComb t c Φ) := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  refine ⟨⟨ε, _, hε, stripDecay_trigComb t c hs Complex.sin fun y z hz =>
    ⟨((differentiableAt_rhoC (abs_im_lt_sqrt_two hz)).const_mul (y : ℂ)).csin,
      (norm_sin_mul_rhoC_le y).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hz (abs_nonneg y)))⟩⟩, fun z => ?_, fun r => ?_⟩
  · unfold sinComb; simp only [rhoC_neg, hΦ.even]
  · unfold sinComb
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Complex.mul_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      sin_mul_rhoC_ofReal_im, hΦ.real]
    ring

theorem conj_trig_rhoC_conj (y : ℝ) {z : ℂ} (hz : |z.im| < Real.sqrt 2) :
    conj (Complex.cos (y * rhoC (conj z))) = Complex.cos (y * rhoC z) ∧
      conj (Complex.sin (y * rhoC (conj z))) = Complex.sin (y * rhoC z) := by
  have h : conj ((y : ℂ) * rhoC (conj z)) = y * rhoC z := by
    rw [rhoC_conj hz, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  constructor
  · rw [← Complex.cos_conj, h]
  · rw [← Complex.sin_conj, h]

/-- `A A^# + B B^# = Σ_{i,j} c_i c_j cos((t_j − t_i) ρ) Φ Φ^#` on the strip. -/
theorem specSq_cosComb_add_specSq_sinComb {N : ℕ} (t c : Fin N → ℝ) (Φ : ℂ → ℂ) {z : ℂ}
    (hz : |z.im| < Real.sqrt 2) :
    specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z =
      ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
        ((c p.1 * c p.2 : ℝ) : ℂ) * rhoCosShift (t p.2 - t p.1) Φ z := by
  have hcos : ∀ i, conj (Complex.cos (t i * rhoC (conj z))) = Complex.cos (t i * rhoC z) :=
    fun i => (conj_trig_rhoC_conj (t i) hz).1
  have hsin : ∀ i, conj (Complex.sin (t i * rhoC (conj z))) = Complex.sin (t i * rhoC z) :=
    fun i => (conj_trig_rhoC_conj (t i) hz).2
  unfold specSq cosComb sinComb rhoCosShift specSq
  rw [map_sum, map_sum, Finset.sum_product]
  simp only [map_mul, Complex.conj_ofReal, hcos, hsin]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ((t j - t i : ℝ) : ℂ) * rhoC z = t j * rhoC z - t i * rhoC z := by push_cast; ring
  rw [e, Complex.cos_sub]
  push_cast
  ring

theorem cosShift_neg (y : ℝ) (Φ : ℂ → ℂ) : rhoCosShift (-y) Φ = rhoCosShift y Φ := by
  funext z; unfold rhoCosShift; push_cast; rw [neg_mul, Complex.cos_neg]

theorem cosineShiftFn_neg (lam : ℕ → ℝ) (Φ : ℂ → ℂ) (y : ℝ) :
    cosineShiftFn lam Φ (-y) = cosineShiftFn lam Φ y := by
  unfold cosineShiftFn; rw [cosShift_neg]

/-- **Real positive definiteness.** -/
theorem sum_sum_cosineShiftFn_nonneg {lam : ℕ → ℝ} (h : WeilPositiveEvenAt 1 lam) {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {N : ℕ} (t c : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * cosineShiftFn lam Φ (t j - t i) := by
  have hgood : ∀ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
      GoodDensity (rhoCosShift (t p.2 - t p.1) Φ) := fun p _ => goodDensity_cosShift _ hΦ
  have hlin := evenWeilDensity_sum hg ((Finset.univ : Finset (Fin N)) ×ˢ Finset.univ)
    (fun p => c p.1 * c p.2) hgood
  have hsum : ∑ i, ∑ j, c i * c j * cosineShiftFn lam Φ (t j - t i) =
      ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
        c p.1 * c p.2 * evenWeilDensity lam (rhoCosShift (t p.2 - t p.1) Φ) := by
    rw [Finset.sum_product]; rfl
  have hA := evenStrip_cosComb t c hΦ
  have hB := evenStrip_sinComb t c hΦ
  have hcongr : evenWeilDensity lam (fun z => ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ
      Finset.univ, ((c p.1 * c p.2 : ℝ) : ℂ) * rhoCosShift (t p.2 - t p.1) Φ z) =
      evenWeilDensity lam (fun z => specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z) := by
    have hI1 : |(I / 2 : ℂ).im| < Real.sqrt 2 := abs_im_lt_sqrt_two (by norm_num [abs_of_pos])
    have hI2 : |(-I / 2 : ℂ).im| < Real.sqrt 2 := abs_im_lt_sqrt_two (by norm_num [abs_of_pos])
    refine evenWeilDensity_congr ?_ ?_ fun r => ?_
    · exact (specSq_cosComb_add_specSq_sinComb t c Φ hI1).symm
    · exact (specSq_cosComb_add_specSq_sinComb t c Φ hI2).symm
    · exact (specSq_cosComb_add_specSq_sinComb t c Φ
        (abs_im_lt_sqrt_two (by simp; norm_num))).symm
  rw [hsum, ← hlin, hcongr,
    evenWeilDensity_add hg (goodDensity_specSq hA) (goodDensity_specSq hB)]
  obtain ⟨εA, CA, hεA, hsA⟩ := hA.strip
  obtain ⟨εB, CB, hεB, hsB⟩ := hB.strip
  exact add_nonneg
    (evenWeilDensity_specSq_nonneg h hg (by norm_num) hεA hsA hA.sym hA.even)
    (evenWeilDensity_specSq_nonneg h hg (by norm_num) hεB hsB hB.sym hB.even)


/-- A real even function that is positive definite with real coefficients is positive definite. -/
theorem positiveDefiniteOnReal_of_real {φ : ℝ → ℝ} (heven : ∀ y, φ (-y) = φ y)
    (hpd : ∀ (N : ℕ) (t c : Fin N → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * φ (t j - t i)) :
    GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal fun y => (φ y : ℂ) := by
  intro N t c
  set α : Fin N → ℝ := fun i => (c i).re
  set β : Fin N → ℝ := fun i => (c i).im
  refine ⟨(∑ i, ∑ j, α i * α j * φ (t j - t i)) + ∑ i, ∑ j, β i * β j * φ (t j - t i),
    add_nonneg (hpd N t α) (hpd N t β), ?_⟩
  have hswap : ∑ i, ∑ j, β i * α j * φ (t j - t i) = ∑ i, ∑ j, α i * β j * φ (t j - t i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← heven, neg_sub]
    ring
  have hpt : ∀ i j, star (c i) * (φ (t j - t i) : ℂ) * c j =
      ((φ (t j - t i) * (α i * α j + β i * β j) : ℝ) : ℂ) +
        ((φ (t j - t i) * (α i * β j - β i * α j) : ℝ) : ℂ) * I := by
    intro i j
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, α, β] <;> ring
  simp_rw [hpt]
  rw [show (∑ i, ∑ j, (((φ (t j - t i) * (α i * α j + β i * β j) : ℝ) : ℂ) +
      ((φ (t j - t i) * (α i * β j - β i * α j) : ℝ) : ℂ) * I)) =
      (((∑ i, ∑ j, φ (t j - t i) * (α i * α j + β i * β j)) : ℝ) : ℂ) +
        (((∑ i, ∑ j, φ (t j - t i) * (α i * β j - β i * α j)) : ℝ) : ℂ) * I by
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]]
  have h0 : (∑ i, ∑ j, φ (t j - t i) * (α i * β j - β i * α j)) = 0 := by
    have e : (∑ i, ∑ j, φ (t j - t i) * (α i * β j - β i * α j)) =
        (∑ i, ∑ j, α i * β j * φ (t j - t i)) - ∑ i, ∑ j, β i * α j * φ (t j - t i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, hswap, sub_self]
  rw [h0, Complex.ofReal_zero, zero_mul, add_zero]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## Continuity -/

theorem cosShift_ofReal_re (y : ℝ) (Φ : ℂ → ℂ) (r : ℝ) :
    (rhoCosShift y Φ r).re = Real.cos (y * Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 := by
  unfold rhoCosShift
  rw [rhoC_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.re_ofReal_mul,
    specSq_re_ofReal]

theorem abs_prime_le_of_strip {K : ℂ → ℂ} {ε C : ℝ} (hε : 0 < ε) (hs : StripDecay K (5 / 4) ε C)
    (hK : GoodDensity K) {n : ℕ} (hn : 1 ≤ n) :
    |1 / Real.pi * ∫ r : ℝ, (K r).re * Real.cos (r * Real.log n)| ≤
      2 * (C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi)) * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
  rw [hK.integral_cos_eq]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := norm_stripInvFT_le (by norm_num) hε hs (Real.log n)
  have hexp : Real.exp (-(5 / 4 * |Real.log n|)) = (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
    rw [abs_of_nonneg (Real.log_natCast_nonneg n), Real.rpow_def_of_pos hn0]; ring_nf
  rw [hexp] at hb
  rw [abs_mul, abs_two]
  have := (Complex.abs_re_le_norm (stripInvFT K (Real.log n))).trans hb
  linarith

theorem continuous_cosineShiftFn {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) : Continuous (cosineShiftFn lam Φ) := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  have hC := hs.const_nonneg (by norm_num)
  have hgood := goodDensity_specSq hΦ
  have hint : Integrable fun r : ℝ => ‖Φ r‖ ^ 2 * |EF.gammaBracket r| := by
    have := hgood.integrable_mul continuous_abs_gammaBracket (M := |gammaLogConst| + 2)
      abs_abs_gammaBracket_le_linear
    simpa [specSq_re_ofReal] using this
  have hint1 : Integrable fun r : ℝ => ‖Φ r‖ ^ 2 := by
    have := hgood.integrable_mul (P := fun _ => 1) continuous_const (M := 1) fun r => by
      simp
    simpa [specSq_re_ofReal] using this
  have hcΦ : Continuous fun r : ℝ => ‖Φ r‖ ^ 2 :=
    ((continuous_ofReal_comp_of_stripDecay hs (by norm_num)).norm).pow 2
  -- the pole part
  have h1 : Continuous fun y : ℝ => (rhoCosShift y Φ (I / 2) + rhoCosShift y Φ (-I / 2)).re := by
    unfold rhoCosShift
    exact Complex.continuous_re.comp (((Complex.continuous_cos.comp
      (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const).add
      ((Complex.continuous_cos.comp (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const))
  -- the archimedean part
  have h2 : Continuous fun y : ℝ => ∫ r : ℝ, (rhoCosShift y Φ r).re * EF.gammaBracket r := by
    simp_rw [cosShift_ofReal_re]
    refine continuous_of_dominated (bound := fun r => ‖Φ r‖ ^ 2 * |EF.gammaBracket r|)
      (fun y => ?_) (fun y => Filter.Eventually.of_forall fun r => ?_) hint
      (Filter.Eventually.of_forall fun r => ?_)
    · exact (((by fun_prop : Continuous fun r : ℝ => Real.cos (y * Real.sqrt (r ^ 2 + 2)))).mul
        hcΦ |>.mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖Φ r‖)]
      have := Real.abs_cos_le_one (y * Real.sqrt (r ^ 2 + 2))
      have h0 : 0 ≤ ‖Φ r‖ ^ 2 * |EF.gammaBracket r| := by positivity
      nlinarith [abs_nonneg (EF.gammaBracket r), sq_nonneg ‖Φ r‖]
    · exact (by fun_prop : Continuous fun y : ℝ => Real.cos (y * Real.sqrt (r ^ 2 + 2)) *
        ‖Φ r‖ ^ 2 * EF.gammaBracket r)
  -- the prime part, locally uniformly
  have h3 : Continuous fun y : ℝ => ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
      (1 / Real.pi * ∫ r : ℝ, (rhoCosShift y Φ r).re * Real.cos (r * Real.log n)) := by
    rw [continuous_iff_continuousAt]
    intro y₀
    set R := |y₀| + 1
    have hball : Set.Ioo (-R) R ∈ 𝓝 y₀ := Ioo_mem_nhds (by
      have := neg_abs_le y₀; linarith) (by have := le_abs_self y₀; linarith)
    refine (ContinuousOn.continuousAt ?_ hball)
    set D := 2 * (Real.exp (R * (5 / 4)) * C ^ 2 * (∫ r : ℝ, Real.exp (-(2 * ε * |r|))) /
      (2 * Real.pi))
    have hD : 0 ≤ D := by
      have : 0 ≤ ∫ r : ℝ, Real.exp (-(2 * ε * |r|)) := integral_nonneg fun _ => (Real.exp_pos _).le
      positivity
    have hCg := growthConst_nonneg hg
    refine continuousOn_tsum (u := fun n : ℕ => Cg * D * ((1 + Real.log n) *
      (n : ℝ) ^ (-(5 / 4 : ℝ)))) (fun n => ?_)
      ((summable_one_add_log_mul_rpow (b₁ := 5 / 4) (by norm_num)).mul_left _)
      (fun n y hy => ?_)
    · refine (continuous_const.mul (continuous_const.mul ?_)).continuousOn
      simp_rw [cosShift_ofReal_re]
      refine continuous_of_dominated (bound := fun r => ‖Φ r‖ ^ 2)
        (fun y => ?_) (fun y => Filter.Eventually.of_forall fun r => ?_) hint1
        (Filter.Eventually.of_forall fun r => ?_)
      · exact (((by fun_prop : Continuous fun r : ℝ => Real.cos (y * Real.sqrt (r ^ 2 + 2)))).mul
          hcΦ |>.mul (by fun_prop)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖Φ r‖)]
        have h1 := Real.abs_cos_le_one (y * Real.sqrt (r ^ 2 + 2))
        have h2 := Real.abs_cos_le_one (r * Real.log n)
        have h0 := sq_nonneg ‖Φ r‖
        calc |Real.cos (y * Real.sqrt (r ^ 2 + 2))| * ‖Φ r‖ ^ 2 * |Real.cos (r * Real.log n)|
            ≤ 1 * ‖Φ r‖ ^ 2 * 1 := by gcongr
          _ = ‖Φ r‖ ^ 2 := by ring
      · exact (by fun_prop : Continuous fun y : ℝ => Real.cos (y * Real.sqrt (r ^ 2 + 2)) *
          ‖Φ r‖ ^ 2 * Real.cos (r * Real.log n))
    · rw [Real.norm_eq_abs, abs_mul]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      have hgy := goodDensity_cosShift y hΦ
      have hsy : StripDecay (rhoCosShift y Φ) (5 / 4) (2 * ε) (Real.exp (R * (5 / 4)) * C ^ 2) := by
        refine ⟨(hgy.strip.choose_spec.choose_spec.2).diff, fun z hz => ?_⟩
        unfold rhoCosShift
        rw [norm_mul]
        have hyR : |y| ≤ R := by
          rw [abs_le]; exact ⟨hy.1.le, hy.2.le⟩
        have h1 : ‖Complex.cos (y * rhoC z)‖ ≤ Real.exp (R * (5 / 4)) :=
          (norm_cos_mul_rhoC_le y).trans (Real.exp_le_exp.mpr
            (mul_le_mul hyR hz (abs_nonneg _) (by positivity)))
        calc ‖Complex.cos (y * rhoC z)‖ * ‖specSq Φ z‖
            ≤ Real.exp (R * (5 / 4)) * (C ^ 2 * Real.exp (-(2 * ε * |z.re|))) :=
              mul_le_mul h1 (norm_specSq_le hs hz) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      have hb := abs_prime_le_of_strip (by positivity) hsy hgy hn
      calc |(if 2 ≤ n then lam n / Real.sqrt n else 0)| *
            |1 / Real.pi * ∫ r : ℝ, (rhoCosShift y Φ r).re * Real.cos (r * Real.log n)|
          ≤ (Cg * (1 + Real.log n)) * (D * (n : ℝ) ^ (-(5 / 4 : ℝ))) := by
            refine mul_le_mul (abs_weight_le hg n) (hb.trans (le_of_eq ?_)) (abs_nonneg _)
              (by have := Real.log_natCast_nonneg n; positivity)
            ring
        _ = Cg * D * ((1 + Real.log n) * (n : ℝ) ^ (-(5 / 4 : ℝ))) := by ring
  unfold cosineShiftFn evenWeilDensity
  exact (h1.add (continuous_const.mul h2)).sub h3

/-- **The cosine-shift measure.**  `φ_Φ` is the characteristic function of a finite positive measure
on the `ρ`-line. -/
theorem exists_cosineShift_measure {lam : ℕ → ℝ} (h : WeilPositiveEvenAt 1 lam) {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∀ y, charFun ν y = (cosineShiftFn lam Φ y : ℂ) :=
  GaloisForLFunctions.HTGeometry.exists_charFun_eq_of_positiveDefinite
    (positiveDefiniteOnReal_of_real (cosineShiftFn_neg lam Φ)
      fun _ t c => sum_sum_cosineShiftFn_nonneg h hg hΦ t c)
    (Complex.continuous_ofReal.comp (continuous_cosineShiftFn hg hΦ))

end RHTower.EvenSector

end
