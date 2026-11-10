import GaloisForLFunctions.InfiniteRankPurityTheory.TheZerosContainNoClassOfOneFrobenius

/-!
# No sequence of zeros approaches a class of one Frobenius

The zeros of `ζ` contain no vertical progression. This module shows that they do not approach one
either: no two-sided sequence of zeros lies within an `ℓ²` perturbation of a vertical progression
in the open strip, at any real part.

* `summable_sq_norm_integral_mul_exp`: Bessel on the lattice of a period. The Fourier–Laplace
  samples `∫_0^∞ K(x) e^{-2πinx/P} dx` of a kernel with uniformly summable translates are the
  Fourier coefficients of the sum of the translates, hence square summable.
* `summable_sq_norm_riemannZeta_div`: `Σ_n |ζ(s + 2πin/P)|² / |s + 2πin/P|² < ∞` in the strip, by
  Parseval for the periodized Laplace kernel; the same sum without the squares diverges.
* `norm_integral_ladderKernel_taylor_le`: `∫ K_{s+η} = ∫ K_s - η ∫ x K_s + O(|η|²)` for
  `|η| ≤ Re s / 2`, with a constant depending on `Re s` only.
* `summable_norm_riemannZeta_div_of_ladder`: if `ζ(s_n + η_n) = 0` for all but finitely many `n`
  with `η ∈ ℓ²`, the two Laplace representations and the Taylor bound give
  `|ζ(s_n)/s_n| ≤ M|η_n|² + |η_n| (|b_n| + C(|a_n| + |ζ(s_n)/s_n|))` with `a, b` and the zeta
  values in `ℓ²`, so the zeta values would be summable.
* `not_cofinite_riemannZeta_eq_zero_of_sq_summable`, `not_cofinite_xi_eq_zero_near_class`: the
  conclusion, for a step `T > 0` and for the class of a Frobenius `q > 1`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

/-! ### Bessel on the lattice of a period -/

/-- The Fourier coefficients of a sum of translates are the Fourier–Laplace samples of the
kernel. -/
theorem integral_tsum_translates_mul_exp {K : ℝ → ℂ} (hK : Measurable K) {P : ℝ} (hP : 0 < P)
    {u : ℕ → ℝ} (hu : Summable u) (hbound : ∀ k : ℕ, ∀ y ∈ Ioc (0 : ℝ) P, ‖K (y + k * P)‖ ≤ u k)
    (hK0 : IntegrableOn K (Ioi (0 : ℝ))) (n : ℤ) :
    (∫ y in (0 : ℝ)..P, (∑' k : ℕ, K (y + k * P))
        * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ)))
      = ∫ x in Ioi (0 : ℝ), K x * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (x : ℂ)) := by
  have hnorm : ∀ x : ℝ, ‖Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (x : ℂ))‖ = 1 := by
    intro x
    rw [Complex.norm_exp]
    simp
  have hmeas : Measurable fun x : ℝ =>
      K x * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (x : ℂ)) :=
    hK.mul (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (x : ℂ))).measurable
  have h := integral_tsum_translates hmeas hP hu
    (fun k y hy => by rw [norm_mul, hnorm, mul_one]; exact hbound k y hy)
    (Integrable.mono' hK0.norm hmeas.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [norm_mul, hnorm, mul_one]))
  rw [← h]
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [← tsum_mul_right]
  exact tsum_congr fun k => by rw [exp_character_shift hP.ne' n k y]

/-- **Bessel on the lattice of a period.** The Fourier–Laplace samples of a kernel with uniformly
summable translates are square summable. -/
theorem summable_sq_norm_integral_mul_exp {K : ℝ → ℂ} (hK : Measurable K) {P : ℝ} (hP : 0 < P)
    {u : ℕ → ℝ} (hu : Summable u) (hbound : ∀ k : ℕ, ∀ y ∈ Ioc (0 : ℝ) P, ‖K (y + k * P)‖ ≤ u k)
    (hK0 : IntegrableOn K (Ioi (0 : ℝ))) :
    Summable fun n : ℤ => ‖∫ x in Ioi (0 : ℝ),
      K x * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (x : ℂ))‖ ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) P)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hL2 : MemLp (fun y : ℝ => ∑' k : ℕ, K (y + k * P)) 2 (volume.restrict (Ioc (0 : ℝ) P)) :=
    MemLp.of_bound (Measurable.tsum fun _ => hK.comp (by fun_prop)).aestronglyMeasurable (∑' k, u k)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun y hy =>
        tsum_of_norm_bounded hu.hasSum fun k => hbound k y hy))
  refine (((hasSum_sq_fourierCoeffOn hP hL2).summable).mul_left (P ^ 2)).congr fun n => ?_
  rw [fourierCoeffOn_eq_integral_mul_exp hP, integral_tsum_translates_mul_exp hK hP hu hbound hK0 n,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hP.le, mul_pow]
  field_simp

/-- The Laplace integrals of the kernel along a progression are square summable. -/
theorem summable_sq_norm_integral_ladderKernel {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) :
    Summable fun n : ℤ =>
      ‖∫ x in Ioi (0 : ℝ), ladderKernel (s + ((2 * π * n / P : ℝ) : ℂ) * I) x‖ ^ 2 := by
  have h := summable_sq_norm_integral_mul_exp (measurable_ladderKernel s) hP
    (summable_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_mul_lt_one hs hP))
    (fun k _ hy => norm_ladderKernel_shift_le hs.le hy.1.le k) (integrableOn_ladderKernel_Ioi hs)
  refine h.congr fun n => ?_
  simp_rw [ladderKernel_add_mul_I]

/-- **Parseval along a progression.** The zeta values `ζ(s_n)/s_n` on a vertical progression in
the strip are square summable. -/
theorem summable_sq_norm_riemannZeta_div {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {P : ℝ}
    (hP : 0 < P) :
    Summable fun n : ℤ => ‖riemannZeta (s + ((2 * π * n / P : ℝ) : ℂ) * I)
      / (s + ((2 * π * n / P : ℝ) : ℂ) * I)‖ ^ 2 := by
  refine (((hasSum_sq_fourierCoeffOn hP (memLp_ladderDefect h0 hP)).summable).mul_left
    (P ^ 2)).congr fun n => ?_
  rw [fourierCoeffOn_ladderDefect h0 h1 hP n, norm_neg, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hP.le, mul_pow]
  field_simp

/-! ### The first moment of the kernel -/

/-- The first moment `x {e^x} e^{-sx}` of the Laplace kernel. -/
def ladderMoment (s : ℂ) (x : ℝ) : ℂ := (x : ℂ) * ladderKernel s x

theorem measurable_ladderMoment (s : ℂ) : Measurable (ladderMoment s) :=
  Complex.measurable_ofReal.mul (measurable_ladderKernel s)

theorem mul_exp_neg_le {c : ℝ} (hc : 0 < c) (x : ℝ) : x * Real.exp (-(c * x)) ≤ 1 / c := by
  have h1 : c * x ≤ Real.exp (c * x) := by linarith [Real.add_one_le_exp (c * x)]
  have h2 : Real.exp (c * x) * Real.exp (-(c * x)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [le_div_iff₀ hc]
  calc x * Real.exp (-(c * x)) * c = c * x * Real.exp (-(c * x)) := by ring
    _ ≤ Real.exp (c * x) * Real.exp (-(c * x)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 1 := h2

theorem norm_ladderMoment_le {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖ladderMoment s x‖ ≤ 2 / s.re * Real.exp (-(s.re / 2 * x)) := by
  rw [ladderMoment, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx]
  have hsplit : Real.exp (-(s.re * x))
      = Real.exp (-(s.re / 2 * x)) * Real.exp (-(s.re / 2 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc x * ‖ladderKernel s x‖ ≤ x * Real.exp (-(s.re * x)) :=
        mul_le_mul_of_nonneg_left (norm_ladderKernel_le s x) hx
    _ = x * Real.exp (-(s.re / 2 * x)) * Real.exp (-(s.re / 2 * x)) := by rw [hsplit]; ring
    _ ≤ 1 / (s.re / 2) * Real.exp (-(s.re / 2 * x)) :=
        mul_le_mul_of_nonneg_right (mul_exp_neg_le (half_pos hs) x) (Real.exp_pos _).le
    _ = 2 / s.re * Real.exp (-(s.re / 2 * x)) := by rw [one_div_div]

theorem integrableOn_ladderMoment_Ioi {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (ladderMoment s) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (g := fun x : ℝ => 2 / s.re * Real.exp (-(s.re / 2) * x))
    ((exp_neg_integrableOn_Ioi 0 (half_pos hs)).const_mul _)
    (measurable_ladderMoment s).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
  simpa only [neg_mul] using norm_ladderMoment_le hs (le_of_lt hx)

theorem ladderMoment_add_mul_I (s : ℂ) (ω x : ℝ) :
    ladderMoment (s + (ω : ℂ) * I) x
      = ladderMoment s x * Complex.exp (-((ω : ℂ) * I) * (x : ℂ)) := by
  rw [ladderMoment, ladderMoment, ladderKernel_add_mul_I, mul_assoc]

/-- The first moments of the kernel along a progression are square summable. -/
theorem summable_sq_norm_integral_ladderMoment {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) :
    Summable fun n : ℤ =>
      ‖∫ x in Ioi (0 : ℝ), ladderMoment (s + ((2 * π * n / P : ℝ) : ℂ) * I) x‖ ^ 2 := by
  have hr : Real.exp (-(s.re / 2 * P)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos (half_pos hs) hP))
  have h := summable_sq_norm_integral_mul_exp (measurable_ladderMoment s) hP
    ((summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left (2 / s.re))
    (fun k y hy => by
      have hy0 : 0 ≤ y + (k : ℝ) * P := add_nonneg hy.1.le (by positivity)
      refine (norm_ladderMoment_le hs hy0).trans
        (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have : 0 ≤ s.re / 2 * y := mul_nonneg (half_pos hs).le hy.1.le
      nlinarith)
    (integrableOn_ladderMoment_Ioi hs)
  refine h.congr fun n => ?_
  simp_rw [ladderMoment_add_mul_I]

/-! ### The second order Taylor bound -/

theorem ladderKernel_add (s η : ℂ) (x : ℝ) :
    ladderKernel (s + η) x = ladderKernel s x * Complex.exp (-η * (x : ℂ)) := by
  rw [ladderKernel, ladderKernel, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The constant of the second order remainder at real part `σ`. -/
def taylorConstant (σ : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), 32 / σ ^ 2 * Real.exp (-(σ / 4) * x)

/-- **Second order Taylor bound.** Within `Re s / 2` of `s` the Laplace integral is its first order
expansion up to `M |η|²`, with `M` depending on `Re s` only. -/
theorem norm_integral_ladderKernel_taylor_le {s η : ℂ} (hs : 0 < s.re) (hη : ‖η‖ ≤ s.re / 2) :
    ‖(∫ x in Ioi (0 : ℝ), ladderKernel (s + η) x) - (∫ x in Ioi (0 : ℝ), ladderKernel s x)
        + η * ∫ x in Ioi (0 : ℝ), ladderMoment s x‖ ≤ taylorConstant s.re * ‖η‖ ^ 2 := by
  have hre : 0 < (s + η).re := by
    have := (abs_le.mp ((Complex.abs_re_le_norm η).trans hη)).1
    rw [Complex.add_re]
    linarith
  have hI1 := integrableOn_ladderKernel_Ioi hre
  have hI2 := integrableOn_ladderKernel_Ioi hs
  have hI3 := integrableOn_ladderMoment_Ioi hs
  have hsum : (∫ x in Ioi (0 : ℝ), ladderKernel (s + η) x) - (∫ x in Ioi (0 : ℝ), ladderKernel s x)
        + η * ∫ x in Ioi (0 : ℝ), ladderMoment s x
      = ∫ x in Ioi (0 : ℝ),
          ladderKernel s x * (Complex.exp (-η * (x : ℂ)) - 1 - (-η * (x : ℂ))) := by
    have e1 : (∫ x in Ioi (0 : ℝ), ladderKernel (s + η) x)
          - (∫ x in Ioi (0 : ℝ), ladderKernel s x)
        = ∫ x in Ioi (0 : ℝ), (ladderKernel (s + η) x - ladderKernel s x) :=
      (integral_sub hI1 hI2).symm
    have e2 : η * ∫ x in Ioi (0 : ℝ), ladderMoment s x
        = ∫ x in Ioi (0 : ℝ), η * ladderMoment s x := (integral_const_mul _ _).symm
    have e3 : (∫ x in Ioi (0 : ℝ), (ladderKernel (s + η) x - ladderKernel s x))
          + (∫ x in Ioi (0 : ℝ), η * ladderMoment s x)
        = ∫ x in Ioi (0 : ℝ),
            ((ladderKernel (s + η) x - ladderKernel s x) + η * ladderMoment s x) :=
      (integral_add (hI1.sub hI2) (hI3.const_mul η)).symm
    rw [e1, e2, e3]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ladderKernel_add, ladderMoment]
    ring
  have hmaj : IntegrableOn (fun x : ℝ => 32 / s.re ^ 2 * Real.exp (-(s.re / 4) * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by positivity : 0 < s.re / 4)).const_mul _
  have hbound : ∀ x ∈ Ioi (0 : ℝ),
      ‖ladderKernel s x * (Complex.exp (-η * (x : ℂ)) - 1 - (-η * (x : ℂ)))‖
        ≤ ‖η‖ ^ 2 * (32 / s.re ^ 2 * Real.exp (-(s.re / 4) * x)) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hw : ‖(-η * (x : ℂ))‖ = ‖η‖ * x := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hx0]
    have hT := Complex.norm_exp_sub_sum_le_norm_mul_exp (-η * (x : ℂ)) 2
    have hsumT : ∑ m ∈ Finset.range 2, (-η * (x : ℂ)) ^ m / (m.factorial : ℂ)
        = 1 + (-η * (x : ℂ)) := by
      simp [Finset.sum_range_succ]
    rw [hsumT, ← sub_sub, hw] at hT
    have hexp : Real.exp (‖η‖ * x) ≤ Real.exp (s.re / 2 * x) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hη hx0)
    have hq := Real.quadratic_le_exp_of_nonneg (x := s.re / 4 * x) (by positivity)
    have hx2 : x ^ 2 ≤ 32 / s.re ^ 2 * Real.exp (s.re / 4 * x) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hs.le hx0]
    rw [norm_mul]
    calc ‖ladderKernel s x‖ * ‖Complex.exp (-η * (x : ℂ)) - 1 - (-η * (x : ℂ))‖
        ≤ Real.exp (-(s.re * x)) * ((‖η‖ * x) ^ 2 * Real.exp (s.re / 2 * x)) :=
          mul_le_mul (norm_ladderKernel_le s x)
            (hT.trans (mul_le_mul_of_nonneg_left hexp (by positivity)))
            (norm_nonneg _) (Real.exp_pos _).le
      _ = ‖η‖ ^ 2 * (x ^ 2 * Real.exp (-(s.re / 2 * x))) := by
          have h : Real.exp (-(s.re * x)) * Real.exp (s.re / 2 * x)
              = Real.exp (-(s.re / 2 * x)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc Real.exp (-(s.re * x)) * ((‖η‖ * x) ^ 2 * Real.exp (s.re / 2 * x))
              = ‖η‖ ^ 2 * x ^ 2 * (Real.exp (-(s.re * x)) * Real.exp (s.re / 2 * x)) := by ring
            _ = ‖η‖ ^ 2 * (x ^ 2 * Real.exp (-(s.re / 2 * x))) := by rw [h]; ring
      _ ≤ ‖η‖ ^ 2 * (32 / s.re ^ 2 * Real.exp (-(s.re / 4) * x)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hprod : Real.exp (s.re / 4 * x) * Real.exp (-(s.re / 2 * x))
              = Real.exp (-(s.re / 4) * x) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc x ^ 2 * Real.exp (-(s.re / 2 * x))
              ≤ 32 / s.re ^ 2 * Real.exp (s.re / 4 * x) * Real.exp (-(s.re / 2 * x)) :=
                mul_le_mul_of_nonneg_right hx2 (Real.exp_pos _).le
            _ = 32 / s.re ^ 2 * Real.exp (-(s.re / 4) * x) := by rw [mul_assoc, hprod]
  rw [hsum]
  refine (norm_integral_le_of_norm_le (hmaj.const_mul (‖η‖ ^ 2))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))).trans ?_
  rw [integral_const_mul, taylorConstant, mul_comm]

/-! ### Ladders of zeros near a progression -/

/-- Products of square summable nonnegative sequences are summable. -/
theorem summable_mul_of_sq {ι : Type*} {a b : ι → ℝ} (ha : Summable fun i => a i ^ 2)
    (hb : Summable fun i => b i ^ 2) (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i) :
    Summable fun i => a i * b i :=
  Summable.of_nonneg_of_le (fun i => mul_nonneg (ha0 i) (hb0 i))
    (fun i => by nlinarith [sq_nonneg (a i - b i), mul_nonneg (ha0 i) (hb0 i)]) (ha.add hb)

/-- **A zero near `s` bounds `ζ(s)/s`.** If `ζ(s + η) = 0` with `η` small, the Laplace
representations at `s` and `s + η` and the Taylor bound give `ζ(s)/s` as `η` times bounded
quantities, up to `M ‖η‖²`. -/
theorem norm_riemannZeta_div_le_of_zero_near {s η : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hη : ‖η‖ ≤ min s.re (1 - s.re) / 4) (hzero : riemannZeta (s + η) = 0) :
    ‖riemannZeta s / s‖ ≤ taylorConstant s.re * ‖η‖ ^ 2
      + ‖η‖ * ‖∫ x in Ioi (0 : ℝ), ladderMoment s x‖
      + 2 / (1 - s.re) * (‖η‖ * (‖∫ x in Ioi (0 : ℝ), ladderKernel s x‖ + ‖riemannZeta s / s‖)) := by
  have hδσ : ‖η‖ ≤ s.re / 4 := hη.trans (by have := min_le_left s.re (1 - s.re); linarith)
  have hδ1 : ‖η‖ ≤ (1 - s.re) / 4 :=
    hη.trans (by have := min_le_right s.re (1 - s.re); linarith)
  have hC0 : 0 ≤ 2 / (1 - s.re) := div_nonneg (by norm_num) (by linarith)
  have habs := abs_le.mp (Complex.abs_re_le_norm η)
  have hre' : (s + η).re = s.re + η.re := Complex.add_re _ _
  have hs'0 : 0 < (s + η).re := by rw [hre']; linarith [norm_nonneg η]
  have hs'1 : (s + η).re < 1 := by rw [hre']; linarith
  have hs'ne : s + η ≠ 1 := fun h => by rw [h, Complex.one_re] at hs'1; exact lt_irrefl _ hs'1
  have hsne : s ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl _ h1
  have hI1 : (∫ x in Ioi (0 : ℝ), ladderKernel (s + η) x) = 1 / (s + η - 1) := by
    rw [integral_ladderKernel hs'0 hs'ne, hzero, zero_div, sub_zero]
  have hI2 := integral_ladderKernel h0 hsne
  have hT := norm_integral_ladderKernel_taylor_le (s := s) (η := η) h0 (by linarith)
  rw [hI1] at hT
  -- the polar terms
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
  have hsub' : s + η - 1 ≠ 0 := sub_ne_zero.mpr hs'ne
  have hpol : 1 / (s + η - 1) - 1 / (s - 1) = -η * (1 / (s + η - 1)) * (1 / (s - 1)) := by
    field_simp
    ring
  have hlow : (1 - s.re) / 2 ≤ ‖s + η - 1‖ := by
    have h := Complex.abs_re_le_norm (s + η - 1)
    have hre1 : (s + η - 1).re = s.re + η.re - 1 := by
      rw [Complex.sub_re, hre', Complex.one_re]
    rw [hre1] at h
    have := neg_abs_le (s.re + η.re - 1)
    linarith
  have hinv' : ‖1 / (s + η - 1)‖ ≤ 2 / (1 - s.re) := by
    have hC' : 2 / (1 - s.re) = 1 / ((1 - s.re) / 2) := by rw [one_div_div]
    rw [norm_div, norm_one, hC']
    exact one_div_le_one_div_of_le (by linarith) hlow
  have hinv : ‖1 / (s - 1)‖
      ≤ ‖∫ x in Ioi (0 : ℝ), ladderKernel s x‖ + ‖riemannZeta s / s‖ := by
    have h : 1 / (s - 1) = (∫ x in Ioi (0 : ℝ), ladderKernel s x) + riemannZeta s / s := by
      rw [hI2]
      ring
    rw [h]
    exact norm_add_le _ _
  have hpolnorm : ‖1 / (s + η - 1) - 1 / (s - 1)‖ ≤ 2 / (1 - s.re)
      * (‖η‖ * (‖∫ x in Ioi (0 : ℝ), ladderKernel s x‖ + ‖riemannZeta s / s‖)) := by
    rw [hpol, norm_mul, norm_mul, norm_neg]
    calc ‖η‖ * ‖1 / (s + η - 1)‖ * ‖1 / (s - 1)‖
        ≤ ‖η‖ * (2 / (1 - s.re))
            * (‖∫ x in Ioi (0 : ℝ), ladderKernel s x‖ + ‖riemannZeta s / s‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hinv' (norm_nonneg _)) hinv (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) hC0)
      _ = _ := by ring
  -- assemble
  have hid : riemannZeta s / s
      = (1 / (s + η - 1) - (∫ x in Ioi (0 : ℝ), ladderKernel s x)
          + η * ∫ x in Ioi (0 : ℝ), ladderMoment s x)
        - η * (∫ x in Ioi (0 : ℝ), ladderMoment s x)
        - (1 / (s + η - 1) - 1 / (s - 1)) := by
    rw [hI2]
    ring
  have h1' := norm_sub_le
    ((1 / (s + η - 1) - (∫ x in Ioi (0 : ℝ), ladderKernel s x)
        + η * ∫ x in Ioi (0 : ℝ), ladderMoment s x)
      - η * (∫ x in Ioi (0 : ℝ), ladderMoment s x))
    (1 / (s + η - 1) - 1 / (s - 1))
  have h2' := norm_sub_le
    (1 / (s + η - 1) - (∫ x in Ioi (0 : ℝ), ladderKernel s x)
        + η * ∫ x in Ioi (0 : ℝ), ladderMoment s x)
    (η * (∫ x in Ioi (0 : ℝ), ladderMoment s x))
  have h3' : ‖η * (∫ x in Ioi (0 : ℝ), ladderMoment s x)‖
      = ‖η‖ * ‖∫ x in Ioi (0 : ℝ), ladderMoment s x‖ := norm_mul _ _
  have hzn := congrArg norm hid
  linarith

/-- **A ladder of zeros near a progression makes the zeta values on it summable.** The ladder may
be indexed by any set of integers: the whole progression, or half of it. -/
theorem summable_norm_riemannZeta_div_of_ladder {ι : Type*} {k : ι → ℤ}
    (hk : Function.Injective k) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {P : ℝ} (hP : 0 < P)
    {η : ι → ℂ} (hη : Summable fun i => ‖η i‖ ^ 2)
    (hzero : ∀ᶠ i in cofinite,
      riemannZeta (ρ + ((2 * π * (k i) / P : ℝ) : ℂ) * I + η i) = 0) :
    Summable fun i => ‖riemannZeta (ρ + ((2 * π * (k i) / P : ℝ) : ℂ) * I)
      / (ρ + ((2 * π * (k i) / P : ℝ) : ℂ) * I)‖ := by
  set σ : ℝ := ρ.re with hσ
  set s : ι → ℂ := fun i => ρ + ((2 * π * (k i) / P : ℝ) : ℂ) * I with hs
  have hsre : ∀ i, (s i).re = σ := fun i => by simp [hs, hσ]
  set δ : ℝ := min σ (1 - σ) / 4 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < min σ (1 - σ) := lt_min h0 (by linarith)
    positivity
  -- the three square summable sequences
  set a : ι → ℝ := fun i => ‖∫ x in Ioi (0 : ℝ), ladderKernel (s i) x‖ with ha
  set b : ι → ℝ := fun i => ‖∫ x in Ioi (0 : ℝ), ladderMoment (s i) x‖ with hb
  set z : ι → ℝ := fun i => ‖riemannZeta (s i) / s i‖ with hz
  have ha2 : Summable fun i => a i ^ 2 :=
    (summable_sq_norm_integral_ladderKernel h0 hP).comp_injective hk
  have hb2 : Summable fun i => b i ^ 2 :=
    (summable_sq_norm_integral_ladderMoment h0 hP).comp_injective hk
  have hz2 : Summable fun i => z i ^ 2 :=
    (summable_sq_norm_riemannZeta_div h0 h1 hP).comp_injective hk
  set M : ℝ := taylorConstant σ with hM
  set C : ℝ := 2 / (1 - σ) with hC
  have hmajor : Summable fun i =>
      M * ‖η i‖ ^ 2 + ‖η i‖ * b i + C * (‖η i‖ * a i + ‖η i‖ * z i) :=
    ((hη.mul_left M).add
      (summable_mul_of_sq hη hb2 (fun _ => norm_nonneg _) fun _ => norm_nonneg _)).add
        (((summable_mul_of_sq hη ha2 (fun _ => norm_nonneg _) fun _ => norm_nonneg _).add
          (summable_mul_of_sq hη hz2 (fun _ => norm_nonneg _) fun _ => norm_nonneg _)).mul_left C)
  -- the perturbations are eventually small
  have hsmall : ∀ᶠ i in cofinite, ‖η i‖ ≤ δ := by
    have h := hη.tendsto_cofinite_zero
    filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ) < δ ^ 2 by positivity))] with i hi
    exact (lt_of_pow_lt_pow_left₀ 2 hδ0.le hi).le
  refine Summable.of_norm_bounded_eventually hmajor ?_
  filter_upwards [hzero, hsmall] with i hi hηi
  rw [norm_norm]
  have h := norm_riemannZeta_div_le_of_zero_near (s := s i) (η := η i)
    (by rw [hsre]; exact h0) (by rw [hsre]; exact h1) (by rw [hsre]; exact hηi) hi
  rw [hsre] at h
  exact h.trans (le_of_eq (by ring))

/-- **No ladder of zeros near a vertical progression.** For `ρ` in the open strip, a step `T > 0`
and a square summable perturbation `η`, the points `ρ + inT + η_n` are not zeros of `ζ` for all
but finitely many `n ∈ ℤ`. -/
theorem not_cofinite_riemannZeta_eq_zero_of_sq_summable {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {T : ℝ} (hT : 0 < T) {η : ℤ → ℂ} (hη : Summable fun n => ‖η n‖ ^ 2) :
    ¬ ∀ᶠ n : ℤ in cofinite, riemannZeta (ρ + ((n * T : ℝ) : ℂ) * I + η n) = 0 := by
  intro hzero
  have hP : 0 < 2 * π / T := by positivity
  have hfreq : ∀ n : ℤ, (2 * π * n / (2 * π / T) : ℝ) = n * T := by
    intro n
    field_simp
  have h := summable_norm_riemannZeta_div_of_ladder (k := id) Function.injective_id h0 h1 hP hη
    (by simpa only [hfreq, id] using hzero)
  simp only [hfreq, id] at h
  exact not_summable_norm_riemannZeta_div h0 h1 hT h

/-- **No sequence of zeros approaches a class of one Frobenius.** For a Frobenius `q > 1` and `ρ`
in the open strip, no two-sided sequence of zeros of `ξ` is within a square summable distance of
the class `ρ + 2πin/log q`. -/
theorem not_cofinite_xi_eq_zero_near_class {q : ℝ} (hq : 1 < q) {ρ : ℂ} (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) {w : ℤ → ℂ}
    (hw : Summable fun n : ℤ => ‖w n - (ρ + ((n * (2 * π / Real.log q) : ℝ) : ℂ) * I)‖ ^ 2) :
    ¬ ∀ᶠ n in cofinite, xi (w n) = 0 := by
  intro hzero
  have hT : 0 < 2 * π / Real.log q := div_pos (by positivity) (Real.log_pos hq)
  refine not_cofinite_riemannZeta_eq_zero_of_sq_summable h0 h1 hT hw ?_
  filter_upwards [hzero] with n hn
  have hpt : ρ + ((n * (2 * π / Real.log q) : ℝ) : ℂ) * I
      + (w n - (ρ + ((n * (2 * π / Real.log q) : ℝ) : ℂ) * I)) = w n := by ring
  rw [hpt]
  exact (xi_eq_zero_iff (re_pos_of_xi_eq_zero hn) fun h => by
    have := re_lt_one_of_xi_eq_zero hn
    rw [h, Complex.one_re] at this
    exact lt_irrefl _ this).mp hn

end GaloisForLFunctions.InfiniteRankPurityTheory
