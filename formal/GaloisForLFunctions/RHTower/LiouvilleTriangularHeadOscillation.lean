import GaloisForLFunctions.RHTower.LiouvilleTriangularPoleSeparation
import GaloisForLFunctions.RHTower.LiouvilleTriangularShortHead
import GaloisForLFunctions.RHTower.LiouvilleSummatoryPolyaBoundary

/-!
# Every uncancelled short triangular head oscillates beyond the three-quarter scale

Write `P(x) = Σ_{n ≤ x} λ(n)(x/n - 1)` and, with `W(y) = Σ_{k ≤ √y} (y/k² - 1)`,
`A(x) = Σ_{m ≤ √x} μ(m) W(x/m)`. The square-lattice remainder `W(y) = Zy - 2√y + O(1)`,
`Z = Σ 1/k²`, splits `A = Z x H₁(√x) - 2√x H₂(√x) + E`, where `H₁, H₂` are the Möbius prefixes
weighted by `1/m` and `1/√m` and `|E(x)| ≤ √x`. In the logarithmic variable the transforms are,
on `Re s > 2`,

`∫ P(e^u) e^{-su} du = ζ(2s)/(s(s-1)ζ(s))`,
`∫ A(e^u) e^{-su} du = Z/((s-1)ζ(2s-1)) - 2/((s-½)ζ(2s-½)) + R(s)`,

with `R` holomorphic on `Re s > ½`. The lower endpoint `m²` of each head integral moves the
zeros of `ζ` to the half-shifted points `(ρ+1)/2`.

Suppose `η(P + cA)(x) ≤ C x^β` for large `x`, `η = ±1`, `c ≠ 0`, `5/8 ≤ β < 3/4`. The clipped
density `(C+1)e^{βu} - η(P + cA)(e^u) + K` is nonnegative, its transform continues analytically to
every real point right of `β`, and Landau's theorem puts its abscissa at `β`. Multiplying the
continuation identity by `D(z) = zU(z)(z-½)U(2z-½)U(2z-1)`, `U(w) = (w-1)ζ(w)`, gives an identity
of holomorphic functions on `Re z > β`. At a zero `w` of `U(2z-1)` with `Re w ≥ ¾` where `U(w)`
and `U(2w-½)` do not vanish (it exists unconditionally, starting from a critical zero), the left
side vanishes and the right side equals `η · 2cZ · w U(w)(w-½)U(2w-½) ≠ 0`.

Hence `P + cA` exceeds `C x^β` and falls below `-C x^β` for arbitrarily large `x`, for every
`c ≠ 0` and `β < 3/4`. In particular the Möbius head cannot be paid separately from the
quadratic remainder `P - 2A` at any exponent below three quarters.
-/

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.RHTower

namespace RHTower.LiouvilleTriangularHeadOscillation

noncomputable section

/-! ## Laplace transforms of partial sums -/

/-- For coefficients of modulus at most one, `∫_0^∞ (Σ_{k ≤ e^u} f k) e^{-su} du = L(f,s)/s`
on `Re s > 1`. -/
theorem integral_partialSum_exp_mul_cexp (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, f k) * Complex.exp (-s * u)
      = LSeries f s / s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖f k‖)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    have hle : ∑ k ∈ Finset.Icc 1 n, ‖f k‖ ≤ (n : ℝ) := by
      refine le_trans (Finset.sum_le_sum fun k _ => hf k) ?_
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      simp
    have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, ‖f k‖ :=
      Finset.sum_nonneg fun k _ => norm_nonneg _
    rw [Real.rpow_one, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hnn, abs_of_nonneg (Nat.cast_nonneg n)]
    exact hle
  have hM := LSeries_eq_mul_integral' f (r := 1) zero_le_one hs hO
  rw [← image_exp_Ioi_zero, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn] at hM
  have hcongr : ∫ u in Ioi (0 : ℝ), |Real.exp u| • ((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊,
        f k) * ((Real.exp u : ℝ) : ℂ) ^ (-(s + 1)))
      = ∫ u in Ioi (0 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, f k) * Complex.exp (-s * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hcpow : ((Real.exp u : ℝ) : ℂ) ^ (-(s + 1)) = Complex.exp (u * (-(s + 1))) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
        ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    rw [abs_of_pos (Real.exp_pos u), hcpow, Complex.real_smul, Complex.ofReal_exp]
    rw [mul_comm (Complex.exp (u : ℂ)), mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hcongr] at hM
  rw [hM, mul_div_cancel_left₀ _ hs0]

/-- Dividing the coefficients by `n^a` shifts the L-series by `a`. -/
theorem LSeries_mul_cpow_neg (f : ℕ → ℂ) (a w : ℂ) :
    LSeries (fun n => f n * (n : ℂ) ^ (-a)) w = LSeries f (w + a) := by
  unfold LSeries
  congr 1
  funext n
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with hn
  · rfl
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have h1 : (n : ℂ) ^ a ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    have h2 : (n : ℂ) ^ w ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    rw [Complex.cpow_add _ _ hn', Complex.cpow_neg]
    field_simp

/-- `L(μ, w) ζ(w) = 1` on `Re w > 1`. -/
theorem LSeries_moebius_mul_riemannZeta_eq_one {w : ℂ} (hw : 1 < w.re) :
    LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) w * riemannZeta w = 1 := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hw, mul_comm]
  exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hw

/-- A function bounded by `C e^{au}` on `u > 0` has an absolutely convergent transform on
`Re s > a`. -/
theorem integrableOn_mul_cexp_of_le {g : ℝ → ℝ} (hg : Measurable g) {C a : ℝ}
    (hb : ∀ u, 0 < u → |g u| ≤ C * Real.exp (a * u)) {s : ℂ} (hs : a < s.re) :
    IntegrableOn (fun u : ℝ => (g u : ℂ) * Complex.exp (-s * u)) (Ioi 0) := by
  have hmaj : IntegrableOn (fun u : ℝ => C * Real.exp (-(s.re - a) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul C
  refine hmaj.mono' ?_ ?_
  · exact (Complex.continuous_ofReal.measurable.comp hg).aestronglyMeasurable.mul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |g u| * Real.exp (-s.re * u) ≤ C * Real.exp (a * u) * Real.exp (-s.re * u) :=
          mul_le_mul_of_nonneg_right (hb u hu) (Real.exp_pos _).le
      _ = C * Real.exp (-(s.re - a) * u) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-! ## The Liouville triangle `P(x) = Σ_{n ≤ x} λ(n)(x/n - 1)` -/

/-- `P(x) = Σ_{n ≤ x} λ(n)(x/n - 1)`. -/
def liouvilleTriangle (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.liouville n : ℤ) : ℝ) * (x / n - 1)

/-- `T(x) = Σ_{n ≤ x} λ(n)/n`. -/
def liouvilleHarmonic (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.liouville n : ℤ) : ℝ) / n

theorem liouvilleTriangle_eq (x : ℝ) :
    liouvilleTriangle x = x * liouvilleHarmonic x - liouvilleSummatory x := by
  unfold liouvilleTriangle liouvilleHarmonic liouvilleSummatory
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem measurable_liouvilleHarmonic : Measurable liouvilleHarmonic := by
  have : liouvilleHarmonic = (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.liouville n : ℤ) : ℝ) / n) ∘ Nat.floor := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

theorem measurable_liouvilleTriangle : Measurable liouvilleTriangle := by
  have h : liouvilleTriangle = fun x => x * liouvilleHarmonic x - liouvilleSummatory x :=
    funext liouvilleTriangle_eq
  rw [h]
  exact (measurable_id.mul measurable_liouvilleHarmonic).sub measurable_liouvilleSummatory

theorem abs_liouvilleHarmonic_le (x : ℝ) : |liouvilleHarmonic x| ≤ ⌊x⌋₊ := by
  unfold liouvilleHarmonic
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, |((ArithmeticFunction.liouville n : ℤ) : ℝ) / n|
      ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < n)]
        exact (div_le_one (by linarith)).mpr ((abs_liouville_le_one n).trans hn1)
    _ = ⌊x⌋₊ := by simp

theorem abs_liouvilleTriangle_exp_le {u : ℝ} (hu : 0 ≤ u) :
    |liouvilleTriangle (Real.exp u)| ≤ 2 * Real.exp (2 * u) := by
  rw [liouvilleTriangle_eq]
  have hE := Real.exp_pos u
  have h1 := (abs_liouvilleHarmonic_le (Real.exp u)).trans (Nat.floor_le hE.le)
  have h2 := abs_liouvilleSummatory_exp_le u
  have h3 : Real.exp u ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have h4 : Real.exp (2 * u) = Real.exp u * Real.exp u := by rw [← Real.exp_add]; ring_nf
  calc |Real.exp u * liouvilleHarmonic (Real.exp u) - liouvilleSummatory (Real.exp u)|
      ≤ |Real.exp u * liouvilleHarmonic (Real.exp u)| + |liouvilleSummatory (Real.exp u)| :=
        abs_sub _ _
    _ = Real.exp u * |liouvilleHarmonic (Real.exp u)| + |liouvilleSummatory (Real.exp u)| := by
        rw [abs_mul, abs_of_pos hE]
    _ ≤ Real.exp u * Real.exp u + Real.exp u := by gcongr
    _ ≤ 2 * Real.exp (2 * u) := by rw [h4] at h3 ⊢; linarith

/-- `∫_0^∞ e^u T(e^u) e^{-su} du = L(λ, s)/(s - 1)` on `Re s > 2`. -/
theorem integral_exp_mul_liouvilleHarmonic {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((Real.exp u * liouvilleHarmonic (Real.exp u) : ℝ) : ℂ)
        * Complex.exp (-s * u)
      = LSeries (fun n => liouvilleC n) s / (s - 1) := by
  have hs1 : 1 < (s - 1).re := by simp; linarith
  have hb : ∀ n, ‖liouvilleC n * (n : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 := by
    intro n
    rw [norm_mul, Complex.cpow_neg_one, norm_inv]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hn1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
        rw [Complex.norm_natCast]; exact_mod_cast hn
      calc ‖liouvilleC n‖ * ‖(n : ℂ)‖⁻¹ ≤ 1 * 1 :=
            mul_le_mul (norm_liouvilleC_le_one n) (inv_le_one_of_one_le₀ hn1)
              (by positivity) zero_le_one
        _ = 1 := by ring
  have key := integral_partialSum_exp_mul_cexp
    (fun n => liouvilleC n * (n : ℂ) ^ (-(1 : ℂ))) hb hs1
  rw [LSeries_mul_cpow_neg, show s - 1 + 1 = s by ring] at key
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  have hexp : Complex.exp (-(s - 1) * u) = Complex.exp u * Complex.exp (-s * u) := by
    rw [← Complex.exp_add]; ring_nf
  rw [hexp]
  unfold liouvilleHarmonic
  push_cast
  simp only [liouvilleC_apply, Complex.cpow_neg_one, div_eq_mul_inv]
  ring

/-- **Transform of the Liouville triangle.** `∫_0^∞ P(e^u) e^{-su} du = ζ(2s)/(s(s-1)ζ(s))`
on `Re s > 2`. -/
theorem integral_liouvilleTriangle_exp_mul_cexp {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), (liouvilleTriangle (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = riemannZeta (2 * s) / (s * (s - 1) * riemannZeta s) := by
  have hs1 : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have hs1' : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have i1 : IntegrableOn (fun u : ℝ => ((Real.exp u * liouvilleHarmonic (Real.exp u) : ℝ) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) := by
    refine integrableOn_mul_cexp_of_le (g := fun u => Real.exp u * liouvilleHarmonic (Real.exp u))
      (C := 1) (a := 2)
      (Real.measurable_exp.mul (measurable_liouvilleHarmonic.comp Real.measurable_exp))
      (fun u hu => ?_) hs
    have hE := Real.exp_pos u
    have h1 := (abs_liouvilleHarmonic_le (Real.exp u)).trans (Nat.floor_le hE.le)
    rw [abs_mul, abs_of_pos hE, one_mul, show Real.exp (2 * u) = Real.exp u * Real.exp u by
      rw [← Real.exp_add]; ring_nf]
    exact mul_le_mul_of_nonneg_left h1 hE.le
  have i2 : IntegrableOn (fun u : ℝ => (liouvilleSummatory (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := 1) (a := 1)
      (measurable_liouvilleSummatory.comp Real.measurable_exp)
      (fun u _ => by simpa using abs_liouvilleSummatory_exp_le u) hs1
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (liouvilleTriangle (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = ((Real.exp u * liouvilleHarmonic (Real.exp u) : ℝ) : ℂ) * Complex.exp (-s * u)
        - (liouvilleSummatory (Real.exp u) : ℂ) * Complex.exp (-s * u) := by
    intro u _
    rw [liouvilleTriangle_eq]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub i1 i2,
    integral_exp_mul_liouvilleHarmonic hs, integral_liouvilleSummatory_exp_mul_cexp hs1,
    LSeries_liouvilleC_eq_div hs1]
  field_simp
  ring

/-! ## A one-sided Landau engine -/

/-- The clipped density `ε e^{βu} - η f(u) + K`. -/
def expOneSidedDensity (f : ℝ → ℝ) (η ε β K : ℝ) (u : ℝ) : NNReal :=
  Real.toNNReal (ε * Real.exp (β * u) - η * f u + K)

theorem measurable_oneSidedDensity {f : ℝ → ℝ} (hf : Measurable f) (η ε β K : ℝ) :
    Measurable (expOneSidedDensity f η ε β K) := by
  unfold expOneSidedDensity
  refine Measurable.real_toNNReal ?_
  exact ((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))).sub
    (measurable_const.mul hf)).add measurable_const

/-- `ν = (ε e^{βu} - η f(u) + K) du` on `(0, ∞)`. -/
def expOneSidedMeasure (f : ℝ → ℝ) (η ε β K : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun u => (expOneSidedDensity f η ε β K u : ENNReal))

theorem oneSidedDensity_coe {f : ℝ → ℝ} {η ε ε' β K : ℝ} (hεε' : ε' ≤ ε)
    (hg : ∀ u, 0 < u → η * f u ≤ ε' * Real.exp (β * u) + K) {u : ℝ} (hu : 0 < u) :
    ((expOneSidedDensity f η ε β K u : ℝ)) = ε * Real.exp (β * u) - η * f u + K := by
  unfold expOneSidedDensity
  have h := hg u hu
  have hE := Real.exp_pos (β * u)
  rw [Real.coe_toNNReal _ (by nlinarith)]

theorem oneSidedDensity_le {f : ℝ → ℝ} {η ε β K B γ : ℝ} (hη : |η| = 1) (hε : 0 ≤ ε)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hβγ : β ≤ γ) (hγ : 0 ≤ γ)
    (hb : ∀ u, 0 < u → |f u| ≤ B * Real.exp (γ * u)) {u : ℝ} (hu : 0 < u) :
    ((expOneSidedDensity f η ε β K u : ℝ)) ≤ (ε + B + K) * Real.exp (γ * u) := by
  unfold expOneSidedDensity
  rw [Real.coe_toNNReal']
  have h1 : Real.exp (β * u) ≤ Real.exp (γ * u) := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : -(η * f u) ≤ B * Real.exp (γ * u) := by
    have h3 : |η * f u| ≤ B * Real.exp (γ * u) := by rw [abs_mul, hη, one_mul]; exact hb u hu
    linarith [neg_abs_le (η * f u)]
  have h4 : 1 ≤ Real.exp (γ * u) := Real.one_le_exp (by positivity)
  refine max_le ?_ (by positivity)
  nlinarith

theorem laplaceMass_oneSidedMeasure_ne_top {f : ℝ → ℝ} (hf : Measurable f)
    {η ε β K B γ σ : ℝ} (hη : |η| = 1) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hB : 0 ≤ B) (hβγ : β ≤ γ)
    (hγ : 0 ≤ γ) (hb : ∀ u, 0 < u → |f u| ≤ B * Real.exp (γ * u)) (hσ : γ < σ) :
    laplaceMass (expOneSidedMeasure f η ε β K) σ ≠ ⊤ := by
  unfold laplaceMass expOneSidedMeasure
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_oneSidedDensity hf η ε β K).coe_nnreal_ennreal hg]
  have hmaj : IntegrableOn (fun u : ℝ => (ε + B + K) * Real.exp (-(σ - γ) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
  refine ne_top_of_le_ne_top hmaj.lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc (expOneSidedDensity f η ε β K u : ℝ) * Real.exp (-σ * u)
      ≤ (ε + B + K) * Real.exp (γ * u) * Real.exp (-σ * u) :=
        mul_le_mul_of_nonneg_right (oneSidedDensity_le hη hε hK hB hβγ hγ hb hu)
          (Real.exp_pos _).le
    _ = (ε + B + K) * Real.exp (-(σ - γ) * u) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

theorem laplaceMass_oneSidedMeasure_eq_top {f : ℝ → ℝ} (hf : Measurable f)
    {η ε ε' β K σ : ℝ} (hεε' : ε' < ε)
    (hg : ∀ u, 0 < u → η * f u ≤ ε' * Real.exp (β * u) + K) (hσ : σ ≤ β) :
    laplaceMass (expOneSidedMeasure f η ε β K) σ = ⊤ := by
  unfold laplaceMass expOneSidedMeasure
  have hg' : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_oneSidedDensity hf η ε β K).coe_nnreal_ennreal hg', eq_top_iff]
  have hδ : 0 < ε - ε' := by linarith
  calc (⊤ : ENNReal) = ENNReal.ofReal (ε - ε') * volume (Ioi (0 : ℝ)) := by
        rw [Real.volume_Ioi, ENNReal.mul_top (by simpa using hδ)]
    _ = ∫⁻ _ in Ioi (0 : ℝ), ENNReal.ofReal (ε - ε') := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), ((fun u => (expOneSidedDensity f η ε β K u : ENNReal))
          * fun u => ENNReal.ofReal (Real.exp (-σ * u))) u := by
        refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [oneSidedDensity_coe hεε'.le hg hu0]
        have h1 := hg u hu0
        have h2 : 1 ≤ Real.exp (β * u) * Real.exp (-σ * u) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        have hE := Real.exp_pos (-σ * u)
        have hE2 := Real.exp_pos (β * u)
        have h3 : (ε - ε') * Real.exp (β * u) ≤ ε * Real.exp (β * u) - η * f u + K := by
          linarith
        calc ε - ε' ≤ (ε - ε') * (Real.exp (β * u) * Real.exp (-σ * u)) :=
              le_mul_of_one_le_right hδ.le h2
          _ = (ε - ε') * Real.exp (β * u) * Real.exp (-σ * u) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h3 hE.le

/-- The abscissa of the one-sided measure lies in `[β, γ]`. -/
theorem isAbscissa_oneSidedMeasure {f : ℝ → ℝ} (hf : Measurable f)
    {η ε ε' β K B γ : ℝ} (hη : |η| = 1) (hε' : 0 ≤ ε') (hεε' : ε' < ε) (hK : 0 ≤ K)
    (hB : 0 ≤ B) (hβγ : β ≤ γ) (hγ : 0 ≤ γ)
    (hb : ∀ u, 0 < u → |f u| ≤ B * Real.exp (γ * u))
    (hg : ∀ u, 0 < u → η * f u ≤ ε' * Real.exp (β * u) + K) :
    IsAbscissa (expOneSidedMeasure f η ε β K)
        (sInf {σ : ℝ | laplaceMass (expOneSidedMeasure f η ε β K) σ ≠ ⊤})
      ∧ β ≤ sInf {σ : ℝ | laplaceMass (expOneSidedMeasure f η ε β K) σ ≠ ⊤}
      ∧ sInf {σ : ℝ | laplaceMass (expOneSidedMeasure f η ε β K) σ ≠ ⊤} ≤ γ := by
  have hε : 0 ≤ ε := by linarith
  set S := {σ : ℝ | laplaceMass (expOneSidedMeasure f η ε β K) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, β < σ := by
    intro σ hσ
    by_contra hle
    exact hσ (laplaceMass_oneSidedMeasure_eq_top hf hεε' hg (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨β, fun σ hσ => (hpos σ hσ).le⟩
  have hmem : ∀ σ, γ < σ → σ ∈ S := fun σ hσ =>
    laplaceMass_oneSidedMeasure_ne_top hf hη hε hK hB hβγ hγ hb hσ
  have hne : S.Nonempty := ⟨γ + 1, hmem _ (by linarith)⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le, ?_⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)
  · exact le_of_forall_pos_le_add fun δ hδ => csInf_le hbdd (hmem _ (by linarith))

/-- On `Re z > γ` the complex transform of the one-sided measure is explicit. -/
theorem complexLaplace_oneSidedMeasure_eq {f : ℝ → ℝ} (hf : Measurable f)
    {η ε ε' β K B γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) (hεε' : ε' ≤ ε)
    (hb : ∀ u, 0 < u → |f u| ≤ B * Real.exp (γ * u))
    (hg : ∀ u, 0 < u → η * f u ≤ ε' * Real.exp (β * u) + K) {z : ℂ} (hz : γ < z.re) :
    complexLaplace (expOneSidedMeasure f η ε β K) z
      = ε / (z - β) + K / z - η * ∫ u in Ioi (0 : ℝ), (f u : ℂ) * Complex.exp (-z * u) := by
  have hz0 : 0 < z.re := by linarith
  have hzβ : 0 < (z - β).re := by simp; linarith
  have hcexp : ∀ w : ℂ, Continuous (fun u : ℝ => Complex.exp (-w * (u : ℂ))) := fun w =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hexpInt : ∀ w : ℂ, 0 < w.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-w * (u : ℂ))) (Ioi 0) := fun w hw =>
    (exp_neg_integrableOn_Ioi 0 hw).mono' (hcexp w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  have hfint := integrableOn_mul_cexp_of_le hf hb hz
  unfold complexLaplace expOneSidedMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul (measurable_oneSidedDensity hf η ε β K)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), expOneSidedDensity f η ε β K u • Complex.exp (-z * (u : ℂ))
      = ((ε : ℂ) * Complex.exp (-(z - β) * (u : ℂ)) + (K : ℂ) * Complex.exp (-z * (u : ℂ)))
        - (η : ℂ) * ((f u : ℂ) * Complex.exp (-z * u)) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul, oneSidedDensity_coe hεε' hg hu]
    push_cast
    rw [show Complex.exp (-(z - β) * (u : ℂ))
      = Complex.exp ((β : ℂ) * (u : ℂ)) * Complex.exp (-z * (u : ℂ)) by
        rw [← Complex.exp_add]; congr 1; ring]
    ring
  have i1 : IntegrableOn (fun u : ℝ => (ε : ℂ) * Complex.exp (-(z - β) * (u : ℂ))) (Ioi 0) :=
    (hexpInt _ hzβ).const_mul _
  have i2 : IntegrableOn (fun u : ℝ => (K : ℂ) * Complex.exp (-z * (u : ℂ))) (Ioi 0) :=
    (hexpInt _ hz0).const_mul _
  have i3 : IntegrableOn (fun u : ℝ => (η : ℂ) * ((f u : ℂ) * Complex.exp (-z * u))) (Ioi 0) :=
    hfint.const_mul _
  have i12 : IntegrableOn (fun u : ℝ => (ε : ℂ) * Complex.exp (-(z - β) * (u : ℂ))
      + (K : ℂ) * Complex.exp (-z * (u : ℂ))) (Ioi 0) := i1.add i2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub i12 i3,
    integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cexp_neg_mul_Ioi hzβ, integral_cexp_neg_mul_Ioi hz0]
  ring

/-- **Landau.** If the transform continues analytically to every real point right of `β`, the
abscissa is `β`. -/
theorem isAbscissa_eq_of_analyticAt_real {ν : Measure ℝ} {c β γ : ℝ} (hc : IsAbscissa ν c)
    (hβc : β ≤ c) (hcγ : c ≤ γ) {Ψ : ℂ → ℂ} (hΨ : ∀ t : ℝ, β < t → AnalyticAt ℂ Ψ t)
    (hagree : ∀ z : ℂ, γ < z.re → complexLaplace ν z = Ψ z) : IsAbscissa ν β := by
  rcases hβc.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp (hΨ c hlt).eventually_analyticAt
    refine false_of_analyticAt_abscissa hc hd (Φ := Ψ) (fun z hz => hball hz) ?_
    intro σ hσc _
    have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hTdiff : DifferentiableOn ℂ (complexLaplace ν) {z : ℂ | c < z.re} :=
      fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
    have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace ν (t : ℂ)) (Ioi c) := by
      intro t ht
      have h1 : AnalyticAt ℂ (complexLaplace ν) (t : ℂ) :=
        hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
      exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
    have hH : AnalyticOnNhd ℝ (fun t : ℝ => Ψ (t : ℂ)) (Ioi c) := by
      intro t ht
      exact (hΨ t (lt_trans hlt ht)).restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
    have hmem : (γ + 1 : ℝ) ∈ Ioi c := by show c < γ + 1; linarith
    have hfg : (fun t : ℝ => complexLaplace ν (t : ℂ)) =ᶠ[𝓝 (γ + 1)]
        (fun t : ℝ => Ψ (t : ℂ)) := by
      refine Filter.eventuallyEq_of_mem (Ioi_mem_nhds (show γ < γ + 1 by linarith))
        fun t ht => ?_
      exact hagree _ (by simpa using ht)
    have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi hmem hfg
    have hσ : complexLaplace ν (σ : ℂ) = Ψ (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
    rw [← hσ, complexLaplace_ofReal]
  · rw [heq]; exact hc

/-- The transform of a measurable function bounded by `e^{u/2}` is holomorphic on `Re z > ½`. -/
theorem differentiableAt_integral_mul_cexp {g : ℝ → ℝ} (hg : Measurable g)
    (hb : ∀ u, 0 < u → |g u| ≤ Real.exp (1 / 2 * u)) {z : ℂ} (hz : 1 / 2 < z.re) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * Complex.exp (-w * u)) z := by
  have hb' : ∀ u, 0 < u → |g u| ≤ 1 * Real.exp (1 / 2 * u) := fun u hu => by
    rw [one_mul]; exact hb u hu
  have hg1 : ∀ u, 0 < u → (-1) * g u ≤ 1 * Real.exp (1 / 2 * u) + 0 := fun u hu => by
    have := neg_abs_le (g u); have := hb u hu; linarith
  have h0 : Measurable (fun _ : ℝ => (0 : ℝ)) := measurable_const
  have hb0 : ∀ u, 0 < u → |(fun _ : ℝ => (0 : ℝ)) u| ≤ 1 * Real.exp (1 / 2 * u) := fun u _ => by
    simp only [abs_zero]; positivity
  have hg0 : ∀ u, 0 < u → 1 * (fun _ : ℝ => (0 : ℝ)) u ≤ 1 * Real.exp (1 / 2 * u) + 0 :=
    fun u _ => by simp only [mul_zero, add_zero, one_mul]; positivity
  obtain ⟨hc1, hlo1, hhi1⟩ := isAbscissa_oneSidedMeasure hg (η := -1) (ε := 2) (ε' := 1)
    (K := 0) (B := 1) (by norm_num) (by norm_num) (by norm_num) le_rfl zero_le_one le_rfl
    (by norm_num) hb' hg1
  obtain ⟨hc2, hlo2, hhi2⟩ := isAbscissa_oneSidedMeasure h0 (η := 1) (ε := 2) (ε' := 1)
    (K := 0) (B := 1) (by norm_num) (by norm_num) (by norm_num) le_rfl zero_le_one le_rfl
    (by norm_num) hb0 hg0
  have e1 := le_antisymm hhi1 hlo1
  have e2 := le_antisymm hhi2 hlo2
  rw [e1] at hc1
  rw [e2] at hc2
  have hV : IsOpen {w : ℂ | 1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * Complex.exp (-w * u)) =ᶠ[𝓝 z]
      fun w => complexLaplace (expOneSidedMeasure g (-1) 2 (1 / 2) 0) w
        - complexLaplace (expOneSidedMeasure (fun _ => 0) 1 2 (1 / 2) 0) w := by
    filter_upwards [hV.mem_nhds hz] with w hw
    have hw' : (1 / 2 : ℝ) < w.re := by simpa using hw
    rw [complexLaplace_oneSidedMeasure_eq hg (by norm_num) le_rfl (by norm_num : (1 : ℝ) ≤ 2)
        hb' hg1 hw',
      complexLaplace_oneSidedMeasure_eq h0 (by norm_num) le_rfl (by norm_num : (1 : ℝ) ≤ 2)
        hb0 hg0 hw']
    simp
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  exact (hasDerivAt_complexLaplace hc1 (by simpa using hz)).differentiableAt.sub
    (hasDerivAt_complexLaplace hc2 (by simpa using hz)).differentiableAt

/-! ## The short triangular Möbius head -/

/-- A finite sum whose length is a measurable natural-number function is measurable. -/
theorem measurable_finsetSum_comp {s : ℕ → Finset ℕ} {F : ℕ → ℝ → ℝ}
    (hF : ∀ n, Measurable (F n)) {N : ℝ → ℕ} (hN : Measurable N) :
    Measurable (fun x => ∑ n ∈ s (N x), F n x) := by
  have hG : Measurable (fun p : ℝ × ℕ => ∑ n ∈ s p.2, F n p.1) :=
    measurable_from_prod_countable_left fun k => by
      dsimp only
      exact Finset.measurable_sum (s k) fun n _ => hF n
  exact hG.comp (measurable_id.prodMk hN)

theorem measurable_squareTriangle : Measurable LiouvilleTriangularShortHead.squareTriangle :=
  measurable_finsetSum_comp (s := Finset.range)
    (F := fun n y => y / ((n : ℝ) + 1) ^ 2 - 1)
    (fun _ => (measurable_id.div_const _).sub measurable_const)
    (Nat.measurable_floor.comp Real.continuous_sqrt.measurable)

theorem abs_moebius_cast_le_one (m : ℕ) : |((ArithmeticFunction.moebius m : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- `A(x) = Σ_{m ≤ √x} μ(m) W(x/m)`, with `W` the triangular transform of the square indicator. -/
def triangularHead (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
    LiouvilleTriangularShortHead.squareTriangle (x / m)

/-- `H₁(y) = Σ_{m ≤ y} μ(m)/m`. -/
def mobiusHarmonic (y : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, ((ArithmeticFunction.moebius m : ℤ) : ℝ) / m

/-- `H₂(y) = Σ_{m ≤ y} μ(m)/√m`. -/
def mobiusRoot (y : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, ((ArithmeticFunction.moebius m : ℤ) : ℝ) / Real.sqrt m

/-- The bounded remainder `E(x) = A(x) - Z x H₁(√x) + 2√x H₂(√x)`. -/
def headRemainder (x : ℝ) : ℝ :=
  triangularHead x - LiouvilleTriangularShortHead.squareMass * x * mobiusHarmonic (Real.sqrt x)
    + 2 * Real.sqrt x * mobiusRoot (Real.sqrt x)

theorem triangularHead_eq (x : ℝ) :
    triangularHead x = LiouvilleTriangularShortHead.squareMass * x * mobiusHarmonic (Real.sqrt x)
      + -2 * Real.sqrt x * mobiusRoot (Real.sqrt x) + headRemainder x := by
  unfold headRemainder; ring

theorem measurable_triangularHead : Measurable triangularHead :=
  measurable_finsetSum_comp (s := Finset.Icc 1)
    (F := fun m x => ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
      LiouvilleTriangularShortHead.squareTriangle (x / m))
    (fun _ => measurable_const.mul (measurable_squareTriangle.comp (measurable_id.div_const _)))
    (Nat.measurable_floor.comp Real.continuous_sqrt.measurable)

theorem measurable_mobiusHarmonic : Measurable mobiusHarmonic := by
  have : mobiusHarmonic = (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius m : ℤ) : ℝ) / m) ∘ Nat.floor := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

theorem measurable_mobiusRoot : Measurable mobiusRoot := by
  have : mobiusRoot = (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius m : ℤ) : ℝ) / Real.sqrt m) ∘ Nat.floor := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

theorem measurable_headRemainder : Measurable headRemainder := by
  unfold headRemainder
  have hs := Real.continuous_sqrt.measurable
  exact (measurable_triangularHead.sub ((measurable_const.mul measurable_id).mul
    (measurable_mobiusHarmonic.comp hs))).add
    ((measurable_const.mul hs).mul (measurable_mobiusRoot.comp hs))

theorem abs_mobiusHarmonic_le (y : ℝ) : |mobiusHarmonic y| ≤ ⌊y⌋₊ := by
  unfold mobiusHarmonic
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, |((ArithmeticFunction.moebius m : ℤ) : ℝ) / m|
      ≤ ∑ _m ∈ Finset.Icc 1 ⌊y⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < m)]
        exact (div_le_one (by linarith)).mpr ((abs_moebius_cast_le_one m).trans hm1)
    _ = ⌊y⌋₊ := by simp

theorem abs_mobiusRoot_le (y : ℝ) : |mobiusRoot y| ≤ ⌊y⌋₊ := by
  unfold mobiusRoot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, |((ArithmeticFunction.moebius m : ℤ) : ℝ) / Real.sqrt m|
      ≤ ∑ _m ∈ Finset.Icc 1 ⌊y⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        have hs1 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm1
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt m)]
        exact (div_le_one (by linarith)).mpr ((abs_moebius_cast_le_one m).trans hs1)
    _ = ⌊y⌋₊ := by simp

/-- `E(x)` is the Möbius sum of the bounded square-lattice remainders. -/
theorem headRemainder_eq (x : ℝ) :
    headRemainder x = ∑ m ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
      ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        (LiouvilleTriangularShortHead.squareTriangle (x / m)
          - LiouvilleTriangularShortHead.squareMass * (x / m) + 2 * Real.sqrt (x / m)) := by
  unfold headRemainder triangularHead mobiusHarmonic mobiusRoot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
  rw [Real.sqrt_div' x (by linarith : (0 : ℝ) ≤ m)]
  field_simp

/-- `|E(x)| ≤ ⌊√x⌋` for `x ≥ 1`. -/
theorem abs_headRemainder_le {x : ℝ} (hx : 1 ≤ x) : |headRemainder x| ≤ ⌊Real.sqrt x⌋₊ := by
  rw [headRemainder_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hsx : Real.sqrt x ≤ x := by nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ x)]
  calc ∑ m ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, |((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        (LiouvilleTriangularShortHead.squareTriangle (x / m)
          - LiouvilleTriangularShortHead.squareMass * (x / m) + 2 * Real.sqrt (x / m))|
      ≤ ∑ _m ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        have hmx : (m : ℝ) ≤ x := by
          have h1 : (m : ℝ) ≤ ⌊Real.sqrt x⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hm).2
          have h2 : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le (by linarith)
          linarith
        have hxm : 1 ≤ x / m := (le_div_iff₀ (by linarith)).mpr (by linarith)
        rw [abs_mul]
        calc |((ArithmeticFunction.moebius m : ℤ) : ℝ)| *
              |LiouvilleTriangularShortHead.squareTriangle (x / m)
                - LiouvilleTriangularShortHead.squareMass * (x / m) + 2 * Real.sqrt (x / m)|
            ≤ 1 * 1 := mul_le_mul (abs_moebius_cast_le_one m)
              (LiouvilleTriangularShortHead.squareTriangle_remainder hxm) (abs_nonneg _)
              zero_le_one
          _ = 1 := one_mul 1
    _ = ⌊Real.sqrt x⌋₊ := by simp

theorem abs_headRemainder_exp_le {u : ℝ} (hu : 0 ≤ u) :
    |headRemainder (Real.exp u)| ≤ Real.exp (1 / 2 * u) := by
  refine (abs_headRemainder_le (Real.one_le_exp hu)).trans ?_
  rw [← sqrt_exp_eq_exp_half_mul]
  exact Nat.floor_le (Real.sqrt_nonneg _)

theorem squareMass_pos : 0 < LiouvilleTriangularShortHead.squareMass := by
  unfold LiouvilleTriangularShortHead.squareMass
  have hs : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)))
  exact hs.tsum_pos (fun n => by positivity) 0 (by norm_num)

/-! ### Transforms of the two head terms -/

theorem integral_comp_half (g : ℝ → ℂ) :
    ∫ u in Ioi (0 : ℝ), g (1 / 2 * u) = 2 * ∫ v in Ioi (0 : ℝ), g v := by
  have h := integral_comp_mul_left_Ioi g 0 (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [mul_zero] at h
  rw [h, show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num, Complex.real_smul]
  push_cast
  ring

theorem mobiusHarmonic_ofReal (y : ℝ) :
    (mobiusHarmonic y : ℂ) = ∑ k ∈ Finset.Icc 1 ⌊y⌋₊,
      ((ArithmeticFunction.moebius k : ℤ) : ℂ) * (k : ℂ) ^ (-(1 : ℂ)) := by
  unfold mobiusHarmonic
  push_cast
  simp only [Complex.cpow_neg_one, div_eq_mul_inv]

theorem ofReal_inv_sqrt_natCast (k : ℕ) :
    (((Real.sqrt k)⁻¹ : ℝ) : ℂ) = (k : ℂ) ^ (-(1 / 2 : ℂ)) := by
  rw [Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_inv,
    Complex.ofReal_cpow (Nat.cast_nonneg k)]
  push_cast
  rfl

theorem mobiusRoot_ofReal (y : ℝ) :
    (mobiusRoot y : ℂ) = ∑ k ∈ Finset.Icc 1 ⌊y⌋₊,
      ((ArithmeticFunction.moebius k : ℤ) : ℂ) * (k : ℂ) ^ (-(1 / 2 : ℂ)) := by
  unfold mobiusRoot
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_eq_mul_inv, ← ofReal_inv_sqrt_natCast]
  push_cast
  ring

theorem norm_moebius_mul_cpow_le {a : ℂ} (ha : 0 ≤ a.re) (ha0 : a ≠ 0) (k : ℕ) :
    ‖((ArithmeticFunction.moebius k : ℤ) : ℂ) * (k : ℂ) ^ (-a)‖ ≤ 1 := by
  rw [norm_mul]
  have hμ : ‖((ArithmeticFunction.moebius k : ℤ) : ℂ)‖ ≤ 1 := by
    rw [show ((ArithmeticFunction.moebius k : ℤ) : ℂ)
      = (((ArithmeticFunction.moebius k : ℤ) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_moebius_cast_le_one k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr ha0), norm_zero, mul_zero]
    exact zero_le_one
  · have h1 : ‖(k : ℂ) ^ (-a)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hk]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk)
        (by simp; linarith)
    calc ‖((ArithmeticFunction.moebius k : ℤ) : ℂ)‖ * ‖(k : ℂ) ^ (-a)‖ ≤ 1 * 1 :=
          mul_le_mul hμ h1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- `∫_0^∞ Z e^u H₁(e^{u/2}) e^{-su} du = Z/((s-1)ζ(2s-1))` on `Re s > 2`. -/
theorem integral_harmonicHead {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.sqrt (Real.exp u)) : ℝ) : ℂ) * Complex.exp (-s * u)
      = LiouvilleTriangularShortHead.squareMass / ((s - 1) * riemannZeta (2 * s - 1)) := by
  set Z := LiouvilleTriangularShortHead.squareMass with hZ
  set g : ℝ → ℂ := fun v => ((Z * Real.exp (2 * v) * mobiusHarmonic (Real.exp v) : ℝ) : ℂ)
    * Complex.exp (-(2 * s) * v) with hg
  have hpt : ∀ u : ℝ, ((Z * Real.exp u * mobiusHarmonic (Real.sqrt (Real.exp u)) : ℝ) : ℂ)
      * Complex.exp (-s * u) = g (1 / 2 * u) := by
    intro u
    simp only [hg]
    rw [sqrt_exp_eq_exp_half_mul, show 2 * (1 / 2 * u) = u by ring]
    congr 2
    push_cast
    ring
  have h2 : 1 < (2 * s - 2).re := by simp; linarith
  have h3 : 1 < (2 * s - 1).re := by simp; linarith
  have hs1 : s - 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hz : riemannZeta (2 * s - 1) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h3
  have hL := LSeries_moebius_mul_riemannZeta_eq_one h3
  have key := integral_partialSum_exp_mul_cexp
    (fun k => ((ArithmeticFunction.moebius k : ℤ) : ℂ) * (k : ℂ) ^ (-(1 : ℂ)))
    (norm_moebius_mul_cpow_le (by simp) one_ne_zero) h2
  rw [LSeries_mul_cpow_neg, show 2 * s - 2 + 1 = 2 * s - 1 by ring] at key
  have hg' : ∫ v in Ioi (0 : ℝ), g v = (Z : ℂ) * ∫ v in Ioi (0 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℂ)
        * (k : ℂ) ^ (-(1 : ℂ))) * Complex.exp (-(2 * s - 2) * v) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [hg]
    rw [← mobiusHarmonic_ofReal]
    push_cast
    rw [show Complex.exp (-(2 * s - 2) * v) = Complex.exp (2 * v) * Complex.exp (-(2 * s) * v) by
      rw [← Complex.exp_add]; ring_nf]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u), integral_comp_half, hg', key]
  have hL' : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 * s - 1)
      = (riemannZeta (2 * s - 1))⁻¹ := eq_inv_of_mul_eq_one_left hL
  have h22 : (2 : ℂ) * s - 2 = 2 * (s - 1) := by ring
  rw [hL', h22]
  field_simp

/-- `∫_0^∞ (-2) e^{u/2} H₂(e^{u/2}) e^{-su} du = -2/((s-½)ζ(2s-½))` on `Re s > 2`. -/
theorem integral_rootHead {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((-2 * Real.sqrt (Real.exp u) *
        mobiusRoot (Real.sqrt (Real.exp u)) : ℝ) : ℂ) * Complex.exp (-s * u)
      = -2 / ((s - 1 / 2) * riemannZeta (2 * s - 1 / 2)) := by
  set g : ℝ → ℂ := fun v => ((-2 * Real.exp v * mobiusRoot (Real.exp v) : ℝ) : ℂ)
    * Complex.exp (-(2 * s) * v) with hg
  have hpt : ∀ u : ℝ, ((-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.sqrt (Real.exp u)) : ℝ)
      : ℂ) * Complex.exp (-s * u) = g (1 / 2 * u) := by
    intro u
    simp only [hg]
    rw [sqrt_exp_eq_exp_half_mul]
    congr 2
    push_cast
    ring
  have h2 : 1 < (2 * s - 1).re := by simp; linarith
  have h3 : 1 < (2 * s - 1 / 2).re := by simp; linarith
  have hs1 : s - 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hz : riemannZeta (2 * s - 1 / 2) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h3
  have hL := LSeries_moebius_mul_riemannZeta_eq_one h3
  have key := integral_partialSum_exp_mul_cexp
    (fun k => ((ArithmeticFunction.moebius k : ℤ) : ℂ) * (k : ℂ) ^ (-(1 / 2 : ℂ)))
    (norm_moebius_mul_cpow_le (by norm_num) (by norm_num)) h2
  rw [LSeries_mul_cpow_neg, show 2 * s - 1 + 1 / 2 = 2 * s - 1 / 2 by ring] at key
  have hg' : ∫ v in Ioi (0 : ℝ), g v = (-2 : ℂ) * ∫ v in Ioi (0 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℂ)
        * (k : ℂ) ^ (-(1 / 2 : ℂ))) * Complex.exp (-(2 * s - 1) * v) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [hg]
    rw [← mobiusRoot_ofReal]
    push_cast
    rw [show Complex.exp (-(2 * s - 1) * v) = Complex.exp v * Complex.exp (-(2 * s) * v) by
      rw [← Complex.exp_add]; ring_nf]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u), integral_comp_half, hg', key]
  have hL' : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 * s - 1 / 2)
      = (riemannZeta (2 * s - 1 / 2))⁻¹ := eq_inv_of_mul_eq_one_left hL
  have h21 : (2 : ℂ) * s - 1 = 2 * (s - 1 / 2) := by ring
  rw [hL', h21]
  field_simp

/-! ### The transform of the complete head -/

/-- The transform of the bounded head remainder. -/
def remainderTransform (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (headRemainder (Real.exp u) : ℂ) * Complex.exp (-z * u)

theorem differentiableAt_remainderTransform {z : ℂ} (hz : 1 / 2 < z.re) :
    DifferentiableAt ℂ remainderTransform z :=
  differentiableAt_integral_mul_cexp (measurable_headRemainder.comp Real.measurable_exp)
    (fun _ hu => abs_headRemainder_exp_le hu.le) hz

theorem analyticOnNhd_remainderTransform :
    AnalyticOnNhd ℂ remainderTransform {z : ℂ | 1 / 2 < z.re} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (differentiableAt_remainderTransform hz).differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem abs_harmonicHead_exp_le (u : ℝ) :
    |LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.sqrt (Real.exp u))|
      ≤ LiouvilleTriangularShortHead.squareMass * Real.exp (3 / 2 * u) := by
  have hZ := squareMass_pos
  have hE := Real.exp_pos u
  rw [sqrt_exp_eq_exp_half_mul]
  have h1 : |mobiusHarmonic (Real.exp (1 / 2 * u))| ≤ Real.exp (1 / 2 * u) :=
    (abs_mobiusHarmonic_le _).trans (Nat.floor_le (Real.exp_pos _).le)
  have h2 : Real.exp (3 / 2 * u) = Real.exp u * Real.exp (1 / 2 * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [abs_mul, abs_mul, abs_of_pos hZ, abs_of_pos hE, h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem abs_rootHead_exp_le (u : ℝ) :
    |-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.sqrt (Real.exp u))|
      ≤ 2 * Real.exp u := by
  rw [sqrt_exp_eq_exp_half_mul]
  have hE := Real.exp_pos (1 / 2 * u)
  have h1 : |mobiusRoot (Real.exp (1 / 2 * u))| ≤ Real.exp (1 / 2 * u) :=
    (abs_mobiusRoot_le _).trans (Nat.floor_le hE.le)
  have h2 : Real.exp u = Real.exp (1 / 2 * u) * Real.exp (1 / 2 * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [abs_mul, abs_mul, abs_of_pos hE, h2]
  norm_num
  nlinarith

theorem abs_triangularHead_exp_le {u : ℝ} (hu : 0 ≤ u) :
    |triangularHead (Real.exp u)|
      ≤ (LiouvilleTriangularShortHead.squareMass + 3) * Real.exp (2 * u) := by
  rw [triangularHead_eq]
  have h1 := abs_harmonicHead_exp_le u
  have h2 := abs_rootHead_exp_le u
  have h3 := abs_headRemainder_exp_le hu
  have hZ := squareMass_pos
  have e1 : Real.exp (3 / 2 * u) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp u ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have e3 : Real.exp (1 / 2 * u) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have hab := abs_add_le (LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.sqrt (Real.exp u)) +
      -2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.sqrt (Real.exp u)))
    (headRemainder (Real.exp u))
  have hab2 := abs_add_le (LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.sqrt (Real.exp u)))
      (-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.sqrt (Real.exp u)))
  nlinarith

/-- `∫_0^∞ A(e^u) e^{-su} du = Z/((s-1)ζ(2s-1)) - 2/((s-½)ζ(2s-½)) + R(s)` on `Re s > 2`. -/
theorem integral_triangularHead_exp_mul_cexp {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), (triangularHead (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = LiouvilleTriangularShortHead.squareMass / ((s - 1) * riemannZeta (2 * s - 1))
        - 2 / ((s - 1 / 2) * riemannZeta (2 * s - 1 / 2)) + remainderTransform s := by
  have hsq := Real.continuous_sqrt.measurable
  have i1 : IntegrableOn (fun u : ℝ => ((LiouvilleTriangularShortHead.squareMass * Real.exp u *
      mobiusHarmonic (Real.sqrt (Real.exp u)) : ℝ) : ℂ) * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le
      (g := fun u => LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.sqrt (Real.exp u)))
      ((measurable_const.mul Real.measurable_exp).mul
        (measurable_mobiusHarmonic.comp (hsq.comp Real.measurable_exp)))
      (fun u _ => abs_harmonicHead_exp_le u) (by linarith)
  have i2 : IntegrableOn (fun u : ℝ => ((-2 * Real.sqrt (Real.exp u) *
      mobiusRoot (Real.sqrt (Real.exp u)) : ℝ) : ℂ) * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le
      (g := fun u => -2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.sqrt (Real.exp u)))
      ((measurable_const.mul (hsq.comp Real.measurable_exp)).mul
        (measurable_mobiusRoot.comp (hsq.comp Real.measurable_exp)))
      (fun u _ => by simpa using abs_rootHead_exp_le u) (C := 2) (a := 1)
      (by linarith)
  have i3 : IntegrableOn (fun u : ℝ => (headRemainder (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := 1) (a := 1 / 2)
      (measurable_headRemainder.comp Real.measurable_exp)
      (fun u hu => by simpa using abs_headRemainder_exp_le hu.le) (by linarith)
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (triangularHead (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = (((LiouvilleTriangularShortHead.squareMass * Real.exp u *
          mobiusHarmonic (Real.sqrt (Real.exp u)) : ℝ) : ℂ) * Complex.exp (-s * u)
        + ((-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.sqrt (Real.exp u)) : ℝ) : ℂ)
          * Complex.exp (-s * u))
        + (headRemainder (Real.exp u) : ℂ) * Complex.exp (-s * u) := by
    intro u _
    rw [triangularHead_eq]
    push_cast
    ring
  have i12 : IntegrableOn (fun u : ℝ => ((LiouvilleTriangularShortHead.squareMass *
      Real.exp u * mobiusHarmonic (Real.sqrt (Real.exp u)) : ℝ) : ℂ) * Complex.exp (-s * u)
      + ((-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.sqrt (Real.exp u)) : ℝ) : ℂ)
        * Complex.exp (-s * u)) (Ioi 0) := i1.add i2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i12 i3,
    integral_add i1 i2, integral_harmonicHead hs, integral_rootHead hs]
  unfold remainderTransform
  ring

/-! ## Every uncancelled head oscillates beyond the three-quarter scale -/

/-- `F_c(x) = P(x) + c A(x)`. -/
def triangleCombination (c x : ℝ) : ℝ := liouvilleTriangle x + c * triangularHead x

theorem measurable_triangleCombination (c : ℝ) : Measurable (triangleCombination c) :=
  measurable_liouvilleTriangle.add (measurable_const.mul measurable_triangularHead)

theorem abs_triangleCombination_exp_le (c : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    |triangleCombination c (Real.exp u)|
      ≤ (2 + |c| * (LiouvilleTriangularShortHead.squareMass + 3)) * Real.exp (2 * u) := by
  unfold triangleCombination
  have h1 := abs_liouvilleTriangle_exp_le hu
  have h2 := abs_triangularHead_exp_le hu
  have hc := abs_nonneg c
  calc |liouvilleTriangle (Real.exp u) + c * triangularHead (Real.exp u)|
      ≤ |liouvilleTriangle (Real.exp u)| + |c| * |triangularHead (Real.exp u)| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ 2 * Real.exp (2 * u)
        + |c| * ((LiouvilleTriangularShortHead.squareMass + 3) * Real.exp (2 * u)) := by
        gcongr
    _ = _ := by ring

theorem zetaResidueUnit_eq {z : ℂ} (hz : z ≠ 1) :
    RHTower.zetaResidueUnit z = (z - 1) * riemannZeta z := by
  rw [RHTower.zetaResidueUnit, Function.update_of_ne hz]

/-- On `Re s > 2` the transform of `F_c` is the three-term pole model plus `c R(s)`. -/
theorem integral_triangleCombination_exp_mul_cexp (c : ℝ) {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), (triangleCombination c (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = LiouvilleTriangularPoleSeparation.poleModel
          (2 * c * LiouvilleTriangularShortHead.squareMass) (-2 * c) 1 s
        + c * remainderTransform s := by
  have i1 : IntegrableOn (fun u : ℝ => (liouvilleTriangle (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := 2) (a := 2)
      (measurable_liouvilleTriangle.comp Real.measurable_exp)
      (fun u hu => abs_liouvilleTriangle_exp_le hu.le) hs
  have i2 : IntegrableOn (fun u : ℝ => (triangularHead (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := LiouvilleTriangularShortHead.squareMass + 3) (a := 2)
      (measurable_triangularHead.comp Real.measurable_exp)
      (fun u hu => abs_triangularHead_exp_le hu.le) hs
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (triangleCombination c (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = (liouvilleTriangle (Real.exp u) : ℂ) * Complex.exp (-s * u)
        + (c : ℂ) * ((triangularHead (Real.exp u) : ℂ) * Complex.exp (-s * u)) := by
    intro u _
    unfold triangleCombination
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i1 (i2.const_mul _),
    integral_const_mul, integral_liouvilleTriangle_exp_mul_cexp hs,
    integral_triangularHead_exp_mul_cexp hs]
  have hs1 : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have hne : ∀ r : ℝ, r < 2 → s - r ≠ 0 := fun r hr h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs1' : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs; linarith
  have hsh : s - 1 / 2 ≠ 0 := by
    have := hne (1 / 2) (by norm_num); push_cast at this; exact this
  have h21 : 2 * s - 1 ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h22 : 2 * s - 1 / 2 ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hz1 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hz2 : riemannZeta (2 * s - 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hz3 : riemannZeta (2 * s - 1 / 2) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hd1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
  have hd2 : 2 * s - 1 - 1 ≠ 0 := sub_ne_zero.mpr h21
  have hd3 : 2 * s - 1 / 2 - 1 ≠ 0 := sub_ne_zero.mpr h22
  have hd4 : 2 * s - 3 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold LiouvilleTriangularPoleSeparation.poleModel
  rw [zetaResidueUnit_eq hs1', zetaResidueUnit_eq h21, zetaResidueUnit_eq h22,
    show (2 : ℂ) * s - 1 - 1 = 2 * (s - 1) by ring,
    show (2 : ℂ) * s - 1 / 2 - 1 = 2 * s - 3 / 2 by ring]
  have e3 : -2 * (c : ℂ) * (2 * s - 3 / 2) /
      ((s - 1 / 2) * ((2 * s - 3 / 2) * riemannZeta (2 * s - 1 / 2)))
      = -2 * c / ((s - 1 / 2) * riemannZeta (2 * s - 1 / 2)) := by
    rw [show -2 * (c : ℂ) * (2 * s - 3 / 2) = (2 * s - 3 / 2) * (-2 * c) by ring,
      show (s - 1 / 2) * ((2 * s - 3 / 2) * riemannZeta (2 * s - 1 / 2))
        = (2 * s - 3 / 2) * ((s - 1 / 2) * riemannZeta (2 * s - 1 / 2)) by ring,
      mul_div_mul_left _ _ hd4]
  rw [e3]
  field_simp
  ring

/-! ### The contradiction at a shifted zero -/

/-- `D(z) = z U(z) (z-½) U(2z-½) U(2z-1)`, `U(w) = (w-1)ζ(w)`. -/
def triangularPoleDenominator (z : ℂ) : ℂ :=
  z * RHTower.zetaResidueUnit z * (z - 1 / 2) * RHTower.zetaResidueUnit (2 * z - 1 / 2)
    * RHTower.zetaResidueUnit (2 * z - 1)

/-- The pole model times `D`, written without denominators. -/
def triangularPoleNumerator (a b : ℂ) (z : ℂ) : ℂ :=
  riemannZeta (2 * z) * ((z - 1 / 2) * RHTower.zetaResidueUnit (2 * z - 1 / 2)
      * RHTower.zetaResidueUnit (2 * z - 1))
    + a * (z * RHTower.zetaResidueUnit z * (z - 1 / 2) * RHTower.zetaResidueUnit (2 * z - 1 / 2))
    + b * (2 * z - 3 / 2) * (z * RHTower.zetaResidueUnit z * RHTower.zetaResidueUnit (2 * z - 1))

theorem poleModel_mul_triangularPoleDenominator (a b : ℂ) {z : ℂ} (h0 : z ≠ 0)
    (hU : RHTower.zetaResidueUnit z ≠ 0) (hh : z - 1 / 2 ≠ 0)
    (hU2 : RHTower.zetaResidueUnit (2 * z - 1 / 2) ≠ 0)
    (hU1 : RHTower.zetaResidueUnit (2 * z - 1) ≠ 0) :
    LiouvilleTriangularPoleSeparation.poleModel a b 1 z * triangularPoleDenominator z
      = triangularPoleNumerator a b z := by
  unfold LiouvilleTriangularPoleSeparation.poleModel triangularPoleDenominator
    triangularPoleNumerator
  generalize RHTower.zetaResidueUnit z = A at *
  generalize RHTower.zetaResidueUnit (2 * z - 1 / 2) = B2 at *
  generalize RHTower.zetaResidueUnit (2 * z - 1) = B1 at *
  generalize riemannZeta (2 * z) = Z2
  generalize hH : z - 1 / 2 = H at *
  have hz : 2 * z - 3 / 2 = 2 * H - 1 / 2 := by rw [← hH]; ring
  rw [hz]
  field_simp

theorem differentiableAt_triangularPoleDenominator (z : ℂ) :
    DifferentiableAt ℂ triangularPoleDenominator z := by
  have hu := fun w => (RHTower.analyticAt_zetaResidueUnit w).differentiableAt
  unfold triangularPoleDenominator
  exact (((differentiableAt_id.mul (hu z)).mul (differentiableAt_id.sub_const _)).mul
    ((hu _).comp z (by fun_prop))).mul ((hu _).comp z (by fun_prop))

theorem differentiableAt_triangularPoleNumerator (a b : ℂ) {z : ℂ} (hz : 2 * z ≠ 1) :
    DifferentiableAt ℂ (triangularPoleNumerator a b) z := by
  have hu := fun w => (RHTower.analyticAt_zetaResidueUnit w).differentiableAt
  have hZ : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) z :=
    ((analyticOn_riemannZeta _ hz).differentiableAt).comp z (by fun_prop)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (2 * z - 1 / 2)) z :=
    (hu _).comp z (by fun_prop)
  have h1 : DifferentiableAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (2 * z - 1)) z :=
    (hu _).comp z (by fun_prop)
  unfold triangularPoleNumerator
  exact ((hZ.mul (((differentiableAt_id.sub_const _).mul h2).mul h1)).add
    ((differentiableAt_const _).mul (((differentiableAt_id.mul (hu z)).mul
      (differentiableAt_id.sub_const _)).mul h2))).add
    (((differentiableAt_const _).mul ((differentiableAt_const _).mul differentiableAt_id
      |>.sub_const _)).mul ((differentiableAt_id.mul (hu z)).mul h1))

theorem analyticAt_poleModel_ofReal (a b d : ℂ) {t : ℝ} (ht : 1 / 2 < t) :
    AnalyticAt ℂ (LiouvilleTriangularPoleSeparation.poleModel a b d) t := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < t).ne'
  have hth : (t : ℂ) - 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2t : 2 * (t : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hU : RHTower.zetaResidueUnit t ≠ 0 := zetaResidueUnit_ofReal_ne_zero (by linarith)
  have hU1 : RHTower.zetaResidueUnit (2 * t - 1) ≠ 0 := by
    have := zetaResidueUnit_ofReal_ne_zero (show (0 : ℝ) < 2 * t - 1 by linarith)
    push_cast at this; exact this
  have hU2 : RHTower.zetaResidueUnit (2 * t - 1 / 2) ≠ 0 := by
    have := zetaResidueUnit_ofReal_ne_zero (show (0 : ℝ) < 2 * t - 1 / 2 by linarith)
    push_cast at this; exact this
  have hZ : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z)) t :=
    (analyticOn_riemannZeta _ h2t).comp (by fun_prop)
  have hA1 : AnalyticAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (2 * z - 1)) t :=
    (RHTower.analyticAt_zetaResidueUnit _).comp (by fun_prop)
  have hA2 : AnalyticAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (2 * z - 1 / 2)) t :=
    (RHTower.analyticAt_zetaResidueUnit _).comp (by fun_prop)
  unfold LiouvilleTriangularPoleSeparation.poleModel
  exact (((analyticAt_const.mul hZ).div
      (analyticAt_id.mul (RHTower.analyticAt_zetaResidueUnit _)) (mul_ne_zero ht0 hU)).add
      (analyticAt_const.div hA1 hU1)).add
    ((analyticAt_const.mul (by fun_prop)).div ((analyticAt_id.sub analyticAt_const).mul hA2)
      (mul_ne_zero hth hU2))

/-- A one-sided bound `ηF_c(e^u) ≤ C e^{βu} + K` with `5/8 ≤ β < 3/4` is impossible. -/
theorem false_of_oneSided {c η C β K : ℝ} (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C)
    (hβlo : 5 / 8 ≤ β) (hβ : β < 3 / 4) (hK : 0 ≤ K)
    (hg : ∀ u, 0 < u → η * triangleCombination c (Real.exp u) ≤ C * Real.exp (β * u) + K) :
    False := by
  set Z := LiouvilleTriangularShortHead.squareMass with hZdef
  have hZ := squareMass_pos
  set f : ℝ → ℝ := fun u => triangleCombination c (Real.exp u) with hfdef
  have hf : Measurable f := (measurable_triangleCombination c).comp Real.measurable_exp
  set B : ℝ := 2 + |c| * (Z + 3) with hBdef
  have hB : 0 ≤ B := by positivity
  have hb : ∀ u, 0 < u → |f u| ≤ B * Real.exp (2 * u) := fun u hu =>
    abs_triangleCombination_exp_le c hu.le
  have hβ0 : 0 ≤ β := by linarith
  have hβ2 : β ≤ 2 := by linarith
  have hCC : C < C + 1 := lt_add_one C
  obtain ⟨hc0, hlo, hhi⟩ := isAbscissa_oneSidedMeasure hf hη hC hCC hK hB hβ2
    (by norm_num) hb hg
  set ν := expOneSidedMeasure f η (C + 1) β K with hνdef
  set a : ℂ := 2 * c * Z with hadef
  set b : ℂ := -2 * c with hbdef
  set Ψ : ℂ → ℂ := fun z => ((C + 1 : ℝ) : ℂ) / (z - β) + (K : ℂ) / z
      - η * (LiouvilleTriangularPoleSeparation.poleModel a b 1 z + c * remainderTransform z)
    with hΨdef
  have hagree : ∀ z : ℂ, 2 < z.re → complexLaplace ν z = Ψ z := by
    intro z hz
    rw [complexLaplace_oneSidedMeasure_eq hf hβ0 hβ2 hCC.le hb hg hz]
    simp only [hΨdef, hfdef]
    rw [integral_triangleCombination_exp_mul_cexp c hz]
  have hΨa : ∀ t : ℝ, β < t → AnalyticAt ℂ Ψ t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < t).ne'
    have htβ : (t : ℂ) - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hP := analyticAt_poleModel_ofReal a b 1 (by linarith : (1 : ℝ) / 2 < t)
    have hR : AnalyticAt ℂ remainderTransform t :=
      analyticOnNhd_remainderTransform t (by simp; linarith)
    simp only [hΨdef]
    exact ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) htβ).add
      (analyticAt_const.div analyticAt_id ht0)).sub
      (analyticAt_const.mul (hP.add (analyticAt_const.mul hR)))
  have hcβ : IsAbscissa ν β := isAbscissa_eq_of_analyticAt_real hc0 hlo hhi hΨa hagree
  set V : Set ℂ := {z : ℂ | β < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  set Lf : ℂ → ℂ := fun z => (((C + 1 : ℝ) : ℂ) / (z - β) + (K : ℂ) / z
      - complexLaplace ν z) * triangularPoleDenominator z with hLf
  set Rf : ℂ → ℂ := fun z => (η : ℂ) * (triangularPoleNumerator a b z
      + c * remainderTransform z * triangularPoleDenominator z) with hRf
  have hLa : AnalyticOnNhd ℂ Lf V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hVo
    have hz' : β < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz'; linarith
    have hzβ : z - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have d1 : DifferentiableAt ℂ (fun z : ℂ => ((C + 1 : ℝ) : ℂ) / (z - β)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const _) hzβ
    have d2 : DifferentiableAt ℂ (fun z : ℂ => (K : ℂ) / z) z :=
      (differentiableAt_const _).div differentiableAt_id hz0
    exact (((d1.add d2).sub (hasDerivAt_complexLaplace hcβ hz').differentiableAt).mul
      (differentiableAt_triangularPoleDenominator z)).differentiableWithinAt
  have hRa : AnalyticOnNhd ℂ Rf V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hVo
    have hz' : β < z.re := hz
    have h2z : 2 * z ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact ((differentiableAt_const _).mul ((differentiableAt_triangularPoleNumerator a b h2z).add
      (((differentiableAt_const _).mul (differentiableAt_remainderTransform (by linarith))).mul
        (differentiableAt_triangularPoleDenominator z)))).differentiableWithinAt
  have hev : Lf =ᶠ[𝓝 (3 : ℂ)] Rf := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with z hz
    have hz' : 2 < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz'; linarith
    have hz1 : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz'; linarith
    have hzh : z - 1 / 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hne1 : 2 * z - 1 ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hne2 : 2 * z - 1 / 2 ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hU : RHTower.zetaResidueUnit z ≠ 0 := by
      rw [zetaResidueUnit_eq hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_lt_re (by linarith))
    have hU1 : RHTower.zetaResidueUnit (2 * z - 1) ≠ 0 := by
      rw [zetaResidueUnit_eq hne1]
      exact mul_ne_zero (sub_ne_zero.mpr hne1)
        (riemannZeta_ne_zero_of_one_lt_re (by simp; linarith))
    have hU2 : RHTower.zetaResidueUnit (2 * z - 1 / 2) ≠ 0 := by
      rw [zetaResidueUnit_eq hne2]
      exact mul_ne_zero (sub_ne_zero.mpr hne2)
        (riemannZeta_ne_zero_of_one_lt_re (by simp; linarith))
    simp only [hLf, hRf]
    rw [hagree z hz', ← poleModel_mul_triangularPoleDenominator a b hz0 hU hzh hU2 hU1]
    simp only [hΨdef]
    ring
  have h3V : (3 : ℂ) ∈ V := by show β < (3 : ℂ).re; norm_num; linarith
  have heq := hLa.eqOn_of_preconnected_of_eventuallyEq hRa
    (convex_halfSpace_re_gt β).isPreconnected h3V hev
  obtain ⟨w, hwlo, hwhi, hwim, hz2w, hzw, hz2w'⟩ :=
    LiouvilleTriangularPoleSeparation.exists_separated_pole
  have hwV : w ∈ V := by show β < w.re; linarith
  have hw1' : 2 * w - 1 ≠ 1 := by
    intro h; rw [h] at hz2w; exact riemannZeta_one_ne_zero hz2w
  have hU1 : RHTower.zetaResidueUnit (2 * w - 1) = 0 := by
    rw [zetaResidueUnit_eq hw1', hz2w, mul_zero]
  have hDw : triangularPoleDenominator w = 0 := by
    unfold triangularPoleDenominator; rw [hU1, mul_zero]
  have h := heq hwV
  simp only [hLf, hRf, hDw, mul_zero, add_zero] at h
  have hNw : triangularPoleNumerator a b w = a * (w * RHTower.zetaResidueUnit w * (w - 1 / 2)
      * RHTower.zetaResidueUnit (2 * w - 1 / 2)) := by
    unfold triangularPoleNumerator; rw [hU1]; ring
  rw [hNw] at h
  have hη0 : (η : ℂ) ≠ 0 := by
    have : η ≠ 0 := by intro h0; rw [h0, abs_zero] at hη; norm_num at hη
    exact_mod_cast this
  have ha : a ≠ 0 := by
    simp only [hadef]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hc))
      (by exact_mod_cast hZ.ne')
  have hw0 : w ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hwlo; linarith
  have hw1 : w ≠ 1 := by intro h0; rw [h0, Complex.one_re] at hwhi; linarith
  have hwh : w - 1 / 2 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hv1 : 2 * w - 1 / 2 ≠ 1 := by
    intro h0; have := congrArg Complex.im h0; simp at this; exact hwim this
  have hUw : RHTower.zetaResidueUnit w ≠ 0 := by
    rw [zetaResidueUnit_eq hw1]; exact mul_ne_zero (sub_ne_zero.mpr hw1) hzw
  have hUv : RHTower.zetaResidueUnit (2 * w - 1 / 2) ≠ 0 := by
    rw [zetaResidueUnit_eq hv1]; exact mul_ne_zero (sub_ne_zero.mpr hv1) hz2w'
  exact (mul_ne_zero hη0 (mul_ne_zero ha (mul_ne_zero (mul_ne_zero (mul_ne_zero hw0 hUw) hwh)
    hUv))) h.symm

/-- A one-sided bound `η F_c(x) ≤ C x^β` for large `x`, `β < 3/4`, is impossible. -/
theorem false_of_eventually_le {c η C β : ℝ} (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C)
    (hβ : β < 3 / 4) (h : ∀ᶠ x in atTop, η * triangleCombination c x ≤ C * x ^ β) : False := by
  set β₁ := max β (5 / 8) with hβ₁def
  have hβ₁lo : 5 / 8 ≤ β₁ := le_max_right _ _
  have hβ₁ : β₁ < 3 / 4 := max_lt hβ (by norm_num)
  have hββ₁ : β ≤ β₁ := le_max_left _ _
  have hu : ∀ᶠ u in atTop,
      η * triangleCombination c (Real.exp u) ≤ C * Real.exp (β₁ * u) := by
    filter_upwards [Real.tendsto_exp_atTop.eventually h, eventually_ge_atTop (0 : ℝ)]
      with u hu hu0
    rw [← Real.exp_mul] at hu
    calc η * triangleCombination c (Real.exp u) ≤ C * Real.exp (u * β) := hu
      _ ≤ C * Real.exp (β₁ * u) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp hu
  set u₁ := max u₀ 0 with hu₁def
  set B : ℝ := 2 + |c| * (LiouvilleTriangularShortHead.squareMass + 3) with hBdef
  have hB : 0 ≤ B := by have := squareMass_pos; positivity
  set K : ℝ := B * Real.exp (2 * u₁) with hKdef
  have hK : 0 ≤ K := by positivity
  refine false_of_oneSided hc hη hC hβ₁lo hβ₁ hK (fun u hu0 => ?_)
  have h4 : 0 ≤ C * Real.exp (β₁ * u) := by positivity
  by_cases hle : u₀ ≤ u
  · have := hu₀ u hle
    linarith
  · have h1 := abs_triangleCombination_exp_le c hu0.le
    have h2 : Real.exp (2 * u) ≤ Real.exp (2 * u₁) :=
      Real.exp_le_exp.mpr (by have := le_max_left u₀ 0; linarith)
    have h3 : η * triangleCombination c (Real.exp u) ≤ |triangleCombination c (Real.exp u)| :=
      calc η * triangleCombination c (Real.exp u)
          ≤ |η * triangleCombination c (Real.exp u)| := le_abs_self _
        _ = |triangleCombination c (Real.exp u)| := by rw [abs_mul, hη, one_mul]
    have h5 : B * Real.exp (2 * u) ≤ K := mul_le_mul_of_nonneg_left h2 hB
    linarith

/-- **Every uncancelled short triangular head oscillates beyond the three-quarter scale.**
For every nonzero real `c`, every `β < 3/4` and every `C ≥ 0`, the function
`P(x) + c A(x)` exceeds `C x^β` and falls below `-C x^β` for arbitrarily large `x`. -/
theorem frequently_gt_and_frequently_lt (c : ℝ) (hc : c ≠ 0) {β C : ℝ} (hβ : β < 3 / 4)
    (hC : 0 ≤ C) :
    (∃ᶠ x in atTop, C * x ^ β < triangleCombination c x) ∧
      (∃ᶠ x in atTop, triangleCombination c x < -(C * x ^ β)) := by
  constructor
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le hc (η := 1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [one_mul]; exact not_lt.mp hx)
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le hc (η := -1) (by norm_num) hC hβ
      (h.mono fun x hx => by have := not_lt.mp hx; linarith)

end

end RHTower.LiouvilleTriangularHeadOscillation
