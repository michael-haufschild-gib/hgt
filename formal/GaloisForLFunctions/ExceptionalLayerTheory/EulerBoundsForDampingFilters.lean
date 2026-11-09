import GaloisForLFunctions.ExceptionalLayerTheory.DampingFiltersReadTheExceptionalDivisor

/-!
# Euler-region upper bounds for damping filters

The absolutely convergent von Mangoldt series gives a bound for the complete
filtered prime current without a hypothesis on the zeros. Mellin inversion
retains one factor of the damping spacing for each root of the filter.
-/

open Complex Filter Set Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem norm_exp_sub_exp_le_re_bound (z w : ℂ) (M : ℝ)
    (hz : z.re ≤ M) (hw : w.re ≤ M) :
    ‖Complex.exp z - Complex.exp w‖ ≤ Real.exp M * ‖z - w‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (Complex.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u hu => by rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hu)
    (convex_halfSpace_re_le M) hw hz

private theorem norm_damping_root_factor_le {R h : ℝ} (hR : 0 ≤ R)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (β : ℝ) {z w : ℂ}
    (hz : z.re ≤ R) (hw : ‖w‖ ≤ R) :
    ‖Complex.exp ((h : ℂ) * (z - β)) -
        Complex.exp ((h : ℂ) * (w - β))‖ ≤
      h * (‖z‖ + R) * Real.exp (R + |β|) := by
  have hb (u : ℂ) (hu : u.re ≤ R) : ((h : ℂ) * (u - β)).re ≤ R + |β| := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, zero_mul, sub_zero]
    calc
      h * (u.re - β) ≤ h * (R + |β|) :=
        mul_le_mul_of_nonneg_left (by linarith only [hu, neg_le_abs β]) hh
      _ ≤ 1 * (R + |β|) := mul_le_mul_of_nonneg_right hh1 (by positivity)
      _ = _ := one_mul _
  have he := norm_exp_sub_exp_le_re_bound ((h : ℂ) * (z - β))
    ((h : ℂ) * (w - β)) (R + |β|) (hb z hz)
    (hb w ((Complex.re_le_norm w).trans hw))
  rw [show (h : ℂ) * (z - β) - (h : ℂ) * (w - β) = (h : ℂ) * (z - w) by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh] at he
  calc
    ‖Complex.exp ((h : ℂ) * (z - β)) - Complex.exp ((h : ℂ) * (w - β))‖ ≤
        Real.exp (R + |β|) * (h * ‖z - w‖) := he
    _ ≤ Real.exp (R + |β|) * (h * (‖z‖ + R)) := by
      gcongr
      exact (norm_sub_le z w).trans (add_le_add_left hw _)
    _ = _ := by ring

/-- On a vertical Euler line, a degree `d` divisor filter retains its full
`h^d` gain, with only polynomial losses in the two height coordinates. -/
theorem exists_divisorDampingFilter_euler_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (β c : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ h t v : ℝ, 0 ≤ h → h ≤ 1 →
      ‖(divisorDampingFilter F ρ β h).eval
        (Complex.exp ((h : ℂ) * (((c : ℂ) + (t + v) * I) - β)))‖ ≤
      (h * B * (1 + |t|) * (1 + |v|)) ^
        (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) := by
  classical
  let S := F.filter (fun q => xiZero q ≠ ρ)
  let R : ℝ := 1 + |c| + ∑ q ∈ S, ‖xiZero q‖
  have hsum : 0 ≤ ∑ q ∈ S, ‖xiZero q‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hR : 1 ≤ R := by dsimp only [R]; positivity
  have hcR : |c| ≤ R := by dsimp only [R]; linarith only [hsum]
  let B := (2 * R + 1) * Real.exp (R + |β|)
  refine ⟨B, by dsimp only [B]; positivity, ?_⟩
  intro h t v hh hh1
  let z : ℂ := (c : ℂ) + (t + v) * I
  have hzre : z.re ≤ R := by simpa [z] using (le_abs_self c).trans hcR
  have hz : ‖z‖ ≤ |c| + |t| + |v| := by
    calc
      ‖z‖ ≤ ‖(c : ℂ)‖ + ‖((t + v : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = |c| + |t + v| := by simp
      _ ≤ |c| + |t| + |v| := by linarith only [abs_add_le t v]
  have hzR : ‖z‖ + R ≤ (2 * R + 1) * (1 + |t|) * (1 + |v|) := by
    have htv := mul_nonneg (abs_nonneg t) (abs_nonneg v)
    have hRt := mul_nonneg (by linarith only [hR] : 0 ≤ 2 * R) (abs_nonneg t)
    have hRv := mul_nonneg (by linarith only [hR] : 0 ≤ 2 * R) (abs_nonneg v)
    have hRtv := mul_nonneg (by linarith only [hR] : 0 ≤ 2 * R) htv
    nlinarith only [hz, hcR, hR, abs_nonneg t, abs_nonneg v, htv, hRt, hRv, hRtv]
  have hfactor (w : ℂ) (hw : ‖w‖ ≤ R) :
      ‖Complex.exp ((h : ℂ) * (z - β)) - Complex.exp ((h : ℂ) * (w - β))‖ ≤
        h * B * (1 + |t|) * (1 + |v|) := by
    calc
      _ ≤ h * (‖z‖ + R) * Real.exp (R + |β|) :=
        norm_damping_root_factor_le (by linarith only [hR]) hh hh1 β hzre hw
      _ ≤ h * ((2 * R + 1) * (1 + |t|) * (1 + |v|)) * Real.exp (R + |β|) := by
        gcongr
      _ = _ := by dsimp only [B]; ring
  change ‖(divisorDampingFilter F ρ β h).eval (Complex.exp ((h : ℂ) * (z - β)))‖ ≤ _
  simp only [divisorDampingFilter, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_mul, norm_prod]
  have hprod :
      (∏ q ∈ S, ‖Complex.exp ((h : ℂ) * (z - β)) -
        Complex.exp ((h : ℂ) * (xiZero q - β))‖) ≤
        (h * B * (1 + |t|) * (1 + |v|)) ^ S.card := by
    calc
      _ ≤ ∏ _q ∈ S, (h * B * (1 + |t|) * (1 + |v|)) := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro q hq
        apply hfactor
        have hqsum := Finset.single_le_sum (fun p _ => norm_nonneg (xiZero p)) hq
        dsimp only [R]
        linarith only [hqsum, abs_nonneg c]
      _ = _ := by simp
  calc
    _ ≤ (h * B * (1 + |t|) * (1 + |v|)) *
        (h * B * (1 + |t|) * (1 + |v|)) ^ S.card :=
      mul_le_mul (hfactor 1 (by simpa using hR)) hprod
        (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; simp [S]

private theorem integrable_gaussian_euler_line {s : ℂ} {c y : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hs : 1 < s.re + c) :
    Integrable (fun v : ℝ => gaussianMBKernel y ((c : ℂ) + v * I) *
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (s + ((c : ℂ) + v * I))) := by
  refine ((integrable_gaussianMBKernel_line hy hc).norm.mul_const
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (s.re + c))).mono'
      ((continuous_gaussianMBKernel_line hy hc).mul
        (continuous_LSeries_vonMangoldt_line hs)).aestronglyMeasurable ?_
  refine Eventually.of_forall fun v => ?_
  rw [norm_mul]
  have hb := norm_LSeries_vonMangoldt_le
    (s := s + ((c : ℂ) + v * I)) (by simpa using hs)
  simpa using mul_le_mul_of_nonneg_left hb
    (norm_nonneg (gaussianMBKernel y ((c : ℂ) + v * I)))

/-- Mellin inversion of the literal filtered prime sum. Every root remains
inside the absolutely convergent Euler integral. -/
theorem primeDampingFilter_eq_euler_integral (P : Polynomial ℂ)
    (σ β a h t c : ℝ) (hc : 0 < c) (hs : 1 < σ + c) :
    primeDampingFilter P σ β a h t = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, P.eval (Complex.exp ((h : ℂ) *
          ((((σ : ℂ) + t * I) + ((c : ℂ) + v * I)) - β))) *
        gaussianMBKernel (Real.exp (-a * t)) ((c : ℂ) + v * I) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (((σ : ℂ) + t * I) + ((c : ℂ) + v * I)) := by
  let s : ℂ := (σ : ℂ) + t * I
  let k : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let L : ℝ → ℂ := fun v =>
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + ((c : ℂ) + v * I))
  let J := Finset.range (P.natDegree + 1)
  have hs' : 1 < s.re + c := by simpa [s] using hs
  have hi (j : ℕ) : Integrable (fun v : ℝ =>
      P.coeff j * dampingSampleWeight β h s j *
        (gaussianMBKernel (geometricGaussianDamping a h t j) ((c : ℂ) + v * I) * L v)) :=
    (integrable_gaussian_euler_line (Real.exp_pos _) hc hs').const_mul _
  have he (j : ℕ) :
      P.coeff j * dampingSampleWeight β h s j *
        gaussianDampedPrimeSum s (geometricGaussianDamping a h t j) =
      k * ∫ v : ℝ, P.coeff j * dampingSampleWeight β h s j *
        (gaussianMBKernel (geometricGaussianDamping a h t j) ((c : ℂ) + v * I) * L v) := by
    rw [gaussianDampedPrimeSum, tsum_term_mul_exp_neg_eq_line_integral
      (Real.exp_pos _) hc _ s (summable_vonMangoldt_rpow_neg hs'), integral_const_mul]
    ring
  calc
    primeDampingFilter P σ β a h t = k * ∫ v : ℝ,
        ∑ j ∈ J, P.coeff j * dampingSampleWeight β h s j *
          (gaussianMBKernel (geometricGaussianDamping a h t j) ((c : ℂ) + v * I) * L v) := by
      change (∑ j ∈ J, _) = _
      simp_rw [he]
      rw [← Finset.mul_sum, integral_finset_sum J (fun j _ => hi j)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      refine Eventually.of_forall fun v => ?_
      have hm := polynomial_dampingFilter_gaussianMode P β a h t s
        (s + ((c : ℂ) + v * I))
      simp only [add_sub_cancel_left] at hm
      calc
        _ = (∑ j ∈ J, P.coeff j * dampingSampleWeight β h s j *
              gaussianMBKernel (geometricGaussianDamping a h t j) ((c : ℂ) + v * I)) * L v := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [hm]

/-- An arithmetic upper bound for the complete prime-only filter, uniform in
height and in `0 ≤ h ≤ 1`. The line `c > 1` uses only absolute convergence
of the actual Euler series; no zero-free strip or finite-layer law enters. -/
theorem exists_primeDampingFilter_arithmetic_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β c : ℝ) (hc : 1 < c) (hσc : σ < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ a h t : ℝ, 0 ≤ h → h ≤ 1 →
      ‖primeDampingFilter (divisorDampingFilter F ρ β h) σ β a h t‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + |t|) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
            Real.exp (a * t * (c - σ) / 2) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let δ := c - σ
  have hδ : 0 < δ := sub_pos.mpr hσc
  obtain ⟨B, hB, hfilter⟩ := exists_divisorDampingFilter_euler_bound F ρ β c
  let E : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c
  have hE : 0 ≤ E := tsum_nonneg fun n => div_nonneg
    ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  let W : ℝ → ℝ := fun v => ‖gaussianMBKernel 1 ((δ : ℂ) + v * I)‖ * (1 + |v|) ^ d
  have hWi : Integrable W := integrable_norm_gaussianMBKernel_mul_pow zero_lt_one hδ d
  let I₀ : ℝ := ∫ v : ℝ, W v
  have hI₀ : 0 ≤ I₀ := integral_nonneg fun v => by dsimp only [W]; positivity
  let k : ℝ := 1 / (2 * Real.pi)
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  let C₀ := k * B ^ d * E * I₀
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro a h t hh hh1
  let s : ℂ := (σ : ℂ) + t * I
  let P := divisorDampingFilter F ρ β h
  let Z := h ^ d * (1 + |t|) ^ d * Real.exp (a * t * δ / 2)
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  let Q : ℝ → ℂ := fun v =>
    P.eval (Complex.exp ((h : ℂ) * ((s + ((δ : ℂ) + v * I)) - β))) *
      gaussianMBKernel (Real.exp (-a * t)) ((δ : ℂ) + v * I) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (s + ((δ : ℂ) + v * I))
  have hre (v : ℝ) : (s + ((δ : ℂ) + v * I)).re = c := by simp [s, δ]
  have hsδ : 1 < s.re + δ := by simpa [s, δ] using hc
  have hpoint (v : ℝ) : ‖Q v‖ ≤ (B ^ d * E * Z) * W v := by
    have hp := hfilter h t v hh hh1
    have hline : s + ((δ : ℂ) + v * I) = (c : ℂ) + (t + v) * I := by
      dsimp only [s, δ]
      push_cast
      ring
    have hL := norm_LSeries_vonMangoldt_le
      (s := s + ((δ : ℂ) + v * I)) (by rw [hre]; exact hc)
    rw [hre] at hL
    have hK : ‖gaussianMBKernel (Real.exp (-a * t)) ((δ : ℂ) + v * I)‖ =
        Real.exp (a * t * δ / 2) * ‖gaussianMBKernel 1 ((δ : ℂ) + v * I)‖ := by
      rw [norm_gaussianMBKernel_line (Real.exp_pos _),
        norm_gaussianMBKernel_line zero_lt_one, Real.one_rpow, mul_one,
        Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [show (-a * t) * -(δ / 2) = a * t * δ / 2 by ring]
      ring
    dsimp only [Q]
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (h * B * (1 + |t|) * (1 + |v|)) ^ d *
          ‖gaussianMBKernel (Real.exp (-a * t)) ((δ : ℂ) + v * I)‖ * E := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          simpa only [hline, P, d] using hp
        · exact hL
        · exact norm_nonneg _
        · positivity
      _ = _ := by
        rw [hK]
        dsimp only [W, Z]
        simp only [mul_pow]
        ring
  have hcont : Continuous Q := by
    have hp : Continuous (fun v : ℝ => P.eval (Complex.exp
        ((h : ℂ) * ((s + ((δ : ℂ) + v * I)) - β)))) := by
      simp_rw [Polynomial.eval_eq_sum_range]
      fun_prop
    exact (hp.mul (continuous_gaussianMBKernel_line (Real.exp_pos _) hδ)).mul
      (continuous_LSeries_vonMangoldt_line hsδ)
  have hQi : Integrable Q :=
    (hWi.const_mul (B ^ d * E * Z)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hpoint)
  have hnorm : ‖∫ v : ℝ, Q v‖ ≤ (B ^ d * E * Z) * I₀ := by
    calc
      _ ≤ ∫ v : ℝ, ‖Q v‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, (B ^ d * E * Z) * W v :=
        integral_mono hQi.norm (hWi.const_mul _) hpoint
      _ = _ := integral_const_mul _ _
  have heq := primeDampingFilter_eq_euler_integral P σ β a h t δ hδ
    (by dsimp only [δ]; linarith only [hc])
  change primeDampingFilter P σ β a h t = (k : ℂ) * ∫ v : ℝ, Q v at heq
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk]
  calc
    k * ‖∫ v : ℝ, Q v‖ ≤ k * ((B ^ d * E * Z) * I₀) :=
      mul_le_mul_of_nonneg_left hnorm hk
    _ = C₀ * Z := by dsimp only [C₀]; ring
    _ ≤ (C₀ + 1) * Z := mul_le_mul_of_nonneg_right (by linarith) hZ
    _ = _ := by dsimp only [Z, d, δ]; ring

/-- Sufficiently fast contraction forces the literal prime filter to zero,
unconditionally. The threshold comes from the absolute Euler abscissa. -/
theorem tendsto_primeDampingFilter_zero_of_fast_contraction (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β a κ : ℝ) (hσ : σ < 1) (ha : 0 < a) (hκ : 0 < κ)
    (hr : a * (1 - σ) / 2 <
      (1 + (F.filter (fun q => xiZero q ≠ ρ)).card : ℕ) * κ) :
    Tendsto (fun t : ℝ =>
      primeDampingFilter (divisorDampingFilter F ρ β (Real.exp (-κ * t)))
        σ β a (Real.exp (-κ * t)) t) atTop (𝓝 0) := by
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let r := (d : ℝ) * κ - a * (1 - σ) / 2
  have hr0 : 0 < r := sub_pos.mpr hr
  let c := 1 + r / a
  have hc : 1 < c := by dsimp only [c]; positivity
  have hrate : a * (c - σ) / 2 < (d : ℝ) * κ := by
    have he : a * (c - σ) / 2 = a * (1 - σ) / 2 + r / 2 := by
      dsimp only [c]
      field_simp
      ring
    rw [he]
    dsimp only [r] at hr0 ⊢
    linarith only [hr0]
  obtain ⟨C, hC, hb⟩ := exists_primeDampingFilter_arithmetic_bound F ρ σ β c hc (hσ.trans hc)
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (C := C * 2 ^ d) (N := d) (sub_pos.mpr hrate)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hh : Real.exp (-κ * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_mul_nonpos_of_nonneg_of_nonneg hκ.le ht0
  have hpow : (1 + t) ^ d ≤ (2 : ℝ) ^ d * t ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [ht]) d
  calc
    _ ≤ C * Real.exp (-κ * t) ^ d * (1 + |t|) ^ d *
        Real.exp (a * t * (c - σ) / 2) := hb a _ t (Real.exp_pos _).le hh
    _ = C * (1 + t) ^ d *
        Real.exp (-(((d : ℝ) * κ - a * (c - σ) / 2) * t)) := by
      rw [abs_of_nonneg ht0, ← Real.exp_nat_mul,
        show -(((d : ℝ) * κ - a * (c - σ) / 2) * t) =
          (d : ℝ) * (-κ * t) + a * t * (c - σ) / 2 by ring, Real.exp_add]
      ring
    _ ≤ C * (2 ^ d * t ^ d) *
        Real.exp (-(((d : ℝ) * κ - a * (c - σ) / 2) * t)) := by gcongr
    _ = _ := by ring

end GaloisForLFunctions.ExceptionalLayerTheory

#print axioms GaloisForLFunctions.ExceptionalLayerTheory.exists_divisorDampingFilter_euler_bound
#print axioms GaloisForLFunctions.ExceptionalLayerTheory.primeDampingFilter_eq_euler_integral
#print axioms GaloisForLFunctions.ExceptionalLayerTheory.exists_primeDampingFilter_arithmetic_bound
#print axioms GaloisForLFunctions.ExceptionalLayerTheory.tendsto_primeDampingFilter_zero_of_fast_contraction
