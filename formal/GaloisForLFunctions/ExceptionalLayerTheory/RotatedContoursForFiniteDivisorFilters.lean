import GaloisForLFunctions.ExceptionalLayerTheory.ComplexGaussianDamping
import GaloisForLFunctions.ExceptionalLayerTheory.ContourBoundsForFiniteDivisorFilters

/-!
# Rotated contours for finite divisor filters

Complex Gaussian damping keeps the exact exceptional residue. The remaining
regular-line integral retains every spacing factor, including as the damping
angle approaches the imaginary axis at reciprocal height.
-/

open Complex Filter Set Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The complete finite-divisor Mellin weight with complex damping angle `φ`. -/
def rotatedDivisorFilteredMellinWeight (F : Finset XiZeroCopy) (ρ : ℂ)
    (σ β h y φ t : ℝ) (z : ℂ) : ℂ :=
  (divisorDampingFilter F ρ β h).eval (Complex.exp ((h : ℂ) * (z - β))) *
    rotatedGaussianKernel y φ (z - ((σ : ℂ) + t * I))

/-- Rotation is an entire multiplier of the positive-strip Mellin weight. -/
theorem analyticOnNhd_rotatedDivisorFilteredMellinWeight
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β h φ t : ℝ) {y : ℝ} (hy : 0 < y) :
    AnalyticOnNhd ℂ (rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t)
      {z : ℂ | σ < z.re} := by
  have he : rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t =
      fun z => Complex.exp (-(φ : ℂ) * I * (z - ((σ : ℂ) + t * I)) / 2) *
        divisorFilteredMellinWeight F ρ σ β h y t z := by
    funext z
    simp only [rotatedDivisorFilteredMellinWeight, rotatedGaussianKernel,
      divisorFilteredMellinWeight]
    ring
  rw [he]
  apply AnalyticOnNhd.mul
  · intro z _
    exact ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).div_const
      (c := (2 : ℂ))).cexp
  · exact analyticOnNhd_divisorFilteredMellinWeight F ρ σ β h t hy

/-- Rotation preserves continuity on every positive Mellin line. -/
theorem continuous_rotatedGaussianKernel_line {y c : ℝ}
    (hy : 0 < y) (hc : 0 < c) (φ : ℝ) :
    Continuous (fun v : ℝ => rotatedGaussianKernel y φ ((c : ℂ) + v * I)) :=
  (by fun_prop : Continuous (fun v : ℝ =>
    Complex.exp (-(φ : ℂ) * I * ((c : ℂ) + v * I) / 2))).mul
      (continuous_gaussianMBKernel_line hy hc)

/-- Angular dependence of a regular-line error is confined to a kernel moment. -/
theorem exists_rotated_filtered_regular_line_moment_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β c : ℝ) (hc1 : c ≠ 1) (hσc : σ < c)
    (hnz : ∀ v : ℝ, riemannZeta ((c : ℂ) + v * I) ≠ 0)
    (hbound : ∃ E : ℝ, 0 < E ∧ ∀ v : ℝ,
      ‖logDeriv riemannZeta ((c : ℂ) + v * I)‖ ≤ E * (1 + |v|)) :
    ∃ C : ℝ, 0 < C ∧ ∀ y h φ t : ℝ, 0 < y → |φ| < Real.pi / 2 → 0 ≤ h → h ≤ 1 →
      let Q := fun v : ℝ =>
        (divisorDampingFilter F ρ β h).eval
          (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
          rotatedGaussianKernel y φ (((c - σ : ℝ) : ℂ) + v * I) *
            (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))
      Integrable Q ∧ ‖∫ v : ℝ, Q v‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + |t|) ^ (2 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
            y ^ (-(c - σ) / 2) *
              (∫ v : ℝ, ‖rotatedGaussianKernel 1 φ (((c - σ : ℝ) : ℂ) + v * I)‖ *
                (1 + |v|) ^ (2 + (F.filter (fun q => xiZero q ≠ ρ)).card)) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let δ := c - σ
  have hδ : 0 < δ := sub_pos.mpr hσc
  obtain ⟨B, hB, hfilter⟩ := exists_divisorDampingFilter_euler_bound F ρ β c
  obtain ⟨E, hE, hlog⟩ := hbound
  let C₀ := B ^ d * E
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro y h φ t hy hφ hh hh1
  let W : ℝ → ℝ := fun v =>
    ‖rotatedGaussianKernel 1 φ ((δ : ℂ) + v * I)‖ * (1 + |v|) ^ (d + 1)
  have hWi : Integrable W :=
    integrable_norm_rotatedGaussianKernel_mul_pow zero_lt_one hδ hφ (d + 1)
  let J := ∫ v : ℝ, W v
  have hJ : 0 ≤ J := integral_nonneg fun v => by dsimp only [W]; positivity
  dsimp only
  let Q : ℝ → ℂ := fun v =>
    (divisorDampingFilter F ρ β h).eval
      (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
        rotatedGaussianKernel y φ ((δ : ℂ) + v * I) *
          (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))
  let Z := h ^ d * (1 + |t|) ^ (d + 1) * y ^ (-δ / 2)
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hpoint (v : ℝ) : ‖Q v‖ ≤ (B ^ d * E * Z) * W v := by
    have hl : ‖logDeriv riemannZeta ((c : ℂ) + (t + v) * I)‖ ≤
        E * (1 + |t|) * (1 + |v|) := by
      have htv : 1 + |t + v| ≤ (1 + |t|) * (1 + |v|) := by
        nlinarith only [abs_add_le t v, mul_nonneg (abs_nonneg t) (abs_nonneg v)]
      have hhlog := hlog (t + v)
      push_cast at hhlog
      exact hhlog.trans (by nlinarith only [htv, hE])
    have hK : ‖rotatedGaussianKernel y φ ((δ : ℂ) + v * I)‖ =
        y ^ (-δ / 2) * ‖rotatedGaussianKernel 1 φ ((δ : ℂ) + v * I)‖ := by
      rw [norm_rotatedGaussianKernel, norm_rotatedGaussianKernel,
        norm_gaussianMBKernel_line hy, norm_gaussianMBKernel_line zero_lt_one,
        Real.one_rpow, mul_one]
      rw [show -(δ / 2) = -δ / 2 by ring]
      ring
    dsimp only [Q]
    rw [norm_mul, norm_mul, norm_neg]
    calc
      _ ≤ (h * B * (1 + |t|) * (1 + |v|)) ^ d *
          ‖rotatedGaussianKernel y φ ((δ : ℂ) + v * I)‖ *
            (E * (1 + |t|) * (1 + |v|)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (hfilter h t v hh hh1) (norm_nonneg _)
        · exact hl
        · exact norm_nonneg _
        · positivity
      _ = _ := by
        rw [hK]
        dsimp only [W, Z]
        simp only [mul_pow, pow_succ]
        ring
  have hlogcont : Continuous (fun u : ℝ => logDeriv riemannZeta ((c : ℂ) + u * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hs1 : (c : ℂ) + u * I ≠ 1 := by
      intro he
      have hh := congrArg Complex.re he
      simp at hh
      exact hc1 hh
    have ha := analyticOn_riemannZeta ((c : ℂ) + u * I) hs1
    have hd : ContinuousAt (logDeriv riemannZeta) ((c : ℂ) + u * I) :=
      ha.deriv.continuousAt.div ha.continuousAt (hnz u)
    exact hd.comp (f := fun u : ℝ => (c : ℂ) + u * I) (by fun_prop)
  have hcont : Continuous Q := by
    have hp : Continuous (fun v : ℝ => (divisorDampingFilter F ρ β h).eval
        (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β)))) := by
      simp_rw [Polynomial.eval_eq_sum_range]
      fun_prop
    have hl : Continuous (fun v : ℝ => -logDeriv riemannZeta ((c : ℂ) + (t + v) * I)) := by
      have hcc := (hlogcont.comp (show Continuous (fun v : ℝ => t + v) by fun_prop)).neg
      change Continuous (fun v : ℝ =>
        -logDeriv riemannZeta ((c : ℂ) + ((t + v : ℝ) : ℂ) * I)) at hcc
      simpa only [Complex.ofReal_add] using hcc
    exact (hp.mul (continuous_rotatedGaussianKernel_line hy hδ φ)).mul hl
  have hQi : Integrable Q :=
    (hWi.const_mul (B ^ d * E * Z)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hpoint)
  refine ⟨hQi, ?_⟩
  have hnorm : ‖∫ v : ℝ, Q v‖ ≤ C₀ * Z * J := by
    calc
      _ ≤ ∫ v : ℝ, ‖Q v‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, (B ^ d * E * Z) * W v :=
        integral_mono hQi.norm (hWi.const_mul _) hpoint
      _ = _ := by rw [integral_const_mul]; dsimp only [C₀, J]; ring
  refine hnorm.trans ?_
  have he : d + 1 = 2 + (F.filter (fun q => xiZero q ≠ ρ)).card := by dsimp only [d]; omega
  calc
    C₀ * Z * J ≤ (C₀ + 1) * Z * J :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hZ) hJ
    _ = _ := by dsimp only [Z, δ, J, W]; rw [he]; ring

/-- The shifted integral keeps every spacing factor, uniformly as the damping
spacing tends to zero. The logarithmic derivative costs one height power. -/
theorem exists_finite_layer_rotated_filtered_line_moment_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β : ℝ) {θ c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c < 1)
    (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re) :
    ∃ C : ℝ, 0 < C ∧ ∀ y h φ t : ℝ, 0 < y → |φ| < Real.pi / 2 → 0 ≤ h → h ≤ 1 →
      let Q := fun v : ℝ =>
        (divisorDampingFilter F ρ β h).eval
          (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
          rotatedGaussianKernel y φ (((c - σ : ℝ) : ℂ) + v * I) *
            (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))
      Integrable Q ∧ ‖∫ v : ℝ, Q v‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + |t|) ^ (2 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
            y ^ (-(c - σ) / 2) *
              (∫ v : ℝ, ‖rotatedGaussianKernel 1 φ (((c - σ : ℝ) : ℂ) + v * I)‖ *
                (1 + |v|) ^ (2 + (F.filter (fun q => xiZero q ≠ ρ)).card)) :=
  exists_rotated_filtered_regular_line_moment_bound F ρ σ β c hc1.ne hσc
    (finite_layer_regular_line_zeta_ne_zero F (by linarith only [hc]) hc1 hgap hrest havoid)
    (exists_finite_layer_regular_line_logDeriv_bound F hc hc1 hgap hrest havoid)

/-- A sufficiently tall positive-strip rectangle extracts exactly the selected
zero. Pole cancellation and unwanted-zero cancellation are exact. -/
theorem finite_layer_rotated_divisorFilter_rectangle (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β h φ t : ℝ) {θ c y : ℝ} (hy : 0 < y)
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
    ∃ H : ℝ, 0 < H ∧ ∀ T : ℝ, H ≤ T →
      rectIntegral (fun z => rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t z *
        (-logDeriv riemannZeta z)) ((c : ℂ) + (-T : ℝ) * I) ((2 : ℂ) + T * I) =
      -(2 * Real.pi * I * ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ρ) := by
  classical
  obtain ⟨H, C, hH, _, hb⟩ := finite_layer_high_strip_logDeriv_bounds F hc hgap hrest
  have hc0 : 0 < c := by linarith only [hc]
  refine ⟨H + |ρ.im| + 1, by linarith only [hH, abs_nonneg ρ.im], ?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith only [hH, abs_nonneg ρ.im, hT]
  have hTH : H ≤ T := by linarith only [hT, abs_nonneg ρ.im]
  have hρT : |ρ.im| < T := by linarith only [hT, hH]
  let z₁ : ℂ := (c : ℂ) + (-T : ℝ) * I
  let z₂ : ℂ := (2 : ℂ) + T * I
  let g := rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t
  let U : Set ℂ := {z | σ < z.re}
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    intro z hz
    have hh := (Complex.mem_reProdIm.mp hz).1
    have hc2 : c ≤ 2 := by linarith only [hc1]
    have hzI : z.re ∈ Icc c 2 := by simpa [z₁, z₂, uIcc_of_le hc2] using hh
    have hzre : c ≤ z.re := hzI.1
    exact hσc.trans_le hzre
  have hedge : ∀ x v : ℝ, c ≤ x → x ≤ 2 → H ≤ |v| → v ≠ 0 →
      zetaResidueUnit ((x : ℂ) + v * I) ≠ 0 := by
    intro x v hx hx2 hv hv0
    apply (Sieve.zetaResidueUnit_ne_zero_iff ?_).2 (hb x v hx hx2 hv).1
    intro he
    apply hv0
    simpa using congrArg Complex.im he
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₁.im * I) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc c 2 := by
      simpa [z₁, z₂, uIcc_of_le (show c ≤ 2 by linarith only [hc1])] using hx
    simpa [z₁] using hedge x (-T) hx'.1 hx'.2
      (by simpa [abs_of_pos hT0] using hTH) (neg_ne_zero.mpr hT0.ne')
  have htop : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₂.im * I) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc c 2 := by
      simpa [z₁, z₂, uIcc_of_le (show c ≤ 2 by linarith only [hc1])] using hx
    simpa [z₂] using hedge x T hx'.1 hx'.2
      (by simpa [abs_of_pos hT0] using hTH) hT0.ne'
  have hright : ∀ v ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₂.re : ℂ) + v * I) ≠ 0 := by
    intro v _
    have hs1 : (2 : ℂ) + v * I ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      norm_num at hr
    simpa [z₂] using (Sieve.zetaResidueUnit_ne_zero_iff hs1).2
      (riemannZeta_ne_zero_of_one_lt_re (by simp))
  have hleft : ∀ v ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₁.re : ℂ) + v * I) ≠ 0 := by
    intro v _
    have hs1 : (c : ℂ) + v * I ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith only [hr, hc1]
    simpa [z₁] using (Sieve.zetaResidueUnit_ne_zero_iff hs1).2
      (finite_layer_regular_line_zeta_ne_zero F hc0 hc1 hgap hrest havoid v)
  have hρG : zetaResidueUnit ρ = 0 := by
    have hz := (xi_zero_iff_zeta_zero_of_mem_strip (hc0.trans hρc) hρ1).1 hρ
    by_contra hn
    have hr1 : ρ ≠ 1 := by intro he; simp [he] at hρ1
    exact ((Sieve.zetaResidueUnit_ne_zero_iff hr1).1 hn) hz
  have hρmem : ρ ∈ Sieve.zetaResidueUnitClosedRectangleZeros z₁ z₂ := by
    apply Sieve.mem_zetaResidueUnitClosedRectangleZeros.mpr
    refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hρG⟩
    · simpa [z₁, z₂, uIcc_of_le (show c ≤ 2 by linarith only [hc1])] using
        (show ρ.re ∈ Icc c 2 from ⟨hρc.le, by linarith only [hρ1]⟩)
    · simpa [z₁, z₂, uIcc_of_le (show -T ≤ T by linarith only [hT0])] using
        (show ρ.im ∈ Icc (-T) T from abs_le.mp hρT.le)
  have hsum : (∑ w ∈ Sieve.zetaResidueUnitClosedRectangleZeros z₁ z₂,
      ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * g w) =
        ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) * g ρ := by
    apply Finset.sum_eq_single ρ
    · intro w hw hne
      obtain ⟨hwK, hwG⟩ := Sieve.mem_zetaResidueUnitClosedRectangleZeros.mp hw
      have hwre := (Complex.mem_reProdIm.mp hwK).1
      have hwc : c ≤ w.re := by
        have hwI : w.re ∈ Icc c 2 := by
          simpa [z₁, z₂, uIcc_of_le (show c ≤ 2 by linarith only [hc1])] using hwre
        exact hwI.1
      obtain ⟨q, hqF, hqw⟩ := finite_layer_residueUnit_zero_mem F hc0 hgap hrest hwc hwG
      have hkill := divisorDampingFilter_kills F ρ β h hqF (by simpa [hqw] using hne)
      rw [hqw] at hkill
      simp only [g, rotatedDivisorFilteredMellinWeight, hkill, zero_mul, mul_zero]
    · exact fun hnot => (hnot hρmem).elim
  have hpole : g 1 = 0 := by
    dsimp only [g, rotatedDivisorFilteredMellinWeight]
    rw [divisorDampingFilter_pole, zero_mul]
  have hid := rectIntegral_weighted_neg_logDeriv_zeta
    (isOpen_lt continuous_const Complex.continuous_re)
    (analyticOnNhd_rotatedDivisorFilteredMellinWeight F ρ σ β h φ t hy) hsub
    (by simpa [z₁] using hc1) (by simp [z₂])
    (by simpa [z₁] using neg_neg_of_pos hT0) (by simpa [z₂] using hT0)
    hbot htop hright hleft
  change rectIntegral (fun z => g z * (-logDeriv riemannZeta z)) z₁ z₂ = _
  rw [hid]
  change 2 * Real.pi * I * (g 1 -
    ∑ w ∈ Sieve.zetaResidueUnitClosedRectangleZeros z₁ z₂,
      ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * g w) = _
  rw [hpole, hsum]
  ring

/-- The sharp Gamma envelope on a compact Mellin strip, with the full angular
margin retained. Heights avoid all Gamma poles. -/
private theorem exists_rotatedGaussianKernel_strip_envelope (l r : ℝ) :
    ∃ B : ℝ, ∃ N : ℕ, 0 ≤ B ∧ ∀ y φ u v : ℝ, 0 < y → l ≤ u → u ≤ r → 2 ≤ |v| →
      ‖rotatedGaussianKernel y φ ((u : ℂ) + v * I)‖ ≤
        B * (1 + |v|) ^ N * y ^ (-(u / 2)) *
          Real.exp (-(Real.pi / 4 - |φ| / 2) * |v|) := by
  obtain ⟨B, N, hB, hb⟩ := HTGeometry.exists_sharp_bound_norm_Gamma_strip (l / 2) (r / 2)
  refine ⟨B / 2, N, by positivity, ?_⟩
  intro y φ u v hy hlu hur hv
  have hi : |v / 2| = |v| / 2 := by rw [abs_div, abs_two]
  have hΓ := hb (((u / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)
    (by simpa using (show l / 2 ≤ u / 2 by linarith only [hlu]))
    (by simpa using (show u / 2 ≤ r / 2 by linarith only [hur]))
    (by simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, hi] using
        (show 1 ≤ |v| / 2 by linarith only [hv]))
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, hi] at hΓ
  have hp : (|v| / 2) ^ N ≤ (1 + |v|) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith only [abs_nonneg v]) N
  have hphase : φ * v / 2 ≤ |φ| * |v| / 2 := by
    have hh := le_abs_self (φ * v)
    rw [abs_mul] at hh
    linarith only [hh]
  rw [norm_rotatedGaussianKernel, norm_gaussianMBKernel_line hy]
  have him : ((u : ℂ) + v * I).im = v := by simp
  rw [him]
  calc
    _ ≤ Real.exp (|φ| * |v| / 2) *
        (1 / 2 * (B * (1 + |v|) ^ N * Real.exp (-(Real.pi * (|v| / 2) / 2))) *
          y ^ (-(u / 2))) := by
      apply mul_le_mul
      · exact Real.exp_le_exp.mpr hphase
      · gcongr
        exact hΓ.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp hB) (Real.exp_pos _).le)
      · positivity
      · positivity
    _ = _ := by
      rw [show -(Real.pi / 4 - |φ| / 2) * |v| =
        |φ| * |v| / 2 + -(Real.pi * (|v| / 2) / 2) by ring, Real.exp_add]
      ring

/-- Every fixed interior angle leaves enough decay to send the horizontal
edges of the complete finite-layer contour to infinity. -/
theorem tendsto_finite_layer_rotated_divisorFilter_horizontal (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β h φ t e : ℝ) {θ c y : ℝ} (hy : 0 < y)
    (hφ : |φ| < Real.pi / 2)
    (hc : 1 / 2 ≤ c) (hc2 : c ≤ 2) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (he : |e| = 1) :
    Tendsto (fun T : ℝ => ∫ x in c..2,
      rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ((x : ℂ) + (e * T) * I) *
        (-logDeriv riemannZeta ((x : ℂ) + (e * T) * I))) atTop (𝓝 0) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let δ := Real.pi / 4 - |φ| / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hφ]
  obtain ⟨H, E, hH, hE, hlog⟩ := finite_layer_high_strip_logDeriv_bounds F hc hgap hrest
  obtain ⟨B, hB, hfilter⟩ := exists_divisorDampingFilter_strip_bound F ρ β 2
  obtain ⟨A, N, hA, hkernel⟩ := exists_rotatedGaussianKernel_strip_envelope (c - σ) (2 - σ)
  let Y := Real.exp (|Real.log y| * ((2 - σ) / 2))
  let D := (h * B) ^ d * A * (1 + |t|) ^ N * Y * Real.exp (δ * |t|) * E
  let k := d + N + 1
  have hD : 0 ≤ D := by dsimp only [D, Y]; positivity
  have hpt (x v : ℝ) (hx : c ≤ x) (hx2 : x ≤ 2) (hv : H + |t| + 2 ≤ |v|) :
      ‖rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ((x : ℂ) + v * I) *
        (-logDeriv riemannZeta ((x : ℂ) + v * I))‖ ≤
        D * (1 + |v|) ^ k * Real.exp (-(δ * |v|)) := by
    have hvH : H ≤ |v| := by linarith only [hv, abs_nonneg t]
    have htri := abs_add_le (v - t) t
    rw [sub_add_cancel] at htri
    have hvt : 2 ≤ |v - t| := by linarith only [hv, htri, hH]
    have hx0 : 0 ≤ x := by linarith only [hc, hx]
    have hxs : 0 < x - σ := sub_pos.mpr (hσc.trans_le hx)
    have hp := hfilter x h 0 v (by rwa [abs_of_nonneg hx0]) hh hh1
    simp only [abs_zero, add_zero, mul_one, zero_add] at hp
    have hk := hkernel y φ (x - σ) (v - t) hy
      (by linarith only [hx]) (by linarith only [hx2]) hvt
    have hdiff : (x : ℂ) + v * I - ((σ : ℂ) + t * I) =
        ((x - σ : ℝ) : ℂ) + ((v - t : ℝ) : ℂ) * I := by push_cast; ring
    have hpoly : (1 + |v - t|) ^ N ≤ (1 + |t|) ^ N * (1 + |v|) ^ N := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have htri' : |v - t| ≤ |v| + |t| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le v (-t)
      nlinarith only [htri', mul_nonneg (abs_nonneg v) (abs_nonneg t)]
    have hyb : y ^ (-((x - σ) / 2)) ≤ Y := by
      rw [Real.rpow_def_of_pos hy]
      apply Real.exp_le_exp.mpr
      have hn := neg_le_abs (Real.log y)
      have hnon := abs_nonneg (Real.log y)
      nlinarith only [hn, hnon, hxs, hx2]
    have hexp : Real.exp (-(δ * |v - t|)) ≤
        Real.exp (δ * |t|) * Real.exp (-(δ * |v|)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hhtri := mul_le_mul_of_nonneg_left htri hδ.le
      linarith only [hhtri]
    rw [rotatedDivisorFilteredMellinWeight, norm_mul, norm_mul, norm_neg, hdiff]
    calc
      _ ≤ (h * B * (1 + |v|)) ^ d *
          (A * ((1 + |t|) ^ N * (1 + |v|) ^ N) * Y *
            (Real.exp (δ * |t|) * Real.exp (-(δ * |v|)))) * (E * (1 + |v|)) := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact hp
          · exact hk.trans (mul_le_mul
              (mul_le_mul (mul_le_mul_of_nonneg_left hpoly hA) hyb
                (Real.rpow_nonneg hy.le _) (by positivity)) hexp
              (Real.exp_pos _).le (by positivity))
          · exact norm_nonneg _
          · positivity
        · exact (hlog x v hx hx2 hvH).2
        · exact norm_nonneg _
        · positivity
      _ = _ := by
        dsimp only [D, k]
        rw [pow_add, pow_add, pow_one]
        simp only [mul_pow]
        ring
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (C := D * (2 - c) * 2 ^ k) (N := k) hδ
  filter_upwards [eventually_ge_atTop (H + |t| + 2)] with T hT
  have hT1 : 1 ≤ T := by linarith only [hT, hH, abs_nonneg t]
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  have heT : |e * T| = T := by rw [abs_mul, he, one_mul, abs_of_nonneg hT0]
  have hb : ∀ x ∈ uIoc c 2,
      ‖rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ((x : ℂ) + (e * T) * I) *
        (-logDeriv riemannZeta ((x : ℂ) + (e * T) * I))‖ ≤
        D * (1 + T) ^ k * Real.exp (-(δ * T)) := by
    intro x hx
    rw [uIoc_of_le hc2] at hx
    have hv : H + |t| + 2 ≤ |e * T| := by rwa [heT]
    simpa only [Complex.ofReal_mul, heT] using hpt x (e * T) hx.1.le hx.2 hv
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [abs_of_nonneg (sub_nonneg.mpr hc2)] at hi
  refine hi.trans ?_
  have hp : (1 + T) ^ k ≤ (2 : ℝ) ^ k * T ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hT1]) k
  calc
    _ ≤ D * ((2 : ℝ) ^ k * T ^ k) * Real.exp (-(δ * T)) * (2 - c) := by gcongr
    _ = _ := by ring

private theorem rotatedDivisorFilteredMellinWeight_shift (F : Finset XiZeroCopy) (ρ : ℂ)
    (σ β h y φ t c v : ℝ) :
    rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ((c : ℂ) + (t + v) * I) =
      (divisorDampingFilter F ρ β h).eval
        (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
          rotatedGaussianKernel y φ (((c - σ : ℝ) : ℂ) + v * I) := by
  unfold rotatedDivisorFilteredMellinWeight
  congr 2
  push_cast
  ring

private theorem integrable_rotated_filtered_line_of_shifted (F : Finset XiZeroCopy) (ρ : ℂ)
    (σ β h y φ t c : ℝ)
    (hi : Integrable (fun v : ℝ =>
      (divisorDampingFilter F ρ β h).eval
        (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
          rotatedGaussianKernel y φ (((c - σ : ℝ) : ℂ) + v * I) *
            (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I)))) :
    Integrable (fun v : ℝ => rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t
      ((c : ℂ) + v * I) * (-logDeriv riemannZeta ((c : ℂ) + v * I))) := by
  have his : Integrable (fun v : ℝ => rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t
      ((c : ℂ) + (t + v) * I) * (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))) := by
    simpa only [rotatedDivisorFilteredMellinWeight_shift] using hi
  convert his.comp_add_right (-t) using 1
  funext v
  simp only [Complex.ofReal_add, Complex.ofReal_neg]
  have he : (t : ℂ) + (v + -t) = v := by ring
  rw [he]

private theorem rotated_filtered_euler_line_integrable (F : Finset XiZeroCopy) (ρ : ℂ)
    (σ β h φ t : ℝ) {y : ℝ} (hy : 0 < y) (hφ : |φ| < Real.pi / 2) (hσ : σ < 2)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (fun v : ℝ => rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t
      ((2 : ℂ) + v * I) * (-logDeriv riemannZeta ((2 : ℂ) + v * I))) := by
  let E : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (2 : ℝ)
  have hE : 0 ≤ E := tsum_nonneg fun n => div_nonneg
    ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hb : ∃ B : ℝ, 0 < B ∧ ∀ v : ℝ,
      ‖logDeriv riemannZeta ((2 : ℂ) + v * I)‖ ≤ B * (1 + |v|) := by
    refine ⟨E + 1, by positivity, fun v => ?_⟩
    have hn := norm_LSeries_vonMangoldt_le (s := (2 : ℂ) + v * I) (by simp)
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simp),
      neg_div, ← logDeriv_apply, norm_neg] at hn
    have hn' : ‖logDeriv riemannZeta ((2 : ℂ) + v * I)‖ ≤ E := by simpa [E] using hn
    exact hn'.trans (by nlinarith only [hE, abs_nonneg v, mul_nonneg hE (abs_nonneg v)])
  obtain ⟨C, _, hC⟩ := exists_rotated_filtered_regular_line_moment_bound F ρ σ β 2 (by norm_num) hσ
    (fun v => riemannZeta_ne_zero_of_one_lt_re (by simp)) hb
  exact integrable_rotated_filtered_line_of_shifted F ρ σ β h y φ t 2 (hC y h φ t hy hφ hh hh1).1

/-- Shifting the full positive-strip contour leaves one exact exceptional
residue. No Gamma pole lies between the two vertical lines. -/
theorem finite_layer_rotated_divisorFilter_line_shift (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β h φ t : ℝ) {θ c y : ℝ} (hy : 0 < y) (hφ : |φ| < Real.pi / 2)
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ v : ℝ, rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ((2 : ℂ) + v * I) *
        (-logDeriv riemannZeta ((2 : ℂ) + v * I))) -
      (∫ v : ℝ, rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ((c : ℂ) + v * I) *
        (-logDeriv riemannZeta ((c : ℂ) + v * I))) =
      -(2 * Real.pi * ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ρ) := by
  let G : ℂ → ℂ := fun z => rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t z *
    (-logDeriv riemannZeta z)
  have hc2 : c ≤ 2 := by linarith only [hc1]
  have hir := rotated_filtered_euler_line_integrable F ρ σ β h φ t hy hφ (hσc.trans_le hc2) hh hh1
  obtain ⟨C, _, hb⟩ := exists_finite_layer_rotated_filtered_line_moment_bound F ρ σ β hc hc1
    hσc hgap hrest havoid
  have hil := integrable_rotated_filtered_line_of_shifted F ρ σ β h y φ t c (hb y h φ t hy hφ hh hh1).1
  have hright := intervalIntegral_tendsto_integral hir tendsto_neg_atTop_atBot tendsto_id
  have hleft := intervalIntegral_tendsto_integral hil tendsto_neg_atTop_atBot tendsto_id
  have hbottom := tendsto_finite_layer_rotated_divisorFilter_horizontal F ρ σ β h φ t (-1)
    hy hφ hc hc2 hσc hgap hrest hh hh1 (by norm_num)
  have htop := tendsto_finite_layer_rotated_divisorFilter_horizontal F ρ σ β h φ t 1
    hy hφ hc hc2 hσc hgap hrest hh hh1 (by norm_num)
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  have hlimit' : Tendsto (fun T : ℝ => rectIntegral G
      ((c : ℂ) + (-T : ℝ) * I) ((2 : ℂ) + T * I)) atTop
      (𝓝 (I • (∫ v : ℝ, G ((2 : ℂ) + v * I)) -
        I • (∫ v : ℝ, G ((c : ℂ) + v * I)))) := by
    simpa [rectIntegral, G] using hlimit
  obtain ⟨H, _, hrect⟩ := finite_layer_rotated_divisorFilter_rectangle F ρ σ β h φ t hy
    hc hc1 hσc hgap hrest havoid hρc hρ1 hρ
  have hevent : (fun T : ℝ => rectIntegral G
      ((c : ℂ) + (-T : ℝ) * I) ((2 : ℂ) + T * I)) =ᶠ[atTop]
      (fun _ => -(2 * Real.pi * I * ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ρ)) := by
    filter_upwards [eventually_ge_atTop H] with T hT
    exact hrect T hT
  have hid := tendsto_nhds_unique (hlimit'.congr' hevent) tendsto_const_nhds
  apply mul_left_cancel₀ Complex.I_ne_zero
  calc
    I * ((∫ v : ℝ, G ((2 : ℂ) + v * I)) - ∫ v : ℝ, G ((c : ℂ) + v * I)) =
        I • (∫ v : ℝ, G ((2 : ℂ) + v * I)) -
          I • (∫ v : ℝ, G ((c : ℂ) + v * I)) := by rw [mul_sub]; rfl
    _ = _ := hid
    _ = _ := by ring

/-- The literal prime filter equals the selected exceptional mode plus the
complete vertical integral on any regular positive Mellin line below it. -/
theorem rotatedPrimeDampingFilter_eq_selected_mode_add_line (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β a h φ t : ℝ) (hφ : |φ| < Real.pi / 2) {θ c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h) σ β a h φ t =
      -((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        rotatedDivisorFilteredMellinWeight F ρ σ β h (Real.exp (-a * t)) φ t ρ +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, rotatedDivisorFilteredMellinWeight F ρ σ β h (Real.exp (-a * t)) φ t
          ((c : ℂ) + v * I) * (-logDeriv riemannZeta ((c : ℂ) + v * I)) := by
  let y := Real.exp (-a * t)
  let G : ℂ → ℂ := fun z => rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t z *
    (-logDeriv riemannZeta z)
  let k : ℝ := 1 / (2 * Real.pi)
  have hσ2 : σ < 2 := by linarith only [hσc, hc1]
  have hp : rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h) σ β a h φ t =
      (k : ℂ) * ∫ v : ℝ, G ((2 : ℂ) + v * I) := by
    rw [rotatedPrimeDampingFilter_eq_euler_integral _ σ β a h φ t (2 - σ)
      (sub_pos.mpr hσ2) hφ (by linarith)]
    have hfun : (fun v : ℝ =>
        (divisorDampingFilter F ρ β h).eval
          (Complex.exp ((h : ℂ) * (((σ : ℂ) + t * I +
            (((2 - σ : ℝ) : ℂ) + v * I)) - β))) *
          rotatedGaussianKernel y φ (((2 - σ : ℝ) : ℂ) + v * I) *
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((σ : ℂ) + t * I + (((2 - σ : ℝ) : ℂ) + v * I))) =
        (fun v : ℝ => G ((2 : ℂ) + ((v + t : ℝ) : ℂ) * I)) := by
      funext v
      have hz : (σ : ℂ) + t * I + (((2 - σ : ℝ) : ℂ) + v * I) =
          (2 : ℂ) + (t + v) * I := by push_cast; ring
      have he : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((2 : ℂ) + (t + v) * I) = -logDeriv riemannZeta ((2 : ℂ) + (t + v) * I) := by
        rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simp),
          logDeriv_apply, neg_div]
      rw [hz, he]
      have hvt : ((v + t : ℝ) : ℂ) = (t : ℂ) + v := by push_cast; ring
      rw [hvt]
      dsimp only [G]
      exact congrArg (fun z : ℂ => z * (-logDeriv riemannZeta ((2 : ℂ) + (t + v) * I)))
        (rotatedDivisorFilteredMellinWeight_shift F ρ σ β h y φ t 2 v).symm
    change (k : ℂ) * ∫ v : ℝ, _ = _
    rw [hfun, integral_add_right_eq_self (fun v : ℝ => G ((2 : ℂ) + v * I)) t]
  have hs := finite_layer_rotated_divisorFilter_line_shift F ρ σ β h φ t (Real.exp_pos (-a * t)) hφ
    hc hc1 hσc hgap hrest havoid hρc hρ1 hρ hh hh1
  change (∫ v : ℝ, G ((2 : ℂ) + v * I)) - (∫ v : ℝ, G ((c : ℂ) + v * I)) =
    -(2 * Real.pi * ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
      rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ρ) at hs
  have hk : (k : ℂ) * (2 * Real.pi : ℂ) = 1 := by
    dsimp only [k]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hhprod := congrArg (fun z : ℂ => (k : ℂ) * z) hs
  rw [mul_sub] at hhprod
  have hm : (k : ℂ) * -(2 * Real.pi * ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
      rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ρ) =
      -((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ρ := by
    calc
      _ = -((k : ℂ) * (2 * Real.pi)) *
          (((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
            rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ρ) := by ring
      _ = _ := by rw [hk]; ring
  rw [hm] at hhprod
  rw [hp]
  linear_combination hhprod

/-- The complete regular-line remainder costs only polynomial height as the
angle approaches the imaginary axis. Every spacing factor survives. -/
theorem exists_finite_layer_boundary_filtered_line_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β : ℝ) {θ c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c < 1)
    (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧ ∀ y h t : ℝ, 0 < y → 1 ≤ t → 0 ≤ h → h ≤ 1 →
      let Q := fun v : ℝ =>
        (divisorDampingFilter F ρ β h).eval
          (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
          rotatedGaussianKernel y (boundaryDampingAngle t) (((c - σ : ℝ) : ℂ) + v * I) *
            (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))
      Integrable Q ∧ ‖∫ v : ℝ, Q v‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) * t ^ N *
          y ^ (-(c - σ) / 2) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let k := d + 1
  have hk : 2 + (F.filter (fun q => xiZero q ≠ ρ)).card = k := by dsimp only [k, d]; omega
  obtain ⟨B, hB, hb⟩ := exists_finite_layer_rotated_filtered_line_moment_bound
    F ρ σ β hc hc1 hσc hgap hrest havoid
  obtain ⟨A, m, hA, ha⟩ := exists_rotatedGaussianKernel_boundary_moment_bound
    (sub_pos.mpr hσc) k
  refine ⟨B * (A + 1) * 2 ^ k, k + m, by positivity, ?_⟩
  intro y h t hy ht hh hh1
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hφ : |boundaryDampingAngle t| < Real.pi / 2 := by
    rw [abs_boundaryDampingAngle ht]
    linarith only [one_div_pos.mpr ht0]
  obtain ⟨hi, hb'⟩ := hb y h (boundaryDampingAngle t) t hy hφ hh hh1
  rw [hk] at hb'
  refine ⟨hi, hb'.trans ?_⟩
  have hm := ha t (boundaryDampingAngle t) ht (le_of_eq (abs_boundaryDampingAngle ht))
  have hp : (1 + |t|) ^ k ≤ (2 : ℝ) ^ k * t ^ k := by
    rw [abs_of_pos ht0, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [ht]) k
  calc
    _ ≤ B * h ^ d * (1 + |t|) ^ k * y ^ (-(c - σ) / 2) * (A * t ^ m) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ B * h ^ d * ((2 : ℝ) ^ k * t ^ k) * y ^ (-(c - σ) / 2) *
        ((A + 1) * t ^ m) := by gcongr; linarith
    _ = _ := by rw [pow_add]; ring

/-- Boundary rotation retains the complete finite-divisor error with no
fixed vertical Gamma loss and no restriction on exponential damping speed. -/
theorem exists_boundaryPrimeDampingFilter_spacing_preserving_error_bound
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β : ℝ) {θ c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧ ∀ a h t : ℝ, 1 ≤ t → 0 ≤ h → h ≤ 1 →
      ‖rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h) σ β a h (boundaryDampingAngle t) t +
        ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
          rotatedDivisorFilteredMellinWeight F ρ σ β h (Real.exp (-a * t)) (boundaryDampingAngle t) t ρ‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) * t ^ N *
          Real.exp (a * t * (c - σ) / 2) := by
  obtain ⟨B, N, hB, hb⟩ := exists_finite_layer_boundary_filtered_line_bound F ρ σ β
    hc hc1 hσc hgap hrest havoid
  let k : ℝ := 1 / (2 * Real.pi)
  have hk : 0 < k := by dsimp only [k]; positivity
  refine ⟨k * B, N, by positivity, ?_⟩
  intro a h t ht hh hh1
  let y := Real.exp (-a * t)
  let φ := boundaryDampingAngle t
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hφ : |φ| < Real.pi / 2 := by
    rw [show φ = boundaryDampingAngle t from rfl, abs_boundaryDampingAngle ht]
    linarith only [one_div_pos.mpr ht0]
  let G : ℂ → ℂ := fun z => rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t z *
    (-logDeriv riemannZeta z)
  let Q : ℝ → ℂ := fun v =>
    (divisorDampingFilter F ρ β h).eval
      (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
        rotatedGaussianKernel y φ (((c - σ : ℝ) : ℂ) + v * I) *
          (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))
  have htran : (∫ v : ℝ, G ((c : ℂ) + v * I)) = ∫ v : ℝ, Q v := by
    calc
      _ = ∫ v : ℝ, G ((c : ℂ) + ((v + t : ℝ) : ℂ) * I) :=
        (integral_add_right_eq_self (fun v : ℝ => G ((c : ℂ) + v * I)) t).symm
      _ = _ := by
        apply integral_congr_ae
        refine Eventually.of_forall fun v => ?_
        have hvt : ((v + t : ℝ) : ℂ) = (t : ℂ) + v := by push_cast; ring
        change G ((c : ℂ) + ((v + t : ℝ) : ℂ) * I) = Q v
        rw [hvt]
        dsimp only [G, Q]
        rw [rotatedDivisorFilteredMellinWeight_shift]
  have heq := rotatedPrimeDampingFilter_eq_selected_mode_add_line F ρ σ β a h φ t hφ
    hc hc1 hσc hgap hrest havoid hρc hρ1 hρ hh hh1
  have heq' : rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h) σ β a h φ t +
      ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ρ =
      (k : ℂ) * ∫ v : ℝ, G ((c : ℂ) + v * I) := by
    change _ = _ at heq
    linear_combination heq
  change ‖rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h) σ β a h φ t +
      ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ρ‖ ≤ _
  rw [heq', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, htran]
  have hnorm := (hb y h t (Real.exp_pos _) ht hh hh1).2
  have hyexp : y ^ (-(c - σ) / 2) = Real.exp (a * t * (c - σ) / 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [hyexp] at hnorm
  exact (mul_le_mul_of_nonneg_left hnorm hk.le).trans_eq (by ring)

#print axioms finite_layer_rotated_divisorFilter_rectangle
#print axioms tendsto_finite_layer_rotated_divisorFilter_horizontal
#print axioms finite_layer_rotated_divisorFilter_line_shift
#print axioms rotatedPrimeDampingFilter_eq_selected_mode_add_line
#print axioms exists_finite_layer_boundary_filtered_line_bound
#print axioms exists_boundaryPrimeDampingFilter_spacing_preserving_error_bound

end GaloisForLFunctions.ExceptionalLayerTheory
