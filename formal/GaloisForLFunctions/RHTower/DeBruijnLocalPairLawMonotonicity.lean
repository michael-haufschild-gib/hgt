import GaloisForLFunctions.RHTower.KiKimLeeFiniteness
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.RHTower.DeBruijnNewmanConstant

/-!
# The local pair law and vertical monotonicity of `|H_t|`

For an even, real, order-one entire `f` and a conjugate pair of zeros `ζ, ζ̄`,

`(|ζ−(z+iλ)||ζ̄−(z+iλ)|)² − (|ζ−(z−iλ)||ζ̄−(z−iλ)|)² = 8 Im z · λ ((Re ζ − Re z)² + (Im z)² + λ² − (Im ζ)²)`,

so the pair never obstructs the growth of `|f|` from `z − iλ` to `z + iλ` as soon as
`(Im ζ)² ≤ (Re ζ − Re z)² + (Im z)² + λ²` (`norm_sub_shift_le_local`): zeros at horizontal distance
at least `|Im ζ|` are harmless, whatever the size of the strip. Consequently `y ↦ |f(x + iy)|` is
nondecreasing on `y ≥ 0` whenever every zero satisfies `(Im ζ)² ≤ (Re ζ − x)²`
(`monotoneOn_norm_vertical`).

For the de Bruijn–Newman deformation this gives:
* for every `t > 0`, `y ↦ |H_t(x + iy)|` is nondecreasing on `y ≥ 0` at all large `|x|`
  (`exists_monotoneOn_norm_riemannHeat_vertical`, from the Ki–Kim–Lee reality at large height);
* the Riemann hypothesis is exactly this monotonicity at every `x` for every `t > 0`
  (`riemannHypothesis_iff_forall_monotoneOn_norm_riemannHeat`).
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower.DeBruijn

noncomputable section

variable {f : ℂ → ℂ}

/-- **The local pair inequality.** -/
theorem pair_dist_le_local {z ζ : ℂ} {lam : ℝ} (hlam : 0 ≤ lam) (hz : 0 ≤ z.im)
    (hb : ζ.im ^ 2 ≤ (ζ.re - z.re) ^ 2 + z.im ^ 2 + lam ^ 2) :
    ‖ζ - (z - lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z - lam * I)‖ ≤
      ‖ζ - (z + lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z + lam * I)‖ := by
  set X := ζ.re - z.re
  set Y := z.im
  set b := ζ.im
  have hsq : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e1 : ‖ζ - (z - lam * I)‖ ^ 2 = X ^ 2 + (b - Y + lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have e2 : ‖(starRingEnd ℂ) ζ - (z - lam * I)‖ ^ 2 = X ^ 2 + (b + Y - lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have e3 : ‖ζ - (z + lam * I)‖ ^ 2 = X ^ 2 + (b - Y - lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have e4 : ‖(starRingEnd ℂ) ζ - (z + lam * I)‖ ^ 2 = X ^ 2 + (b + Y + lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have hdiff : (‖ζ - (z + lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z + lam * I)‖) ^ 2 -
      (‖ζ - (z - lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z - lam * I)‖) ^ 2 =
      8 * Y * lam * (X ^ 2 + Y ^ 2 + lam ^ 2 - b ^ 2) := by
    rw [mul_pow, mul_pow, e1, e2, e3, e4]
    ring
  have hnn : 0 ≤ 8 * Y * lam * (X ^ 2 + Y ^ 2 + lam ^ 2 - b ^ 2) := by
    have : 0 ≤ X ^ 2 + Y ^ 2 + lam ^ 2 - b ^ 2 := by linarith
    positivity
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp (by linarith)

theorem norm_weierstrassE1_pair_le_local {ζ z : ℂ} (hζ : ζ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (hz : 0 ≤ z.im) (hb : ζ.im ^ 2 ≤ (ζ.re - z.re) ^ 2 + z.im ^ 2 + lam ^ 2) :
    ‖weierstrassE1 ((z - lam * I) / ζ)‖ * ‖weierstrassE1 ((z - lam * I) / (starRingEnd ℂ) ζ)‖ ≤
      ‖weierstrassE1 ((z + lam * I) / ζ)‖ *
        ‖weierstrassE1 ((z + lam * I) / (starRingEnd ℂ) ζ)‖ := by
  rw [norm_weierstrassE1_pair hζ, norm_weierstrassE1_pair hζ]
  have hre : (z - lam * I).re = (z + lam * I).re := by simp
  rw [hre]
  have hζn : 0 < ‖ζ‖ ^ 2 := by have := norm_pos_iff.mpr hζ; positivity
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
    (pair_dist_le_local hlam hz hb) hζn.le) (Real.exp_pos _).le

theorem tsum_nonneg_of_involution {ι : Type*} {φ : ι → ℝ} (hφ : Summable φ)
    (σ : ι ≃ ι) (hpair : ∀ q, 0 ≤ φ q + φ (σ q)) : 0 ≤ ∑' q, φ q := by
  have hφσ : Summable (fun q => φ (σ q)) := σ.summable_iff.mpr hφ
  have hsplit : ∑' q, (φ q + φ (σ q)) = (∑' q, φ q) + ∑' q, φ (σ q) := hφ.tsum_add hφσ
  have hσeq : ∑' q, φ (σ q) = ∑' q, φ q := σ.tsum_eq φ
  have h : 0 ≤ ∑' q, (φ q + φ (σ q)) := tsum_nonneg hpair
  linarith

/-- **The local shift comparison.** If every zero `ζ` of `f` satisfies
`(Im ζ)² ≤ (Re ζ − Re z)² + (Im z)² + λ²`, then `‖f(z − iλ)‖ ≤ ‖f(z + iλ)‖`. -/
theorem norm_sub_shift_le_local {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {lam : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 0 ≤ z.im)
    (hloc : ∀ ζ, f ζ = 0 → ζ.im ^ 2 ≤ (ζ.re - z.re) ^ 2 + z.im ^ 2 + lam ^ 2)
    (hu : f (z - lam * I) ≠ 0) (hv : f (z + lam * I) ≠ 0) :
    ‖f (z - lam * I)‖ ≤ ‖f (z + lam * I)‖ := by
  have hsum := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hane := zeroCopyPoint_ne_zero hf hf0
  rw [norm_eq_exp_tsum hC hf hf0 heven hbound hu, norm_eq_exp_tsum hC hf hf0 heven hbound hv]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hsu := summable_log_norm_weierstrassE1 hsum (z - lam * I)
  have hsv := summable_log_norm_weierstrassE1 hsum (z + lam * I)
  rw [← sub_nonneg, ← hsv.tsum_sub hsu]
  refine tsum_nonneg_of_involution (hsv.sub hsu) (zeroCopyConj hf hconj) (fun q => ?_)
  rw [zeroCopyPoint_conj hf hconj q]
  set ζ := zeroCopyPoint f q
  have hζ := hane q
  have hζz : f ζ = 0 := apply_zeroCopyPoint hf q
  have hne : ∀ w : ℂ, f w ≠ 0 → ∀ ξ : ℂ, f ξ = 0 → ξ ≠ 0 → 0 < ‖weierstrassE1 (w / ξ)‖ := by
    intro w hw ξ hξ hξ0
    refine norm_pos_iff.mpr (weierstrassE1_ne_zero ?_)
    intro h1
    rw [div_eq_one_iff_eq hξ0] at h1
    exact hw (h1 ▸ hξ)
  have hζcz : f ((starRingEnd ℂ) ζ) = 0 := by rw [hconj, hζz, map_zero]
  have hζc0 : (starRingEnd ℂ) ζ ≠ 0 := (map_ne_zero _).mpr hζ
  have key := norm_weierstrassE1_pair_le_local hζ hlam hz (hloc ζ hζz)
  have p1 := hne _ hu ζ hζz hζ
  have p2 := hne _ hu _ hζcz hζc0
  have p3 := hne _ hv ζ hζz hζ
  have p4 := hne _ hv _ hζcz hζc0
  have hlog := Real.log_le_log (mul_pos p1 p2) key
  rw [Real.log_mul p1.ne' p2.ne', Real.log_mul p3.ne' p4.ne'] at hlog
  linarith

/-- **Vertical monotonicity.** If every zero of `f` satisfies `(Im ζ)² ≤ (Re ζ − x)²`, then
`y ↦ ‖f(x + iy)‖` is nondecreasing on `y ≥ 0`. -/
theorem monotoneOn_norm_vertical {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {x : ℝ} (hloc : ∀ ζ, f ζ = 0 → ζ.im ^ 2 ≤ (ζ.re - x) ^ 2) :
    MonotoneOn (fun y : ℝ => ‖f ((x : ℂ) + I * y)‖) (Ici 0) := by
  intro y₁ hy₁ y₂ hy₂ h12
  simp only [mem_Ici] at hy₁ hy₂
  rcases eq_or_lt_of_le h12 with h | h
  · rw [h]
  simp only
  by_cases hz1 : f ((x : ℂ) + I * y₁) = 0
  · rw [hz1, norm_zero]; exact norm_nonneg _
  have hz2 : f ((x : ℂ) + I * y₂) ≠ 0 := by
    intro h0
    have := hloc _ h0
    simp at this
    nlinarith
  set z : ℂ := (x : ℂ) + I * ((y₁ + y₂) / 2 : ℝ) with hz
  set lam : ℝ := (y₂ - y₁) / 2 with hlam
  have hzm : z - lam * I = (x : ℂ) + I * y₁ := by rw [hz, hlam]; push_cast; ring
  have hzp : z + lam * I = (x : ℂ) + I * y₂ := by rw [hz, hlam]; push_cast; ring
  have hzre : z.re = x := by simp [hz]
  have hzim : z.im = (y₁ + y₂) / 2 := by simp [hz]
  have h := norm_sub_shift_le_local hC hf hf0 heven hconj hbound (lam := lam) (z := z)
    (by rw [hlam]; linarith) (by rw [hzim]; linarith)
    (fun ζ hζ => by
      have := hloc ζ hζ
      rw [hzre, hzim]
      nlinarith [sq_nonneg ((y₁ + y₂) / 2), sq_nonneg lam])
    (by rw [hzm]; exact hz1) (by rw [hzp]; exact hz2)
  rwa [hzm, hzp] at h

/-! ## The de Bruijn–Newman deformation -/

theorem riemannHeat_analytic {t : ℝ} (ht : 0 ≤ t) : AnalyticOnNhd ℂ (riemannHeat t) univ :=
  (differentiable_riemannHeat ht).differentiableOn.analyticOnNhd isOpen_univ

theorem riemannHeat_conj {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    riemannHeat t ((starRingEnd ℂ) z) = (starRingEnd ℂ) (riemannHeat t z) :=
  (riemannKernel_superExp.mul_exp_sq ht).cosTransform_conj z

theorem monotoneOn_norm_riemannHeat_vertical {t x : ℝ} (ht : 0 ≤ t)
    (hloc : ∀ ζ, riemannHeat t ζ = 0 → ζ.im ^ 2 ≤ (ζ.re - x) ^ 2) :
    MonotoneOn (fun y : ℝ => ‖riemannHeat t ((x : ℂ) + I * y)‖) (Ici 0) := by
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq ht).exists_envelope
  exact monotoneOn_norm_vertical hC (riemannHeat_analytic ht) (riemannHeat_zero_ne ht)
    (riemannHeat_neg ht) (riemannHeat_conj ht) hbound hloc

/-- **Vertical monotonicity at large height.** For every `t > 0`, `y ↦ |H_t(x + iy)|` is
nondecreasing on `y ≥ 0` for all large `|x|`. -/
theorem exists_monotoneOn_norm_riemannHeat_vertical {t : ℝ} (ht : 0 < t) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ |x| →
      MonotoneOn (fun y : ℝ => ‖riemannHeat t ((x : ℂ) + I * y)‖) (Ici 0) := by
  obtain ⟨X₁, hX₁⟩ := exists_riemannHeat_zeros_real ht
  refine ⟨|X₁| + 1, fun x hx => monotoneOn_norm_riemannHeat_vertical ht.le fun ζ hζ => ?_⟩
  by_cases him : ζ.im = 0
  · rw [him]; nlinarith [sq_nonneg (ζ.re - x)]
  have hre : |ζ.re| < X₁ := by
    by_contra h
    exact him (hX₁ ζ hζ (not_lt.mp h))
  have him2 : ζ.im ^ 2 ≤ 1 / 4 :=
    (riemannHeat_zeros_im_sq_le ht hζ).trans (max_le (by linarith) (by norm_num))
  have hdist : 1 ≤ |ζ.re - x| := by
    have h1 := abs_sub_abs_le_abs_sub x ζ.re
    rw [abs_sub_comm] at h1
    linarith [le_abs_self X₁]
  have : 1 ≤ (ζ.re - x) ^ 2 := by nlinarith [sq_abs (ζ.re - x), abs_nonneg (ζ.re - x)]
  linarith

/-- **The Riemann hypothesis as vertical monotonicity along the flow.** RH holds iff for every
heat time `t > 0` and every `x`, `y ↦ |H_t(x + iy)|` is nondecreasing on `y ≥ 0`. -/
theorem riemannHypothesis_iff_forall_monotoneOn_norm_riemannHeat :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      MonotoneOn (fun y : ℝ => ‖riemannHeat t ((x : ℂ) + I * y)‖) (Ici 0) := by
  rw [riemannHypothesis_iff_newmanConstant_eq_zero]
  constructor
  · intro h0 t ht x
    have hmem := (mem_realRootedTimes_iff ht.le).mpr (by rw [h0]; exact ht.le)
    exact monotoneOn_norm_riemannHeat_vertical ht.le fun ζ hζ => by
      rw [hmem.2 ζ hζ]; nlinarith [sq_nonneg (ζ.re - x)]
  · intro hmono
    refine le_antisymm ?_ newmanConstant_nonneg
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add, ← mem_realRootedTimes_iff hε.le]
    refine ⟨hε.le, fun ζ hζ => ?_⟩
    by_contra him
    -- move the zero to the upper half-plane
    obtain ⟨w, hw, hwim⟩ : ∃ w : ℂ, riemannHeat ε w = 0 ∧ 0 < w.im := by
      rcases lt_or_gt_of_ne him with h | h
      · refine ⟨(starRingEnd ℂ) ζ, ?_, by simpa using h⟩
        rw [riemannHeat_conj hε.le, hζ, map_zero]
      · exact ⟨ζ, hζ, h⟩
    -- `H_ε` vanishes on the vertical segment below `w`
    have hseg : ∀ y : ℝ, 0 ≤ y → y ≤ w.im → riemannHeat ε ((w.re : ℂ) + I * y) = 0 := by
      intro y hy0 hyw
      have hm := hmono ε hε w.re hy0 hwim.le hyw
      have hw' : (w.re : ℂ) + I * (w.im : ℂ) = w := by
        apply Complex.ext <;> simp
      simp only [hw', hw, norm_zero] at hm
      exact norm_le_zero_iff.mp hm
    set G : ℂ → ℂ := fun v => riemannHeat ε ((w.re : ℂ) + I * v) with hG
    have hGd : Differentiable ℂ G := by
      have := differentiable_riemannHeat hε.le
      simp only [hG]
      fun_prop
    have hGzero := GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval hGd (t₀ := w.im / 2)
      (r := w.im / 2) (by linarith) (fun y hy => by
        rw [abs_lt] at hy
        exact hseg y (by linarith) (by linarith))
    have h0 : riemannHeat ε 0 = 0 := by
      have := hGzero (-(w.re : ℂ) / I)
      simp only [hG] at this
      rwa [show (w.re : ℂ) + I * (-(w.re : ℂ) / I) = 0 by field_simp; ring] at this
    exact riemannHeat_zero_ne hε.le h0

end

end RHTower.DeBruijn
