import GaloisForLFunctions.RHTower.ZetaSubconvexStripBound

/-!
# Phragmén–Lindelöf interpolation of `ζ` between two vertical lines

**Theorem** (`exists_norm_riemannZeta_le_interp`).  Let `0 ≤ a < b ≤ 3/2` and `1 ≤ p_b ≤ p_a ≤ 2`.
If `‖(s−1)ζ(s)‖ ≤ M_a |t|^{p_a}` on `Re s = a` and `‖(s−1)ζ(s)‖ ≤ M_b |t|^{p_b}` on `Re s = b`, for
`|t| ≥ 8`, then there is `C` with

  `‖ζ(σ + it)‖ ≤ C t^{p_a − 1 − (p_a − p_b)(σ − a)/(b − a)}`   for `a ≤ σ ≤ b`, `t ≥ 8`.

Proof: the Phragmén–Lindelöf principle in the strip `a ≤ Re s ≤ b` for
`F(s) = (s−1)ζ(s) exp((s − it₀)²) t₀^{−(A − Bs)}` with `B = (p_a − p_b)/(b − a)` and `A = p_a + Ba`,
so that `A − Ba = p_a` and `A − Bb = p_b`.  On each edge `(|t|/t₀)^p e^{−(t−t₀)²} ≤ 2` for `0 ≤ p ≤ 2`.
-/

open Complex

namespace RHTower

noncomputable section

theorem exists_norm_riemannZeta_le_interp {a b pa pb Ma Mb : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 3 / 2) (hpb : 1 ≤ pb) (hpab : pb ≤ pa) (hpa : pa ≤ 2) (hMa : 0 ≤ Ma) (hMb : 0 ≤ Mb)
    (hA : ∀ y : ℝ, 8 ≤ |y| → ‖zetaEntire ((a : ℂ) + (y : ℂ) * I)‖ ≤ Ma * |y| ^ pa)
    (hB : ∀ y : ℝ, 8 ≤ |y| → ‖zetaEntire ((b : ℂ) + (y : ℂ) * I)‖ ≤ Mb * |y| ^ pb) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, a ≤ σ → σ ≤ b → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ C * t ^ (pa - 1 - (pa - pb) * (σ - a) / (b - a)) := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (0 : ℂ) 10).exists_bound_of_continuousOn
    (differentiable_zetaEntire.continuous.continuousOn (s := Metric.closedBall (0 : ℂ) 10))
  obtain ⟨K, hK⟩ : ∃ K, K = max K₀ 0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hK ▸ le_max_right _ _
  have hba : 0 < b - a := by linarith
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = (pa - pb) / (b - a) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = pa + B * a := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; exact div_nonneg (by linarith) hba.le
  have hAleft : A - B * a = pa := by rw [hAdef]; ring
  have hAright : A - B * b = pb := by rw [hAdef, hBdef]; field_simp; ring
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = max (K * Real.exp (9 / 4)) (2 * Real.exp (9 / 4) * max Ma Mb) :=
    ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; exact le_max_of_le_left (by positivity)
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro σ t₀ hσ1 hσ2 ht₀
  have ht₀0 : 0 < t₀ := by linarith
  have hlog0 : 0 ≤ Real.log t₀ := Real.log_nonneg (by linarith)
  set F : ℂ → ℂ := fun z => zetaEntire z * subconvexWeight A B t₀ z with hFdef
  have hFd : Differentiable ℂ F :=
    differentiable_zetaEntire.mul (differentiable_subconvexWeight A B t₀)
  have hFn : ∀ z, ‖F z‖ = ‖zetaEntire z‖ * ‖subconvexWeight A B t₀ z‖ := fun z => norm_mul _ _
  have hWstrip : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖subconvexWeight A B t₀ z‖ ≤ Real.exp (9 / 4) := by
    intro z h1 h2
    rw [norm_subconvexWeight]
    have ha' : Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) ≤ Real.exp (9 / 4) := by
      apply Real.exp_le_exp.mpr
      have : z.re ^ 2 ≤ 9 / 4 := by nlinarith
      nlinarith [sq_nonneg (z.im - t₀)]
    have hb' : Real.exp (-(A - B * z.re) * Real.log t₀) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ A - B * z.re := by linarith [mul_le_mul_of_nonneg_left h2 hB0]
      nlinarith
    calc Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) * Real.exp (-(A - B * z.re) * Real.log t₀)
        ≤ Real.exp (9 / 4) * 1 := mul_le_mul ha' hb' (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (9 / 4) := mul_one _
  have hgrowth : ∃ c < Real.pi / (b - a), ∃ D,
      F =O[Filter.comap (abs ∘ Complex.im) Filter.atTop
        ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (D * Real.exp (c * |z.im|)) := by
    refine ⟨1, ?_, 3, ?_⟩
    · rw [lt_div_iff₀ hba]; linarith [Real.pi_gt_three]
    · apply Asymptotics.IsBigO.of_bound (5 * Real.exp 2 * 64 * Real.exp (9 / 4))
      have hmem : {z : ℂ | 2 ≤ |z.im|} ∩ (Complex.re ⁻¹' Set.Ioo a b) ∈
          Filter.comap (abs ∘ Complex.im) Filter.atTop
            ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo a b) :=
        Filter.inter_mem_inf (Filter.preimage_mem_comap (Filter.Ici_mem_atTop 2))
          (Filter.mem_principal_self _)
      filter_upwards [hmem] with z hz
      obtain ⟨hzi, hzs⟩ := hz
      simp only [Set.mem_setOf_eq] at hzi
      simp only [Set.mem_preimage, Set.mem_Ioo] at hzs
      rw [hFn, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
      have h1 := norm_zetaEntire_strip_le (z := z) (by linarith) (by linarith) hzi
      have h2 := hWstrip z hzs.1.le hzs.2.le
      have h3 := four_add_cube_le_exp_exp (abs_nonneg z.im)
      calc ‖zetaEntire z‖ * ‖subconvexWeight A B t₀ z‖
          ≤ (5 * Real.exp 2 * (4 + |z.im|) ^ 3) * Real.exp (9 / 4) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ ≤ (5 * Real.exp 2 * (64 * Real.exp (3 * Real.exp |z.im|))) * Real.exp (9 / 4) := by
            gcongr
        _ = 5 * Real.exp 2 * 64 * Real.exp (9 / 4) * Real.exp (3 * Real.exp |z.im|) := by
            ring
  -- one edge `Re s = e` with exponent `p` and constant `M`
  have hedge : ∀ (e p M : ℝ), 0 ≤ e → e ≤ 3 / 2 → 0 ≤ p → p ≤ 2 → 0 ≤ M → M ≤ max Ma Mb →
      (∀ y : ℝ, 8 ≤ |y| → ‖zetaEntire ((e : ℂ) + (y : ℂ) * I)‖ ≤ M * |y| ^ p) →
      A - B * e = p → ∀ z : ℂ, z.re = e → ‖F z‖ ≤ C₁ := by
    intro e p M he0 he1 hp0 hp2 hM0 hMle hbd hAe z hz
    obtain ⟨y, hy⟩ : ∃ y, y = z.im := ⟨_, rfl⟩
    have hz' : z = (e : ℂ) + (y : ℂ) * I := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [hz, hy]
    have hW : ‖subconvexWeight A B t₀ z‖
        = Real.exp (e ^ 2) * Real.exp (-(y - t₀) ^ 2) * t₀ ^ (-p) := by
      rw [norm_subconvexWeight, hz, ← hy, hAe, Real.rpow_def_of_pos ht₀0]
      simp only [← Real.exp_add]
      congr 1; ring
    have hee : Real.exp (e ^ 2) ≤ Real.exp (9 / 4) := Real.exp_le_exp.mpr (by nlinarith)
    rw [hFn, hW, hz']
    rcases le_or_gt |y| 8 with hsmall | hbig
    · have hball : (e : ℂ) + (y : ℂ) * I ∈ Metric.closedBall (0 : ℂ) 10 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
        simp only [mul_zero, sub_zero, mul_one, add_zero, zero_add]
        rw [abs_of_nonneg he0]; linarith
      have hG : ‖zetaEntire ((e : ℂ) + (y : ℂ) * I)‖ ≤ K :=
        (hK₀ _ hball).trans (hK ▸ le_max_left _ _)
      have hw2 : Real.exp (-(y - t₀) ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hw3 : t₀ ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      calc ‖zetaEntire ((e : ℂ) + (y : ℂ) * I)‖
            * (Real.exp (e ^ 2) * Real.exp (-(y - t₀) ^ 2) * t₀ ^ (-p))
          ≤ K * (Real.exp (9 / 4) * 1 * 1) := by gcongr
        _ ≤ C₁ := by rw [hC₁, mul_one, mul_one]; exact le_max_left _ _
    · have hG := hbd y hbig.le
      have hratio : |y| ^ p * t₀ ^ (-p) = (|y| / t₀) ^ p := by
        rw [Real.rpow_neg ht₀0.le, Real.div_rpow (abs_nonneg _) ht₀0.le]
        exact (div_eq_mul_inv _ _).symm
      have hq := abs_div_rpow_le_one_add_sq (t := y) (t₀ := t₀) (p := p) (by linarith) hp0 hp2
      have hg := one_add_abs_sq_mul_exp_neg_sq_le (y - t₀)
      have hneg : -(y - t₀) ^ 2 = -((y - t₀) ^ 2) := by ring
      rw [hneg]
      calc ‖zetaEntire ((e : ℂ) + (y : ℂ) * I)‖
            * (Real.exp (e ^ 2) * Real.exp (-((y - t₀) ^ 2)) * t₀ ^ (-p))
          ≤ (M * |y| ^ p) * (Real.exp (9 / 4) * Real.exp (-((y - t₀) ^ 2)) * t₀ ^ (-p)) := by
            gcongr
        _ = M * Real.exp (9 / 4) * ((|y| ^ p * t₀ ^ (-p)) * Real.exp (-((y - t₀) ^ 2))) := by
            ring
        _ ≤ M * Real.exp (9 / 4) * ((1 + |y - t₀|) ^ 2 * Real.exp (-((y - t₀) ^ 2))) := by
            rw [hratio]; gcongr
        _ ≤ max Ma Mb * Real.exp (9 / 4) * 2 := by gcongr
        _ = 2 * Real.exp (9 / 4) * max Ma Mb := by ring
        _ ≤ C₁ := by rw [hC₁]; exact le_max_right _ _
  have hleft := hedge a pa Ma ha (by linarith) (by linarith) hpa hMa (le_max_left _ _) hA hAleft
  have hright := hedge b pb Mb (by linarith) hb (by linarith) (by linarith) hMb (le_max_right _ _)
    hB hAright
  have hre : ((σ : ℂ) + (t₀ : ℂ) * I).re = σ := by simp
  have hPL := PhragmenLindelof.vertical_strip (a := a) (b := b) (C := C₁) (f := F)
    (z := (σ : ℂ) + (t₀ : ℂ) * I) hFd.diffContOnCl hgrowth hleft hright
    (by rw [hre]; exact hσ1) (by rw [hre]; exact hσ2)
  rw [hFn, norm_subconvexWeight] at hPL
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im, mul_zero, mul_one, zero_add,
    add_zero, sub_self] at hPL
  have hz1 : (σ : ℂ) + (t₀ : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hrp : Real.exp (-(A - B * σ) * Real.log t₀) = t₀ ^ (-(A - B * σ)) := by
    rw [Real.rpow_def_of_pos ht₀0]; ring_nf
  rw [hrp] at hPL
  have hexp1 : 1 ≤ Real.exp (σ ^ 2 - 0 ^ 2) :=
    Real.one_le_exp (by rw [sq, sq, zero_mul, sub_zero]; exact mul_self_nonneg σ)
  have hpos : 0 < t₀ ^ (-(A - B * σ)) := Real.rpow_pos_of_pos ht₀0 _
  have hGle : ‖zetaEntire ((σ : ℂ) + (t₀ : ℂ) * I)‖ ≤ C₁ * t₀ ^ (A - B * σ) := by
    have h1 : ‖zetaEntire ((σ : ℂ) + (t₀ : ℂ) * I)‖ * t₀ ^ (-(A - B * σ)) ≤ C₁ := by
      calc ‖zetaEntire ((σ : ℂ) + (t₀ : ℂ) * I)‖ * t₀ ^ (-(A - B * σ))
          ≤ ‖zetaEntire ((σ : ℂ) + (t₀ : ℂ) * I)‖
            * (Real.exp (σ ^ 2 - 0 ^ 2) * t₀ ^ (-(A - B * σ))) := by
            gcongr; exact le_mul_of_one_le_left hpos.le hexp1
        _ ≤ C₁ := by simpa using hPL
    rw [Real.rpow_neg ht₀0.le] at h1
    have hp' : 0 < t₀ ^ (A - B * σ) := Real.rpow_pos_of_pos ht₀0 _
    rwa [mul_inv_le_iff₀ hp'] at h1
  rw [zetaEntire_eq hz1, norm_mul] at hGle
  have hn : t₀ ≤ ‖(σ : ℂ) + (t₀ : ℂ) * I - 1‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp [abs_of_pos ht₀0]
  have hζ : ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖ ≤ C₁ * t₀ ^ (A - B * σ) / t₀ := by
    rw [le_div_iff₀ ht₀0]
    calc ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖ * t₀
        ≤ ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖ * ‖(σ : ℂ) + (t₀ : ℂ) * I - 1‖ := by gcongr
      _ = ‖(σ : ℂ) + (t₀ : ℂ) * I - 1‖ * ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖ := by ring
      _ ≤ C₁ * t₀ ^ (A - B * σ) := hGle
  have hexp : A - B * σ - 1 = pa - 1 - (pa - pb) * (σ - a) / (b - a) := by
    rw [hAdef, hBdef]; field_simp; ring
  have hsub : C₁ * t₀ ^ (A - B * σ) / t₀ = C₁ * t₀ ^ (pa - 1 - (pa - pb) * (σ - a) / (b - a)) := by
    rw [mul_div_assoc, ← Real.rpow_sub_one ht₀0.ne', hexp]
  rw [hsub] at hζ
  calc ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖
      ≤ C₁ * t₀ ^ (pa - 1 - (pa - pb) * (σ - a) / (b - a)) := hζ
    _ ≤ (C₁ + 1) * t₀ ^ (pa - 1 - (pa - pb) * (σ - a) / (b - a)) := by
        gcongr; linarith

end

end RHTower
