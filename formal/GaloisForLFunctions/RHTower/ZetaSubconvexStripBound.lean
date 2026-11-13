import GaloisForLFunctions.RHTower.ZetaCriticalLineWeylBound
import GaloisForLFunctions.RHTower.ZetaConvexityBound

/-!
# The subconvex bound interpolated across the right half of the critical strip

For `0 < η ≤ 1/2` there is `C` with

`‖ζ(σ + it)‖ ≤ C t^{(1/6 + η)(1 + η − σ)/(1/2 + η)}` for `1/2 ≤ σ ≤ 1 + η` and `t ≥ 8`

(`exists_norm_riemannZeta_le_subconvex`).  At `σ = 1/2` the exponent is `1/6 + η`, at `σ = 1 + η`
it is `0`.

The proof is the Phragmén–Lindelöf principle in the strip `1/2 ≤ Re s ≤ 1 + η`, applied to
`F(s) = (s−1)ζ(s) · exp((s − it₀)²) · t₀^{−(A − Bs)}` with `p = 7/6 + η`, `B = (p − 1)/(1/2 + η)` and
`A = p + B/2`, so that `A − B/2 = p` and `A − B(1 + η) = 1`.  On the left edge
`‖(s−1)ζ(s)‖ ≤ (8400/η)|t|^p` by Weyl's bound `‖ζ(½+it)‖ ≤ 4200 t^{1/6} log t` and
`log t ≤ t^η/η`; on the right edge `‖(s−1)ζ(s)‖ ≤ (1 + 1/η)(1 + |t|)`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The critical-line bound for every `|t| ≥ 8`, with the logarithm absorbed:
`‖ζ(½ + it)‖ ≤ (4200/η)|t|^{1/6+η}`. -/
theorem norm_riemannZeta_half_le_abs_rpow {η y : ℝ} (hη : 0 < η) (hy : 8 ≤ |y|) :
    ‖riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I)‖ ≤ 4200 / η * |y| ^ (1 / 6 + η) := by
  have key : ∀ u : ℝ, 8 ≤ u →
      ‖riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ 4200 / η * u ^ (1 / 6 + η) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    refine (norm_riemannZeta_half_le_sixth hu).trans ?_
    have hlog := Real.log_le_rpow_div hu0.le hη
    calc 4200 * u ^ (1 / 6 : ℝ) * Real.log u ≤ 4200 * u ^ (1 / 6 : ℝ) * (u ^ η / η) := by
          gcongr
      _ = 4200 / η * (u ^ (1 / 6 : ℝ) * u ^ η) := by ring
      _ = 4200 / η * u ^ (1 / 6 + η) := by rw [← Real.rpow_add hu0]
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h] at hy ⊢; exact key y hy
  · rw [abs_of_neg h] at hy ⊢
    have hc : (1 / 2 : ℂ) + (y : ℂ) * I = starRingEnd ℂ ((1 / 2 : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hc, riemannZeta_conj, Complex.norm_conj]
    exact key (-y) hy

/-- On the left edge, `‖(s−1)ζ(s)‖ ≤ (8400/η)|t|^{7/6+η}` for `|t| ≥ 8`. -/
theorem norm_zetaEntire_half_edge_le {η y : ℝ} (hη : 0 < η) (hy : 8 ≤ |y|) :
    ‖zetaEntire (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ 8400 / η * |y| ^ (7 / 6 + η) := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I := ⟨_, rfl⟩
  rw [← hz]
  have hzre : z.re = 1 / 2 := by rw [hz]; simp
  have hz1 : z ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hzre] at this; norm_num at this
  rw [zetaEntire_eq hz1, norm_mul]
  have hζ : ‖riemannZeta z‖ ≤ 4200 / η * |y| ^ (1 / 6 + η) := by
    have := norm_riemannZeta_half_le_abs_rpow hη hy
    rw [show (1 / 2 : ℂ) + (y : ℂ) * I = z by rw [hz]; push_cast; ring] at this
    exact this
  have hn : ‖z - 1‖ ≤ 2 * |y| := by
    have e : z - 1 = ((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I := by rw [hz]; push_cast; ring
    rw [e]; refine (norm_add_le _ _).trans ?_
    simp only [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs]
    norm_num; linarith
  have hy0 : 0 < |y| := by linarith
  have hpow : |y| ^ (7 / 6 + η) = |y| * |y| ^ (1 / 6 + η) := by
    rw [show (7 / 6 : ℝ) + η = 1 + (1 / 6 + η) by ring, Real.rpow_add hy0, Real.rpow_one]
  calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ (2 * |y|) * (4200 / η * |y| ^ (1 / 6 + η)) := by gcongr
    _ = 8400 / η * (|y| * |y| ^ (1 / 6 + η)) := by ring
    _ = 8400 / η * |y| ^ (7 / 6 + η) := by rw [hpow]

/-- The Phragmén–Lindelöf weight `exp((s − it₀)²) · exp(−(A − Bs) log t₀)`. -/
def subconvexWeight (A B t₀ : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((s - (t₀ : ℂ) * I) ^ 2) * Complex.exp (-((A : ℂ) - (B : ℂ) * s) * (Real.log t₀ : ℂ))

theorem differentiable_subconvexWeight (A B t₀ : ℝ) : Differentiable ℂ (subconvexWeight A B t₀) := by
  unfold subconvexWeight; fun_prop

theorem norm_subconvexWeight (A B t₀ : ℝ) (z : ℂ) :
    ‖subconvexWeight A B t₀ z‖
      = Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) * Real.exp (-(A - B * z.re) * Real.log t₀) := by
  unfold subconvexWeight
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  congr 2
  · simp [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  · simp [Complex.mul_re]

/-- **The interpolated subconvex bound with its constant.**  Let `0 < η ≤ 1/2` and let `K` bound
`‖(s−1)ζ(s)‖` on the segment `s = ½ + iy`, `|y| ≤ 8`.  Then for `1/2 ≤ σ ≤ 1+η` and `t ≥ 8`,
`‖ζ(σ+it)‖ ≤ C t^{(1/6+η)(1+η−σ)/(1/2+η)}` with
`C = max (K e^{1/4}) (max (16800 e^{1/4}/η) (4(1+1/η)e^{9/4}))`. -/
theorem norm_riemannZeta_le_subconvex_of_segment {η K : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hK0 : 0 ≤ K)
    (hKseg : ∀ y : ℝ, |y| ≤ 8 → ‖zetaEntire (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ K)
    {σ t₀ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 + η) (ht₀ : 8 ≤ t₀) :
    ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖
      ≤ max (K * Real.exp (1 / 4))
          (max (8400 / η * Real.exp (1 / 4) * 2) (4 * (1 + 1 / η) * Real.exp (9 / 4)))
        * t₀ ^ ((1 / 6 + η) * (1 + η - σ) / (1 / 2 + η)) := by
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 7 / 6 + η := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (p - 1) / (1 / 2 + η) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = p + B / 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB, hp]; exact div_nonneg (by linarith) (by linarith)
  have hAleft : A - B * (1 / 2) = p := by rw [hA]; ring
  have hAright : A - B * (1 + η) = 1 := by
    rw [hA, hB]; field_simp; ring
  obtain ⟨CL, hCL⟩ : ∃ CL, CL = 8400 / η * Real.exp (1 / 4) * 2 := ⟨_, rfl⟩
  obtain ⟨CR, hCR⟩ : ∃ CR, CR = 4 * (1 + 1 / η) * Real.exp (9 / 4) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = max (K * Real.exp (1 / 4)) (max CL CR) := ⟨_, rfl⟩
  rw [← hCL, ← hCR, ← hC₁]
  have ht₀0 : 0 < t₀ := by linarith
  have hlog0 : 0 ≤ Real.log t₀ := Real.log_nonneg (by linarith)
  set F : ℂ → ℂ := fun z => zetaEntire z * subconvexWeight A B t₀ z with hFdef
  have hFd : Differentiable ℂ F :=
    differentiable_zetaEntire.mul (differentiable_subconvexWeight A B t₀)
  have hFn : ∀ z, ‖F z‖ = ‖zetaEntire z‖ * ‖subconvexWeight A B t₀ z‖ := fun z => norm_mul _ _
  -- the weight on the strip
  have hWstrip : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 1 + η →
      ‖subconvexWeight A B t₀ z‖ ≤ Real.exp (9 / 4) := by
    intro z h1 h2
    rw [norm_subconvexWeight]
    have ha : Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) ≤ Real.exp (9 / 4) := by
      apply Real.exp_le_exp.mpr
      have : z.re ^ 2 ≤ 9 / 4 := by nlinarith
      nlinarith [sq_nonneg (z.im - t₀)]
    have hb : Real.exp (-(A - B * z.re) * Real.log t₀) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ A - B * z.re := by linarith [mul_le_mul_of_nonneg_left h2 hB0]
      nlinarith
    calc Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) * Real.exp (-(A - B * z.re) * Real.log t₀)
        ≤ Real.exp (9 / 4) * 1 := mul_le_mul ha hb (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (9 / 4) := mul_one _
  -- growth in the strip
  have hgrowth : ∃ c < Real.pi / (1 + η - 1 / 2), ∃ D,
      F =O[Filter.comap (abs ∘ Complex.im) Filter.atTop
        ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo (1 / 2) (1 + η))]
        fun z => Real.exp (D * Real.exp (c * |z.im|)) := by
    refine ⟨1, ?_, 3, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]; linarith [Real.pi_gt_three]
    · apply Asymptotics.IsBigO.of_bound (5 * Real.exp 2 * 64 * Real.exp (9 / 4))
      have hmem : {z : ℂ | 2 ≤ |z.im|} ∩ (Complex.re ⁻¹' Set.Ioo (1 / 2) (1 + η)) ∈
          Filter.comap (abs ∘ Complex.im) Filter.atTop
            ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo (1 / 2) (1 + η)) :=
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
  -- left edge
  have hleft : ∀ z : ℂ, z.re = 1 / 2 → ‖F z‖ ≤ C₁ := by
    intro z hz
    obtain ⟨y, hy⟩ : ∃ y, y = z.im := ⟨_, rfl⟩
    have hz' : z = ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [hz, hy]
    have hWl : ‖subconvexWeight A B t₀ z‖
        = Real.exp (1 / 4) * Real.exp (-(y - t₀) ^ 2) * t₀ ^ (-p) := by
      rw [norm_subconvexWeight, hz, ← hy, hAleft, Real.rpow_def_of_pos ht₀0]
      simp only [← Real.exp_add]
      congr 1; ring
    rw [hFn, hWl, hz']
    rcases le_or_gt |y| 8 with hsmall | hbig
    · have hG : ‖zetaEntire (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ K := hKseg y hsmall
      have hw2 : Real.exp (-(y - t₀) ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hw3 : t₀ ^ (-p) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by rw [hp]; linarith)
      calc ‖zetaEntire (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖
            * (Real.exp (1 / 4) * Real.exp (-(y - t₀) ^ 2) * t₀ ^ (-p))
          ≤ K * (Real.exp (1 / 4) * 1 * 1) := by
            gcongr
        _ ≤ C₁ := by rw [hC₁, mul_one, mul_one]; exact le_max_left _ _
    · have hG := norm_zetaEntire_half_edge_le hη hbig.le
      rw [← hp] at hG
      have hratio : |y| ^ p * t₀ ^ (-p) = (|y| / t₀) ^ p := by
        rw [Real.rpow_neg ht₀0.le, Real.div_rpow (abs_nonneg _) ht₀0.le]
        exact (div_eq_mul_inv _ _).symm
      have hq := abs_div_rpow_le_one_add_sq (t := y) (t₀ := t₀) (p := p)
        (by linarith) (by rw [hp]; positivity) (by rw [hp]; linarith)
      have hg := one_add_abs_sq_mul_exp_neg_sq_le (y - t₀)
      have hneg : -(y - t₀) ^ 2 = -((y - t₀) ^ 2) := by ring
      rw [hneg]
      calc ‖zetaEntire (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖
            * (Real.exp (1 / 4) * Real.exp (-((y - t₀) ^ 2)) * t₀ ^ (-p))
          ≤ (8400 / η * |y| ^ p)
            * (Real.exp (1 / 4) * Real.exp (-((y - t₀) ^ 2)) * t₀ ^ (-p)) := by
            gcongr
        _ = 8400 / η * Real.exp (1 / 4)
            * ((|y| ^ p * t₀ ^ (-p)) * Real.exp (-((y - t₀) ^ 2))) := by
            ring
        _ ≤ 8400 / η * Real.exp (1 / 4)
            * ((1 + |y - t₀|) ^ 2 * Real.exp (-((y - t₀) ^ 2))) := by
            rw [hratio]; gcongr
        _ ≤ 8400 / η * Real.exp (1 / 4) * 2 := by gcongr
        _ = CL := by rw [hCL]
        _ ≤ C₁ := by rw [hC₁]; exact le_max_of_le_right (le_max_left _ _)
  -- right edge
  have hright : ∀ z : ℂ, z.re = 1 + η → ‖F z‖ ≤ C₁ := by
    intro z hz
    obtain ⟨y, hy⟩ : ∃ y, y = z.im := ⟨_, rfl⟩
    have hz' : z = ((1 + η : ℝ) : ℂ) + (y : ℂ) * I := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [hz, hy]
    have hWr : ‖subconvexWeight A B t₀ z‖
        = Real.exp ((1 + η) ^ 2) * Real.exp (-(y - t₀) ^ 2) / t₀ := by
      rw [norm_subconvexWeight, hz, ← hy, hAright]
      have e : Real.exp (-(1 : ℝ) * Real.log t₀) = t₀⁻¹ := by
        rw [neg_one_mul, Real.exp_neg, Real.exp_log ht₀0]
      rw [e, div_eq_mul_inv, ← Real.exp_add]
      congr 2
    rw [hFn, hWr, hz']
    have hG := norm_zetaEntire_right_edge_le (t := y) hη (by linarith)
    have hw1 : Real.exp ((1 + η) ^ 2) ≤ Real.exp (9 / 4) := Real.exp_le_exp.mpr (by nlinarith)
    have hlin : (1 + |y|) / t₀ ≤ 2 * (1 + |y - t₀|) := by
      rw [div_le_iff₀ ht₀0]
      have habs : |y| ≤ t₀ + |y - t₀| := by
        have := abs_add_le (y - t₀) t₀
        rw [sub_add_cancel, abs_of_pos ht₀0] at this; linarith only [this]
      have hd := abs_nonneg (y - t₀)
      have hdt : |y - t₀| ≤ t₀ * |y - t₀| := le_mul_of_one_le_left hd (by linarith only [ht₀])
      linarith only [habs, hdt, hd, ht₀]
    have hg := one_add_abs_sq_mul_exp_neg_sq_le (y - t₀)
    have hg' : (1 + |y - t₀|) * Real.exp (-((y - t₀) ^ 2)) ≤ 2 := by
      refine le_trans ?_ hg
      gcongr
      exact le_self_pow₀ (by linarith only [abs_nonneg (y - t₀)]) (by norm_num)
    have hneg : -(y - t₀) ^ 2 = -((y - t₀) ^ 2) := by ring
    rw [hneg]
    calc ‖zetaEntire (((1 + η : ℝ) : ℂ) + (y : ℂ) * I)‖
          * (Real.exp ((1 + η) ^ 2) * Real.exp (-((y - t₀) ^ 2)) / t₀)
        ≤ ((1 + 1 / η) * (1 + |y|)) * (Real.exp (9 / 4) * Real.exp (-((y - t₀) ^ 2)) / t₀) := by
          gcongr
      _ = (1 + 1 / η) * Real.exp (9 / 4) * ((1 + |y|) / t₀) * Real.exp (-((y - t₀) ^ 2)) := by
          ring
      _ ≤ (1 + 1 / η) * Real.exp (9 / 4) * (2 * (1 + |y - t₀|)) * Real.exp (-((y - t₀) ^ 2)) := by
          gcongr
      _ = 2 * (1 + 1 / η) * Real.exp (9 / 4) * ((1 + |y - t₀|) * Real.exp (-((y - t₀) ^ 2))) := by
          ring
      _ ≤ 2 * (1 + 1 / η) * Real.exp (9 / 4) * 2 := by gcongr
      _ = CR := by rw [hCR]; ring
      _ ≤ C₁ := by rw [hC₁]; exact le_max_of_le_right (le_max_right _ _)
  -- Phragmén–Lindelöf
  have hre : ((σ : ℂ) + (t₀ : ℂ) * I).re = σ := by simp
  have hPL := PhragmenLindelof.vertical_strip (a := 1 / 2) (b := 1 + η) (C := C₁) (f := F)
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
  have hexp : A - B * σ - 1 = (1 / 6 + η) * (1 + η - σ) / (1 / 2 + η) := by
    rw [hA, hB, hp]; field_simp; ring
  have hsub : C₁ * t₀ ^ (A - B * σ) / t₀ = C₁ * t₀ ^ ((1 / 6 + η) * (1 + η - σ) / (1 / 2 + η)) := by
    rw [mul_div_assoc, ← Real.rpow_sub_one ht₀0.ne', hexp]
  rw [hsub] at hζ
  exact hζ

/-- **The interpolated subconvex bound.**  For `0 < η ≤ 1/2` there is `C > 0` with
`‖ζ(σ+it)‖ ≤ C t^{(1/6+η)(1+η−σ)/(1/2+η)}` whenever `1/2 ≤ σ ≤ 1+η` and `t ≥ 8`. -/
theorem exists_norm_riemannZeta_le_subconvex {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 + η → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ C * t ^ ((1 / 6 + η) * (1 + η - σ) / (1 / 2 + η)) := by
  -- the segment constant from compactness
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (0 : ℂ) 10).exists_bound_of_continuousOn
    (differentiable_zetaEntire.continuous.continuousOn (s := Metric.closedBall (0 : ℂ) 10))
  have hseg : ∀ y : ℝ, |y| ≤ 8 →
      ‖zetaEntire (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ max K₀ 0 := by
    intro y hsmall
    have hball : ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I ∈ Metric.closedBall (0 : ℂ) 10 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
      simp only [mul_zero, sub_zero, mul_one, add_zero, zero_add]
      norm_num; linarith
    exact (hK₀ _ hball).trans (le_max_left _ _)
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = max (max K₀ 0 * Real.exp (1 / 4))
      (max (8400 / η * Real.exp (1 / 4) * 2) (4 * (1 + 1 / η) * Real.exp (9 / 4))) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    exact le_max_of_le_left (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le)
  refine ⟨C₁ + 1, by linarith, fun σ t hσ1 hσ2 ht => ?_⟩
  have h := norm_riemannZeta_le_subconvex_of_segment hη hη2 (le_max_right K₀ 0) hseg hσ1 hσ2 ht
  rw [← hC₁] at h
  refine h.trans ?_
  gcongr
  linarith

end

end RHTower
