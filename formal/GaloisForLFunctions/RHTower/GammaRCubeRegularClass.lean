import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift
import GaloisForLFunctions.RHTower.GammaRCubeThetaPairsL2
import GaloisForLFunctions.HTGeometry.GammaVerticalUniformDecay

/-!
# The strip-regular antisymmetric class for `ζ(s)³`'s functional equation

`StripRegular Ψ`: `Ψ` is holomorphic on `0 < Re s < 1` and decays faster than every power of
`|Im s|`, uniformly on closed substrips. For such `Ψ` the inverse Mellin transform
`mellinInv c Ψ` does not depend on `c ∈ (0,1)` (vertical contour shift).

The theta test symbols `Ψ_y(s) = Γℝ(s)³ (y^{-s} - y^{s-1})` are strip-regular, antisymmetric
(`Ψ_y(s) = -G(s) Ψ_y(1-s)` with `G = Γℝ³/Γℝ(1-·)³`), and invert to the theta test functions
`K₂(y x) - y⁻¹ K₂(x/y)`. A self-dual relation holding on the whole antisymmetric strip-regular
class therefore gives the theta relation of `ζ(s)³`'s functional equation.

Supporting estimates: uniform polynomial decay of `Γ` and `Γℝ` on closed vertical substrips of
`Re s > 0`.
-/

open Complex MeasureTheory Filter Set Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Holomorphy on the open strip `0 < Re s < 1` with decay of every polynomial order, uniformly on
closed substrips. -/
structure StripRegular (Ψ : ℂ → ℂ) : Prop where
  diff : ∀ s : ℂ, 0 < s.re → s.re < 1 → DifferentiableAt ℂ Ψ s
  decay : ∀ a b : ℝ, 0 < a → b < 1 → ∀ K : ℕ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
    ‖Ψ s‖ ≤ C / (1 + s.im ^ 2) ^ K

private theorem norm_cpow_neg_le {x : ℝ} (hx : 0 < x) {c₁ c₂ : ℝ} {s : ℂ} (hs : s.re ∈ uIcc c₁ c₂) :
    ‖(x : ℂ) ^ (-s)‖ ≤ x ^ (-c₁) + x ^ (-c₂) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, neg_re]
  rw [Set.mem_uIcc] at hs
  have h1 : 0 ≤ x ^ (-c₁) := Real.rpow_nonneg hx.le _
  have h2 : 0 ≤ x ^ (-c₂) := Real.rpow_nonneg hx.le _
  rcases le_or_gt x 1 with hx1 | hx1
  · rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show -s.re ≥ -c₂ by linarith)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show -s.re ≥ -c₁ by linarith)
      linarith
  · rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have := Real.rpow_le_rpow_of_exponent_le hx1.le (show -s.re ≤ -c₁ by linarith)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le hx1.le (show -s.re ≤ -c₂ by linarith)
      linarith

/-- The inverse Mellin transform of a strip-regular function does not depend on the abscissa. -/
theorem mellinInv_eq_of_stripRegular {Ψ : ℂ → ℂ} (hΨ : StripRegular Ψ) {c₁ c₂ : ℝ}
    (h1 : 0 < c₁) (h1' : c₁ < 1) (h2 : 0 < c₂) (h2' : c₂ < 1) {x : ℝ} (hx : 0 < x) :
    mellinInv c₁ Ψ x = mellinInv c₂ Ψ x := by
  unfold mellinInv
  congr 1
  obtain ⟨C, hC⟩ := hΨ.decay (min c₁ c₂) (max c₁ c₂) (lt_min h1 h2) (max_lt h1' h2') 1
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc c₁ c₂ → 0 < s.re ∧ s.re < 1 := by
    intro s hs
    rw [Set.mem_uIcc] at hs
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> constructor <;> linarith
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have key := integral_vertical_line_shift_of_decay
    (Φ := fun s : ℂ => (x : ℂ) ^ (-s) * Ψ s) (c₁ := c₁) (c₂ := c₂)
    (C := (x ^ (-c₁) + x ^ (-c₂)) * C)
    (fun s hs => by
      obtain ⟨hs0, hs1⟩ := hstrip s hs
      exact ((differentiableAt_id.neg).const_cpow (Or.inl hx0)).mul (hΨ.diff s hs0 hs1))
    (fun s hs => by
      have hs' := hs
      rw [Set.mem_uIcc] at hs'
      have hmin : min c₁ c₂ ≤ s.re := by
        rcases hs' with ⟨ha, _⟩ | ⟨ha, _⟩
        · exact min_le_iff.mpr (Or.inl ha)
        · exact min_le_iff.mpr (Or.inr ha)
      have hmax : s.re ≤ max c₁ c₂ := by
        rcases hs' with ⟨_, hb⟩ | ⟨_, hb⟩
        · exact le_max_iff.mpr (Or.inr hb)
        · exact le_max_iff.mpr (Or.inl hb)
      have hb := hC s hmin hmax
      rw [pow_one] at hb
      rw [norm_mul]
      calc ‖(x : ℂ) ^ (-s)‖ * ‖Ψ s‖ ≤ (x ^ (-c₁) + x ^ (-c₂)) * (C / (1 + s.im ^ 2)) :=
            mul_le_mul (norm_cpow_neg_le hx hs) hb (norm_nonneg _) (by positivity)
        _ = (x ^ (-c₁) + x ^ (-c₂)) * C / (1 + s.im ^ 2) := by ring)
  simpa [smul_eq_mul] using key

/-- Uniform polynomial decay of `Γ` on a compact-width strip `a ≤ Re z ≤ M`, `a > 0`, for all heights. -/
theorem exists_bound_norm_Gamma_strip_one_add_sq {a M : ℝ} (ha : 0 < a) (hM : a ≤ M) (k : ℕ) :
    ∃ C : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ M → ‖Complex.Gamma z‖ ≤ C / (1 + z.im ^ 2) ^ k := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_uniform_bound_norm_Gamma_vertical (lt_of_lt_of_le ha hM) (2 * k)
  -- compact part
  have hK : IsCompact ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) '' (Icc a M ×ˢ Icc (-1) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn Complex.Gamma
      ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) '' (Icc a M ×ˢ Icc (-1) 1)) := by
    rintro _ ⟨p, hp, rfl⟩
    refine (Complex.differentiableAt_Gamma _ (fun m hm => ?_)).continuousAt.continuousWithinAt
    have := congrArg Complex.re hm
    simp at this
    have hp1 := hp.1.1
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max (B * 2 ^ k) (C₁ * 2 ^ k), fun z hza hzM => ?_⟩
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  have hden : 0 < (1 + z.im ^ 2) ^ k := by positivity
  rcases le_or_gt |z.im| 1 with ht | ht
  · have hmem : z ∈ (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) '' (Icc a M ×ˢ Icc (-1) 1) :=
      ⟨(z.re, z.im), ⟨⟨hza, hzM⟩, abs_le.mp ht⟩, hz.symm⟩
    have h1 := hB z hmem
    have hsq : (1 + z.im ^ 2) ^ k ≤ 2 ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [abs_le.mp ht, sq_abs z.im]
    rw [le_div_iff₀ hden]
    calc ‖Complex.Gamma z‖ * (1 + z.im ^ 2) ^ k ≤ B * 2 ^ k :=
          mul_le_mul h1 hsq hden.le (le_trans (norm_nonneg _) h1)
      _ ≤ _ := le_max_left _ _
  · -- `|Im z| > 1`: use the polynomial decay at height `|Im z|`
    have hbound : ‖Complex.Gamma z‖ ≤ C₁ / |z.im| ^ (2 * k) := by
      rcases le_or_gt 0 z.im with him | him
      · have := hC₁ z.re z.im (lt_of_lt_of_le ha hza) hzM (by rw [abs_of_nonneg him] at ht; exact ht.le)
        rw [← hz] at this
        rw [abs_of_nonneg him]; exact this
      · have := hC₁ z.re (-z.im) (lt_of_lt_of_le ha hza) hzM (by rw [abs_of_neg him] at ht; exact ht.le)
        have hconj : (z.re : ℂ) + ((-z.im : ℝ) : ℂ) * I = (starRingEnd ℂ) z := by
          apply Complex.ext <;> simp
        rw [hconj, Complex.Gamma_conj, Complex.norm_conj] at this
        rw [abs_of_neg him]; exact this
    have hsq : (1 + z.im ^ 2) ^ k ≤ 2 ^ k * |z.im| ^ (2 * k) := by
      rw [pow_mul, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [sq_abs z.im, ht]
    have habs : 0 < |z.im| ^ (2 * k) := by positivity
    rw [le_div_iff₀ hden]
    calc ‖Complex.Gamma z‖ * (1 + z.im ^ 2) ^ k
        ≤ (C₁ / |z.im| ^ (2 * k)) * (2 ^ k * |z.im| ^ (2 * k)) :=
          mul_le_mul hbound hsq hden.le (by positivity)
      _ = C₁ * 2 ^ k := by field_simp
      _ ≤ _ := le_max_right _ _

/-- `Γℝ` is differentiable on `Re s > 0`. -/
theorem differentiableAt_gammaR_of_re_pos {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have hfun : Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z; exact Gammaℝ_def z
  rw [hfun]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine DifferentiableAt.mul ((differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hpi)) ?_
  refine (Complex.differentiableAt_Gamma _ (fun m hm => ?_)).comp s (differentiableAt_id.div_const 2)
  have := congrArg Complex.re hm
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- Uniform polynomial decay of `Γℝ` on closed substrips of `Re s > 0`. -/
theorem exists_bound_norm_gammaR_strip {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Gammaℝ s‖ ≤ C / (1 + s.im ^ 2) ^ k := by
  obtain ⟨C, hC⟩ := exists_bound_norm_Gamma_strip_one_add_sq (a := a / 2) (M := b / 2)
    (by positivity) (by linarith) k
  refine ⟨4 ^ k * max C 0, fun s hsa hsb => ?_⟩
  rw [Gammaℝ_def, norm_mul]
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp; linarith
  have hG := hC (s / 2) (by simp; linarith) (by simp; linarith)
  have him : (s / 2).im = s.im / 2 := by simp
  rw [him] at hG
  have hden : 0 < (1 + s.im ^ 2) ^ k := by positivity
  have hden2 : 0 < (1 + (s.im / 2) ^ 2) ^ k := by positivity
  have hcmp : (1 + s.im ^ 2) ^ k ≤ 4 ^ k * (1 + (s.im / 2) ^ 2) ^ k := by
    rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); nlinarith [sq_nonneg s.im]
  have hG' : ‖Complex.Gamma (s / 2)‖ ≤ max C 0 / (1 + (s.im / 2) ^ 2) ^ k :=
    hG.trans (div_le_div_of_nonneg_right (le_max_left _ _) hden2.le)
  calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ ≤ 1 * (max C 0 / (1 + (s.im / 2) ^ 2) ^ k) :=
        mul_le_mul hpi hG' (norm_nonneg _) zero_le_one
    _ ≤ 4 ^ k * max C 0 / (1 + s.im ^ 2) ^ k := by
        rw [one_mul, div_le_div_iff₀ hden2 hden]
        have h0 : 0 ≤ max C 0 := le_max_right _ _
        nlinarith [hcmp, h0]

/-- The Mellin symbol `Γℝ(s)³ (y^{-s} - y^{s-1})` of the theta test function
`K₂(y·) - y⁻¹ K₂(·/y)`. -/
def thetaTestSymbol (y : ℝ) (s : ℂ) : ℂ := Gammaℝ s ^ 3 * ((y : ℂ) ^ (-s) - (y : ℂ) ^ (s - 1))

private theorem norm_cpow_sub_one_le {x : ℝ} (hx : 0 < x) {c₁ c₂ : ℝ} {s : ℂ}
    (hs : s.re ∈ uIcc c₁ c₂) : ‖(x : ℂ) ^ (s - 1)‖ ≤ x ^ (c₁ - 1) + x ^ (c₂ - 1) := by
  have h := norm_cpow_neg_le hx (c₁ := 1 - c₁) (c₂ := 1 - c₂) (s := 1 - s) (by
    rw [Set.mem_uIcc] at hs ⊢
    simp only [sub_re, one_re]
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; constructor <;> linarith
    · left; constructor <;> linarith)
  rw [show -(1 - s) = s - 1 by ring, show -(1 - c₁) = c₁ - 1 by ring,
    show -(1 - c₂) = c₂ - 1 by ring] at h
  exact h

/-- The theta test symbols are strip-regular. -/
theorem stripRegular_thetaTestSymbol {y : ℝ} (hy : 0 < y) : StripRegular (thetaTestSymbol y) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  refine ⟨fun s h0 _ => ?_, fun a b ha hb K => ?_⟩
  · exact ((differentiableAt_gammaR_of_re_pos h0).pow 3).mul
      ((differentiableAt_id.neg.const_cpow (Or.inl hy0)).sub
        ((differentiableAt_id.sub_const 1).const_cpow (Or.inl hy0)))
  · by_cases hab : a ≤ b
    · obtain ⟨C, hC⟩ := exists_bound_norm_gammaR_strip ha hab K
      set L := (y ^ (-a) + y ^ (-b)) + (y ^ (a - 1) + y ^ (b - 1)) with hL
      refine ⟨(max C 0) ^ 3 * L, fun s hsa hsb => ?_⟩
      have hmem : s.re ∈ uIcc a b := by rw [Set.uIcc_of_le hab]; exact ⟨hsa, hsb⟩
      have hden : 0 < (1 + s.im ^ 2) ^ K := by positivity
      have hG : ‖Gammaℝ s‖ ≤ max C 0 / (1 + s.im ^ 2) ^ K :=
        (hC s hsa hsb).trans (div_le_div_of_nonneg_right (le_max_left _ _) hden.le)
      have hG3 : ‖Gammaℝ s ^ 3‖ ≤ (max C 0) ^ 3 / (1 + s.im ^ 2) ^ K := by
        rw [norm_pow]
        have h1 : ‖Gammaℝ s‖ ^ 3 ≤ (max C 0 / (1 + s.im ^ 2) ^ K) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) hG 3
        refine h1.trans ?_
        rw [div_pow, div_le_div_iff₀ (by positivity) hden]
        have hone : 1 ≤ (1 + s.im ^ 2) ^ K := one_le_pow₀ (by nlinarith [sq_nonneg s.im])
        have h0 : 0 ≤ (max C 0) ^ 3 := by positivity
        calc (max C 0) ^ 3 * (1 + s.im ^ 2) ^ K ≤ (max C 0) ^ 3 * ((1 + s.im ^ 2) ^ K) ^ 3 := by
              apply mul_le_mul_of_nonneg_left _ h0
              calc (1 + s.im ^ 2) ^ K = (1 + s.im ^ 2) ^ K * 1 * 1 := by ring
                _ ≤ (1 + s.im ^ 2) ^ K * (1 + s.im ^ 2) ^ K * (1 + s.im ^ 2) ^ K := by gcongr
                _ = ((1 + s.im ^ 2) ^ K) ^ 3 := by ring
          _ = _ := by ring
      have hP : ‖(y : ℂ) ^ (-s) - (y : ℂ) ^ (s - 1)‖ ≤ L :=
        (norm_sub_le _ _).trans (add_le_add (norm_cpow_neg_le hy hmem) (norm_cpow_sub_one_le hy hmem))
      unfold thetaTestSymbol
      rw [norm_mul]
      calc ‖Gammaℝ s ^ 3‖ * ‖(y : ℂ) ^ (-s) - (y : ℂ) ^ (s - 1)‖
          ≤ ((max C 0) ^ 3 / (1 + s.im ^ 2) ^ K) * L :=
            mul_le_mul hG3 hP (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · exact ⟨0, fun s hsa hsb => absurd (le_trans hsa hsb) hab⟩

/-- The theta test symbol is antisymmetric: `Ψ(s) = -G(s) Ψ(1-s)` with `G = Γℝ³/Γℝ(1-·)³`. -/
theorem thetaTestSymbol_antisymm {y : ℝ} (s : ℂ) (h1 : s.re < 1) :
    thetaTestSymbol y s = -(Gammaℝ s ^ 3 / Gammaℝ (1 - s) ^ 3) * thetaTestSymbol y (1 - s) := by
  have hne : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  unfold thetaTestSymbol
  rw [show -(1 - s) = s - 1 by ring, show 1 - s - 1 = -s by ring]
  field_simp
  ring

/-- The theta test function `K₂(y x) - y⁻¹ K₂(x/y)`. -/
def thetaTestFunction (y : ℝ) (x : ℝ) : ℂ :=
  gammaRPowKernel 2 (y * x) - ((y⁻¹ : ℝ) : ℂ) * gammaRPowKernel 2 (y⁻¹ * x)

private theorem mellinConvergent_scaled {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => gammaRPowKernel 2 (y * x)) s :=
  (MellinConvergent.comp_mul_left hy).mpr (hasMellin_gammaRPowKernel 2 hs).1

private theorem mellinConvergent_thetaTest {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (thetaTestFunction y) s := by
  have h1 := mellinConvergent_scaled hy hs
  have h2 := (mellinConvergent_scaled (inv_pos.mpr hy) hs).const_smul ((y⁻¹ : ℝ) : ℂ)
  unfold MellinConvergent at h1 h2 ⊢
  have := h1.sub h2
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, thetaTestFunction, smul_eq_mul]
  ring

/-- `mellin (K₂(y·) - y⁻¹K₂(·/y)) = Γℝ³ (y^{-s} - y^{s-1})` on `Re s > 0`. -/
theorem mellin_thetaTestFunction {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) :
    mellin (thetaTestFunction y) s = thetaTestSymbol y s := by
  have h1 := mellinConvergent_scaled hy hs
  have h2 := (mellinConvergent_scaled (inv_pos.mpr hy) hs).const_smul ((y⁻¹ : ℝ) : ℂ)
  have hsplit : mellin (thetaTestFunction y) s
      = mellin (fun x : ℝ => gammaRPowKernel 2 (y * x)) s
        - mellin (fun x : ℝ => ((y⁻¹ : ℝ) : ℂ) • gammaRPowKernel 2 (y⁻¹ * x)) s := by
    unfold mellin
    rw [← integral_sub h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [thetaTestFunction, smul_eq_mul]; ring
  rw [hsplit, mellin_const_smul, mellin_comp_mul_left _ _ hy,
    mellin_comp_mul_left _ _ (inv_pos.mpr hy), (hasMellin_gammaRPowKernel 2 hs).2]
  unfold thetaTestSymbol
  have hyarg : (y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  simp only [smul_eq_mul, Complex.ofReal_inv]
  rw [Complex.inv_cpow _ _ hyarg, ← Complex.cpow_neg, neg_neg]
  have : (y : ℂ) ^ (s - 1) = (y : ℂ)⁻¹ * (y : ℂ) ^ s := by
    rw [Complex.cpow_sub _ _ hy0, Complex.cpow_one]; ring
  rw [this]; ring

/-- Mellin inversion for the theta test functions: on every line `0 < c < 1`,
`mellinInv c Ψ_y x = K₂(y x) - y⁻¹ K₂(x / y)`. -/
theorem mellinInv_thetaTestSymbol {y : ℝ} (hy : 0 < y) {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {x : ℝ} (hx : 0 < x) : mellinInv c (thetaTestSymbol y) x = thetaTestFunction y x := by
  have hcre : 0 < ((c : ℂ)).re := by simpa using hc
  have hconv := mellinConvergent_thetaTest hy hcre
  have hvert : VerticalIntegrable (mellin (thetaTestFunction y)) c := by
    obtain ⟨C, hC⟩ := (stripRegular_thetaTestSymbol hy).decay c c hc hc1 1
    unfold VerticalIntegrable
    have hcont : Continuous fun t : ℝ => thetaTestSymbol y ((c : ℂ) + t * I) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact ((stripRegular_thetaTestSymbol hy).diff _ (by simpa using hc) (by simpa using hc1)
        ).continuousAt.comp (by fun_prop)
    have hint : Integrable fun t : ℝ => thetaTestSymbol y ((c : ℂ) + t * I) := by
      refine (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      have := hC ((c : ℂ) + t * I) (by simp) (by simp)
      simpa [div_eq_mul_inv] using this
    refine hint.congr (Eventually.of_forall fun t => ?_)
    show thetaTestSymbol y ((c : ℂ) + t * I) = mellin (thetaTestFunction y) ((c : ℂ) + t * I)
    rw [mellin_thetaTestFunction hy (s := (c : ℂ) + t * I) (by simpa using hc)]
  have hcontx : ContinuousAt (thetaTestFunction y) x := by
    unfold thetaTestFunction
    have h1 : ContinuousAt (fun x : ℝ => gammaRPowKernel 2 (y * x)) x :=
      ((continuousOn_gammaRPowKernel 2).continuousAt (Ioi_mem_nhds (mul_pos hy hx))).comp
        (by fun_prop)
    have h2 : ContinuousAt (fun x : ℝ => gammaRPowKernel 2 (y⁻¹ * x)) x :=
      ((continuousOn_gammaRPowKernel 2).continuousAt
        (Ioi_mem_nhds (mul_pos (inv_pos.mpr hy) hx))).comp (by fun_prop)
    exact h1.sub (continuousAt_const.mul h2)
  have hinv := mellinInv_mellin_eq c (thetaTestFunction y) hx hconv hvert hcontx
  rw [← hinv]
  unfold mellinInv
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show (x : ℂ) ^ (-((c : ℂ) + t * I)) • thetaTestSymbol y ((c : ℂ) + t * I)
    = (x : ℂ) ^ (-((c : ℂ) + t * I)) • mellin (thetaTestFunction y) ((c : ℂ) + t * I)
  rw [mellin_thetaTestFunction hy (s := (c : ℂ) + t * I) (by simpa using hc)]

end RHTower
