import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay
import GaloisForLFunctions.RHTower.KuznetsovSameSignWeightSigma

/-!
# Uniform bounds for `W(σ+it, ν)` on `1 ≤ σ ≤ 2`

On every vertical strip `a ≤ Re z ≤ b` with `a > 0`,
`|Γ(x+iy)| ≤ C (1+|y|)^M e^{−π|y|/2}` and `|1/Γ(x+iy)| ≤ C (1+|y|)^M e^{π|y|/2}` for all `y`
(`exists_bound_norm_Gamma_strip_all`, `exists_bound_norm_inv_Gamma_strip_all`; the corpus bounds for
`|y| ≥ 1` plus compactness).  With `W(b, ν) = √π 2^{−(b−½)} Γ(b−½+ν)Γ(b−½−ν)/Γ(b)` and
`|t+r| + |t−r| = 2 max(|t|, |r|)` this gives, uniformly in `1 ≤ σ ≤ 2`,

`|W(σ+it, ir)|² ≤ D (1+|t|)^L (1+|r|)^L e^{−π(2 max(|t|,|r|) − |t|)}`

(`exists_bound_norm_whittMellin_imag_sq`), and for the real parameters `0 ≤ ν ≤ ½`, through
`Γ(z) = Γ(z+1)/z`, `|W(σ+it, ν)|² ≤ D (1+|t|)^L e^{−π|t|} t⁻²` (`exists_bound_norm_whittMellin_real_sq`).
Both are combined for `ν = ν(λ)` in `exists_bound_norm_whittMellin_specParam_sq`.
-/

open Complex

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

/-! ## `Γ` and `1/Γ` on vertical strips -/

/-- **`|Γ(x+iy)| ≤ C (1+|y|)^M e^{−π|y|/2}`** on `a ≤ x ≤ b`, `0 < a`, for every `y`. -/
theorem exists_bound_norm_Gamma_strip_all {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∃ M : ℕ, 0 ≤ C ∧ ∀ x y : ℝ, a ≤ x → x ≤ b →
      ‖Complex.Gamma ((x : ℂ) + y * Complex.I)‖ ≤
        C * (1 + |y|) ^ M * Real.exp (-(Real.pi * |y| / 2)) := by
  obtain ⟨C₁, M, hC₁, h₁⟩ := HTGeometry.exists_bound_norm_Gamma_vertical_strip ha b
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Complex.Gamma ((p.1 : ℂ) + p.2 * Complex.I))
      (Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1) := fun p hp => by
    have hre : 0 < ((p.1 : ℂ) + p.2 * Complex.I).re := by simp; linarith [hp.1.1]
    have hg : ContinuousAt Complex.Gamma ((p.1 : ℂ) + p.2 * Complex.I) :=
      (Complex.differentiableAt_Gamma _ fun m => ne_neg_nat_of_re_pos hre m).continuousAt
    exact (ContinuousAt.comp (g := Complex.Gamma) (f := fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I)
      hg ((by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I).continuousAt)
      ).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ (max C₂ 0 * Real.exp (Real.pi / 2)), M, by positivity, fun x y hx1 hx2 => ?_⟩
  by_cases hy : 1 ≤ |y|
  · calc ‖Complex.Gamma ((x : ℂ) + y * Complex.I)‖ ≤ C₁ * |y| ^ M * Real.exp (-(Real.pi * |y| / 2)) :=
          h₁ x y hx1 hx2 hy
      _ ≤ max C₁ (max C₂ 0 * Real.exp (Real.pi / 2)) * (1 + |y|) ^ M *
          Real.exp (-(Real.pi * |y| / 2)) := by
          gcongr
          · exact le_max_left _ _
          · linarith
  · push Not at hy
    have hmem : (x, y) ∈ Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1 :=
      ⟨⟨hx1, hx2⟩, ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩⟩
    have h2 := hC₂ (x, y) hmem
    have he : Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * |y| / 2)) ≥ 1 := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [Real.pi_pos, abs_nonneg y])
    have hp : 1 ≤ (1 + |y|) ^ M := one_le_pow₀ (by linarith [abs_nonneg y])
    calc ‖Complex.Gamma ((x : ℂ) + y * Complex.I)‖ ≤ max C₂ 0 := h2.trans (le_max_left _ _)
      _ ≤ max C₂ 0 * (Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * |y| / 2))) :=
          le_mul_of_one_le_right (le_max_right _ _) he
      _ ≤ max C₂ 0 * Real.exp (Real.pi / 2) * (1 + |y|) ^ M * Real.exp (-(Real.pi * |y| / 2)) := by
          have : 0 ≤ max C₂ 0 * Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * |y| / 2)) := by
            positivity
          nlinarith
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- **`|1/Γ(x+iy)| ≤ C (1+|y|)^M e^{π|y|/2}`** on `a ≤ x ≤ b`, for every `y`. -/
theorem exists_bound_norm_inv_Gamma_strip_all (a b : ℝ) :
    ∃ C : ℝ, ∃ M : ℕ, 0 ≤ C ∧ ∀ x y : ℝ, a ≤ x → x ≤ b →
      ‖(Complex.Gamma ((x : ℂ) + y * Complex.I))⁻¹‖ ≤
        C * (1 + |y|) ^ M * Real.exp (Real.pi * |y| / 2) := by
  obtain ⟨C₁, M, hC₁, h₁⟩ := HTGeometry.exists_bound_norm_inv_Gamma_strip a b
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Complex.Gamma ((p.1 : ℂ) + p.2 * Complex.I))⁻¹)
      (Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp
      (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I)).continuousOn
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ (max C₂ 0), M, by positivity, fun x y hx1 hx2 => ?_⟩
  by_cases hy : 1 ≤ |y|
  · have h := h₁ ((x : ℂ) + y * Complex.I) (by simpa using hx1) (by simpa using hx2) (by simpa using hy)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_zero, zero_add, mul_one, add_zero] at h
    calc _ ≤ C₁ * |y| ^ M * Real.exp (Real.pi * |y| / 2) := h
      _ ≤ _ := by
          gcongr
          · exact le_max_left _ _
          · linarith
  · push Not at hy
    have hmem : (x, y) ∈ Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1 :=
      ⟨⟨hx1, hx2⟩, ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩⟩
    have h2 := hC₂ (x, y) hmem
    have hp : 1 ≤ (1 + |y|) ^ M * Real.exp (Real.pi * |y| / 2) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [abs_nonneg y]))
        (Real.one_le_exp (by positivity))
    calc _ ≤ max C₂ 0 := h2.trans (le_max_left _ _)
      _ ≤ max C₂ 0 * ((1 + |y|) ^ M * Real.exp (Real.pi * |y| / 2)) :=
          le_mul_of_one_le_right (le_max_right _ _) hp
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (by positivity)) (by positivity)

/-! ## The Whittaker–Mellin factor -/

theorem abs_add_add_abs_sub (t r : ℝ) : |t + r| + |t - r| = 2 * max |t| |r| := by
  rcases le_total 0 t with ht | ht <;> rcases le_total 0 r with hr | hr <;>
    rcases le_total |t| |r| with h | h <;>
    simp only [max_eq_left, max_eq_right, h] <;>
    rcases abs_cases t with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases r with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases (t + r) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rcases abs_cases (t - r) with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
    linarith

theorem norm_two_cpow_neg_le {b : ℂ} (hb : 1 / 2 ≤ b.re) : ‖(2 : ℂ) ^ (-(b - 1 / 2))‖ ≤ 1 := by
  rw [norm_two_cpow]
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
  simp only [Complex.neg_re, Complex.sub_re]
  norm_num
  linarith

/-- **`|W(σ+it, ir)|² ≤ D (1+|t|)^L (1+|r|)^L e^{−π(2 max(|t|,|r|) − |t|)}`**, `1 ≤ σ ≤ 2`. -/
theorem exists_bound_norm_whittMellin_imag_sq :
    ∃ D : ℝ, ∃ L : ℕ, 0 ≤ D ∧ ∀ σ t r : ℝ, 1 ≤ σ → σ ≤ 2 →
      ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 ≤
        D * (1 + |t|) ^ L * (1 + |r|) ^ L *
          Real.exp (-(Real.pi * (2 * max |t| |r| - |t|))) := by
  obtain ⟨C, M, hC, hG⟩ := exists_bound_norm_Gamma_strip_all (a := 1 / 2) (b := 3 / 2) (by norm_num)
  obtain ⟨C', M', hC', hI⟩ := exists_bound_norm_inv_Gamma_strip_all 1 2
  refine ⟨Real.pi * C ^ 4 * C' ^ 2, 4 * M + 2 * M', by positivity, fun σ t r h1 h2 => ?_⟩
  have hb : 1 / 2 < ((σ : ℂ) + t * Complex.I).re := by simp; linarith
  rw [whittMellin_eq hb]
  have e1 : (σ : ℂ) + t * Complex.I - 1 / 2 + r * Complex.I =
      (((σ - 1 / 2 : ℝ)) : ℂ) + ((t + r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have e2 : (σ : ℂ) + t * Complex.I - 1 / 2 - r * Complex.I =
      (((σ - 1 / 2 : ℝ)) : ℂ) + ((t - r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [e1, e2, div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul]
  have hA := hG (σ - 1 / 2) (t + r) (by linarith) (by linarith)
  have hB := hG (σ - 1 / 2) (t - r) (by linarith) (by linarith)
  have hR := hI σ t h1 h2
  have h2c := norm_two_cpow_neg_le (b := (σ : ℂ) + t * Complex.I) (by simp; linarith)
  have hsq : ‖(Real.sqrt Real.pi : ℂ)‖ = Real.sqrt Real.pi := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [hsq]
  have htr : (1 + |t + r|) ≤ (1 + |t|) * (1 + |r|) := by
    have := abs_add_le t r; nlinarith [abs_nonneg t, abs_nonneg r]
  have htr' : (1 + |t - r|) ≤ (1 + |t|) * (1 + |r|) := by
    have := abs_sub t r; nlinarith [abs_nonneg t, abs_nonneg r]
  set P := ‖Complex.Gamma ((((σ - 1 / 2 : ℝ)) : ℂ) + ((t + r : ℝ) : ℂ) * Complex.I)‖
  set Q := ‖Complex.Gamma ((((σ - 1 / 2 : ℝ)) : ℂ) + ((t - r : ℝ) : ℂ) * Complex.I)‖
  set R := ‖(Complex.Gamma ((σ : ℂ) + t * Complex.I))⁻¹‖
  set T := ‖(2 : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2))‖
  have hP0 : 0 ≤ P := norm_nonneg _
  have hQ0 : 0 ≤ Q := norm_nonneg _
  have hR0 : 0 ≤ R := norm_nonneg _
  have hT0 : 0 ≤ T := norm_nonneg _
  have hexp : Real.exp (-(Real.pi * |t + r| / 2)) * Real.exp (-(Real.pi * |t - r| / 2)) *
      Real.exp (Real.pi * |t| / 2) = Real.exp (-(Real.pi * (2 * max |t| |r| - |t|)) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1
    have h := abs_add_add_abs_sub t r
    linear_combination (-(Real.pi) / 2) * h
  have hmain : Real.sqrt Real.pi * T * P * Q * R ≤ Real.sqrt Real.pi * 1 *
      (C * ((1 + |t|) * (1 + |r|)) ^ M * Real.exp (-(Real.pi * |t + r| / 2))) *
      (C * ((1 + |t|) * (1 + |r|)) ^ M * Real.exp (-(Real.pi * |t - r| / 2))) *
      (C' * (1 + |t|) ^ M' * Real.exp (Real.pi * |t| / 2)) := by
    gcongr
    · exact hA.trans (by gcongr)
    · exact hB.trans (by gcongr)
  have hsqrt : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  calc (Real.sqrt Real.pi * T * P * Q * R) ^ 2
      ≤ (Real.sqrt Real.pi * 1 *
        (C * ((1 + |t|) * (1 + |r|)) ^ M * Real.exp (-(Real.pi * |t + r| / 2))) *
        (C * ((1 + |t|) * (1 + |r|)) ^ M * Real.exp (-(Real.pi * |t - r| / 2))) *
        (C' * (1 + |t|) ^ M' * Real.exp (Real.pi * |t| / 2))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hmain 2
    _ = Real.sqrt Real.pi ^ 2 * C ^ 4 * C' ^ 2 * (1 + |t|) ^ (4 * M + 2 * M') * (1 + |r|) ^ (4 * M) *
          (Real.exp (-(Real.pi * |t + r| / 2)) * Real.exp (-(Real.pi * |t - r| / 2)) *
            Real.exp (Real.pi * |t| / 2)) ^ 2 := by rw [mul_pow (1 + |t|) (1 + |r|)]; ring
    _ = Real.pi * C ^ 4 * C' ^ 2 * (1 + |t|) ^ (4 * M + 2 * M') * (1 + |r|) ^ (4 * M) *
          (Real.exp (-(Real.pi * |t + r| / 2)) * Real.exp (-(Real.pi * |t - r| / 2)) *
            Real.exp (Real.pi * |t| / 2)) ^ 2 := by rw [hsqrt]
    _ ≤ Real.pi * C ^ 4 * C' ^ 2 * (1 + |t|) ^ (4 * M + 2 * M') * (1 + |r|) ^ (4 * M + 2 * M') *
          (Real.exp (-(Real.pi * |t + r| / 2)) * Real.exp (-(Real.pi * |t - r| / 2)) *
            Real.exp (Real.pi * |t| / 2)) ^ 2 := by
        gcongr
        · linarith [abs_nonneg r]
        · omega
    _ = _ := by
        rw [hexp, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(Real.pi * (2 * max |t| |r| - |t|)) / 2) =
          -(Real.pi * (2 * max |t| |r| - |t|)) by push_cast; ring]

/-- **`|W(σ+it, ν)|² ≤ D (1+|t|)^L e^{−π|t|} t⁻²`** for `0 ≤ ν ≤ ½`, `1 ≤ σ ≤ 2`, `t ≠ 0`. -/
theorem exists_bound_norm_whittMellin_real_sq :
    ∃ D : ℝ, ∃ L : ℕ, 0 ≤ D ∧ ∀ σ t ν : ℝ, 1 ≤ σ → σ ≤ 2 → 0 ≤ ν → ν ≤ 1 / 2 → t ≠ 0 →
      ‖whittMellin ((σ : ℂ) + t * Complex.I) ν‖ ^ 2 ≤
        D * (1 + |t|) ^ L * Real.exp (-(Real.pi * |t|)) * (t ^ 2)⁻¹ := by
  obtain ⟨C, M, hC, hG⟩ := exists_bound_norm_Gamma_strip_all (a := 1 / 2) (b := 5 / 2) (by norm_num)
  obtain ⟨C', M', hC', hI⟩ := exists_bound_norm_inv_Gamma_strip_all 1 2
  refine ⟨Real.pi * C ^ 4 * C' ^ 2, 4 * M + 2 * M', by positivity, fun σ t ν h1 h2 hν0 hν1 ht => ?_⟩
  have hb : 1 / 2 < ((σ : ℂ) + t * Complex.I).re := by simp; linarith
  rw [whittMellin_eq hb]
  set x₀ : ℝ := σ - 1 / 2 - ν with hx₀
  have e1 : (σ : ℂ) + t * Complex.I - 1 / 2 + ν =
      (((σ - 1 / 2 + ν : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
  have e2 : (σ : ℂ) + t * Complex.I - 1 / 2 - ν = (x₀ : ℂ) + (t : ℂ) * Complex.I := by
    rw [hx₀]; push_cast; ring
  have hne : (x₀ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h; apply ht; have := congrArg Complex.im h; simpa using this
  have hshift : Complex.Gamma ((x₀ : ℂ) + (t : ℂ) * Complex.I) =
      Complex.Gamma ((((x₀ + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I) / ((x₀ : ℂ) + (t : ℂ) * Complex.I) := by
    rw [eq_div_iff hne, mul_comm, ← Complex.Gamma_add_one _ hne]; congr 1; push_cast; ring
  have hden : |t| ≤ ‖(x₀ : ℂ) + (t : ℂ) * Complex.I‖ := by
    have := Complex.abs_im_le_norm ((x₀ : ℂ) + (t : ℂ) * Complex.I); simpa using this
  set P := ‖Complex.Gamma ((((σ - 1 / 2 + ν : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ with hP
  set Q := ‖Complex.Gamma ((((x₀ + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ with hQ
  set Z := ‖(x₀ : ℂ) + (t : ℂ) * Complex.I‖ with hZ
  set R := ‖(Complex.Gamma ((σ : ℂ) + t * Complex.I))⁻¹‖ with hR
  set T := ‖(2 : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2))‖ with hT
  have hnorm : ‖(Real.sqrt Real.pi : ℂ) * (2 : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2)) *
      Complex.Gamma ((σ : ℂ) + t * Complex.I - 1 / 2 + ν) *
      Complex.Gamma ((σ : ℂ) + t * Complex.I - 1 / 2 - ν) / Complex.Gamma ((σ : ℂ) + t * Complex.I)‖ =
      Real.sqrt Real.pi * T * P * (Q / Z) * R := by
    rw [e1, e2, hshift, norm_div, norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), hR, norm_inv, div_eq_mul_inv _ ‖Complex.Gamma _‖]
  rw [hnorm]
  have hA := hG (σ - 1 / 2 + ν) t (by linarith) (by linarith)
  have hB := hG (x₀ + 1) t (by rw [hx₀]; linarith) (by rw [hx₀]; linarith)
  have hRb := hI σ t h1 h2
  have h2c := norm_two_cpow_neg_le (b := (σ : ℂ) + t * Complex.I) (by simp; linarith)
  have htpos : 0 < |t| := abs_pos.2 ht
  have hQZ : Q / Z ≤ (C * (1 + |t|) ^ M * Real.exp (-(Real.pi * |t| / 2))) / |t| :=
    (div_le_div_of_nonneg_left (norm_nonneg _) htpos hden).trans
      (div_le_div_of_nonneg_right hB htpos.le)
  have hmain : Real.sqrt Real.pi * T * P * (Q / Z) * R ≤ Real.sqrt Real.pi * 1 *
      (C * (1 + |t|) ^ M * Real.exp (-(Real.pi * |t| / 2))) *
      ((C * (1 + |t|) ^ M * Real.exp (-(Real.pi * |t| / 2))) / |t|) *
      (C' * (1 + |t|) ^ M' * Real.exp (Real.pi * |t| / 2)) := by
    have hP0 : 0 ≤ P := norm_nonneg _
    have hQ0 : 0 ≤ Q / Z := div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hR0 : 0 ≤ R := norm_nonneg _
    have hT0 : 0 ≤ T := norm_nonneg _
    gcongr
  have hsqrt : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hexp : (Real.exp (-(Real.pi * |t| / 2)) * Real.exp (-(Real.pi * |t| / 2)) *
      Real.exp (Real.pi * |t| / 2)) ^ 2 = Real.exp (-(Real.pi * |t|)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  calc (Real.sqrt Real.pi * T * P * (Q / Z) * R) ^ 2 ≤ _ := pow_le_pow_left₀ (by positivity) hmain 2
    _ = Real.sqrt Real.pi ^ 2 * C ^ 4 * C' ^ 2 * (1 + |t|) ^ (4 * M + 2 * M') *
          (Real.exp (-(Real.pi * |t| / 2)) * Real.exp (-(Real.pi * |t| / 2)) *
            Real.exp (Real.pi * |t| / 2)) ^ 2 * (|t| ^ 2)⁻¹ := by
        field_simp
        ring
    _ = _ := by rw [hsqrt, hexp, ht2]

/-- **Uniform bound for `ν = ν(λ)`**: `|W(σ+it, ν(λ))|² ≤ D (1+|t|)^L (1+κ)^L e^{−π(2max(|t|,κ)−|t|)}
(1 + t⁻²)`, `κ = κ(λ)`, `1 ≤ σ ≤ 2`, `t ≠ 0`, `λ ≥ 0`. -/
theorem exists_bound_norm_whittMellin_specParam_sq :
    ∃ D : ℝ, ∃ L : ℕ, 0 ≤ D ∧ ∀ σ t lam : ℝ, 1 ≤ σ → σ ≤ 2 → 0 ≤ lam → t ≠ 0 →
      ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 ≤
        D * (1 + |t|) ^ L * (1 + specKappa lam) ^ L *
          Real.exp (-(Real.pi * (2 * max |t| (specKappa lam) - |t|))) * (1 + (t ^ 2)⁻¹) := by
  obtain ⟨D₁, L₁, hD₁, h₁⟩ := exists_bound_norm_whittMellin_imag_sq
  obtain ⟨D₂, L₂, hD₂, h₂⟩ := exists_bound_norm_whittMellin_real_sq
  refine ⟨D₁ + D₂, L₁ + L₂, by positivity, fun σ t lam h1 h2 hlam ht => ?_⟩
  have hκ0 : 0 ≤ specKappa lam := Real.sqrt_nonneg _
  have ht2 : 0 ≤ (t ^ 2)⁻¹ := by positivity
  have hp1 : 1 ≤ (1 + |t|) ^ (L₁ + L₂) := one_le_pow₀ (by linarith [abs_nonneg t])
  have hp2 : 1 ≤ (1 + specKappa lam) ^ (L₁ + L₂) := one_le_pow₀ (by linarith)
  unfold specParam
  split_ifs with h
  · -- `λ ≤ ¼`: real parameter, `κ = 0`
    have hκ : specKappa lam = 0 := by
      unfold specKappa; rw [max_eq_right (by linarith), Real.sqrt_zero]
    rw [hκ]
    have hν0 : 0 ≤ Real.sqrt (1 / 4 - lam) := Real.sqrt_nonneg _
    have hν1 : Real.sqrt (1 / 4 - lam) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    refine (h₂ σ t _ h1 h2 hν0 hν1 ht).trans ?_
    rw [max_eq_left (abs_nonneg t), show 2 * |t| - |t| = |t| by ring, add_zero, one_pow, mul_one]
    have hp : (1 + |t|) ^ L₂ ≤ (1 + |t|) ^ (L₁ + L₂) :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
    have hD : D₂ ≤ D₁ + D₂ := by linarith
    have hE := Real.exp_pos (-(Real.pi * |t|))
    calc D₂ * (1 + |t|) ^ L₂ * Real.exp (-(Real.pi * |t|)) * (t ^ 2)⁻¹
        ≤ (D₁ + D₂) * (1 + |t|) ^ (L₁ + L₂) * Real.exp (-(Real.pi * |t|)) * (t ^ 2)⁻¹ := by gcongr
      _ ≤ _ := by
          have : 0 ≤ (D₁ + D₂) * (1 + |t|) ^ (L₁ + L₂) * Real.exp (-(Real.pi * |t|)) := by positivity
          nlinarith
  · -- `λ > ¼`: imaginary parameter `ν = iκ`
    have hκ : specKappa lam = Real.sqrt (lam - 1 / 4) := by
      unfold specKappa; rw [max_eq_left (by linarith)]
    rw [hκ, mul_comm Complex.I]
    refine (h₁ σ t _ h1 h2).trans ?_
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hpt : (1 + |t|) ^ L₁ ≤ (1 + |t|) ^ (L₁ + L₂) :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
    have hpr : (1 + Real.sqrt (lam - 1 / 4)) ^ L₁ ≤ (1 + Real.sqrt (lam - 1 / 4)) ^ (L₁ + L₂) :=
      pow_le_pow_right₀ (by linarith [Real.sqrt_nonneg (lam - 1 / 4)]) (by omega)
    have hD : D₁ ≤ D₁ + D₂ := by linarith
    have hE := Real.exp_pos (-(Real.pi * (2 * max |t| (Real.sqrt (lam - 1 / 4)) - |t|)))
    calc D₁ * (1 + |t|) ^ L₁ * (1 + Real.sqrt (lam - 1 / 4)) ^ L₁ *
          Real.exp (-(Real.pi * (2 * max |t| (Real.sqrt (lam - 1 / 4)) - |t|)))
        ≤ (D₁ + D₂) * (1 + |t|) ^ (L₁ + L₂) * (1 + Real.sqrt (lam - 1 / 4)) ^ (L₁ + L₂) *
          Real.exp (-(Real.pi * (2 * max |t| (Real.sqrt (lam - 1 / 4)) - |t|))) := by gcongr
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith)

end

end GaloisForLFunctions.RHTower.DeckPointPair
