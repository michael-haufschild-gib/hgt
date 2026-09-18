import GaloisForLFunctions.HTGeometry.EulerMaclaurinSecondOrder

/-!
# Envelope of a weighted block Dirichlet sum

For integers `1 ≤ K₁ < K₂`, an exponent `a ≥ 3` and a real frequency `u`, the block sum
`S(u) = Σ_{K₁ ≤ k ≤ K₂} k^{a+iu} / K₂^a` is compared with the integral
`K₂^{-a} ∫_{K₁}^{K₂} x^{a+iu} dx = K₂^{-a} (K₂^{s+1} − K₁^{s+1})/(s+1)`, `s = a + iu`, by
second-order Euler–Maclaurin.  The integral has modulus between `(K₂^{a+1} − K₁^{a+1})/(K₂^a |s+1|)`
and `(K₂^{a+1} + K₁^{a+1})/(K₂^a |s+1|)`, and the Euler–Maclaurin remainder is at most
`1 + (K₂ − K₁)(a+|u|)(a+1+|u|)/(8K₂²)`.  For large `a` the envelope is nearly monotone in `|u|`.
-/

open Complex Set Finset intervalIntegral MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The complex exponent `a + iu`. -/
def blockExponent (a : ℕ) (u : ℝ) : ℂ := (a : ℂ) + (u : ℂ) * I

/-- The weighted block sum `Σ_{K₁ ≤ k ≤ K₂} k^{a+iu} / K₂^a`. -/
def blockSum (K₁ K₂ a : ℕ) (u : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc K₁ K₂, (k : ℂ) ^ blockExponent a u / (K₂ : ℂ) ^ a

/-- The block integral `K₂^{-a}(K₂^{s+1} − K₁^{s+1})/(s+1)`. -/
def blockIntegral (K₁ K₂ a : ℕ) (u : ℝ) : ℂ :=
  ((K₂ : ℂ) ^ (blockExponent a u + 1) - (K₁ : ℂ) ^ (blockExponent a u + 1)) /
    (blockExponent a u + 1) / (K₂ : ℂ) ^ a

@[simp] theorem blockExponent_re (a : ℕ) (u : ℝ) : (blockExponent a u).re = a := by
  simp [blockExponent]

@[simp] theorem blockExponent_im (a : ℕ) (u : ℝ) : (blockExponent a u).im = u := by
  simp [blockExponent]

theorem blockExponent_ne_zero {a : ℕ} (ha : 1 ≤ a) (u : ℝ) : blockExponent a u ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  omega

theorem blockExponent_sub_one_ne_zero {a : ℕ} (ha : 2 ≤ a) (u : ℝ) :
    blockExponent a u - 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have : (a : ℝ) = 1 := by linarith
  have : a = 1 := by exact_mod_cast this
  omega

theorem blockExponent_sub_two_ne_zero {a : ℕ} (ha : 3 ≤ a) (u : ℝ) :
    blockExponent a u - 2 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have : (a : ℝ) = 2 := by linarith
  have : a = 2 := by exact_mod_cast this
  omega

theorem norm_blockExponent_le (a : ℕ) (u : ℝ) : ‖blockExponent a u‖ ≤ a + |u| := by
  unfold blockExponent
  calc ‖(a : ℂ) + (u : ℂ) * I‖ ≤ ‖(a : ℂ)‖ + ‖(u : ℂ) * I‖ := norm_add_le _ _
    _ = a + |u| := by simp [Complex.norm_real, Real.norm_eq_abs]

theorem norm_blockExponent_sub_one_le (a : ℕ) (u : ℝ) :
    ‖blockExponent a u - 1‖ ≤ a + 1 + |u| := by
  unfold blockExponent
  calc ‖(a : ℂ) + (u : ℂ) * I - 1‖ = ‖((a : ℂ) - 1) + (u : ℂ) * I‖ := by ring_nf
    _ ≤ ‖(a : ℂ) - 1‖ + ‖(u : ℂ) * I‖ := norm_add_le _ _
    _ ≤ (‖(a : ℂ)‖ + ‖(1 : ℂ)‖) + |u| := by
        gcongr
        · exact norm_sub_le _ _
        · simp [Complex.norm_real, Real.norm_eq_abs]
    _ = a + 1 + |u| := by simp

theorem norm_blockExponent_add_one (a : ℕ) (u : ℝ) :
    ‖blockExponent a u + 1‖ = Real.sqrt (((a : ℝ) + 1) ^ 2 + u ^ 2) := by
  unfold blockExponent
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

/-! ## The Euler–Maclaurin comparison -/

section EM

variable {K₁ K₂ a : ℕ} {u : ℝ}

/-- The shifted summand `x ↦ (x + K₁)^{s} / K₂^a`. -/
def blockShifted (K₁ K₂ a : ℕ) (u : ℝ) (x : ℝ) : ℂ :=
  ((x + K₁ : ℝ) : ℂ) ^ blockExponent a u / (K₂ : ℂ) ^ a

def blockShifted' (K₁ K₂ a : ℕ) (u : ℝ) (x : ℝ) : ℂ :=
  blockExponent a u * ((x + K₁ : ℝ) : ℂ) ^ (blockExponent a u - 1) / (K₂ : ℂ) ^ a

def blockShifted'' (K₁ K₂ a : ℕ) (u : ℝ) (x : ℝ) : ℂ :=
  blockExponent a u * (blockExponent a u - 1) * ((x + K₁ : ℝ) : ℂ) ^ (blockExponent a u - 2) /
    (K₂ : ℂ) ^ a

theorem hasDerivAt_blockShifted (h1 : 1 ≤ K₁) (ha : 1 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (blockShifted K₁ K₂ a u) (blockShifted' K₁ K₂ a u x) x := by
  have hne : x + (K₁ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K₁ := by exact_mod_cast h1
    linarith
  have h := hasDerivAt_ofReal_cpow_const hne (blockExponent_ne_zero ha u)
  have h2 := (h.comp_add_const x (K₁ : ℝ)).div_const ((K₂ : ℂ) ^ a)
  exact h2

theorem hasDerivAt_blockShifted' (h1 : 1 ≤ K₁) (ha : 2 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (blockShifted' K₁ K₂ a u) (blockShifted'' K₁ K₂ a u x) x := by
  have hne : x + (K₁ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K₁ := by exact_mod_cast h1
    linarith
  have h := hasDerivAt_ofReal_cpow_const hne (blockExponent_sub_one_ne_zero ha u)
  have h2 := (((h.comp_add_const x (K₁ : ℝ)).const_mul (blockExponent a u)).div_const
    ((K₂ : ℂ) ^ a))
  refine h2.congr_deriv ?_
  unfold blockShifted''
  rw [show blockExponent a u - 1 - 1 = blockExponent a u - 2 by ring]
  ring

theorem continuousOn_blockShifted'' (h1 : 1 ≤ K₁) (ha : 3 ≤ a) :
    ContinuousOn (blockShifted'' K₁ K₂ a u) (Ici (0 : ℝ)) := by
  intro x hx
  have hne : x + (K₁ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K₁ := by exact_mod_cast h1
    have : 0 ≤ x := hx
    linarith
  have h := hasDerivAt_ofReal_cpow_const hne (blockExponent_sub_two_ne_zero ha u)
  have h2 := (((h.comp_add_const x (K₁ : ℝ)).const_mul
    (blockExponent a u * (blockExponent a u - 1))).div_const ((K₂ : ℂ) ^ a))
  exact h2.continuousAt.continuousWithinAt

/-- Euler–Maclaurin for the block sum. -/
theorem blockSum_eq_em (h1 : 1 ≤ K₁) (h12 : K₁ ≤ K₂) (ha : 3 ≤ a) :
    blockSum K₁ K₂ a u =
      (∫ x in (0 : ℝ)..((K₂ - K₁ : ℕ) : ℝ), blockShifted K₁ K₂ a u x) +
        (blockShifted K₁ K₂ a u 0 + blockShifted K₁ K₂ a u ((K₂ - K₁ : ℕ) : ℝ)) / 2 -
        ∫ x in (0 : ℝ)..((K₂ - K₁ : ℕ) : ℝ),
          ((bernoulliHalfPer x : ℝ) : ℂ) * blockShifted'' K₁ K₂ a u x := by
  have hem := euler_maclaurin_second_order (f := blockShifted K₁ K₂ a u)
    (f' := blockShifted' K₁ K₂ a u) (f'' := blockShifted'' K₁ K₂ a u) (K₂ - K₁)
    (fun x hx => hasDerivAt_blockShifted h1 (by omega) hx)
    (fun x hx => hasDerivAt_blockShifted' h1 (by omega) hx)
    (continuousOn_blockShifted'' h1 ha)
  rw [← hem]
  unfold blockSum
  have hIcc : Finset.Icc K₁ K₂ = Finset.Ico K₁ (K₂ + 1) := by
    ext k; simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range, show K₂ + 1 - K₁ = (K₂ - K₁) + 1 by omega]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold blockShifted
  congr 2
  push_cast
  ring

theorem integral_blockShifted (h12 : K₁ ≤ K₂) :
    (∫ x in (0 : ℝ)..((K₂ - K₁ : ℕ) : ℝ), blockShifted K₁ K₂ a u x) =
      blockIntegral K₁ K₂ a u := by
  unfold blockShifted blockIntegral
  rw [intervalIntegral.integral_div]
  congr 1
  have := intervalIntegral.integral_comp_add_right (fun y : ℝ => ((y : ℝ) : ℂ) ^ blockExponent a u)
    (K₁ : ℝ) (a := 0) (b := ((K₂ - K₁ : ℕ) : ℝ))
  rw [this, zero_add, show ((K₂ - K₁ : ℕ) : ℝ) + (K₁ : ℝ) = (K₂ : ℝ) by
    rw [Nat.cast_sub h12]; ring]
  have hre : (-1 : ℝ) < (blockExponent a u).re := by
    rw [blockExponent_re]
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  rw [integral_cpow (Or.inl hre)]
  simp

theorem norm_blockShifted_zero_le (h1 : 1 ≤ K₁) (h12 : K₁ ≤ K₂) :
    ‖blockShifted K₁ K₂ a u 0‖ ≤ 1 := by
  unfold blockShifted
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have hK₁pos : (0 : ℝ) < K₁ := by exact_mod_cast h1
  have hK₂pos : (0 : ℝ) < K₂ := by
    linarith [(by exact_mod_cast h12 : (K₁ : ℝ) ≤ K₂)]
  rw [div_le_one (by positivity)]
  rw [zero_add, Complex.norm_cpow_eq_rpow_re_of_pos hK₁pos, blockExponent_re,
    Real.rpow_natCast]
  exact pow_le_pow_left₀ hK₁pos.le (by exact_mod_cast h12) a

theorem norm_blockShifted_end (h12 : K₁ ≤ K₂) (hK₂ : 1 ≤ K₂) :
    ‖blockShifted K₁ K₂ a u ((K₂ - K₁ : ℕ) : ℝ)‖ = 1 := by
  unfold blockShifted
  have hK₂pos : (0 : ℝ) < K₂ := by exact_mod_cast hK₂
  rw [show ((K₂ - K₁ : ℕ) : ℝ) + (K₁ : ℝ) = (K₂ : ℝ) by rw [Nat.cast_sub h12]; ring]
  rw [norm_div, norm_pow, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hK₂pos,
    blockExponent_re, Real.rpow_natCast, div_self (by positivity)]

theorem norm_blockShifted''_le (h1 : 1 ≤ K₁) (h12 : K₁ ≤ K₂) (ha : 2 ≤ a) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ ((K₂ - K₁ : ℕ) : ℝ)) :
    ‖blockShifted'' K₁ K₂ a u x‖ ≤ (a + |u|) * (a + 1 + |u|) / (K₂ : ℝ) ^ 2 := by
  unfold blockShifted''
  have hK₁pos : (0 : ℝ) < K₁ := by exact_mod_cast h1
  have hK₂pos : (0 : ℝ) < K₂ := by linarith [(by exact_mod_cast h12 : (K₁ : ℝ) ≤ K₂)]
  have hxpos : 0 < x + (K₁ : ℝ) := by linarith
  have hxK : x + (K₁ : ℝ) ≤ K₂ := by
    rw [Nat.cast_sub h12] at hx; linarith
  rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  have hre : (blockExponent a u - 2).re = (a : ℝ) - 2 := by simp
  rw [hre]
  have hpow : (x + (K₁ : ℝ)) ^ ((a : ℝ) - 2) ≤ (K₂ : ℝ) ^ ((a : ℝ) - 2) :=
    Real.rpow_le_rpow hxpos.le hxK (by
      have : (2 : ℝ) ≤ a := by exact_mod_cast ha
      linarith)
  have hK2 : (K₂ : ℝ) ^ ((a : ℝ) - 2) / (K₂ : ℝ) ^ a = 1 / (K₂ : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast (K₂ : ℝ) a, ← Real.rpow_natCast (K₂ : ℝ) 2,
      div_eq_iff (by positivity), one_div, ← Real.rpow_neg hK₂pos.le, ← Real.rpow_add hK₂pos]
    push_cast; ring_nf
  calc ‖blockExponent a u‖ * ‖blockExponent a u - 1‖ * (x + (K₁ : ℝ)) ^ ((a : ℝ) - 2) /
        (K₂ : ℝ) ^ a
      ≤ (a + |u|) * (a + 1 + |u|) * (K₂ : ℝ) ^ ((a : ℝ) - 2) / (K₂ : ℝ) ^ a := by
        gcongr
        · exact norm_blockExponent_le a u
        · exact norm_blockExponent_sub_one_le a u
    _ = (a + |u|) * (a + 1 + |u|) * ((K₂ : ℝ) ^ ((a : ℝ) - 2) / (K₂ : ℝ) ^ a) := by ring
    _ = (a + |u|) * (a + 1 + |u|) / (K₂ : ℝ) ^ 2 := by rw [hK2]; ring

/-- The Euler–Maclaurin remainder bound. -/
theorem norm_blockSum_sub_blockIntegral_le (h1 : 1 ≤ K₁) (h12 : K₁ ≤ K₂) (ha : 3 ≤ a) :
    ‖blockSum K₁ K₂ a u - blockIntegral K₁ K₂ a u‖ ≤
      1 + ((K₂ - K₁ : ℕ) : ℝ) * ((a + |u|) * (a + 1 + |u|)) / (8 * (K₂ : ℝ) ^ 2) := by
  have hK₂ : 1 ≤ K₂ := le_trans h1 h12
  rw [blockSum_eq_em h1 h12 ha, integral_blockShifted h12]
  have hN0 : (0 : ℝ) ≤ ((K₂ - K₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) ((K₂ - K₁ : ℕ) : ℝ),
      ‖((bernoulliHalfPer x : ℝ) : ℂ) * blockShifted'' K₁ K₂ a u x‖ ≤
        (1 / 8) * ((a + |u|) * (a + 1 + |u|) / (K₂ : ℝ) ^ 2) := by
    intro x hx
    rw [Set.uIoc_of_le hN0] at hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    · exact abs_bernoulliHalfPer_le x
    · exact norm_blockShifted''_le h1 h12 (by omega) hx.1.le hx.2
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [sub_zero, abs_of_nonneg hN0] at hint
  have hbdry : ‖(blockShifted K₁ K₂ a u 0 + blockShifted K₁ K₂ a u ((K₂ - K₁ : ℕ) : ℝ)) / 2‖ ≤ 1 := by
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le (blockShifted K₁ K₂ a u 0) (blockShifted K₁ K₂ a u ((K₂ - K₁ : ℕ) : ℝ))
    have h0 := norm_blockShifted_zero_le (u := u) (a := a) h1 h12
    have hend := norm_blockShifted_end (u := u) (a := a) h12 hK₂
    linarith
  calc ‖blockIntegral K₁ K₂ a u +
        (blockShifted K₁ K₂ a u 0 + blockShifted K₁ K₂ a u ((K₂ - K₁ : ℕ) : ℝ)) / 2 -
        (∫ x in (0 : ℝ)..((K₂ - K₁ : ℕ) : ℝ),
          ((bernoulliHalfPer x : ℝ) : ℂ) * blockShifted'' K₁ K₂ a u x) -
        blockIntegral K₁ K₂ a u‖
      = ‖(blockShifted K₁ K₂ a u 0 + blockShifted K₁ K₂ a u ((K₂ - K₁ : ℕ) : ℝ)) / 2 -
        (∫ x in (0 : ℝ)..((K₂ - K₁ : ℕ) : ℝ),
          ((bernoulliHalfPer x : ℝ) : ℂ) * blockShifted'' K₁ K₂ a u x)‖ := by
        congr 1; ring
    _ ≤ ‖(blockShifted K₁ K₂ a u 0 + blockShifted K₁ K₂ a u ((K₂ - K₁ : ℕ) : ℝ)) / 2‖ +
        ‖∫ x in (0 : ℝ)..((K₂ - K₁ : ℕ) : ℝ),
          ((bernoulliHalfPer x : ℝ) : ℂ) * blockShifted'' K₁ K₂ a u x‖ := norm_sub_le _ _
    _ ≤ 1 + (1 / 8) * ((a + |u|) * (a + 1 + |u|) / (K₂ : ℝ) ^ 2) * ((K₂ - K₁ : ℕ) : ℝ) :=
        add_le_add hbdry hint
    _ = _ := by ring

end EM

/-! ## The modulus of the block integral -/

section Modulus

variable {K₁ K₂ a : ℕ} {u : ℝ}

theorem norm_blockIntegral_eq :
    ‖blockIntegral K₁ K₂ a u‖ =
      ‖(K₂ : ℂ) ^ (blockExponent a u + 1) - (K₁ : ℂ) ^ (blockExponent a u + 1)‖ /
        (Real.sqrt (((a : ℝ) + 1) ^ 2 + u ^ 2) * (K₂ : ℝ) ^ a) := by
  unfold blockIntegral
  rw [norm_div, norm_div, norm_pow, Complex.norm_natCast, norm_blockExponent_add_one, div_div]

theorem norm_natCast_cpow_blockExponent_add_one {K : ℕ} (hK : 1 ≤ K) (a : ℕ) (u : ℝ) :
    ‖(K : ℂ) ^ (blockExponent a u + 1)‖ = (K : ℝ) ^ (a + 1) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  rw [show (K : ℂ) = ((K : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hKpos]
  have : (blockExponent a u + 1).re = ((a + 1 : ℕ) : ℝ) := by simp
  rw [this, Real.rpow_natCast]

theorem norm_blockIntegral_ge (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) :
    ((K₂ : ℝ) ^ (a + 1) - (K₁ : ℝ) ^ (a + 1)) /
        (Real.sqrt (((a : ℝ) + 1) ^ 2 + u ^ 2) * (K₂ : ℝ) ^ a) ≤
      ‖blockIntegral K₁ K₂ a u‖ := by
  rw [norm_blockIntegral_eq]
  gcongr
  calc (K₂ : ℝ) ^ (a + 1) - (K₁ : ℝ) ^ (a + 1)
      = ‖(K₂ : ℂ) ^ (blockExponent a u + 1)‖ - ‖(K₁ : ℂ) ^ (blockExponent a u + 1)‖ := by
        rw [norm_natCast_cpow_blockExponent_add_one hK₂,
          norm_natCast_cpow_blockExponent_add_one hK₁]
    _ ≤ _ := norm_sub_norm_le _ _

theorem norm_blockIntegral_le (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) :
    ‖blockIntegral K₁ K₂ a u‖ ≤
      ((K₂ : ℝ) ^ (a + 1) + (K₁ : ℝ) ^ (a + 1)) /
        (Real.sqrt (((a : ℝ) + 1) ^ 2 + u ^ 2) * (K₂ : ℝ) ^ a) := by
  rw [norm_blockIntegral_eq]
  gcongr
  calc ‖(K₂ : ℂ) ^ (blockExponent a u + 1) - (K₁ : ℂ) ^ (blockExponent a u + 1)‖
      ≤ ‖(K₂ : ℂ) ^ (blockExponent a u + 1)‖ + ‖(K₁ : ℂ) ^ (blockExponent a u + 1)‖ :=
        norm_sub_le _ _
    _ = _ := by
        rw [norm_natCast_cpow_blockExponent_add_one hK₂,
          norm_natCast_cpow_blockExponent_add_one hK₁]

/-- **The two-sided envelope of the block sum.** -/
theorem norm_blockSum_ge (h1 : 1 ≤ K₁) (h12 : K₁ ≤ K₂) (ha : 3 ≤ a) :
    ((K₂ : ℝ) ^ (a + 1) - (K₁ : ℝ) ^ (a + 1)) /
        (Real.sqrt (((a : ℝ) + 1) ^ 2 + u ^ 2) * (K₂ : ℝ) ^ a) -
      (1 + ((K₂ - K₁ : ℕ) : ℝ) * ((a + |u|) * (a + 1 + |u|)) / (8 * (K₂ : ℝ) ^ 2)) ≤
      ‖blockSum K₁ K₂ a u‖ := by
  have hK₂ : 1 ≤ K₂ := le_trans h1 h12
  have h := norm_blockSum_sub_blockIntegral_le (u := u) h1 h12 ha
  have h2 := norm_blockIntegral_ge (u := u) (a := a) h1 hK₂
  have h3 := norm_sub_norm_le (blockIntegral K₁ K₂ a u) (blockSum K₁ K₂ a u)
  rw [norm_sub_rev] at h3
  linarith

theorem norm_blockSum_le (h1 : 1 ≤ K₁) (h12 : K₁ ≤ K₂) (ha : 3 ≤ a) :
    ‖blockSum K₁ K₂ a u‖ ≤
      ((K₂ : ℝ) ^ (a + 1) + (K₁ : ℝ) ^ (a + 1)) /
        (Real.sqrt (((a : ℝ) + 1) ^ 2 + u ^ 2) * (K₂ : ℝ) ^ a) +
      (1 + ((K₂ - K₁ : ℕ) : ℝ) * ((a + |u|) * (a + 1 + |u|)) / (8 * (K₂ : ℝ) ^ 2)) := by
  have hK₂ : 1 ≤ K₂ := le_trans h1 h12
  have h := norm_blockSum_sub_blockIntegral_le (u := u) h1 h12 ha
  have h2 := norm_blockIntegral_le (u := u) (a := a) h1 hK₂
  have h3 := norm_sub_norm_le (blockSum K₁ K₂ a u) (blockIntegral K₁ K₂ a u)
  linarith

end Modulus

end

end RHTower
