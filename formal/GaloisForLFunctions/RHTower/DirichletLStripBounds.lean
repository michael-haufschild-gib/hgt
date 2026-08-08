import GaloisForLFunctions.RHTower.DirichletCompletedLConjugate
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.WaveTraceSpectrum

/-!
# Edge bounds for the Dirichlet L-function

The right edge of the Phragmén–Lindelöf strip is elementary: on `Re s ≥ 2` the Dirichlet series
converges absolutely and is bounded by `∑ n^{-2}`, uniformly in `s`.

For the left edge and for the growth condition inside the strip one needs the Archimedean factor,
and the first ingredient is a uniform bound for `Γ` on a vertical strip of positive real parts:
`‖Γ v‖ ≤ Γ (Re v)` and `Γ` is continuous on a compact interval of the positive ray.
-/

open Complex
open GaloisForLFunctions.HTGeometry
open scoped LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- A Dirichlet character is bounded by one. -/
theorem norm_dirichletCharacter_le_one (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    ‖χ a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · exact le_of_eq (norm_dirichletCharacter_apply χ ha)
  · rw [χ.map_nonunit ha, norm_zero]
    norm_num

/-- **Right edge of the strip.**  On `Re s ≥ 2` the L-function is bounded, uniformly in `s`. -/
theorem exists_bound_LFunction_of_two_le_re (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ s.re → ‖DirichletCharacter.LFunction χ s‖ ≤ C := by
  have hsum : Summable fun n : ℕ => (((n : ℝ)) ^ (2 : ℝ))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hnn : 0 ≤ ∑' n : ℕ, (((n : ℝ)) ^ (2 : ℝ))⁻¹ := tsum_nonneg fun n => by positivity
  refine ⟨1 + ∑' n : ℕ, (((n : ℝ)) ^ (2 : ℝ))⁻¹, by linarith, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs1, LSeries]
  have hb : ∀ n : ℕ, ‖LSeries.term (↗χ) s n‖ ≤ (((n : ℝ)) ^ (2 : ℝ))⁻¹ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      simp
    · rw [LSeries.term_of_ne_zero hn, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hmono : ((n : ℝ)) ^ (2 : ℝ) ≤ ((n : ℝ)) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hn1 hs
      have hpos2 : (0 : ℝ) < ((n : ℝ)) ^ (2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
      have hposs : (0 : ℝ) < ((n : ℝ)) ^ s.re := Real.rpow_pos_of_pos (by linarith) _
      have hchi : ‖χ ((n : ℕ) : ZMod N)‖ ≤ 1 := norm_dirichletCharacter_le_one χ _
      rw [div_le_iff₀ hposs]
      rw [inv_mul_eq_div, le_div_iff₀ hpos2]
      have hkey : ‖χ ((n : ℕ) : ZMod N)‖ * ((n : ℝ)) ^ (2 : ℝ) ≤ 1 * ((n : ℝ)) ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_right hchi hpos2.le
      linarith
  have hsummable : Summable fun n : ℕ => ‖LSeries.term (↗χ) s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hsum
  refine le_trans (norm_tsum_le_tsum_norm hsummable) ?_
  have hle := Summable.tsum_le_tsum hb hsummable hsum
  linarith

omit [NeZero N] in
/-- `Γ` is bounded on every compact interval of the positive ray. -/
theorem exists_bound_Gamma_Icc {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, a ≤ x → x ≤ b → Real.Gamma x ≤ B := by
  rcases le_or_gt a b with hab | hab
  · have hcont : ContinuousOn Real.Gamma (Set.Icc a b) := by
      intro x hx
      refine ContinuousAt.continuousWithinAt ?_
      refine (Real.differentiableAt_Gamma ?_).continuousAt
      intro m
      have hxpos : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      intro hcon
      rw [hcon] at hxpos
      linarith
    obtain ⟨x₀, _, hmax⟩ :=
      isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hcont
    refine ⟨max (Real.Gamma x₀) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx1 hx2 => ?_⟩
    exact le_trans (hmax ⟨hx1, hx2⟩) (le_max_left _ _)
  · exact ⟨1, one_pos, fun x hx1 hx2 => absurd (le_trans hx1 hx2) (not_le.mpr hab)⟩

omit [NeZero N] in
/-- **Uniform bound for the complex `Γ` on a strip of positive real parts.** -/
theorem exists_bound_norm_Gamma_strip {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : ℂ, a ≤ v.re → v.re ≤ b → ‖Complex.Gamma v‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_bound_Gamma_Icc (a := a) (b := b) ha
  refine ⟨B, hB, fun v hv1 hv2 => ?_⟩
  exact le_trans (norm_Gamma_le_Gamma_re (lt_of_lt_of_le ha hv1)) (hbound v.re hv1 hv2)

omit [NeZero N] in
/-- Inversion preserves parity. -/
theorem inv_even_iff {χ : DirichletCharacter ℂ N} : (χ⁻¹).Even ↔ χ.Even := by
  have hval : χ⁻¹ (-1) = (χ (-1))⁻¹ := MulChar.inv_apply_eq_inv' χ (-1)
  constructor
  · intro h
    show χ (-1) = 1
    have h' : (χ (-1))⁻¹ = 1 := by rw [← hval]; exact h
    rw [← inv_inv (χ (-1)), h', inv_one]
  · intro h
    show χ⁻¹ (-1) = 1
    rw [hval, show χ (-1) = 1 from h, inv_one]

omit [NeZero N] in
/-- The Archimedean factor only sees the parity, which inversion preserves. -/
theorem gammaFactor_inv (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.gammaFactor χ⁻¹ s = DirichletCharacter.gammaFactor χ s := by
  rcases χ.even_or_odd with hev | hod
  · rw [hev.gammaFactor_def, (inv_even_iff.mpr hev).gammaFactor_def]
  · have hodinv : (χ⁻¹).Odd := by
      show χ⁻¹ (-1) = -1
      rw [MulChar.inv_apply_eq_inv', show χ (-1) = -1 from hod]
      norm_num
    rw [hod.gammaFactor_def, hodinv.gammaFactor_def]

omit [NeZero N] in
/-- The Archimedean factor is a shifted `Gammaℝ`, with the shift determined by the parity. -/
theorem gammaFactor_eq_Gammaℝ (χ : DirichletCharacter ℂ N) :
    ∃ d : ℝ, (d = 0 ∨ d = 1) ∧
      ∀ s : ℂ, DirichletCharacter.gammaFactor χ s = Complex.Gammaℝ (s + (d : ℂ)) := by
  rcases χ.even_or_odd with hev | hod
  · exact ⟨0, Or.inl rfl, fun s => by rw [hev.gammaFactor_def]; norm_num⟩
  · exact ⟨1, Or.inr rfl, fun s => by rw [hod.gammaFactor_def]; norm_num⟩

omit [NeZero N] in
/-- The sine is bounded by the exponential of the imaginary part. -/
theorem norm_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| :=
  GaloisForLFunctions.HTGeometry.norm_csin_le_exp_abs_im z

omit [NeZero N] in
/-- **Uniform bound for `Γ` on a vertical strip away from the real axis.**  Shifting right past the
poles costs nothing: each shift factor has modulus at least `|Im v| ≥ 1`. -/
theorem exists_bound_norm_Gamma_strip_off_axis (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : ℂ, a ≤ v.re → v.re ≤ b → 1 ≤ |v.im| → ‖Complex.Gamma v‖ ≤ B := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 0 < a + m := by
    refine ⟨⌈|a|⌉₊ + 1, ?_⟩
    have h1 : |a| ≤ (⌈|a|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : -a ≤ |a| := neg_le_abs a
    push_cast
    linarith
  obtain ⟨B, hB, hbound⟩ := exists_bound_norm_Gamma_strip (a := a + m) (b := b + m) hm
  refine ⟨B, hB, fun v hv1 hv2 hvim => ?_⟩
  have him : ∀ i : ℕ, (v + (i : ℂ)).im = v.im := by intro i; simp
  have hne : ∀ i : ℕ, i < m → v + (i : ℂ) ≠ 0 := by
    intro i _ h
    have hi := him i
    rw [h] at hi
    simp only [Complex.zero_im] at hi
    rw [← hi] at hvim
    norm_num at hvim
  have hprod := norm_Gamma_add_nat v m hne
  have hb : ∀ i ∈ Finset.range m, (1 : ℝ) ≤ ‖v + (i : ℂ)‖ := by
    intro i _
    have h := Complex.abs_im_le_norm (v + (i : ℂ))
    rw [him i] at h
    linarith
  have hge : (1 : ℝ) ≤ ∏ i ∈ Finset.range m, ‖v + (i : ℂ)‖ := by
    calc (1 : ℝ) = ∏ _i ∈ Finset.range m, (1 : ℝ) := by rw [Finset.prod_const, one_pow]
      _ ≤ ∏ i ∈ Finset.range m, ‖v + (i : ℂ)‖ := Finset.prod_le_prod (fun i _ => zero_le_one) hb
  have hshift : ‖Complex.Gamma (v + (m : ℂ))‖ ≤ B := by
    refine hbound _ ?_ ?_ <;> rw [Complex.add_re] <;> simp <;> linarith
  nlinarith [hprod, hge, hshift, norm_nonneg (Complex.Gamma v)]

omit [NeZero N] in
/-- **Reciprocal `Γ` bound on a strip away from the real axis.**  From the reflection formula:
`Γ(z) Γ(1-z) sin(π z) = π`, with `‖Γ(1-z)‖` bounded on the reflected strip and
`‖sin(π z)‖ ≤ e^{π |Im z|}`. -/
theorem exists_lower_bound_norm_Gamma_strip (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      Real.pi ≤ B * Real.exp (Real.pi * |z.im|) * ‖Complex.Gamma z‖ := by
  obtain ⟨B, hB, hbound⟩ := exists_bound_norm_Gamma_strip_off_axis (1 - b) (1 - a)
  refine ⟨B, hB, fun z hz1 hz2 hzim => ?_⟩
  have hzim0 : z.im ≠ 0 := by
    intro h
    rw [h] at hzim
    norm_num at hzim
  have hsinne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    intro h
    rw [Complex.sin_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have h1 := congrArg Complex.im hn
    have hL : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
    have hR : (((n : ℤ) : ℂ) * ((Real.pi : ℝ) : ℂ)).im = 0 := by simp
    rw [hL, hR] at h1
    rcases mul_eq_zero.mp h1 with hp | hi
    · exact absurd hp Real.pi_ne_zero
    · exact hzim0 hi
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have hclear : Complex.Gamma z * Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z)
      = ((Real.pi : ℝ) : ℂ) := by
    rw [hrefl, div_mul_cancel₀ _ hsinne]
  have hnorm := congrArg (fun w : ℂ => ‖w‖) hclear
  simp only [norm_mul] at hnorm
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hnorm
  have hone : ‖Complex.Gamma (1 - z)‖ ≤ B := by
    refine hbound _ ?_ ?_ ?_
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]; exact hzim
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
    refine (norm_sin_le _).trans (le_of_eq ?_)
    congr 1
    have : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
    rw [this, abs_mul, abs_of_pos Real.pi_pos]
  have hGnn : 0 ≤ ‖Complex.Gamma z‖ := norm_nonneg _
  have hexp : 0 < Real.exp (Real.pi * |z.im|) := Real.exp_pos _
  have step1 : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ *
      ‖Complex.sin ((Real.pi : ℂ) * z)‖
      ≤ ‖Complex.Gamma z‖ * B * ‖Complex.sin ((Real.pi : ℂ) * z)‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hone hGnn) (norm_nonneg _)
  have step2 : ‖Complex.Gamma z‖ * B * ‖Complex.sin ((Real.pi : ℂ) * z)‖
      ≤ ‖Complex.Gamma z‖ * B * Real.exp (Real.pi * |z.im|) :=
    mul_le_mul_of_nonneg_left hsin (mul_nonneg hGnn hB.le)
  linarith [hnorm, step1, step2]

end RHTower
