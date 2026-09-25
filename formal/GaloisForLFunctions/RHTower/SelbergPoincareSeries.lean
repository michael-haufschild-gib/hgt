import Mathlib

open UpperHalfPlane EisensteinSeries

/-!
# Non-holomorphic Poincaré series for `Γ(N)`

`P_m(z, s) = Σ_{γ ∈ Γ∞(N)\Γ(N)} Im(γz)^s e(m γz / N)`, summed over the right cosets of the translation
subgroup `Γ∞(N) = ⟨T^N⟩` (`poincare`). The summand is `Γ∞(N)`-invariant (`term_Hinf`), cosets are determined by
bottom rows (`rightRel_of_bottom`), so for `Re s > 1` the series converges absolutely by comparison with
`Σ |cz + d|^{-2σ}` (`summable_termQ`), and it is `Γ(N)`-invariant (`poincare_smul`).
-/

namespace GaloisForLFunctions.RHTower.SelbergPoincare

/-- `Σ_{(c,d) ≠ 0} |cz + d|^{-2σ}` converges for `σ > 1`. -/
theorem summable_norm_rpow (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : Fin 2 → ℤ => ‖(x 0 : ℂ) * z + x 1‖ ^ (-2 * σ) := by
  have hr := r_pos z
  apply (((summable_one_div_norm_rpow (k := 2 * σ) (by linarith)).mul_left (r z ^ (-2 * σ)))).of_nonneg_of_le
  · intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp only [Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, norm_zero]
      rw [Real.zero_rpow (by linarith)]
      positivity
    · have h := r_mul_max_le z hx
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      calc ‖(x 0 : ℂ) * z + x 1‖ ^ (-2 * σ) ≤ (r z * ‖x‖) ^ (-2 * σ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h (by linarith)
        _ = r z ^ (-2 * σ) * ‖x‖ ^ (-(2 * σ)) := by rw [Real.mul_rpow hr.le hxpos.le, neg_mul]


open CongruenceSubgroup ModularGroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable (N : ℕ)

theorem T_pow_mem (N : ℕ) : T ^ (N : ℤ) ∈ Gamma N := by
  rw [Gamma_mem, coe_T_zpow]; simp

/-- The translations `T^{Nk}` inside `Γ(N)`. -/
def Hinf : Subgroup (Gamma N) := Subgroup.zpowers ⟨T ^ (N : ℤ), T_pow_mem N⟩

theorem mem_Hinf {h : Gamma N} (hh : h ∈ Hinf N) : ∃ k : ℤ, (h : SL(2, ℤ)) = T ^ ((N : ℤ) * k) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact ⟨k, by simp only [Subgroup.coe_zpow, zpow_mul]⟩

/-- Same bottom row in `Γ(N)` means same `Γ∞(N)`-coset. -/
theorem rightRel_of_bottom {γ δ : Gamma N} (h0 : (γ : SL(2, ℤ)) 1 0 = (δ : SL(2, ℤ)) 1 0)
    (h1 : (γ : SL(2, ℤ)) 1 1 = (δ : SL(2, ℤ)) 1 1) :
    QuotientGroup.rightRel (Hinf N) γ δ := by
  rw [QuotientGroup.rightRel_apply]
  obtain ⟨hga, hgb, hgc, hgd⟩ := Gamma_mem.mp γ.2
  obtain ⟨hda, hdb, hdc, hdd⟩ := Gamma_mem.mp δ.2
  have hb : (N : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hgb
  have hb' : (N : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hdb
  set k := (γ : SL(2, ℤ)) 0 0 * (δ : SL(2, ℤ)) 0 1 - (δ : SL(2, ℤ)) 0 0 * (γ : SL(2, ℤ)) 0 1
  have hk : (N : ℤ) ∣ k := dvd_sub (dvd_mul_of_dvd_right hb' _) (dvd_mul_of_dvd_right hb _)
  obtain ⟨t, ht⟩ := hk
  refine Subgroup.mem_zpowers_iff.mpr ⟨t, ?_⟩
  apply Subtype.ext
  have hdetγ := (γ : SL(2, ℤ)).2
  have hdetδ := (δ : SL(2, ℤ)).2
  rw [Matrix.det_fin_two] at hdetγ hdetδ
  simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv, ← zpow_mul]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_T_zpow, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  simp only [k] at ht
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [h0, h1]; linarith
  · linarith
  · rw [h0, h1]; ring
  · rw [← h0, ← h1]; linarith

/-- The summand `Im(γz)^s e(m γz/N)`. -/
noncomputable def term (m : ℕ) (s : ℂ) (z : ℍ) (γ : Gamma N) : ℂ :=
  (((γ : SL(2, ℤ)) • z).im : ℂ) ^ s *
    Complex.exp (2 * Real.pi * Complex.I * m * (((γ : SL(2, ℤ)) • z : ℍ) : ℂ) / N)

theorem term_Hinf (m : ℕ) (s : ℂ) (z : ℍ) {h : Gamma N} (hh : h ∈ Hinf N) (γ : Gamma N) (hN : 0 < N) :
    term N m s z (h * γ) = term N m s z γ := by
  obtain ⟨k, hk⟩ := mem_Hinf N hh
  have hsm : ((h * γ : Gamma N) : SL(2, ℤ)) • z = (T ^ ((N : ℤ) * k)) • ((γ : SL(2, ℤ)) • z) := by
    rw [Subgroup.coe_mul, mul_smul, hk]
  unfold term
  rw [hsm]
  have hc : (((T ^ ((N : ℤ) * k)) • ((γ : SL(2, ℤ)) • z) : ℍ) : ℂ) = (((γ : SL(2, ℤ)) • z : ℍ) : ℂ) + ((N * k : ℤ) : ℂ) := by
    rw [modular_T_zpow_smul]; simp [add_comm]
  have hi : ((T ^ ((N : ℤ) * k)) • ((γ : SL(2, ℤ)) • z)).im = ((γ : SL(2, ℤ)) • z).im := by
    rw [← UpperHalfPlane.coe_im, hc]; simp
  rw [hi, hc]
  congr 1
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show 2 * Real.pi * Complex.I * m * ((((γ : SL(2, ℤ)) • z : ℍ) : ℂ) + ((N * k : ℤ) : ℂ)) / N =
      2 * Real.pi * Complex.I * m * (((γ : SL(2, ℤ)) • z : ℍ) : ℂ) / N + (m * k : ℤ) * (2 * Real.pi * Complex.I) by
      push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

variable [hN : NeZero N]

/-- The cosets `Γ∞(N) \ Γ(N)`. -/
abbrev Cosets := Quotient (QuotientGroup.rightRel (Hinf N))

/-- The summand on cosets. -/
noncomputable def termQ (m : ℕ) (s : ℂ) (z : ℍ) : Cosets N → ℂ :=
  Quotient.lift (term N m s z) (by
    intro a b hab
    have hmem : b * a⁻¹ ∈ Hinf N := QuotientGroup.rightRel_apply.mp hab
    have := term_Hinf N m s z hmem a (Nat.pos_of_ne_zero hN.out)
    rw [inv_mul_cancel_right] at this
    exact this.symm)

theorem termQ_mk (m : ℕ) (s : ℂ) (z : ℍ) (γ : Gamma N) :
    termQ N m s z (Quotient.mk _ γ) = term N m s z γ := rfl

/-- The non-holomorphic Poincaré series `P_m(z, s) = Σ_{γ ∈ Γ∞\Γ(N)} Im(γz)^s e(m γz/N)`. -/
noncomputable def poincare (m : ℕ) (s : ℂ) (z : ℍ) : ℂ := ∑' q : Cosets N, termQ N m s z q

/-- The bottom row of a coset representative. -/
noncomputable def bottom (q : Cosets N) : Fin 2 → ℤ := ![((Quotient.out q : Gamma N) : SL(2, ℤ)) 1 0,
  ((Quotient.out q : Gamma N) : SL(2, ℤ)) 1 1]

omit hN in
theorem bottom_injective : Function.Injective (bottom N) := by
  intro q q' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [bottom, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  exact Quotient.sound (rightRel_of_bottom N h0 h1)

omit hN in
theorem norm_term_le (m : ℕ) (s : ℂ) (z : ℍ) (γ : Gamma N) :
    ‖term N m s z γ‖ ≤ z.im ^ s.re *
      ‖((((γ : SL(2, ℤ)) 1 0 : ℤ) : ℂ) * z + (((γ : SL(2, ℤ)) 1 1 : ℤ) : ℂ))‖ ^ (-2 * s.re) := by
  unfold term
  set w := (γ : SL(2, ℤ)) • z
  have hw := w.im_pos
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw]
  have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * m * (w : ℂ) / N)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    have : (2 * Real.pi * Complex.I * m * (w : ℂ) / N).re = -(2 * Real.pi * m * w.im / N) := by
      simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
      field_simp
    rw [this]
    have : 0 ≤ 2 * Real.pi * m * w.im / N := by positivity
    linarith
  have him : w.im = z.im / Complex.normSq ((((γ : SL(2, ℤ)) 1 0 : ℤ) : ℂ) * z + (((γ : SL(2, ℤ)) 1 1 : ℤ) : ℂ)) := by
    simp only [w]
    rw [ModularGroup.im_smul_eq_div_normSq]
    rfl
  set D := ((((γ : SL(2, ℤ)) 1 0 : ℤ) : ℂ) * z + (((γ : SL(2, ℤ)) 1 1 : ℤ) : ℂ))
  have hD : 0 < ‖D‖ := by
    rw [norm_pos_iff]; intro h0; rw [h0, map_zero, div_zero] at him; linarith
  have hpow : w.im ^ s.re = z.im ^ s.re * ‖D‖ ^ (-2 * s.re) := by
    rw [him, Complex.normSq_eq_norm_sq, Real.div_rpow z.im_pos.le (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hD.le, div_eq_mul_inv, ← Real.rpow_neg hD.le]
    congr 2; push_cast; ring
  calc w.im ^ s.re * ‖Complex.exp (2 * Real.pi * Complex.I * m * (w : ℂ) / N)‖ ≤ w.im ^ s.re * 1 :=
        mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hw.le _)
    _ = _ := by rw [mul_one, hpow]

/-- **Absolute convergence** of the Poincaré series for `Re s > 1`. -/
theorem summable_termQ (m : ℕ) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    Summable (fun q : Cosets N => ‖termQ N m s z q‖) := by
  have hsum := ((summable_norm_rpow z hs).comp_injective (bottom_injective N)).mul_left (z.im ^ s.re)
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) hsum
  have hq : termQ N m s z q = term N m s z (Quotient.out q) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq]
  refine (norm_term_le N m s z _).trans (le_of_eq ?_)
  simp [bottom]

/-- Right multiplication by `δ ∈ Γ(N)` permutes the cosets. -/
def rightMul (δ : Gamma N) : Cosets N ≃ Cosets N where
  toFun := Quotient.map (· * δ) (fun a b hab => by
    have hab' : QuotientGroup.rightRel (Hinf N) a b := hab
    show QuotientGroup.rightRel (Hinf N) _ _
    rw [QuotientGroup.rightRel_apply] at hab' ⊢
    simpa [mul_assoc] using hab')
  invFun := Quotient.map (· * δ⁻¹) (fun a b hab => by
    have hab' : QuotientGroup.rightRel (Hinf N) a b := hab
    show QuotientGroup.rightRel (Hinf N) _ _
    rw [QuotientGroup.rightRel_apply] at hab' ⊢
    simpa [mul_assoc] using hab')
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h a => simp [Quotient.map_mk]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h a => simp [Quotient.map_mk]

omit hN in
theorem term_smul (m : ℕ) (s : ℂ) (z : ℍ) (γ δ : Gamma N) :
    term N m s ((δ : SL(2, ℤ)) • z) γ = term N m s z (γ * δ) := by
  simp only [term, Subgroup.coe_mul, mul_smul]

/-- **`Γ(N)`-invariance** of the Poincaré series. -/
theorem poincare_smul (m : ℕ) (s : ℂ) (z : ℍ) (δ : Gamma N) :
    poincare N m s ((δ : SL(2, ℤ)) • z) = poincare N m s z := by
  unfold poincare
  rw [← (rightMul N δ).tsum_eq (termQ N m s z)]
  apply tsum_congr
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
    show term N m s ((δ : SL(2, ℤ)) • z) a = term N m s z (a * δ)
    exact term_smul N m s z a δ

end GaloisForLFunctions.RHTower.SelbergPoincare
