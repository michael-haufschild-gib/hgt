import GaloisForLFunctions.RHTower.HalfWeightThetaMultiplier
import GaloisForLFunctions.RHTower.SelbergPoincareSeries

/-!
# Weight-½ Eisenstein series on `Γ₀(4M)` with nebentypus

With the unitary theta multiplier `j(γ,z) = J(γ,z)/|J(γ,z)|` (`jU`, cocycle `jU_mul`, `|j| = 1`,
invariant under left translation by `T^k`), and a Dirichlet character `ψ` mod `4M`,

`E(z, w; ψ) = Σ_{γ ∈ ⟨T⟩\Γ₀(4M)} ψ̄(d) \overline{j(γ,z)} Im(γz)^w`   (`eisHalf`).

* The summand is `⟨T⟩`-invariant (`eTerm_HinfT`) and cosets are determined by bottom rows
  (`rightRel_of_bottom'`), so for `Re w > 1` the series converges absolutely by comparison with
  `Σ |cz+d|^{-2 Re w}` (`summable_eTermQ`).
* `eisHalf_smul`: `E(δz, w; ψ) = ψ(d_δ) j(δ,z) E(z, w; ψ)` for `δ ∈ Γ₀(4M)`, from
  `d_{γδ} ≡ d_γ d_δ (mod 4M)` and the cocycle relation.

This is the Eisenstein series of Shimura's integral: `u(4z) \overline{θ(z)} y^{1/4} E(z, w; ψ)`
is `Γ₀(4M)`-invariant when `u` has nebentypus `ψ̄`.
-/

open Complex Matrix CongruenceSubgroup ModularGroup
open scoped MatrixGroups Real

namespace GaloisForLFunctions.RHTower.HalfWeight

/-! ### The unit multiplier `j = J/|J|` -/

/-- The unitary theta multiplier `j(γ, z) = J(γ, z)/|J(γ, z)|`. -/
noncomputable def jU (γ : SL(2, ℤ)) (z : UpperHalfPlane) : ℂ := J γ z / (‖J γ z‖ : ℂ)

theorem norm_J_pos (γ : SL(2, ℤ)) (z : UpperHalfPlane) : 0 < ‖J γ z‖ :=
  norm_pos_iff.2 (J_ne_zero γ z)

theorem norm_jU (γ : SL(2, ℤ)) (z : UpperHalfPlane) : ‖jU γ z‖ = 1 := by
  rw [jU, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_J_pos γ z),
    div_self (norm_J_pos γ z).ne']

theorem jU_mul (γ γ' : SL(2, ℤ)) (z : UpperHalfPlane) :
    jU (γ * γ') z = jU γ (γ' • z) * jU γ' z := by
  have h1 := norm_J_pos γ (γ' • z)
  have h2 := norm_J_pos γ' z
  rw [jU, jU, jU, J_mul, norm_mul]
  push_cast
  field_simp

theorem star_jU_mul_self (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    starRingEnd ℂ (jU γ z) * jU γ z = 1 := by
  rw [Complex.conj_mul', norm_jU]; simp

theorem theta_add_int (w : ℂ) (k : ℤ) : theta (w + k) = theta w := by
  rw [theta_eq_tsum, theta_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [show 2 * π * I * (n : ℂ) ^ 2 * (w + k) = 2 * π * I * (n : ℂ) ^ 2 * w +
      ((n ^ 2 * k : ℤ) : ℂ) * (2 * π * I) by push_cast; ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem J_T_zpow_mul (k : ℤ) (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    J (T ^ k * γ) z = J γ z := by
  rw [J, J, mul_smul]
  congr 1
  rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  push_cast
  rw [add_comm]
  exact theta_add_int _ k

theorem jU_T_zpow_mul (k : ℤ) (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    jU (T ^ k * γ) z = jU γ z := by
  rw [jU, jU, J_T_zpow_mul]

/-! ### The weight-½ Eisenstein series on `Γ₀(4M)` -/

variable (M : ℕ)

theorem T_mem_Gamma0 : T ∈ Gamma0 (4 * M) := by
  rw [Gamma0_mem, coe_T]; simp

theorem Gamma0_4M_le : Gamma0 (4 * M) ≤ Gamma0 4 := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by norm_num) h)

/-- The translations `⟨T⟩ ⊂ Γ₀(4M)`. -/
def HinfT : Subgroup (Gamma0 (4 * M)) := Subgroup.zpowers ⟨T, T_mem_Gamma0 M⟩

theorem mem_HinfT {h : Gamma0 (4 * M)} (hh : h ∈ HinfT M) :
    ∃ k : ℤ, (h : SL(2, ℤ)) = T ^ k := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact ⟨k, by simp only [Subgroup.coe_zpow]⟩

/-- Same bottom row means same `⟨T⟩`-coset. -/
theorem rightRel_of_bottom' {γ δ : Gamma0 (4 * M)} (h0 : ent γ 1 0 = ent δ 1 0)
    (h1 : ent γ 1 1 = ent δ 1 1) : QuotientGroup.rightRel (HinfT M) γ δ := by
  rw [QuotientGroup.rightRel_apply]
  simp only [ent] at h0 h1
  refine Subgroup.mem_zpowers_iff.mpr ⟨(γ : SL(2, ℤ)) 0 0 * (δ : SL(2, ℤ)) 0 1 -
    (δ : SL(2, ℤ)) 0 0 * (γ : SL(2, ℤ)) 0 1, ?_⟩
  apply Subtype.ext
  have hdetγ := (γ : SL(2, ℤ)).2
  have hdetδ := (δ : SL(2, ℤ)).2
  rw [Matrix.det_fin_two] at hdetγ hdetδ
  simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_T_zpow, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [h0, h1]; linarith
  · linarith
  · rw [h0, h1]; ring
  · rw [← h0, ← h1]; linarith

variable (ψ : DirichletCharacter ℂ (4 * M))

/-- The summand `ψ̄(d) \overline{j(γ,z)} Im(γz)^w`. -/
noncomputable def eTerm (w : ℂ) (z : UpperHalfPlane) (γ : Gamma0 (4 * M)) : ℂ :=
  starRingEnd ℂ (ψ (ent γ 1 1 : ZMod (4 * M))) * starRingEnd ℂ (jU γ z) *
    ((((γ : SL(2, ℤ)) • z).im : ℝ) : ℂ) ^ w

theorem ent_T_zpow_mul_11 (k : ℤ) (γ : SL(2, ℤ)) : ent (T ^ k * γ) 1 1 = ent γ 1 1 := by
  simp [ent]

theorem ent_T_zpow_mul_10 (k : ℤ) (γ : SL(2, ℤ)) : ent (T ^ k * γ) 1 0 = ent γ 1 0 := by
  simp [ent]

theorem eTerm_HinfT (w : ℂ) (z : UpperHalfPlane) {h : Gamma0 (4 * M)} (hh : h ∈ HinfT M)
    (γ : Gamma0 (4 * M)) : eTerm M ψ w z (h * γ) = eTerm M ψ w z γ := by
  obtain ⟨k, hk⟩ := mem_HinfT M hh
  have hc : ((h * γ : Gamma0 (4 * M)) : SL(2, ℤ)) = T ^ k * (γ : SL(2, ℤ)) := by
    rw [Subgroup.coe_mul, hk]
  unfold eTerm
  rw [hc, ent_T_zpow_mul_11, jU_T_zpow_mul, mul_smul]
  congr 3
  rw [UpperHalfPlane.modular_T_zpow_smul]
  simp

/-- The cosets `⟨T⟩ \ Γ₀(4M)`. -/
abbrev CosetsT := Quotient (QuotientGroup.rightRel (HinfT M))

/-- The summand on cosets. -/
noncomputable def eTermQ (w : ℂ) (z : UpperHalfPlane) : CosetsT M → ℂ :=
  Quotient.lift (eTerm M ψ w z) (by
    intro a b hab
    have hmem : b * a⁻¹ ∈ HinfT M := QuotientGroup.rightRel_apply.mp hab
    have := eTerm_HinfT M ψ w z hmem a
    rw [inv_mul_cancel_right] at this
    exact this.symm)

/-- **The weight-½ Eisenstein series** `E(z, w; ψ) = Σ_{⟨T⟩\Γ₀(4M)} ψ̄(d) \overline{j(γ,z)} Im(γz)^w`. -/
noncomputable def eisHalf (w : ℂ) (z : UpperHalfPlane) : ℂ := ∑' q : CosetsT M, eTermQ M ψ w z q

/-- The bottom row of a coset representative. -/
noncomputable def bottomT (q : CosetsT M) : Fin 2 → ℤ :=
  ![ent (Quotient.out q : Gamma0 (4 * M)) 1 0, ent (Quotient.out q : Gamma0 (4 * M)) 1 1]

theorem bottomT_injective : Function.Injective (bottomT M) := by
  intro q q' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [bottomT, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  exact Quotient.sound (rightRel_of_bottom' M h0 h1)

theorem norm_char_le (x : ZMod (4 * M)) : ‖ψ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · exact le_of_eq (ψ.unit_norm_eq_one hx.unit)
  · rw [ψ.map_nonunit hx]; simp

theorem norm_eTerm_le (w : ℂ) (z : UpperHalfPlane) (γ : Gamma0 (4 * M)) :
    ‖eTerm M ψ w z γ‖ ≤ z.im ^ w.re *
      ‖(ent γ 1 0 : ℂ) * z + (ent γ 1 1 : ℂ)‖ ^ (-2 * w.re) := by
  unfold eTerm
  set v := (γ : SL(2, ℤ)) • z
  have hv := v.im_pos
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, norm_jU, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have him : v.im = z.im / Complex.normSq ((ent γ 1 0 : ℂ) * z + (ent γ 1 1 : ℂ)) := by
    simp only [v]
    rw [ModularGroup.im_smul_eq_div_normSq, denom_ent]
  set D := (ent γ 1 0 : ℂ) * z + (ent γ 1 1 : ℂ)
  have hD : 0 < ‖D‖ := by
    rw [norm_pos_iff]; intro h0; rw [h0, map_zero, div_zero] at him; linarith
  have hpow : v.im ^ w.re = z.im ^ w.re * ‖D‖ ^ (-2 * w.re) := by
    rw [him, Complex.normSq_eq_norm_sq, Real.div_rpow z.im_pos.le (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hD.le, div_eq_mul_inv, ← Real.rpow_neg hD.le]
    congr 2; push_cast; ring
  rw [hpow]
  have h1 := norm_char_le M ψ (ent γ 1 1 : ZMod (4 * M))
  have h2 : 0 ≤ z.im ^ w.re * ‖D‖ ^ (-2 * w.re) := by positivity
  nlinarith

/-- **Absolute convergence** for `Re w > 1`. -/
theorem summable_eTermQ {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    Summable (fun q : CosetsT M => ‖eTermQ M ψ w z q‖) := by
  have hsum := ((SelbergPoincare.summable_norm_rpow z hw).comp_injective
    (bottomT_injective M)).mul_left (z.im ^ w.re)
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) hsum
  have hq : eTermQ M ψ w z q = eTerm M ψ w z (Quotient.out q) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq]
  refine (norm_eTerm_le M ψ w z _).trans (le_of_eq ?_)
  simp [bottomT]

/-! ### The transformation law -/

/-- Right multiplication by `δ ∈ Γ₀(4M)` permutes the cosets. -/
def rightMulT (δ : Gamma0 (4 * M)) : CosetsT M ≃ CosetsT M where
  toFun := Quotient.map (· * δ) (fun a b hab => by
    have hab' : QuotientGroup.rightRel (HinfT M) a b := hab
    show QuotientGroup.rightRel (HinfT M) _ _
    rw [QuotientGroup.rightRel_apply] at hab' ⊢
    simpa [mul_assoc] using hab')
  invFun := Quotient.map (· * δ⁻¹) (fun a b hab => by
    have hab' : QuotientGroup.rightRel (HinfT M) a b := hab
    show QuotientGroup.rightRel (HinfT M) _ _
    rw [QuotientGroup.rightRel_apply] at hab' ⊢
    simpa [mul_assoc] using hab')
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h a => simp [Quotient.map_mk]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h a => simp [Quotient.map_mk]

theorem ent_mul_11 (γ δ : SL(2, ℤ)) :
    ent (γ * δ) 1 1 = ent γ 1 0 * ent δ 0 1 + ent γ 1 1 * ent δ 1 1 := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem c_zmod_eq_zero (γ : Gamma0 (4 * M)) : ((ent γ 1 0 : ℤ) : ZMod (4 * M)) = 0 := by
  have := γ.2
  rw [Gamma0_mem] at this
  exact this

theorem d_zmod_mul (γ δ : Gamma0 (4 * M)) :
    ((ent ((γ : SL(2, ℤ)) * δ) 1 1 : ℤ) : ZMod (4 * M)) =
      ((ent γ 1 1 : ℤ) : ZMod (4 * M)) * ((ent δ 1 1 : ℤ) : ZMod (4 * M)) := by
  rw [ent_mul_11]; push_cast; rw [c_zmod_eq_zero]; ring

theorem isUnit_d (δ : Gamma0 (4 * M)) : IsUnit ((ent δ 1 1 : ℤ) : ZMod (4 * M)) := by
  have hdet := det_entries δ
  have h : ((ent δ 0 0 : ℤ) : ZMod (4 * M)) * ((ent δ 1 1 : ℤ) : ZMod (4 * M)) = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod (4 * M))) hdet
    push_cast at this
    rw [c_zmod_eq_zero, mul_zero, sub_zero] at this
    exact this
  exact IsUnit.of_mul_eq_one_right _ h

theorem star_char_mul_self (x : ZMod (4 * M)) (hx : IsUnit x) :
    starRingEnd ℂ (ψ x) * ψ x = 1 := by
  have h1 : ‖ψ x‖ = 1 := by
    have := ψ.unit_norm_eq_one hx.unit
    rwa [IsUnit.unit_spec] at this
  rw [Complex.conj_mul', h1]; simp

theorem eTerm_smul (w : ℂ) (z : UpperHalfPlane) (γ δ : Gamma0 (4 * M)) :
    eTerm M ψ w ((δ : SL(2, ℤ)) • z) γ =
      ψ (ent δ 1 1 : ZMod (4 * M)) * jU δ z * eTerm M ψ w z (γ * δ) := by
  unfold eTerm
  rw [Subgroup.coe_mul, d_zmod_mul, jU_mul, map_mul, map_mul, map_mul, mul_smul]
  have h1 := star_char_mul_self M ψ _ (isUnit_d M δ)
  have h2 := star_jU_mul_self (δ : SL(2, ℤ)) z
  set X := starRingEnd ℂ (ψ (ent γ 1 1 : ZMod (4 * M))) * starRingEnd ℂ (jU γ (δ • z)) *
    ((((γ : SL(2, ℤ)) • (δ : SL(2, ℤ)) • z).im : ℝ) : ℂ) ^ w
  linear_combination (-X) * h1 -
    X * (starRingEnd ℂ (ψ (ent δ 1 1 : ZMod (4 * M))) * ψ (ent δ 1 1 : ZMod (4 * M))) * h2

/-- **Automorphy of the weight-½ Eisenstein series**: `E(δz, w; ψ) = ψ(d) j(δ, z) E(z, w; ψ)` for
`δ ∈ Γ₀(4M)`. -/
theorem eisHalf_smul (w : ℂ) (z : UpperHalfPlane) (δ : Gamma0 (4 * M)) :
    eisHalf M ψ w ((δ : SL(2, ℤ)) • z) =
      ψ (ent δ 1 1 : ZMod (4 * M)) * jU δ z * eisHalf M ψ w z := by
  unfold eisHalf
  have h : ∀ q : CosetsT M, eTermQ M ψ w ((δ : SL(2, ℤ)) • z) q =
      ψ (ent δ 1 1 : ZMod (4 * M)) * jU δ z * eTermQ M ψ w z (rightMulT M δ q) := by
    intro q
    induction q using Quotient.inductionOn with
    | h a => exact eTerm_smul M ψ w z a δ
  rw [tsum_congr h, tsum_mul_left, (rightMulT M δ).tsum_eq (eTermQ M ψ w z)]

end GaloisForLFunctions.RHTower.HalfWeight
