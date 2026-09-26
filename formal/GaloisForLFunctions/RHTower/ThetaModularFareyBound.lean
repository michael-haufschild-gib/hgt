import GaloisForLFunctions.Bottcher.ModularLambda

/-!
# The `SL(2,ℤ)` modulus law for `θ₂, θ₃, θ₄` and a Farey-type bound for `θ₃·h`

Index the even theta constants by the nonzero vectors of `𝔽₂²`: `(0,1) ↦ θ₂`, `(1,1) ↦ θ₃`,
`(1,0) ↦ θ₄`.  For every `g ∈ SL(2,ℤ)`, `|θ_v(gz)| = |cz+d|^{1/2} |θ_{v·ḡ}(z)|` with `ḡ = g mod 2`
(`thetaModulusLaw`).  Consequently `θ₃` is carried to `θ₂` exactly when the bottom row of `g` is
odd/odd (`charAct_three_inv_eq_two_iff`).  With sharp bounds on `{im ≥ 4/5}` this gives, after
reduction into the fundamental domain, `|θ₂⁴θ₄⁴/θ₃⁷(τ)| ≤ C|cτ+d|^{-1/2}e^{(7π/4) im(gτ)}` when
`(c,d)` is odd/odd and `≤ C|cτ+d|^{-1/2}` otherwise (`norm_thetaForm_farey`): the only exponential
growth of `θ₃·h` sits at the zero-charge cusps.
-/

open Complex UpperHalfPlane ModularGroup
open scoped MatrixGroups Real

namespace RHTower

noncomputable section

open Bottcher

/-- The automorphy denominator `cz + d` of `g ∈ SL(2,ℤ)`. -/
def slDen (g : SL(2, ℤ)) (z : ℂ) : ℂ := ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)

theorem slDen_ne_zero (g : SL(2, ℤ)) (z : ℍ) : slDen g z ≠ 0 := by
  have h := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) z
  rw [ModularGroup.denom_apply] at h
  simpa [slDen] using h

theorem coe_sl_smul (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = (((g 0 0 : ℤ) : ℂ) * z + ((g 0 1 : ℤ) : ℂ)) / slDen g z := by
  rw [coe_specialLinearGroup_apply]; simp [slDen]

theorem slDen_mul (g h : SL(2, ℤ)) (z : ℍ) :
    slDen (g * h) z = slDen g ((h • z : ℍ) : ℂ) * slDen h z := by
  have hne : ((h 1 0 : ℤ) : ℂ) * (z : ℂ) + ((h 1 1 : ℤ) : ℂ) ≠ 0 := slDen_ne_zero h z
  rw [coe_sl_smul]
  simp only [slDen, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  field_simp
  ring

theorem slDen_one (z : ℂ) : slDen 1 z = 1 := by simp [slDen]

/-- Mod-two reduction. -/
def slRed (g : SL(2, ℤ)) : SL(2, ZMod 2) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2)) g

/-- The three even theta constants indexed by nonzero vectors of `𝔽₂²`:
`(0,1) ↦ θ₂`, `(1,1) ↦ θ₃`, `(1,0) ↦ θ₄`. -/
def thetaChar (v : Fin 2 → ZMod 2) : ℂ → ℂ :=
  if v = ![0, 1] then thetaTwo else if v = ![1, 1] then thetaThree
  else if v = ![1, 0] then thetaFour else fun _ => 0

/-- Right action of `SL(2,𝔽₂)` on row vectors. -/
def charAct (v : Fin 2 → ZMod 2) (g : SL(2, ZMod 2)) : Fin 2 → ZMod 2 :=
  Matrix.vecMul v (g : Matrix (Fin 2) (Fin 2) (ZMod 2))

theorem charAct_mul (v : Fin 2 → ZMod 2) (g h : SL(2, ZMod 2)) :
    charAct v (g * h) = charAct (charAct v g) h := by
  simp [charAct, Matrix.vecMul_vecMul]

theorem charAct_ne_zero {v : Fin 2 → ZMod 2} (hv : v ≠ 0) (g : SL(2, ZMod 2)) :
    charAct v g ≠ 0 := by
  intro h
  apply hv
  have h2 := congrArg (fun w => Matrix.vecMul w ((g⁻¹ : SL(2, ZMod 2)) :
    Matrix (Fin 2) (Fin 2) (ZMod 2))) h
  simp only [charAct, Matrix.vecMul_vecMul, Matrix.zero_vecMul] at h2
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.vecMul_one] at h2
  exact h2

/-- **Modulus law.** `|θ_v(g z)| = |cz+d|^{1/2} |θ_{v·ḡ}(z)|` for every nonzero characteristic. -/
def ThetaModulusLaw (g : SL(2, ℤ)) : Prop :=
  ∀ (z : ℍ) (v : Fin 2 → ZMod 2), v ≠ 0 →
    ‖thetaChar v ((g • z : ℍ) : ℂ)‖ =
      ‖slDen g z‖ ^ (1 / 2 : ℝ) * ‖thetaChar (charAct v (slRed g)) z‖


theorem char_cases (v : Fin 2 → ZMod 2) (hv : v ≠ 0) :
    v = ![0, 1] ∨ v = ![1, 1] ∨ v = ![1, 0] := by
  revert v; decide

theorem slRed_S : ((slRed ModularGroup.S : SL(2, ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
    !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [slRed, ModularGroup.S]

theorem slRed_T : ((slRed ModularGroup.T : SL(2, ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
    !![1, 1; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [slRed, ModularGroup.T]

theorem thetaChar_two : thetaChar ![0, 1] = thetaTwo := by simp [thetaChar]
theorem thetaChar_three : thetaChar ![1, 1] = thetaThree := by
  unfold thetaChar; rw [if_neg (by decide), if_pos rfl]
theorem thetaChar_four : thetaChar ![1, 0] = thetaFour := by
  unfold thetaChar; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem norm_cpow_half_sl (x : ℂ) (hx : x ≠ 0) : ‖x ^ (1 / 2 : ℂ)‖ = ‖x‖ ^ (1 / 2 : ℝ) := by
  rw [Complex.norm_cpow_of_ne_zero hx]; norm_num

theorem thetaModulusLaw_S : ThetaModulusLaw ModularGroup.S := by
  intro z v hv
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  have hcoe : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
    rw [modular_S_smul, UpperHalfPlane.coe_mk]; simp [neg_div, one_div, inv_neg]
  have hden : slDen ModularGroup.S z = z := by simp [slDen, ModularGroup.S]
  have hIz : Complex.I / (z : ℂ) ≠ 0 := div_ne_zero Complex.I_ne_zero hz0
  have hmIz : -Complex.I * (z : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0
  have hnI : ‖1 / (Complex.I / (z : ℂ)) ^ (1 / 2 : ℂ)‖ = ‖(z : ℂ)‖ ^ (1 / 2 : ℝ) := by
    rw [norm_div, norm_one, norm_cpow_half_sl _ hIz, norm_div, Complex.norm_I,
      Real.div_rpow zero_le_one (norm_nonneg _), Real.one_rpow, one_div_one_div]
  have hnm : ‖(-Complex.I * (z : ℂ)) ^ (1 / 2 : ℂ)‖ = ‖(z : ℂ)‖ ^ (1 / 2 : ℝ) := by
    rw [norm_cpow_half_sl _ hmIz, norm_mul, norm_neg, Complex.norm_I, one_mul]
  rw [hcoe, hden]
  unfold charAct
  rw [slRed_S]
  rcases char_cases v hv with rfl | rfl | rfl
  · have : Matrix.vecMul ![(0 : ZMod 2), 1] !![0, 1; 1, 0] = ![1, 0] := by decide
    rw [this, thetaChar_two, thetaChar_four, thetaTwo_S _ hz0, norm_mul, hnI]
  · have : Matrix.vecMul ![(1 : ZMod 2), 1] !![0, 1; 1, 0] = ![1, 1] := by decide
    rw [this, thetaChar_three, thetaThree_S _ hz0, norm_mul, hnm]
  · have : Matrix.vecMul ![(1 : ZMod 2), 0] !![0, 1; 1, 0] = ![0, 1] := by decide
    rw [this, thetaChar_four, thetaChar_two, thetaFour_S _ hz0, norm_mul, hnI]

theorem thetaModulusLaw_T : ThetaModulusLaw ModularGroup.T := by
  intro z v hv
  have hcoe : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    rw [modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring
  have hden : slDen ModularGroup.T z = 1 := by simp [slDen, ModularGroup.T]
  rw [hcoe, hden, norm_one, Real.one_rpow, one_mul]
  unfold charAct
  rw [slRed_T]
  rcases char_cases v hv with rfl | rfl | rfl
  · have : Matrix.vecMul ![(0 : ZMod 2), 1] !![1, 1; 0, 1] = ![0, 1] := by decide
    rw [this, thetaChar_two, thetaTwo_add_one, norm_mul, Complex.norm_exp]
    have : ((Real.pi : ℂ) * Complex.I / 4).re = 0 := by simp
    rw [this, Real.exp_zero, one_mul]
  · have : Matrix.vecMul ![(1 : ZMod 2), 1] !![1, 1; 0, 1] = ![1, 0] := by decide
    rw [this, thetaChar_three, thetaChar_four, thetaThree_add_one]
  · have : Matrix.vecMul ![(1 : ZMod 2), 0] !![1, 1; 0, 1] = ![1, 1] := by decide
    rw [this, thetaChar_four, thetaChar_three, thetaFour_add_one]


theorem thetaModulusLaw_one : ThetaModulusLaw 1 := by
  intro z v _
  have hden : slDen 1 (z : ℂ) = 1 := slDen_one _
  have hred : slRed 1 = 1 := map_one _
  rw [one_smul, hden, hred, norm_one, Real.one_rpow, one_mul]
  simp [charAct]

theorem thetaModulusLaw_mul {x y : SL(2, ℤ)} (hx : ThetaModulusLaw x) (hy : ThetaModulusLaw y) :
    ThetaModulusLaw (x * y) := by
  intro z v hv
  have hred : slRed (x * y) = slRed x * slRed y := map_mul _ _ _
  rw [mul_smul, hx (y • z) v hv, hy z _ (charAct_ne_zero hv _), slDen_mul, norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _), hred, charAct_mul]
  ring

theorem thetaModulusLaw_inv {x : SL(2, ℤ)} (hx : ThetaModulusLaw x) : ThetaModulusLaw x⁻¹ := by
  intro z v hv
  set w := charAct v (slRed x⁻¹) with hw
  have hw0 : w ≠ 0 := charAct_ne_zero hv _
  have h := hx (x⁻¹ • z) w hw0
  have hback : charAct w (slRed x) = v := by
    rw [hw, ← charAct_mul, show slRed x⁻¹ * slRed x = 1 by simp [slRed]]
    simp [charAct]
  rw [smul_inv_smul, hback] at h
  have hcoc := slDen_mul x x⁻¹ z
  rw [mul_inv_cancel, slDen_one] at hcoc
  have hn : ‖slDen x ((x⁻¹ • z : ℍ) : ℂ)‖ * ‖slDen x⁻¹ z‖ = 1 := by
    rw [← norm_mul, ← hcoc, norm_one]
  have hpos : 0 < ‖slDen x ((x⁻¹ • z : ℍ) : ℂ)‖ := norm_pos_iff.mpr (slDen_ne_zero _ _)
  have hpos' : 0 < ‖slDen x⁻¹ (z : ℂ)‖ := norm_pos_iff.mpr (slDen_ne_zero _ _)
  have hr : ‖slDen x ((x⁻¹ • z : ℍ) : ℂ)‖ ^ (1 / 2 : ℝ) * ‖slDen x⁻¹ (z : ℂ)‖ ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.mul_rpow hpos.le hpos'.le, hn, Real.one_rpow]
  have hrpos : 0 < ‖slDen x ((x⁻¹ • z : ℍ) : ℂ)‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
  rw [h, ← mul_assoc, mul_comm (‖slDen x⁻¹ (z : ℂ)‖ ^ (1 / 2 : ℝ)), hr, one_mul]

/-- **The modulus law holds for all of `SL(2,ℤ)`.** -/
theorem thetaModulusLaw (g : SL(2, ℤ)) : ThetaModulusLaw g := by
  have hmem : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact thetaModulusLaw_S
      · exact thetaModulusLaw_T
  | one => exact thetaModulusLaw_one
  | mul x y _ _ hx hy => exact thetaModulusLaw_mul hx hy
  | inv x _ hx => exact thetaModulusLaw_inv hx


/-! ## Theta bounds on `{im ≥ 4/5}` -/

theorem exp_neg_two_fifths_pi_lt : Real.exp (-(2 / 5 * Real.pi)) < 7 / 20 := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have h1 : Real.exp (-(2 / 5 * Real.pi)) ≤ Real.exp (-(6 / 5)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : 1 + 6 / 5 + (6 / 5 : ℝ) ^ 2 / 2 ≤ Real.exp (6 / 5) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have h3 : Real.exp (-(6 / 5)) = (Real.exp (6 / 5))⁻¹ := Real.exp_neg _
  have h4 : (Real.exp (6 / 5))⁻¹ < 7 / 20 := by
    rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]; norm_num at h2 ⊢; linarith
  linarith

theorem norm_jacobiTheta₂_half_sub_two_le {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ - 2‖ ≤ 4 / 5 := by
  have hτ0 : 0 < τ.im := by linarith
  set t : ℝ := Real.exp (-(Real.pi / 2 * τ.im)) with ht_def
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have ht35 : t < 7 / 20 := by
    have : Real.exp (-(Real.pi / 2 * τ.im)) ≤ Real.exp (-(2 / 5 * Real.pi)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith [exp_neg_two_fifths_pi_lt]
  have ht1 : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hnat : Summable (fun n : ℕ => t ^ n) := summable_geometric_of_lt_one ht0 ht1
  have hgsum : Summable (fun n : ℤ => t ^ n.natAbs) := by
    rw [summable_int_iff_summable_nat_and_neg]; exact ⟨by simpa using hnat, by simpa using hnat⟩
  have hgval : ∑' n : ℤ, t ^ n.natAbs = (1 + t) / (1 - t) := by
    have heven : (fun n : ℤ => t ^ n.natAbs).Even := fun n => by simp only [Int.natAbs_neg]
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hgsum]
    have hpnat : (∑' n : ℕ+, t ^ ((n : ℤ)).natAbs) = t / (1 - t) := by
      have h1 : (∑' n : ℕ+, t ^ ((n : ℤ)).natAbs) = ∑' n : ℕ+, t ^ ((n : ℕ)) := by
        apply tsum_congr; intro n; simp
      rw [h1, tsum_pnat_eq_tsum_succ (f := fun k => t ^ k),
        show (fun n : ℕ => t ^ (n + 1)) = (fun n => t * t ^ n) from by funext n; rw [pow_succ]; ring,
        tsum_mul_left, tsum_geometric_of_lt_one ht0 ht1, div_eq_mul_inv]
    rw [hpnat, show ((0 : ℤ)).natAbs = 0 from rfl, pow_zero]
    simp only [nsmul_eq_mul]
    field_simp
    ring
  set f : ℤ → ℂ := fun n => jacobiTheta₂_term n (τ / 2) τ with hf_def
  have hfsum : Summable f := (summable_jacobiTheta₂_term_iff (τ / 2) τ).mpr hτ0
  set c : ℤ → ℂ := fun n => if n = 0 ∨ n = -1 then 1 else 0 with hc_def
  have hcHS : HasSum c (∑ i ∈ ({0, -1} : Finset ℤ), c i) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn; rw [hc_def]; simp only; rw [if_neg]; rintro (rfl | rfl) <;> simp at hn
  have hc_tsum : ∑' n, c n = 2 := by
    rw [hcHS.tsum_eq, Finset.sum_pair (show (0 : ℤ) ≠ -1 by norm_num)]; norm_num [hc_def]
  have hcsum : Summable c := hcHS.summable
  have hbound : ∀ n : ℤ, ‖f n - c n‖ ≤ t * t ^ n.natAbs := by
    intro n
    by_cases h : n = 0 ∨ n = -1
    · rcases h with rfl | rfl
      · rw [hf_def, hc_def]; simp only [jacobiTheta₂_half_term_zero]; norm_num; positivity
      · rw [hf_def, hc_def]; simp only [jacobiTheta₂_half_term_negone]; norm_num; positivity
    · have hc0 : c n = 0 := by rw [hc_def]; simp only; rw [if_neg h]
      rw [hc0, sub_zero, hf_def, norm_jacobiTheta₂_half_term]
      have hne : n ≠ -1 := fun he => h (Or.inr he)
      have hne0 : n ≠ 0 := fun he => h (Or.inl he)
      have hcomp : |(n : ℝ)| ≤ (n : ℝ) ^ (2 : ℕ) + n := sq_add_self_ge_abs n hne
      have hge1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne0
      have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [ht_def, ← pow_succ', ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hpt : 0 < Real.pi * τ.im := mul_pos Real.pi_pos hτ0
      push_cast
      rw [habs]
      nlinarith [hcomp, hge1, hpt]
  have hmajor : Summable (fun n : ℤ => t * t ^ n.natAbs) := hgsum.mul_left t
  have hfcsum : Summable (fun n => ‖f n - c n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hmajor
  have hjt : jacobiTheta₂ (τ / 2) τ = ∑' n, f n := rfl
  have he : jacobiTheta₂ (τ / 2) τ - 2 = ∑' n, (f n - c n) := by
    rw [hjt, Summable.tsum_sub hfsum hcsum, hc_tsum]
  rw [he]
  calc ‖∑' n, (f n - c n)‖ ≤ ∑' n, ‖f n - c n‖ := norm_tsum_le_tsum_norm hfcsum
    _ ≤ ∑' n : ℤ, t * t ^ n.natAbs := Summable.tsum_mono hfcsum hmajor hbound
    _ = t * ((1 + t) / (1 - t)) := by rw [tsum_mul_left, hgval]
    _ ≤ 4 / 5 := by
        rw [mul_div_assoc', div_le_iff₀ h1t]; nlinarith

theorem norm_thetaTwo_bounds {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    Real.exp (-Real.pi * τ.im / 4) ≤ ‖thetaTwo τ‖ ∧
      ‖thetaTwo τ‖ ≤ 3 * Real.exp (-Real.pi * τ.im / 4) := by
  have h := norm_jacobiTheta₂_half_sub_two_le hτ
  have hexp : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4)‖ = Real.exp (-Real.pi * τ.im / 4) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hlo : 1 ≤ ‖jacobiTheta₂ (τ / 2) τ‖ := by
    have := norm_sub_norm_le (2 : ℂ) (2 - jacobiTheta₂ (τ / 2) τ)
    rw [sub_sub_cancel, norm_sub_rev] at this
    norm_num at this; linarith
  have hhi : ‖jacobiTheta₂ (τ / 2) τ‖ ≤ 3 := by
    have := norm_le_insert' (jacobiTheta₂ (τ / 2) τ) 2
    calc ‖jacobiTheta₂ (τ / 2) τ‖ = ‖(jacobiTheta₂ (τ / 2) τ - 2) + 2‖ := by ring_nf
      _ ≤ ‖jacobiTheta₂ (τ / 2) τ - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 := by norm_num; linarith
  unfold thetaTwo
  rw [norm_mul, hexp]
  have hE := Real.exp_pos (-Real.pi * τ.im / 4)
  constructor
  · nlinarith
  · nlinarith

theorem norm_thetaThree_sub_one_le_third {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    ‖thetaThree τ - 1‖ ≤ 1 / 3 := by
  have hτ0 : 0 < τ.im := by linarith
  have h := norm_jacobiTheta_sub_one_le hτ0
  have hr : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-(4 / 5 * Real.pi)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hr2 : Real.exp (-(4 / 5 * Real.pi)) < 49 / 400 := by
    have := exp_neg_two_fifths_pi_lt
    have hsq : Real.exp (-(4 / 5 * Real.pi)) = Real.exp (-(2 / 5 * Real.pi)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hsq]; nlinarith [Real.exp_pos (-(2 / 5 * Real.pi))]
  have hpos := Real.exp_pos (-Real.pi * τ.im)
  have hthree : thetaThree τ = jacobiTheta τ := by rw [thetaThree, jacobiTheta_eq_jacobiTheta₂]
  rw [hthree]
  refine h.trans ?_
  have hden : 351 / 400 < 1 - Real.exp (-Real.pi * τ.im) := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

theorem norm_thetaThree_bounds {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    1 / 2 ≤ ‖thetaThree τ‖ ∧ ‖thetaThree τ‖ ≤ 2 := by
  have h := norm_thetaThree_sub_one_le_third hτ
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (1 - thetaThree τ)
    rw [sub_sub_cancel, norm_sub_rev, norm_one] at this; linarith
  · calc ‖thetaThree τ‖ = ‖(thetaThree τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖thetaThree τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith

theorem norm_thetaFour_bounds {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    1 / 2 ≤ ‖thetaFour τ‖ ∧ ‖thetaFour τ‖ ≤ 2 := by
  have h := norm_thetaThree_bounds (τ := τ + 1) (by simpa using hτ)
  rwa [thetaThree_add_one] at h


/-! ## The Farey-type bound -/

theorem norm_thetaChar_le_three {w : Fin 2 → ZMod 2} (hw : w ≠ 0) {z : ℂ} (hz : (4 : ℝ) / 5 ≤ z.im) :
    ‖thetaChar w z‖ ≤ 3 := by
  rcases char_cases w hw with rfl | rfl | rfl
  · rw [thetaChar_two]
    have h := (norm_thetaTwo_bounds hz).2
    have : Real.exp (-Real.pi * z.im / 4) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    nlinarith
  · rw [thetaChar_three]; linarith [(norm_thetaThree_bounds hz).2]
  · rw [thetaChar_four]; linarith [(norm_thetaFour_bounds hz).2]

theorem half_le_norm_thetaChar {w : Fin 2 → ZMod 2} (hw : w ≠ 0) (h2 : w ≠ ![0, 1]) {z : ℂ}
    (hz : (4 : ℝ) / 5 ≤ z.im) : 1 / 2 ≤ ‖thetaChar w z‖ := by
  rcases char_cases w hw with rfl | rfl | rfl
  · exact absurd rfl h2
  · rw [thetaChar_three]; exact (norm_thetaThree_bounds hz).1
  · rw [thetaChar_four]; exact (norm_thetaFour_bounds hz).1

theorem norm_thetaChar_le_two {w : Fin 2 → ZMod 2} (hw : w ≠ 0) (h2 : w ≠ ![0, 1]) {z : ℂ}
    (hz : (4 : ℝ) / 5 ≤ z.im) : ‖thetaChar w z‖ ≤ 2 := by
  rcases char_cases w hw with rfl | rfl | rfl
  · exact absurd rfl h2
  · rw [thetaChar_three]; exact (norm_thetaThree_bounds hz).2
  · rw [thetaChar_four]; exact (norm_thetaFour_bounds hz).2

theorem slRed_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    ((slRed g : SL(2, ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j = ((g i j : ℤ) : ZMod 2) := by
  simp [slRed]

theorem charAct_three_inv_eq_two_iff (g : SL(2, ℤ)) :
    charAct ![1, 1] (slRed g⁻¹) = ![0, 1] ↔ Odd (g 1 0) ∧ Odd (g 1 1) := by
  have hinv : slRed g⁻¹ = (slRed g)⁻¹ := map_inv _ _
  have key : charAct ![1, 1] (slRed g⁻¹) = ![0, 1] ↔ ![1, 1] = charAct ![0, 1] (slRed g) := by
    constructor
    · intro h
      have := congrArg (fun w => charAct w (slRed g)) h
      rw [← charAct_mul, hinv, inv_mul_cancel] at this
      simpa [charAct] using this
    · intro h
      rw [h, ← charAct_mul, hinv, mul_inv_cancel]
      simp [charAct]
  rw [key]
  have hrow : charAct ![0, 1] (slRed g) = ![((g 1 0 : ℤ) : ZMod 2), ((g 1 1 : ℤ) : ZMod 2)] := by
    ext j
    fin_cases j <;> simp [charAct, Matrix.vecMul, dotProduct, Fin.sum_univ_two, slRed_apply]
  rw [hrow, ← ZMod.intCast_eq_one_iff_odd, ← ZMod.intCast_eq_one_iff_odd]
  constructor
  · intro h
    have h0 : ((g 1 0 : ℤ) : ZMod 2) = 1 := by have := congrFun h 0; simpa using this.symm
    have h1 : ((g 1 1 : ℤ) : ZMod 2) = 1 := by have := congrFun h 1; simpa using this.symm
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    ext j; fin_cases j <;> simp [h0, h1]

/-- **Farey-type bound for `θ₂⁴θ₄⁴/θ₃⁷ = θ₃·h`.**  After reduction `g τ ∈ 𝒟`, the form is bounded by
`|cτ+d|^{-1/2}` times `e^{(7π/4) im(gτ)}` when the bottom row of `g` is odd/odd (the reducing cusp is
a zero-charge cusp), and by `|cτ+d|^{-1/2}` otherwise. -/
theorem norm_thetaForm_farey (τ : ℍ) :
    ∃ g : SL(2, ℤ), (4 : ℝ) / 5 ≤ (g • τ).im ∧
      ‖thetaTwo τ ^ 4 * thetaFour τ ^ 4 / thetaThree τ ^ 7‖ ≤
        3 ^ 8 * 2 ^ 7 * ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) *
          (if Odd (g 1 0) ∧ Odd (g 1 1) then Real.exp (7 * Real.pi / 4 * (g • τ).im) else 1) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  refine ⟨g, ?_, ?_⟩
  · have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := (g • τ).im_pos
    nlinarith
  set z' : ℍ := g • τ with hz'
  have him : (4 : ℝ) / 5 ≤ (z' : ℂ).im := by
    have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := z'.im_pos
    show (4 : ℝ) / 5 ≤ z'.im
    nlinarith
  have hτeq : (τ : ℂ) = ((g⁻¹ • z' : ℍ) : ℂ) := by rw [hz', inv_smul_smul]
  have hlaw := thetaModulusLaw g⁻¹ z'
  set D : ℝ := ‖slDen g⁻¹ (z' : ℂ)‖ with hD
  have hcoc := slDen_mul g⁻¹ g τ
  rw [inv_mul_cancel, slDen_one, ← hz'] at hcoc
  have hDpos : 0 < D := norm_pos_iff.mpr (slDen_ne_zero _ _)
  have hGpos : 0 < ‖slDen g (τ : ℂ)‖ := norm_pos_iff.mpr (slDen_ne_zero _ _)
  have hDG : D * ‖slDen g (τ : ℂ)‖ = 1 := by rw [hD, ← norm_mul, ← hcoc, norm_one]
  have hDhalf : D ^ (1 / 2 : ℝ) = ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) := by
    have : D = ‖slDen g (τ : ℂ)‖⁻¹ := by field_simp; linarith
    rw [this, Real.inv_rpow hGpos.le, Real.rpow_neg hGpos.le]
  set a2 := charAct ![0, 1] (slRed g⁻¹)
  set a3 := charAct ![1, 1] (slRed g⁻¹)
  set a4 := charAct ![1, 0] (slRed g⁻¹)
  have hn2 : (![0, 1] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hn3 : (![1, 1] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hn4 : (![1, 0] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have e2 := hlaw _ hn2
  have e3 := hlaw _ hn3
  have e4 := hlaw _ hn4
  rw [thetaChar_two, ← hτeq] at e2
  rw [thetaChar_three, ← hτeq] at e3
  rw [thetaChar_four, ← hτeq] at e4
  have ha2 : a2 ≠ 0 := charAct_ne_zero hn2 _
  have ha3 : a3 ≠ 0 := charAct_ne_zero hn3 _
  have ha4 : a4 ≠ 0 := charAct_ne_zero hn4 _
  -- injectivity of the action separates the images
  have hinj : ∀ {u v : Fin 2 → ZMod 2}, charAct u (slRed g⁻¹) = charAct v (slRed g⁻¹) → u = v := by
    intro u v h
    have := congrArg (fun w => charAct w (slRed g⁻¹)⁻¹) h
    simp only [← charAct_mul, mul_inv_cancel] at this
    simpa [charAct] using this
  set A := ‖thetaChar a2 (z' : ℂ)‖
  set B := ‖thetaChar a3 (z' : ℂ)‖
  set C := ‖thetaChar a4 (z' : ℂ)‖
  have hA3 : A ≤ 3 := norm_thetaChar_le_three ha2 him
  have hC3 : C ≤ 3 := norm_thetaChar_le_three ha4 him
  have hA0 : 0 ≤ A := norm_nonneg _
  have hC0 : 0 ≤ C := norm_nonneg _
  have hθ3ne : thetaThree (τ : ℂ) ≠ 0 := thetaThree_ne_zero_of_im_pos τ.im_pos
  have hB0 : 0 < B := by
    have : ‖thetaThree (τ : ℂ)‖ = D ^ (1 / 2 : ℝ) * B := e3
    have h' : 0 < ‖thetaThree (τ : ℂ)‖ := norm_pos_iff.mpr hθ3ne
    rw [this] at h'
    exact pos_of_mul_pos_right h' (Real.rpow_nonneg hDpos.le _)
  have hnorm : ‖thetaTwo τ ^ 4 * thetaFour τ ^ 4 / thetaThree τ ^ 7‖ =
      D ^ (1 / 2 : ℝ) * (A ^ 4 * C ^ 4 / B ^ 7) := by
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow, e2, e3, e4]
    have hs : 0 < D ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hDpos _
    field_simp
  rw [hnorm, hDhalf]
  have hSpos : 0 < ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hGpos _
  by_cases hpar : Odd (g 1 0) ∧ Odd (g 1 1)
  · rw [if_pos hpar]
    have ha3eq : a3 = ![0, 1] := (charAct_three_inv_eq_two_iff g).mpr hpar
    have ha2ne : a2 ≠ ![0, 1] := by
      intro h; exact absurd (hinj (h.trans ha3eq.symm)) (by decide)
    have ha4ne : a4 ≠ ![0, 1] := by
      intro h; exact absurd (hinj (h.trans ha3eq.symm)) (by decide)
    have hA2 : A ≤ 2 := norm_thetaChar_le_two ha2 ha2ne him
    have hC2 : C ≤ 2 := norm_thetaChar_le_two ha4 ha4ne him
    have hBlo : Real.exp (-Real.pi * (z' : ℂ).im / 4) ≤ B := by
      have := (norm_thetaTwo_bounds him).1
      simp only [B, ha3eq, thetaChar_two]; exact this
    have hE : 0 < Real.exp (-Real.pi * (z' : ℂ).im / 4) := Real.exp_pos _
    have hB7 : Real.exp (-Real.pi * (z' : ℂ).im / 4) ^ 7 ≤ B ^ 7 := pow_le_pow_left₀ hE.le hBlo 7
    have hE7 : Real.exp (-Real.pi * (z' : ℂ).im / 4) ^ 7 * Real.exp (7 * Real.pi / 4 * (g • τ).im) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      have : ((7 : ℕ) : ℝ) * (-Real.pi * (z' : ℂ).im / 4) + 7 * Real.pi / 4 * (g • τ).im = 0 := by
        rw [hz']; simp only [UpperHalfPlane.coe_im]; push_cast; ring
      rw [this, Real.exp_zero]
    have hnum : A ^ 4 * C ^ 4 ≤ 2 ^ 8 := by
      have h1 : A ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ hA0 hA2 4
      have h2 : C ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ hC0 hC2 4
      nlinarith [pow_nonneg hA0 4, pow_nonneg hC0 4]
    have hkey : A ^ 4 * C ^ 4 / B ^ 7 ≤ 3 ^ 8 * 2 ^ 7 * Real.exp (7 * Real.pi / 4 * (g • τ).im) := by
      rw [div_le_iff₀ (pow_pos hB0 7)]
      have hX := Real.exp_pos (7 * Real.pi / 4 * (g • τ).im)
      nlinarith [hB7, hE7, hnum, pow_pos hE 7]
    calc ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (A ^ 4 * C ^ 4 / B ^ 7)
        ≤ ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) *
            (3 ^ 8 * 2 ^ 7 * Real.exp (7 * Real.pi / 4 * (g • τ).im)) :=
          mul_le_mul_of_nonneg_left hkey hSpos.le
      _ = _ := by ring
  · rw [if_neg hpar, mul_one]
    have ha3ne : a3 ≠ ![0, 1] := fun h => hpar ((charAct_three_inv_eq_two_iff g).mp h)
    have hBlo : 1 / 2 ≤ B := half_le_norm_thetaChar ha3 ha3ne him
    have hnum : A ^ 4 * C ^ 4 ≤ 3 ^ 8 := by
      have h1 : A ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ hA0 hA3 4
      have h2 : C ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ hC0 hC3 4
      nlinarith [pow_nonneg hA0 4, pow_nonneg hC0 4]
    have hB7 : (1 / 2 : ℝ) ^ 7 ≤ B ^ 7 := pow_le_pow_left₀ (by norm_num) hBlo 7
    have hkey : A ^ 4 * C ^ 4 / B ^ 7 ≤ 3 ^ 8 * 2 ^ 7 := by
      rw [div_le_iff₀ (pow_pos hB0 7)]
      nlinarith [hB7, hnum]
    calc ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (A ^ 4 * C ^ 4 / B ^ 7)
        ≤ ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (3 ^ 8 * 2 ^ 7) :=
          mul_le_mul_of_nonneg_left hkey hSpos.le
      _ = _ := by ring

end

end RHTower
