import GaloisForLFunctions.Bottcher.Gamma2Generators
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.GroupTheory.CoprodI

/-!
# Sanov's theorem for `Γ(2)` and its winding homomorphism

Let `A = [[1,2],[0,1]]` and `B = [[1,0],[2,1]]` (`sanovA`, `sanovB`).

* **Sanov** (`sanov_free`): `A` and `B` generate a free group of rank two, i.e.
  `FreeGroup.lift ![A, B]` is injective.
* **Generation** (`gammaTwo_eq_closure`): `Γ(2) = ⟨A, B, −1⟩`.
* **Winding** (`gammaTwoWinding`): there is a homomorphism `Γ(2) → ℤ` (written multiplicatively)
  with `A ↦ 1`, `B ↦ 0`, `−1 ↦ 0`, the exponent sum of `A`.

**Proofs.**
* Ping-pong on the upper half-plane with
  `X_A = {Re z ≥ 1}`, `Y_A = {Re z < −1}`, `X_B = {Re(Sz) < −1}`, `Y_B = {Re(Sz) ≥ 1}`.
  Here `A` is the translation by `2`, and `B = S⁻¹A⁻¹S` with `Sz = −1/z`.
* Generation is `Bottcher.Gamma2_eq_closure`.
* The matrices with `a ≡ d ≡ 1 (mod 4)` and `b, c` even form a subgroup (`sanovModFourSubgroup`).
  It contains `⟨A, B⟩` but not `−1`, so `Γ(2) = ⟨A, B⟩ ⊔ −⟨A, B⟩` (disjoint union). The winding is
  the exponent sum of `A` after removing the sign.
-/

open Matrix ModularGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The generators -/

/-- `A = [[1,2],[0,1]]`. -/
def sanovA : SL(2, ℤ) := ⟨!![1, 2; 0, 1], by norm_num [Matrix.det_fin_two_of]⟩

/-- `B = [[1,0],[2,1]]`. -/
def sanovB : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by norm_num [Matrix.det_fin_two_of]⟩

theorem sanovA_eq : sanovA = ModularGroup.T ^ 2 :=
  Subtype.ext (by rw [Bottcher.Tsq_coe]; rfl)

theorem sanovB_eq : sanovB = Bottcher.Rgen := rfl

theorem sanovA_mem : sanovA ∈ Gamma 2 := by
  rw [sanovA_eq]; exact Bottcher.Tsq_mem_Gamma2

theorem sanovB_mem : sanovB ∈ Gamma 2 := Bottcher.Rgen_mem_Gamma2

/-- **Generation:** `Γ(2) = ⟨A, B, −1⟩`. -/
theorem gammaTwo_eq_closure :
    Gamma 2 = Subgroup.closure ({sanovA, sanovB, -1} : Set SL(2, ℤ)) := by
  rw [sanovA_eq, sanovB_eq]; exact Bottcher.Gamma2_eq_closure

/-! ## Ping-pong on the upper half-plane -/

/-- The generator family `![A, B]`. -/
def sanovGen : Fin 2 → SL(2, ℤ) := fun i => if i = 0 then sanovA else sanovB

theorem sanovB_eq_conj : sanovB = ModularGroup.S⁻¹ * sanovA⁻¹ * ModularGroup.S := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv]
  simp only [sanovA, sanovB, ModularGroup.S, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sanovA_smul_re (z : ℍ) : (sanovA • z).re = 2 + z.re := by
  rw [sanovA_eq, ← zpow_natCast, modular_T_zpow_smul, vadd_re]; norm_num

theorem sanovA_inv_smul_re (z : ℍ) : (sanovA⁻¹ • z).re = -2 + z.re := by
  rw [sanovA_eq, ← zpow_natCast, ← zpow_neg, modular_T_zpow_smul, vadd_re]; norm_num

/-- `Re(Sz) = −Re z/|z|²`. -/
theorem sanov_S_smul_re (z : ℍ) :
    (ModularGroup.S • z).re = -z.re / (z.re ^ 2 + z.im ^ 2) := by
  rw [UpperHalfPlane.re, modular_S_smul]
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.neg_re, Complex.neg_im]
  change -z.re / (-z.re * -z.re + -z.im * -z.im) = -z.re / (z.re ^ 2 + z.im ^ 2)
  ring_nf

/-- The ping-pong sets `X_A = {Re ≥ 1}`, `X_B = {Re(Sz) < −1}`. -/
def sanovX : Fin 2 → Set ℍ := ![{z | 1 ≤ z.re}, {z | (ModularGroup.S • z).re < -1}]

/-- The ping-pong sets `Y_A = {Re < −1}`, `Y_B = {Re(Sz) ≥ 1}`. -/
def sanovY : Fin 2 → Set ℍ := ![{z | z.re < -1}, {z | 1 ≤ (ModularGroup.S • z).re}]

theorem S_smul_re_mem_Icc_of_one_le_re {z : ℍ} (hz : 1 ≤ z.re) :
    -1 ≤ (ModularGroup.S • z).re ∧ (ModularGroup.S • z).re < 1 := by
  rw [sanov_S_smul_re]
  have hy := z.im_pos
  have hden : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hden]; nlinarith
  · rw [div_lt_iff₀ hden]; nlinarith

theorem S_smul_re_mem_Icc_of_re_lt {z : ℍ} (hz : z.re < -1) :
    -1 ≤ (ModularGroup.S • z).re ∧ (ModularGroup.S • z).re < 1 := by
  rw [sanov_S_smul_re]
  have hy := z.im_pos
  have hden : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hden]; nlinarith
  · rw [div_lt_iff₀ hden]; nlinarith

theorem sanovB_inv_eq_conj : sanovB⁻¹ = ModularGroup.S⁻¹ * sanovA * ModularGroup.S := by
  rw [sanovB_eq_conj, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, inv_inv, mul_assoc]

theorem sanovB_smul_S_re (z : ℍ) :
    (ModularGroup.S • (sanovB • z)).re = -2 + (ModularGroup.S • z).re := by
  rw [sanovB_eq_conj, mul_smul, mul_smul, ← mul_smul ModularGroup.S, mul_inv_cancel, one_smul,
    sanovA_inv_smul_re]

theorem sanovB_inv_smul_S_re (z : ℍ) :
    (ModularGroup.S • (sanovB⁻¹ • z)).re = 2 + (ModularGroup.S • z).re := by
  rw [sanovB_inv_eq_conj, mul_smul, mul_smul, ← mul_smul ModularGroup.S, mul_inv_cancel, one_smul,
    sanovA_smul_re]

theorem sanovGen_eq : (fun i : Fin 2 => if i = 0 then sanovA else sanovB) = ![sanovA, sanovB] := by
  funext i; fin_cases i <;> rfl

/-- **Sanov:** `A` and `B` generate a free group of rank two. -/
theorem sanov_free :
    Function.Injective (FreeGroup.lift (fun i : Fin 2 => if i = 0 then sanovA else sanovB)) := by
  rw [sanovGen_eq]
  refine FreeGroup.injective_lift_of_ping_pong _ sanovX sanovY ?_ ?_ ?_ ?_ ?_ ?_
  · -- nonempty
    intro i
    fin_cases i
    · refine ⟨⟨1 + Complex.I, by simp⟩, ?_⟩
      show 1 ≤ (1 + Complex.I).re
      simp
    · refine ⟨⟨1 / 2 + Complex.I / 4, by simp⟩, ?_⟩
      show (ModularGroup.S • (⟨1 / 2 + Complex.I / 4, _⟩ : ℍ)).re < -1
      rw [sanov_S_smul_re]
      show -(1 / 2 + Complex.I / 4).re / ((1 / 2 + Complex.I / 4).re ^ 2 +
        (1 / 2 + Complex.I / 4).im ^ 2) < -1
      simp
      norm_num
  · -- the X are disjoint
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [Function.onFun, Set.disjoint_left]
      intro z hz hz'
      have h1 : 1 ≤ z.re := hz
      have h2 : (ModularGroup.S • z).re < -1 := hz'
      have := (S_smul_re_mem_Icc_of_one_le_re h1).1
      linarith
    · rw [Function.onFun, Set.disjoint_left]
      intro z hz hz'
      have h1 : 1 ≤ z.re := hz'
      have h2 : (ModularGroup.S • z).re < -1 := hz
      have := (S_smul_re_mem_Icc_of_one_le_re h1).1
      linarith
    · exact absurd rfl hij
  · -- the Y are disjoint
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [Function.onFun, Set.disjoint_left]
      intro z hz hz'
      have h1 : z.re < -1 := hz
      have h2 : 1 ≤ (ModularGroup.S • z).re := hz'
      have := (S_smul_re_mem_Icc_of_re_lt h1).2
      linarith
    · rw [Function.onFun, Set.disjoint_left]
      intro z hz hz'
      have h1 : z.re < -1 := hz'
      have h2 : 1 ≤ (ModularGroup.S • z).re := hz
      have := (S_smul_re_mem_Icc_of_re_lt h1).2
      linarith
    · exact absurd rfl hij
  · -- X i and Y j are disjoint
    intro i j
    rw [Set.disjoint_left]
    intro z hz hz'
    fin_cases i <;> fin_cases j
    · have h1 : 1 ≤ z.re := hz
      have h2 : z.re < -1 := hz'
      linarith
    · have h1 : 1 ≤ z.re := hz
      have h2 : 1 ≤ (ModularGroup.S • z).re := hz'
      have := (S_smul_re_mem_Icc_of_one_le_re h1).2
      linarith
    · have h1 : (ModularGroup.S • z).re < -1 := hz
      have h2 : z.re < -1 := hz'
      have := (S_smul_re_mem_Icc_of_re_lt h2).1
      linarith
    · have h1 : (ModularGroup.S • z).re < -1 := hz
      have h2 : 1 ≤ (ModularGroup.S • z).re := hz'
      linarith
  · -- `a i • (Y i)ᶜ ⊆ X i`
    intro i
    fin_cases i
    · rintro _ ⟨z, hz, rfl⟩
      have h1 : ¬ z.re < -1 := hz
      show 1 ≤ (sanovA • z).re
      rw [sanovA_smul_re]; push Not at h1; linarith
    · rintro _ ⟨z, hz, rfl⟩
      have h1 : ¬ 1 ≤ (ModularGroup.S • z).re := hz
      show (ModularGroup.S • (sanovB • z)).re < -1
      rw [sanovB_smul_S_re]; push Not at h1; linarith
  · -- `a⁻¹ i • (X i)ᶜ ⊆ Y i`
    intro i
    fin_cases i
    · rintro _ ⟨z, hz, rfl⟩
      have h1 : ¬ 1 ≤ z.re := hz
      show (sanovA⁻¹ • z).re < -1
      rw [sanovA_inv_smul_re]; push Not at h1; linarith
    · rintro _ ⟨z, hz, rfl⟩
      have h1 : ¬ (ModularGroup.S • z).re < -1 := hz
      show 1 ≤ (ModularGroup.S • (sanovB⁻¹ • z)).re
      rw [sanovB_inv_smul_S_re]; push Not at h1; linarith

/-! ## The sign and the winding homomorphism -/

/-- The matrices `[[a,b],[c,d]]` with `a ≡ d ≡ 1 (mod 4)` and `b, c` even form a subgroup. -/
def sanovModFourSubgroup : Subgroup SL(2, ℤ) where
  carrier := {g | (4 : ℤ) ∣ g.val 0 0 - 1 ∧ (4 : ℤ) ∣ g.val 1 1 - 1 ∧ (2 : ℤ) ∣ g.val 0 1 ∧
    (2 : ℤ) ∣ g.val 1 0}
  mul_mem' := by
    rintro g h ⟨ha, hd, hb, hc⟩ ⟨ha', hd', hb', hc'⟩
    have e : ∀ i j, (g * h).val i j = g.val i 0 * h.val 0 j + g.val i 1 * h.val 1 j := by
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have h4 : ∀ x y : ℤ, (2 : ℤ) ∣ x → (2 : ℤ) ∣ y → (4 : ℤ) ∣ x * y := fun x y hx hy => by
      have := mul_dvd_mul hx hy; norm_num at this; exact this
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e]
      have : g.val 0 0 * h.val 0 0 + g.val 0 1 * h.val 1 0 - 1 =
          (g.val 0 0 - 1) * h.val 0 0 + (h.val 0 0 - 1) + g.val 0 1 * h.val 1 0 := by ring
      rw [this]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left ha _) ha') (h4 _ _ hb hc')
    · rw [e]
      have : g.val 1 0 * h.val 0 1 + g.val 1 1 * h.val 1 1 - 1 =
          g.val 1 0 * h.val 0 1 + ((g.val 1 1 - 1) * h.val 1 1 + (h.val 1 1 - 1)) := by ring
      rw [this]
      exact dvd_add (h4 _ _ hc hb') (dvd_add (dvd_mul_of_dvd_left hd _) hd')
    · rw [e]
      exact dvd_add (dvd_mul_of_dvd_right hb' _) (dvd_mul_of_dvd_left hb _)
    · rw [e]
      exact dvd_add (dvd_mul_of_dvd_left hc _) (dvd_mul_of_dvd_right hc' _)
  one_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  inv_mem' := by
    rintro g ⟨ha, hd, hb, hc⟩
    have e : (g⁻¹).val = !![g.val 1 1, -g.val 0 1; -g.val 1 0, g.val 0 0] := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> simp only [Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    · exact hd
    · exact ha
    · exact (dvd_neg).mpr hb
    · exact (dvd_neg).mpr hc

theorem sanovA_mem_modFour : sanovA ∈ sanovModFourSubgroup := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem sanovB_mem_modFour : sanovB ∈ sanovModFourSubgroup := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem neg_one_not_mem_modFour : (-1 : SL(2, ℤ)) ∉ sanovModFourSubgroup := by
  rintro ⟨ha, -, -, -⟩
  have : ((-1 : SL(2, ℤ)).val 0 0) = -1 := by
    rw [Matrix.SpecialLinearGroup.coe_neg]; simp
  rw [this] at ha
  norm_num at ha

/-- The free subgroup `⟨A, B⟩`. -/
abbrev sanovSubgroup : Subgroup SL(2, ℤ) :=
  (FreeGroup.lift (fun i : Fin 2 => if i = 0 then sanovA else sanovB)).range

theorem sanovA_mem_sanovSubgroup : sanovA ∈ sanovSubgroup :=
  ⟨FreeGroup.of 0, by rw [FreeGroup.lift_apply_of]; rfl⟩

theorem sanovB_mem_sanovSubgroup : sanovB ∈ sanovSubgroup :=
  ⟨FreeGroup.of 1, by rw [FreeGroup.lift_apply_of]; rfl⟩

theorem sanovSubgroup_le_modFour : sanovSubgroup ≤ sanovModFourSubgroup := by
  refine FreeGroup.range_lift_le ?_
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact sanovA_mem_modFour
  · exact sanovB_mem_modFour

/-- `−1 ∉ ⟨A, B⟩`. -/
theorem neg_one_not_mem_sanovSubgroup : (-1 : SL(2, ℤ)) ∉ sanovSubgroup := fun h =>
  neg_one_not_mem_modFour (sanovSubgroup_le_modFour h)

theorem sanov_neg_inv_eq (g : SL(2, ℤ)) : (-g)⁻¹ = -g⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])

/-- Every element of `Γ(2)` is `±` an element of `⟨A, B⟩`. -/
theorem mem_or_neg_mem_sanovSubgroup {g : SL(2, ℤ)} (hg : g ∈ Gamma 2) :
    g ∈ sanovSubgroup ∨ -g ∈ sanovSubgroup := by
  rw [gammaTwo_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact Or.inl sanovA_mem_sanovSubgroup
    · exact Or.inl sanovB_mem_sanovSubgroup
    · right; rw [neg_neg]; exact one_mem _
  | one => exact Or.inl (one_mem _)
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (mul_mem hx hy)
    · right; rw [← mul_neg]; exact mul_mem hx hy
    · right; rw [← neg_mul]; exact mul_mem hx hy
    · left; rw [← neg_mul_neg]; exact mul_mem hx hy
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (inv_mem hx)
    · right; rw [← sanov_neg_inv_eq]; exact inv_mem hx

open Classical in
/-- The sign-removing projection `Γ(2) → ⟨A, B⟩`, `±h ↦ h`. -/
def gammaTwoToSanov : Gamma 2 →* sanovSubgroup where
  toFun g := if h : (g : SL(2, ℤ)) ∈ sanovSubgroup then ⟨g, h⟩
    else ⟨-g, (mem_or_neg_mem_sanovSubgroup g.2).resolve_left h⟩
  map_one' := by
    have h1 : ((1 : Gamma 2) : SL(2, ℤ)) ∈ sanovSubgroup := by
      rw [OneMemClass.coe_one]; exact one_mem _
    rw [dif_pos h1]; apply Subtype.ext; simp
  map_mul' := by
    intro x y
    have hx := mem_or_neg_mem_sanovSubgroup x.2
    have hy := mem_or_neg_mem_sanovSubgroup y.2
    simp only [Subgroup.coe_mul]
    by_cases hx' : (x : SL(2, ℤ)) ∈ sanovSubgroup <;> by_cases hy' : (y : SL(2, ℤ)) ∈ sanovSubgroup
    · rw [dif_pos hx', dif_pos hy', dif_pos (mul_mem hx' hy')]; rfl
    · have hy'' := hy.resolve_left hy'
      have hxy : ¬ (x : SL(2, ℤ)) * y ∈ sanovSubgroup := fun h => hy' (by
        have := mul_mem (inv_mem hx') h; rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
      rw [dif_pos hx', dif_neg hy', dif_neg hxy]
      apply Subtype.ext; simp only [Subgroup.coe_mul]; rw [mul_neg]
    · have hx'' := hx.resolve_left hx'
      have hxy : ¬ (x : SL(2, ℤ)) * y ∈ sanovSubgroup := fun h => hx' (by
        have := mul_mem h (inv_mem hy'); rwa [mul_assoc, mul_inv_cancel, mul_one] at this)
      rw [dif_neg hx', dif_pos hy', dif_neg hxy]
      apply Subtype.ext; simp only [Subgroup.coe_mul]; rw [neg_mul]
    · have hx'' := hx.resolve_left hx'
      have hy'' := hy.resolve_left hy'
      have hxy : (x : SL(2, ℤ)) * y ∈ sanovSubgroup := by
        rw [← neg_mul_neg]; exact mul_mem hx'' hy''
      rw [dif_neg hx', dif_neg hy', dif_pos hxy]
      apply Subtype.ext; simp only [Subgroup.coe_mul]; rw [neg_mul_neg]

/-- The exponent sum of the first generator on the free group of rank two. -/
def sanovExponentSum : FreeGroup (Fin 2) →* Multiplicative ℤ :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then Multiplicative.ofAdd 1 else 1)

/-- **The winding homomorphism** `Γ(2) → ℤ`: the exponent sum of `A` after removing the sign. -/
def gammaTwoWinding : Gamma 2 →* Multiplicative ℤ :=
  sanovExponentSum.comp ((MonoidHom.ofInjective sanov_free).symm.toMonoidHom.comp gammaTwoToSanov)

theorem gammaTwoToSanov_of_mem {g : Gamma 2} (hg : (g : SL(2, ℤ)) ∈ sanovSubgroup) :
    gammaTwoToSanov g = ⟨g, hg⟩ := by
  classical
  show (if h : (g : SL(2, ℤ)) ∈ sanovSubgroup then _ else _) = _
  rw [dif_pos hg]

theorem ofInjective_symm_sanovA :
    (MonoidHom.ofInjective sanov_free).symm ⟨sanovA, sanovA_mem_sanovSubgroup⟩ = FreeGroup.of 0 := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [MonoidHom.ofInjective_apply, FreeGroup.lift_apply_of]
  rfl

theorem ofInjective_symm_sanovB :
    (MonoidHom.ofInjective sanov_free).symm ⟨sanovB, sanovB_mem_sanovSubgroup⟩ = FreeGroup.of 1 := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [MonoidHom.ofInjective_apply, FreeGroup.lift_apply_of]
  rfl

theorem gammaTwoWinding_sanovA : gammaTwoWinding ⟨sanovA, sanovA_mem⟩ = Multiplicative.ofAdd 1 := by
  simp only [gammaTwoWinding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [gammaTwoToSanov_of_mem (g := ⟨sanovA, sanovA_mem⟩) sanovA_mem_sanovSubgroup]
  rw [show (⟨((⟨sanovA, sanovA_mem⟩ : Gamma 2) : SL(2, ℤ)), sanovA_mem_sanovSubgroup⟩ :
    sanovSubgroup) = ⟨sanovA, sanovA_mem_sanovSubgroup⟩ from rfl, ofInjective_symm_sanovA,
    sanovExponentSum, FreeGroup.lift_apply_of, if_pos rfl]

theorem gammaTwoWinding_sanovB : gammaTwoWinding ⟨sanovB, sanovB_mem⟩ = 1 := by
  simp only [gammaTwoWinding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [gammaTwoToSanov_of_mem (g := ⟨sanovB, sanovB_mem⟩) sanovB_mem_sanovSubgroup]
  rw [show (⟨((⟨sanovB, sanovB_mem⟩ : Gamma 2) : SL(2, ℤ)), sanovB_mem_sanovSubgroup⟩ :
    sanovSubgroup) = ⟨sanovB, sanovB_mem_sanovSubgroup⟩ from rfl, ofInjective_symm_sanovB,
    sanovExponentSum, FreeGroup.lift_apply_of, if_neg (by decide)]

theorem gammaTwoWinding_neg_one :
    gammaTwoWinding ⟨-1, Bottcher.negOne_mem_Gamma2⟩ = 1 := by
  classical
  have hmap : gammaTwoToSanov ⟨-1, Bottcher.negOne_mem_Gamma2⟩ = 1 := by
    show (if h : ((-1 : SL(2, ℤ))) ∈ sanovSubgroup then _ else _) = _
    rw [dif_neg neg_one_not_mem_sanovSubgroup]
    apply Subtype.ext
    simp
  simp only [gammaTwoWinding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hmap, map_one, map_one]

end GaloisForLFunctions.HTGeometry
