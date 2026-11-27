import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicBlockReassociation
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicFourierExpansion
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularBlockCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperBlockWhittaker

/-! Twisted tails are normalized averages over the right unipotent block
and its rectangle. A column Fourier step absorbs one more coordinate
into the right block. -/

noncomputable section
open Matrix
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

local notation "Rect" => fun i j : ℕ => Matrix (Fin i) (Fin j) (ZMod g)
local notation "U" => upperUnitriangular g

/-- The simple root at the boundary of a rectangle and its right block. -/
def lastRowFirstColumn (X : Rect (a + 1) b) : ZMod g :=
  if hb : 0 < b then X (Fin.last a) ⟨0, hb⟩ else 0

/-- Average over the right unitriangular block and the rectangle, with
a prescribed phase in the rectangle. -/
def tailAverage (ψ : AddChar (ZMod g) ℂ) (φ : Rect a b → ZMod g)
    (F : Gn g (a + b) → ℂ) (A : Gn g a) : ℂ :=
  (Nat.card (Rect a b × U b) : ℂ)⁻¹ * ∑ z : Rect a b × U b,
    (ψ (φ z.1) * (whittakerCharacter ψ b z.2 : ℂ))⁻¹ * F (upperBlockUnit A z.1 z.2.val)

private def rightRowEquiv : Rect 1 b × U b ≃ U (1 + b) where
  toFun q := unitriangularBlock 1 q.1 q.2
  invFun u := (upperRightBlock u.val.val, (unitriangularLevi u).2)
  left_inv q := by
    apply Prod.ext
    · exact upperRightBlock_upperBlockMatrix 1 q.1 q.2.val.val
    · exact congrArg (fun z : U 1 × U b => z.2) (unitriangularLevi_block (1 : U 1) q.1 q.2)
  right_inv u := by
    letI := unitriangular_one_subsingleton (g := g)
    have he : (unitriangularLevi u).1 = (1 : U 1) := Subsingleton.elim _ _
    change unitriangularBlock 1 (upperRightBlock u.val.val) (unitriangularLevi u).2 = u
    rw [← he]
    exact unitriangularBlockEquiv.left_inv u

private theorem whittaker_rightRow (ψ : AddChar (ZMod g) ℂ) (X : Rect 1 b) (D : U b) :
    (whittakerCharacter ψ (1 + b) (rightRowEquiv (X, D)) : ℂ) =
      ψ (lastRowFirstColumn X) * (whittakerCharacter ψ b D : ℂ) := by
  cases b with
  | zero =>
    change ψ 0 = ψ (lastRowFirstColumn X) * ψ 0
    simp [lastRowFirstColumn]
  | succ b =>
    rw [lastRowFirstColumn, dif_pos (Nat.succ_pos b), show
      (⟨0, Nat.succ_pos b⟩ : Fin (b + 1)) = 0 from Fin.ext (by simp)]
    have he : rightRowEquiv (X, D) =
        ⟨upperBlockUnit (1 : Gn g 1) X D.val, isUniUp_upperBlockMatrix X D.property⟩ :=
      Subtype.ext rfl
    rw [he]
    exact whittakerCharacter_upperBlock (a := 0) ψ X D

private theorem reindexUnit_left_inverse {n m : ℕ} (e : Fin n ≃ Fin m) (x : Gn g n) :
    reindexUnit e.symm (reindexUnit e x) = x := by
  apply Units.ext
  ext i j
  simp only [reindexUnit_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

private theorem additiveCharacter_neg (ψ : AddChar (ZMod g) ℂ) (x : ZMod g) : ψ (-x) = (ψ x)⁻¹ := by
  have h : ψ (-x) * ψ x = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  exact (inv_eq_of_mul_eq_one_left h).symm

/-- The Fourier coefficient in the exposed column is the next tail average
with the corresponding phase on the first column of its rectangle. -/
theorem mirabolicFourier_tailAverage (ψ : AddChar (ZMod g) ℂ)
    (F : Gn g ((a + 1) + b) → ℂ) (A : Gn g a) (r : Fin a → ZMod g) :
    mirabolicFourier ψ (tailAverage (a := a + 1) (b := b) ψ lastRowFirstColumn F) A r =
      tailAverage (a := a) (b := 1 + b) ψ (fun Y => r ⬝ᵥ (fun i => Y i (Fin.castAdd b 0)))
        (fun x => F (reindexUnit (finCongr (Nat.add_assoc a 1 b).symm) x)) A := by
  let Col := Fin a → ZMod g
  let R := Rect (a + 1) b
  let R' := Rect a (1 + b)
  let R₁ := Rect 1 b
  let e : Col × (R × U b) ≃ R' × U (1 + b) :=
    (Equiv.prodAssoc Col R (U b)).symm.trans
      ((mirabolicRectangleEquiv.prodCongr (Equiv.refl _)).trans
        ((Equiv.prodAssoc R' R₁ (U b)).trans ((Equiv.refl _).prodCongr rightRowEquiv)))
  let φ (z : Col × (R × U b)) :=
    (ψ (lastRowFirstColumn z.2.1) * (whittakerCharacter ψ b z.2.2 : ℂ))⁻¹ *
      F (upperBlockUnit (mirabolicBlock A z.1) z.2.1 z.2.2.val) * ψ (-(r ⬝ᵥ z.1))
  have hc : (g : ℂ) ^ a * (Nat.card (R × U b) : ℂ) = (Nat.card (R' × U (1 + b)) : ℂ) := by
    have h := Nat.card_congr e
    rw [Nat.card_prod Col _, Nat.card_fun, Nat.card_fin, Nat.card_zmod] at h
    exact_mod_cast h
  have he (v : Col) (X : R) (D : U b) :
      φ (v, X, D) =
        (ψ (r ⬝ᵥ (fun i => (e (v, X, D)).1 i (Fin.castAdd b 0))) *
          (whittakerCharacter ψ (1 + b) (e (v, X, D)).2 : ℂ))⁻¹ *
            F (reindexUnit (finCongr (Nat.add_assoc a 1 b).symm)
              (upperBlockUnit A (e (v, X, D)).1 (e (v, X, D)).2.val)) := by
    let Y := (mirabolicRectangleEquiv (v, X)).1
    let Z := (mirabolicRectangleEquiv (v, X)).2
    change φ (v, X, D) =
      (ψ (r ⬝ᵥ (fun i => Y i (Fin.castAdd b 0))) *
        (whittakerCharacter ψ (1 + b) (rightRowEquiv (Z, D)) : ℂ))⁻¹ *
          F (reindexUnit (finCongr (Nat.add_assoc a 1 b).symm)
            (upperBlockUnit A Y (rightRowEquiv (Z, D)).val))
    have hv : (fun i => Y i (Fin.castAdd b 0)) = v := by
      funext i
      simp [Y, mirabolicRectangleEquiv]
    have hZ : lastRowFirstColumn Z = lastRowFirstColumn X := by
      by_cases hb : 0 < b
      · simp only [lastRowFirstColumn, dif_pos hb, Z, mirabolicRectangleEquiv, Equiv.coe_fn_mk]
        rfl
      · simp only [lastRowFirstColumn, dif_neg hb]
    have hmat : reindexUnit (finCongr (Nat.add_assoc a 1 b).symm)
        (upperBlockUnit A Y (rightRowEquiv (Z, D)).val) =
          upperBlockUnit (mirabolicBlock A v) X D.val := by
      change reindexUnit (finCongr (Nat.add_assoc a 1 b).symm)
        (upperBlockUnit A (mirabolicRectangleEquiv (v, X)).1
          (upperBlockUnit (1 : Gn g 1) (mirabolicRectangleEquiv (v, X)).2 D.val)) = _
      rw [← upperBlockUnit_mirabolic_assoc A v X D.val]
      exact reindexUnit_left_inverse (finCongr (Nat.add_assoc a 1 b)) _
    rw [hv, whittaker_rightRow, hZ, hmat]
    simp only [φ, additiveCharacter_neg, mul_inv]
    ring
  calc
    _ = ((g : ℂ) ^ a)⁻¹ * (Nat.card (R × U b) : ℂ)⁻¹ * ∑ z, φ z := by
      unfold mirabolicFourier columnFourier tailAverage
      conv_rhs => rw [Fintype.sum_prod_type]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun z _ => ?_
      dsimp only [φ]
      ring
    _ = _ := by
      rw [← mul_inv, hc]
      unfold tailAverage
      congr 1
      exact Fintype.sum_equiv e _ _ fun z => he z.1 z.2.1 z.2.2

/-- The twisted tail average of a class function is invariant under
conjugation in the leading mirabolic subgroup. -/
theorem tailAverage_isMirabolicClass (ψ : AddChar (ZMod g) ℂ)
    (F : Gn g (a + 1 + b) → ℂ) (hF : IsClass F) :
    IsMirabolicClass (tailAverage (a := a + 1) (b := b) ψ lastRowFirstColumn F) := by
  intro x _ y hy
  let R := Rect (a + 1) b
  let e : R ≃ R :=
    ⟨fun X => y.val * X, fun X => y.inv * X,
      fun X => by
        change y.inv * (y.val * X) = X
        rw [← Matrix.mul_assoc, y.inv_val, Matrix.one_mul],
      fun X => by
        change y.val * (y.inv * X) = X
        rw [← Matrix.mul_assoc, y.val_inv, Matrix.one_mul]⟩
  let A := upperBlockUnit y (0 : R) (1 : Gn g b)
  have hA : A⁻¹ = upperBlockUnit y⁻¹ (0 : R) (1 : Gn g b) := by
    apply inv_eq_of_mul_eq_one_left
    rw [upperBlockUnit_mul]
    simp
  have hc (X : R) (D : Gn g b) :
      upperBlockUnit (y * x * y⁻¹) (y.val * X) D = A * upperBlockUnit x X D * A⁻¹ := by
    rw [hA]
    simp only [A, upperBlockUnit_mul, Units.val_one, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.mul_one, add_zero, zero_add, one_mul, mul_one]
  have hyrow := (mem_mirabolicSubgroup_iff y).mp hy
  have hp (X : R) : lastRowFirstColumn (y.val * X) = lastRowFirstColumn X := by
    unfold lastRowFirstColumn
    split_ifs with hb
    · rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (Fin.last a) (Finset.mem_univ _)]
      · rw [hyrow, Pi.single_eq_same, one_mul]
      · intro j _ hj
        rw [hyrow, Pi.single_eq_of_ne hj, zero_mul]
    · rfl
  unfold tailAverage
  congr 1
  symm
  refine Fintype.sum_equiv (e.prodCongr (Equiv.refl _)) _ _ fun z => ?_
  change (ψ (lastRowFirstColumn z.1) * (whittakerCharacter ψ b z.2 : ℂ))⁻¹ *
      F (upperBlockUnit x z.1 z.2.val) =
    (ψ (lastRowFirstColumn (y.val * z.1)) * (whittakerCharacter ψ b z.2 : ℂ))⁻¹ *
      F (upperBlockUnit (y * x * y⁻¹) (y.val * z.1) z.2.val)
  rw [hp, hc, hF]

end GlobalTheory.GLq
