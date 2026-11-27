import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicExpansion
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicRightUnitriangular

/-! On the leading diagonal block, each term of the mirabolic expansion
is Harish–Chandra induction with a Gelfand–Graev character. -/

noncomputable section
open Matrix GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

private theorem tl_self (A : Mt g a) : tl a A = A := by
  ext i j
  exact dif_pos ⟨i.isLt, j.isLt⟩

private theorem toG_val (A : Gn g a) : toG A.val = A := by
  apply Units.ext
  rw [toG, dif_pos A.isUnit, IsUnit.unit_spec]

private theorem entN_mirabolicBlock (A : Gn g (a + b)) (v : Fin (a + b) → ZMod g)
    {i j : ℕ} (hi : i < a + b) (hj : j < a + b) :
    entN (mirabolicBlock A v).val i j = entN A.val i j := by
  have hi' : i < a + b + 1 := by omega
  have hj' : j < a + b + 1 := by omega
  simp only [entN, hi, hj, hi', hj', and_self, dif_pos]
  change upperBlockMatrix A.val (fun t (_ : Fin 1) => v t) (1 : Mt g 1)
      (Fin.castAdd 1 ⟨i, hi⟩) (Fin.castAdd 1 ⟨j, hj⟩) = _
  simp only [upperBlockMatrix, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₁₁]

private theorem entN_mirabolicBlock_last (A : Gn g (a + b + 1))
    (v : Fin (a + b + 1) → ZMod g) :
    entN (mirabolicBlock A v).val (a + b) (a + b + 1) = v (Fin.last (a + b)) := by
  simp only [entN, show a + b < a + b + 1 + 1 by omega,
    Nat.lt_succ_self (a + b + 1), and_self, dif_pos]
  change upperBlockMatrix A.val (fun t (_ : Fin 1) => v t) (1 : Mt g 1)
    ((Fin.last (a + b)).castAdd 1) (Fin.natAdd (a + b + 1) 0) = _
  simp [upperBlockMatrix]

/-- The left block and the superdiagonal sum on the right can be read
directly from the ambient matrix. -/
private def rightInducingValue (ψ : AddChar (ZMod g) ℂ) (α : Gn g a → ℂ)
    {n : ℕ} (x : Gn g n) : ℂ :=
  α (toG (tl a x.val)) *
    ψ (∑ j ∈ Finset.range (n - a - 1), entN x.val (a + j) (a + j + 1))

private theorem sum_entN_br (X : Mt g (a + b)) :
    (∑ j ∈ Finset.range (b - 1), entN (br a b X) j (j + 1)) =
      ∑ j ∈ Finset.range (a + b - a - 1), entN X (a + j) (a + j + 1) := by
  rw [show a + b - a - 1 = b - 1 by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  have h := Finset.mem_range.mp hj
  have h₁ : j < b := by omega
  have h₂ : j + 1 < b := by omega
  have h₃ : a + j < a + b := by omega
  have h₄ : a + j + 1 < a + b := by omega
  rw [show entN (br a b X) j (j + 1) = br a b X ⟨j, h₁⟩ ⟨j + 1, h₂⟩ from
    dif_pos ⟨h₁, h₂⟩, br_apply_add X ⟨j, h₁⟩ ⟨j + 1, h₂⟩]
  exact (show entN X (a + j) (a + j + 1) = X ⟨a + j, h₃⟩ ⟨a + j + 1, h₄⟩ from
    dif_pos ⟨h₃, h₄⟩).symm

private theorem rightUnitriangularFunction_eq_value (ψ : AddChar (ZMod g) ℂ)
    (α : Gn g a → ℂ) (u : rightUnitriangularParabolic g a b) :
    rightUnitriangularFunction ψ α u = rightInducingValue ψ α u.val.val := by
  let p : twoBlockParabolic g a b := u.val
  let X : Mt g (a + b) := p.val.val
  let A := (twoBlockLevi p).1
  have hL : A = toG (tl a X) := by
    apply Units.ext
    have h : IsUnit (tl a X) := A.isUnit
    change tl a X = (toG (tl a X)).val
    rw [toG, dif_pos h, IsUnit.unit_spec]
  change α A *
    ψ (∑ j ∈ Finset.range (b - 1), entN (br a b X) j (j + 1)) =
    α (toG (tl a X)) *
      ψ (∑ j ∈ Finset.range (a + b - a - 1), entN X (a + j) (a + j + 1))
  exact congrArg₂ (· * ·) (congrArg α hL) (congrArg ψ (sum_entN_br X))

private theorem rightInducingValue_unit (ψ : AddChar (ZMod g) ℂ) (α : Gn g a → ℂ)
    (A : Gn g a) (v : Fin a → ZMod g) :
    rightInducingValue ψ α (mirabolicBlock A v) = α A := by
  have h : tl a (mirabolicBlock A v).val = A.val := by
    ext i j
    exact (entN_mirabolicBlock (b := 0) A v i.isLt j.isLt).trans
      (dif_pos ⟨i.isLt, j.isLt⟩)
  simp [rightInducingValue, h, toG_val]

private theorem rightInducingValue_succ (ψ : AddChar (ZMod g) ℂ) (α : Gn g a → ℂ)
    (A : Gn g (a + b + 1)) (v : Fin (a + b + 1) → ZMod g) :
    rightInducingValue ψ α (mirabolicBlock A v) =
      ψ (v (Fin.last (a + b))) * rightInducingValue ψ α A := by
  have hL : tl a (mirabolicBlock A v).val = tl a A.val := by
    ext i j
    have hi := i.isLt
    have hj := j.isLt
    exact entN_mirabolicBlock (b := b + 1) A v (by omega) (by omega)
  unfold rightInducingValue
  rw [hL, show a + b + 1 + 1 - a - 1 = b + 1 by omega,
    show a + b + 1 - a - 1 = b by omega, Finset.sum_range_succ,
    entN_mirabolicBlock_last]
  have hs : (∑ j ∈ Finset.range b, entN (mirabolicBlock A v).val (a + j) (a + j + 1)) =
      ∑ j ∈ Finset.range b, entN A.val (a + j) (a + j + 1) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have h := Finset.mem_range.mp hj
    exact entN_mirabolicBlock (b := b + 1) A v (by omega) (by omega)
  rw [hs, ψ.map_add_eq_mul]
  ring

private theorem mirabolicInductionAt_last (ψ : AddChar (ZMod g) ℂ) (α : Gn g a → ℂ) :
    mirabolicInductionAt ψ a (Fin.last a) α = fun u => α (mirabolicLevi u) := by
  cases a with
  | zero =>
    rw [mirabolicInductionAt, Fin.lastCases_last]
    rfl
  | succ a =>
    rw [mirabolicInductionAt, Fin.lastCases_last]
    rfl

/-- Iterated last-column induction equals a single induction from the
mirabolic subgroup with unitriangular right block. -/
private theorem mirabolicInductionAt_eq_induced_right (ψ : AddChar (ZMod g) ℂ)
    (α : Gn g a → ℂ) (hα : IsClass α) (b : ℕ) :
    mirabolicInductionAt ψ (a + b) ⟨a, Nat.lt_succ_of_le (Nat.le_add_right a b)⟩ α =
      inducedFunction (mirabolicRightUnitriangular g a b)
        (fun u => rightInducingValue ψ α u.val.val) := by
  induction b with
  | zero =>
    have hbase (u : mirabolicSubgroup g a) :
        rightInducingValue ψ α u.val = α (mirabolicLevi u) := by
      obtain ⟨A, v, hu⟩ := exists_mirabolicBlock u.property
      rw [show u = mirabolicUnit A v from Subtype.ext hu, mirabolicLevi_unit]
      exact rightInducingValue_unit ψ α A v
    rw [mirabolicRightUnitriangular_zero]
    simp only [hbase]
    change mirabolicInductionAt ψ a (Fin.last a) α = _
    calc
      _ = fun u : mirabolicSubgroup g a => α (mirabolicLevi u) := mirabolicInductionAt_last ψ α
      _ = _ := (inducedFunction_top (fun u : mirabolicSubgroup g a => α (mirabolicLevi u)) (by
        intro x u
        simpa only [map_mul, map_inv] using hα (mirabolicLevi u) (mirabolicLevi x))).symm
  | succ b ih =>
    let i : Fin (a + b + 1) := ⟨a, Nat.lt_succ_of_le (Nat.le_add_right a b)⟩
    change mirabolicInductionAt ψ (a + b + 1) i.castSucc α = _
    rw [mirabolicInductionAt, Fin.lastCases_castSucc, show
      mirabolicInductionAt ψ (a + b) i α = _ from ih, mirabolicInduce_inducedFunction]
    let K := mirabolicInducingSubgroup g (a + b)
    let H := mirabolicRightUnitriangular g a b
    let π := mirabolicInducingLevi (g := g) (m := a + b)
    let P := H.comap π
    have hstep (u : K) :
        (mirabolicLastCharacter ψ u : ℂ) * rightInducingValue ψ α (π u).val =
          rightInducingValue ψ α u.val.val := by
      let A := mirabolicLevi u.val
      let v := mirabolicColumn u.val
      have hu : mirabolicUnit A v = u.val := mirabolicCoordinates.left_inv u.val
      rw [mirabolicLastCharacter_apply, ← hu, mirabolicColumn_unit, single_dotProduct, one_mul]
      exact (rightInducingValue_succ ψ α A v).symm
    let e := P.equivMapOfInjective K.subtype K.subtype_injective
    let f (u : P.map K.subtype) := (mirabolicLastCharacter ψ (e.symm u).val : ℂ) *
      rightInducingValue ψ α (π (e.symm u).val).val
    have hf : f = fun u => rightInducingValue ψ α u.val.val := by
      funext u
      have hu : (e.symm u).val.val = u.val :=
        congrArg (fun x : P.map K.subtype => x.val) (e.apply_symm_apply u)
      exact (hstep (e.symm u).val).trans (congrArg
        (fun x : mirabolicSubgroup g (a + b + 1) => rightInducingValue ψ α x.val) hu)
    change inducedFunction (P.map K.subtype) f = _
    rw [hf, mirabolicRightUnitriangular_succ]
    rfl

/-- The rank-zero Gelfand–Graev character is the trivial character. -/
theorem gg_zero (ψ : AddChar (ZMod g) ℂ) : gg ψ 0 = fun _ => 1 := by
  funext x
  have h : x = 1 := Subsingleton.elim _ _
  subst x
  letI : Unique (upperUnitriangular g 0) := ⟨⟨1⟩, fun z => Subsingleton.elim z 1⟩
  have hcard : Nat.card (upperUnitriangular g 0) = 1 := Nat.card_unique
  rw [gg_eq_inducedFunction, inducedFunction, Fintype.sum_subsingleton _ 1, hcard]
  simp only [mul_one, inv_one, extendByZero_of_mem _ _ (Subgroup.one_mem _), Nat.cast_one, one_mul]
  change (whittakerCharacter ψ 0 1 : ℂ) = 1
  simp

/-- A Gelfand–Graev factor of rank zero leaves Harish–Chandra induction unchanged. -/
theorem hc_gg_zero (ψ : AddChar (ZMod g) ℂ) (α : Gn g a → ℂ) (hα : IsClass α) :
    hc a 0 α (gg ψ 0) a = α := by
  change hc a 0 α (gg ψ 0) (a + 0) = α
  rw [hc_eq_inducedFunction (a := a) (b := 0) α (gg ψ 0), gg_zero]
  have hP : twoBlockParabolic g a 0 = ⊤ := by
    ext x
    simp only [Subgroup.mem_top, iff_true]
    show InPar a x.val
    intro i _ _ hi
    exact (Nat.not_le_of_lt i.isLt hi).elim
  have hL (u : twoBlockParabolic g a 0) : (twoBlockLevi u).1 = u.val := by
    apply Units.ext
    change tl a u.val.val = u.val.val
    exact tl_self u.val.val
  have hf : (fun u : twoBlockParabolic g a 0 => α (twoBlockLevi u).1 * 1) =
      fun u => α u.val := by
    funext u
    exact (mul_one _).trans (congrArg α (hL u))
  rw [hf, hP]
  exact inducedFunction_top α fun x y => hα y x

private theorem inducedFunction_map_eq_of_ambient {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (R : Subgroup H) (f : R → ℂ) (F : G → ℂ) (hf : ∀ r, f r = F r.val.val) :
    let e := R.equivMapOfInjective H.subtype H.subtype_injective
    inducedFunction (R.map H.subtype) (fun u => f (e.symm u)) =
      inducedFunction (R.map H.subtype) (fun u => F u.val) := by
  let e := R.equivMapOfInjective H.subtype H.subtype_injective
  apply congrArg (inducedFunction (R.map H.subtype))
  funext u
  have hu : (e.symm u).val.val = u.val :=
    congrArg (fun v : R.map H.subtype => v.val) (e.apply_symm_apply u)
  exact (hf (e.symm u)).trans (congrArg F hu)

/-- Evaluation at the embedded diagonal matrix replaces the recursive
induction by a Harish–Chandra product. -/
theorem mirabolicInductionAt_diag (ψ : AddChar (ZMod g) ℂ) {m : ℕ}
    (i : Fin (m + 1)) (α : Gn g i.val → ℂ) (hα : IsClass α) (A : Gn g m) :
    mirabolicInductionAt ψ m i α (mirabolicUnit A 0) =
      hc i.val (m - i.val) α (gg ψ (m - i.val)) m A := by
  obtain ⟨a, ha⟩ := i
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ ha)
  rw [show a + b - a = b by omega]
  cases b with
  | zero =>
    change mirabolicInductionAt ψ a (Fin.last a) α (mirabolicUnit A 0) = hc a 0 α (gg ψ 0) a A
    rw [hc_gg_zero ψ α hα]
    exact (congrFun (mirabolicInductionAt_last ψ α) (mirabolicUnit A 0)).trans
      (congrArg α (mirabolicLevi_unit A 0))
  | succ b =>
    let i : Fin (a + b + 1) := ⟨a, Nat.lt_succ_of_le (Nat.le_add_right a b)⟩
    change mirabolicInductionAt ψ (a + b + 1) i.castSucc α (mirabolicUnit A 0) = _
    rw [mirabolicInductionAt, Fin.lastCases_castSucc, mirabolicInduce_diag, show
      mirabolicInductionAt ψ (a + b) i α = _ from mirabolicInductionAt_eq_induced_right ψ α hα b]
    rw [inducedFunction_inducedFunction, hc_eq_induced_rightUnitriangular ψ α hα]
    let M := mirabolicSubgroup g (a + b)
    let R := mirabolicRightUnitriangular g a b
    let P := twoBlockParabolic g a (b + 1)
    let U := rightUnitriangularParabolic g a (b + 1)
    have hR : R.map M.subtype = U.map P.subtype := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, rightUnitriangularParabolic_le_mirabolic hx⟩, hx, rfl⟩
    let f := rightInducingValue ψ α (n := a + b + 1)
    have hleft := inducedFunction_map_eq_of_ambient M R (fun u => f u.val.val) f (fun _ => rfl)
    have hright := inducedFunction_map_eq_of_ambient P U (rightUnitriangularFunction ψ α) f
      (rightUnitriangularFunction_eq_value ψ α)
    exact (congrFun hleft A).trans
      ((congrArg (fun H : Subgroup (Gn g (a + b + 1)) =>
        inducedFunction H (fun u => f u.val) A) hR).trans (congrFun hright A).symm)

end GlobalTheory.GLq
