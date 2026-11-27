import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicInduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter

/-! The list parabolic consists of block upper triangular matrices, and
its Levi projection reads off each diagonal block. -/

noncomputable section
open scoped Classical

open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

/-- Membership in the flag parabolic is vanishing strictly below its diagonal blocks. -/
theorem mem_listParabolic_iff (L : List (Pc g)) (x : Gn g (degL L)) :
    x ∈ listParabolic L ↔
      ∀ i j : Fin (degL L), listBlockOf L j < listBlockOf L i → x.val i j = 0 := by
  induction L with
  | nil =>
    exact ⟨fun _ i => Fin.elim0 i, fun _ => Subgroup.mem_top x⟩
  | cons p L ih =>
    let P := twoBlockParabolic g p.1 (degL L)
    let Q := tailParabolic p L
    constructor
    · intro hx
      change x ∈ Q.map P.subtype at hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      have hr := (ih (rightLevi q)).mp (show rightLevi q ∈ listParabolic L from hq)
      intro i j
      refine Fin.addCases (m := p.1) (n := degL L) (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (m := p.1) (n := degL L) (fun j => ?_) (fun j => ?_) j
      · intro h
        exact (not_lt_of_ge ((listBlockOf_left p L i).trans (listBlockOf_left p L j).symm).le h).elim
      · intro h
        exact (not_lt_of_ge ((listBlockOf_left p L i).le.trans (Fin.zero_le _)) h).elim
      · intro _
        exact q.property (Fin.natAdd p.1 i) (Fin.castAdd (degL L) j) j.isLt (Nat.le_add_right _ _)
      · intro h
        have h' : (listBlockOf L j).succ < (listBlockOf L i).succ :=
          lt_of_le_of_lt (listBlockOf_right p L j).symm.le
            (lt_of_lt_of_le h (listBlockOf_right p L i).le)
        have he := hr i j (Fin.succ_lt_succ_iff.mp h')
        change br p.1 (degL L) q.val.val i j = 0 at he
        exact (br_apply_add q.val.val i j).symm.trans he
    · intro hx
      have hp : InPar p.1 x.val := (inPar_iff_lowerLeft_zero x.val).mpr fun i j =>
        hx (Fin.natAdd p.1 i) (Fin.castAdd (degL L) j) (by simp)
      let q : P := ⟨x, hp⟩
      have hq : rightLevi q ∈ listParabolic L := (ih (rightLevi q)).mpr fun i j h => by
        change br p.1 (degL L) x.val i j = 0
        exact (br_apply_add (x.val : Mt g (p.1 + degL L)) i j).trans
          (hx (Fin.natAdd p.1 i) (Fin.natAdd p.1 j)
            (by simpa only [listBlockOf_right, Fin.succ_lt_succ_iff] using h))
      change x ∈ Q.map P.subtype
      exact Subgroup.mem_map.mpr ⟨q, hq, rfl⟩

theorem upperUnitriangular_le_listParabolic (L : List (Pc g)) :
    upperUnitriangular g (degL L) ≤ listParabolic L := by
  intro x hx
  apply (mem_listParabolic_iff L x).mpr
  intro i j h
  have hij : j < i := lt_of_not_ge fun e => (not_lt_of_ge (listBlockOf_mono L e)) h
  exact (mem_upperUnitriangular.mp hx i j).1 hij

/-- Projection to the general linear group of one diagonal block. -/
def listBlockLevi : (L : List (Pc g)) → (k : Fin L.length) → listParabolic L →* Gn g (L.get k).1
  | [], k => Fin.elim0 k
  | p :: L, k =>
    let P := twoBlockParabolic g p.1 (degL L)
    let Q := tailParabolic p L
    let e := (listParabolicConsEquiv p L).symm.toMonoidHom
    let π : P →* Gn g p.1 × Gn g (degL L) := twoBlockLevi
    Fin.cases ((((MonoidHom.fst _ _).comp π).comp Q.subtype).comp e)
      (fun k => ((listBlockLevi L k).comp (tailLevi p L)).comp e) k

/-- The entries of a Levi projection are the corresponding submatrix entries. -/
theorem listBlockLevi_apply (L : List (Pc g)) (k : Fin L.length) (x : listParabolic L)
    (i j : Fin (L.get k).1) :
    (listBlockLevi L k x).val i j = x.val.val (listBlockEmbedding L k i) (listBlockEmbedding L k j) := by
  induction L with
  | nil => exact Fin.elim0 k
  | cons p L ih =>
    let e := listParabolicConsEquiv p L
    let q := e.symm x
    have hq : q.val.val = x.val := congrArg Subtype.val (e.apply_symm_apply x)
    revert i j
    refine Fin.cases ?_ (fun k => ?_) k
    · intro i j
      change tl p.1 q.val.val.val i j = x.val.val (listBlockEmbedding (p :: L) 0 i)
        (listBlockEmbedding (p :: L) 0 j)
      rw [tl_apply_add, hq, listBlockEmbedding_zero, listBlockEmbedding_zero]
    · intro i j
      change (listBlockLevi L k (tailLevi p L q)).val i j =
        x.val.val (listBlockEmbedding (p :: L) k.succ i) (listBlockEmbedding (p :: L) k.succ j)
      rw [ih]
      change br p.1 (degL L) q.val.val.val (listBlockEmbedding L k i) (listBlockEmbedding L k j) = _
      rw [br_apply_add, hq, listBlockEmbedding_succ, listBlockEmbedding_succ]

/-- The parabolic inducing character is the product over its diagonal blocks. -/
theorem listParabolicCharacter_eq_prod (L : List (Pc g)) (x : listParabolic L) :
    listParabolicCharacter L x = ∏ i : Fin L.length, (L.get i).2 (listBlockLevi L i x) := by
  induction L with
  | nil => simp [listParabolicCharacter]
  | cons p L ih =>
    let q := (listParabolicConsEquiv p L).symm x
    let f (i : Fin (L.length + 1)) := ((p :: L).get i).2 (listBlockLevi (p :: L) i x)
    change listParabolicCharacter (p :: L) x = ∏ i : Fin (L.length + 1), f i
    rw [Fin.prod_univ_succ f]
    change listParabolicCharacter L (tailLevi p L q) * p.2 (twoBlockLevi q.val).1 =
      p.2 (twoBlockLevi q.val).1 * ∏ i : Fin L.length, (L.get i).2 (listBlockLevi L i (tailLevi p L q))
    rw [ih]
    exact mul_comm _ _

section CommonDimension

variable (L : List (Pc g)) {n : ℕ} (h : degL L = n)

/-- The parabolic of a block list in the common ambient matrix dimension. -/
def listParabolicAt : Subgroup (Gn g n) := by
  subst n
  exact listParabolic L

def listBlockOfAt : Fin n → Fin L.length := by
  subst n
  exact listBlockOf L

def listBlockEmbeddingAt (k : Fin L.length) : Fin (L.get k).1 ↪ Fin n := by
  subst n
  exact listBlockEmbedding L k

def listBlockLeviAt (k : Fin L.length) : listParabolicAt L h →* Gn g (L.get k).1 := by
  subst n
  exact listBlockLevi L k

def listParabolicCharacterAt : listParabolicAt L h → ℂ := by
  subst n
  exact listParabolicCharacter L

omit [Fact g.Prime] in
theorem listBlockOfAt_embedding (k : Fin L.length) (j : Fin (L.get k).1) :
    listBlockOfAt L h (listBlockEmbeddingAt L h k j) = k := by
  subst n
  exact listBlockOf_listBlockEmbedding L k j

omit [Fact g.Prime] in
theorem exists_listBlockCoordinateAt (i : Fin n) :
    ∃ j : Fin (L.get (listBlockOfAt L h i)).1,
      listBlockEmbeddingAt L h (listBlockOfAt L h i) j = i := by
  subst n
  exact exists_listBlockCoordinate L i

theorem mem_listParabolicAt_iff (x : Gn g n) :
    x ∈ listParabolicAt L h ↔
      ∀ i j : Fin n, listBlockOfAt L h j < listBlockOfAt L h i → x.val i j = 0 := by
  subst n
  exact mem_listParabolic_iff L x

theorem upperUnitriangular_le_listParabolicAt :
    upperUnitriangular g n ≤ listParabolicAt L h := by
  subst n
  exact upperUnitriangular_le_listParabolic L

theorem listBlockLeviAt_apply (k : Fin L.length) (x : listParabolicAt L h) (i j : Fin (L.get k).1) :
    (listBlockLeviAt L h k x).val i j = x.val.val (listBlockEmbeddingAt L h k i) (listBlockEmbeddingAt L h k j) := by
  subst n
  exact listBlockLevi_apply L k x i j

theorem listParabolicCharacterAt_eq_prod (x : listParabolicAt L h) :
    listParabolicCharacterAt L h x = ∏ i : Fin L.length, (L.get i).2 (listBlockLeviAt L h i x) := by
  subst n
  exact listParabolicCharacter_eq_prod L x

theorem hcL_eq_inducedFunction_listParabolicAt (hL : ∀ p ∈ L, IsClass p.2) :
    hcL L n = GaloisForLFunctions.inducedFunction (listParabolicAt L h) (listParabolicCharacterAt L h) := by
  subst n
  exact hcL_eq_inducedFunction_listParabolic L hL

theorem isChar_listParabolicCharacterAt (hL : ∀ p ∈ L, IsChar p.2) :
    IsChar (listParabolicCharacterAt L h) := by
  subst n
  exact isChar_listParabolicCharacter L hL

end CommonDimension

end GlobalTheory.GLq
