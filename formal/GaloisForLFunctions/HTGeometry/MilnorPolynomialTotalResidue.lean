import GaloisForLFunctions.HTGeometry.MilnorTotalResidueSurjective
import GaloisForLFunctions.HTGeometry.MilnorResidueInfinity

/-!
# The surjective total residue of a rational function field

For `F(t)`, finite places are indexed by monic irreducible polynomials.  This
file assembles their Milnor residues into one finite-support homomorphism and
proves that it is surjective.  The proof uses the already formalized
single-place lift: it realizes one prescribed residue while killing all other
finite residues, then performs finite-support induction.

Thus the exact local-to-global residue sequence is available as an actual
direct-sum map.  This is the function-field analogue of the ABHN
surjectivity-and-kernel target.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- The direct sum of degree-`n` Milnor `K`-groups of all finite residue fields
of `F(t)`. -/
abbrev MilnorPolynomialTotalResidueTarget (n : ℕ) :=
  Π₀ q : MonicIrred F, MilnorKDeg (polyResidueField q.2.1) n

/-- The residue at `q`, with the canonical transport from degree
`n.succ - 1` to degree `n`. -/
noncomputable def milnorPolynomialResidueSucc (q : MonicIrred F) (n : ℕ) :
    MilnorKDeg (RatFunc F) n.succ →+ MilnorKDeg (polyResidueField q.2.1) n :=
  (milnorDegCongr (Nat.succ_sub_one n)).comp
    (milnorResidue (polyResidueData q.2.1) n.succ)

/-- The finite-support sum of all finite-place residues of `K^M_{n+1}(F(t))`.
-/
noncomputable def milnorPolynomialTotalResidue (n : ℕ) :
    MilnorKDeg (RatFunc F) n.succ →+
      MilnorPolynomialTotalResidueTarget (F := F) n := by
  classical
  let f : MilnorKDeg (RatFunc F) n.succ →
      MilnorPolynomialTotalResidueTarget (F := F) n := fun x => by
    exact DFinsupp.mk (finite_polyResidue_ne_zero (F := F) n.succ x).toFinset
      fun q => milnorPolynomialResidueSucc q.1 n x
  have hf : ∀ (x : MilnorKDeg (RatFunc F) n.succ) (q : MonicIrred F),
      f x q = milnorPolynomialResidueSucc q n x := by
    intro x q
    dsimp [f]
    split_ifs with hq
    · rfl
    · symm
      have hzero : milnorResidue (polyResidueData q.2.1) n.succ x = 0 := by
        apply Classical.byContradiction
        intro h
        exact hq ((finite_polyResidue_ne_zero (F := F) n.succ x).mem_toFinset.mpr h)
      rw [show milnorPolynomialResidueSucc q n x =
        milnorDegCongr (Nat.succ_sub_one n)
          (milnorResidue (polyResidueData q.2.1) n.succ x) by rfl, hzero]
      exact map_zero _
  exact
    { toFun := f
      map_zero' := by
        ext q
        change f 0 q = 0
        rw [hf]
        exact map_zero _
      map_add' := by
        intro x y
        ext q
        change f (x + y) q = f x q + f y q
        rw [hf, hf, hf]
        exact (milnorPolynomialResidueSucc q n).map_add x y }

/-- Evaluation of the total residue at one monic irreducible is the defining
local residue. -/
theorem milnorPolynomialTotalResidue_apply (n : ℕ)
    (x : MilnorKDeg (RatFunc F) n.succ) (q : MonicIrred F) :
    milnorPolynomialTotalResidue (F := F) n x q =
      milnorPolynomialResidueSucc q n x := by
  classical
  unfold milnorPolynomialTotalResidue
  dsimp
  split_ifs with hq
  · rfl
  · symm
    have hzero : milnorResidue (polyResidueData q.2.1) n.succ x = 0 := by
      apply Classical.byContradiction
      intro h
      exact hq ((finite_polyResidue_ne_zero (F := F) n.succ x).mem_toFinset.mpr h)
    rw [show milnorPolynomialResidueSucc q n x =
      milnorDegCongr (Nat.succ_sub_one n)
        (milnorResidue (polyResidueData q.2.1) n.succ x) by rfl, hzero]
    exact map_zero _

/-- The canonical degree transport in one coordinate preserves vanishing. -/
theorem milnorPolynomialResidueSucc_eq_zero_iff (q : MonicIrred F) (n : ℕ)
    (x : MilnorKDeg (RatFunc F) n.succ) :
    milnorPolynomialResidueSucc q n x = 0 ↔
      milnorResidue (polyResidueData q.2.1) n.succ x = 0 := by
  cases n <;> rfl

/-- Membership in the total-residue kernel is pointwise vanishing of every
finite-place Milnor residue. -/
theorem milnorPolynomialTotalResidue_mem_ker_iff (n : ℕ)
    (x : MilnorKDeg (RatFunc F) n.succ) :
    x ∈ (milnorPolynomialTotalResidue (F := F) n).ker ↔
      ∀ q : MonicIrred F, milnorResidue (polyResidueData q.2.1) n.succ x = 0 := by
  constructor
  · intro hx q
    have hq := congrArg (fun f => f q) hx
    rw [milnorPolynomialTotalResidue_apply, DFinsupp.zero_apply] at hq
    exact (milnorPolynomialResidueSucc_eq_zero_iff q n x).mp hq
  · intro hx
    apply DFinsupp.ext
    intro q
    rw [milnorPolynomialTotalResidue_apply]
    simp only [DFinsupp.zero_apply]
    exact (milnorPolynomialResidueSucc_eq_zero_iff q n x).mpr (hx q)

/-- Local vanishing of the bundled total residue forces a class to come from
the constant field.  This transports the existing kernel theorem to the
actual finite-support localization map. -/
theorem milnorPolynomialTotalResidue_mem_ker_implies_mem_constRange (n : ℕ)
    (x : MilnorKDeg (RatFunc F) n.succ)
    (hx : x ∈ (milnorPolynomialTotalResidue (F := F) n).ker) :
    x ∈ AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n.succ) := by
  apply mem_range_of_residues_zero (F := F) n x
  intro π hπ hmonic
  let q : MonicIrred F := ⟨π, hπ, hmonic⟩
  exact (milnorPolynomialTotalResidue_mem_ker_iff (F := F) n x).mp hx q

/-- Constants have zero residue at every finite place. -/
theorem milnorPolynomialTotalResidue_const_eq_zero (n : ℕ)
    (x : MilnorKDeg F n.succ) :
    milnorPolynomialTotalResidue (F := F) n
      (milnorKDegMap (ratFuncConstHom (F := F)) n.succ x) = 0 := by
  apply DFinsupp.ext
  intro q
  rw [milnorPolynomialTotalResidue_apply]
  change milnorDegCongr (Nat.succ_sub_one n)
      (milnorResidue (polyResidueData q.2.1) n.succ
        (milnorKDegMap (ratFuncConstHom (F := F)) n.succ x)) = 0
  rw [polyResidue_degreeFiltration_eq_zero q.2.1 (d := 0) q.2.1.natDegree_pos _]
  exact map_zero _
  exact range_milnorKDegMap_const_le n.succ ⟨x, rfl⟩

/-- The constant-field image is contained in the total-residue kernel. -/
theorem milnorPolynomialTotalResidue_constRange_le_ker (n : ℕ) :
    AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n.succ)
      ≤ (milnorPolynomialTotalResidue (F := F) n).ker := by
  rintro y ⟨x, rfl⟩
  exact milnorPolynomialTotalResidue_const_eq_zero n x

/-- **Exactness at `K^M_{n+1}(F(t))`.** The kernel of all finite residues is
exactly the image of the constant field. -/
theorem milnorPolynomialTotalResidue_ker_eq_constRange (n : ℕ) :
    (milnorPolynomialTotalResidue (F := F) n).ker =
      AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n.succ) := by
  apply le_antisymm
  · exact fun x hx => milnorPolynomialTotalResidue_mem_ker_implies_mem_constRange n x hx
  · exact milnorPolynomialTotalResidue_constRange_le_ker n

/-- The constant-field map and total finite residue map are exact. -/
theorem milnorPolynomialTotalResidue_exact (n : ℕ) :
    Function.Exact (milnorKDegMap (ratFuncConstHom (F := F)) n.succ)
      (milnorPolynomialTotalResidue (F := F) n) := by
  rw [AddMonoidHom.exact_iff]
  exact milnorPolynomialTotalResidue_ker_eq_constRange n

/-- **Global realization of finite local residue data.** Every finite-support
family of local Milnor `K_n` classes is the total residue of one class of
`K^M_{n+1}(F(t))`. -/
theorem milnorPolynomialTotalResidue_surjective (n : ℕ) :
    Function.Surjective (milnorPolynomialTotalResidue (F := F) n) := by
  classical
  intro z
  induction z using DFinsupp.induction with
  | h0 =>
      exact ⟨0, by
        ext q
        rw [milnorPolynomialTotalResidue_apply]
        exact map_zero _⟩
  | @ha q b f hqzero hb hsurj =>
      obtain ⟨y, hyq, hyother⟩ :=
        exists_residue_single (F := F) n q.1.natDegree q rfl b
      obtain ⟨z, hz⟩ := hsurj
      refine ⟨y + z, ?_⟩
      ext q'
      rw [milnorPolynomialTotalResidue_apply, map_add]
      have hzq' := congrArg (fun a => a q') hz
      rw [milnorPolynomialTotalResidue_apply] at hzq'
      by_cases hqq' : q = q'
      · subst q'
        have hyq' : milnorPolynomialResidueSucc q n y = b := by
          change milnorDegCongr (Nat.succ_sub_one n)
            (milnorResidue (polyResidueData q.2.1) n.succ y) = b
          rw [hyq]
          rfl
        have hzqzero : milnorPolynomialResidueSucc q n z = 0 := by
          rw [hzq', hqzero]
        rw [DFinsupp.add_apply, DFinsupp.single_eq_same, hqzero, add_zero]
        rw [hzqzero, add_zero]
        exact hyq'
      · rw [DFinsupp.add_apply, DFinsupp.single_eq_of_ne (Ne.symm hqq'), zero_add]
        have hyother' : milnorPolynomialResidueSucc q' n y = 0 := by
          change milnorDegCongr (Nat.succ_sub_one n)
            (milnorResidue (polyResidueData q'.2.1) n.succ y) = 0
          rw [hyother q' (Ne.symm hqq')]
          exact map_zero _
        rw [hyother', zero_add]
        exact hzq'

/-- **Milnor's finite-place short exact sequence for `F(t)`.** -/
theorem milnorPolynomialTotalResidue_short_exact (n : ℕ) :
    Function.Injective (milnorKDegMap (ratFuncConstHom (F := F)) n.succ) ∧
      Function.Exact (milnorKDegMap (ratFuncConstHom (F := F)) n.succ)
        (milnorPolynomialTotalResidue (F := F) n) ∧
      Function.Surjective (milnorPolynomialTotalResidue (F := F) n) := by
  exact ⟨milnorKDegMap_ratFuncConstHom_injective n.succ,
    milnorPolynomialTotalResidue_exact n,
    milnorPolynomialTotalResidue_surjective n⟩

end GaloisForLFunctions.HTGeometry
