import GaloisForLFunctions.HTGeometry.MilnorNorm
import GaloisForLFunctions.HTGeometry.MilnorPolynomialTotalResidue

/-!
# Global reciprocity for Milnor residues on a rational function field

The finite-place total residue of `F(t)` is already an exact direct-sum map.
This file assembles the Bass--Tate norms of its coordinates and proves that
their sum cancels the residue at infinity.  Thus every Milnor class satisfies
the projective-line reciprocity law

`Σ_π N_{κ(π)/F}(∂_π x) + ∂_∞ x = 0`.

This is the function-field local-invariant sum underlying the global
reciprocity portion of Albert--Brauer--Hasse--Noether.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {F : Type*} [Field F]

local instance milnorPolynomialGlobalReciprocityDecidableEqMonicIrred :
    DecidableEq (MonicIrred F) := Classical.decEq _

/-- The finite sum of the Bass--Tate norm maps over all monic irreducible
places of `F(t)`. -/
noncomputable def milnorPolynomialTotalNorm (n : ℕ) :
    MilnorPolynomialTotalResidueTarget (F := F) n →+ MilnorKDeg F n := by
  classical
  exact
    { toFun := fun z => z.sum fun q x => milnorNormAt q n x
      map_zero' := by
        simp [DFinsupp.sum]
      map_add' := by
        intro a b
        rw [DFinsupp.sum_add_index]
        · intro q
          exact (milnorNormAt q n).map_zero
        · intro q x y
          exact (milnorNormAt q n).map_add x y }

/-- Evaluation of the total norm on one finite-place contribution. -/
theorem milnorPolynomialTotalNorm_single (q : MonicIrred F) (n : ℕ)
    (x : MilnorKDeg (polyResidueField q.2.1) n) :
    milnorPolynomialTotalNorm (F := F) n (DFinsupp.single q x) =
      milnorNormAt q n x := by
  classical
  unfold milnorPolynomialTotalNorm
  apply DFinsupp.sum_single_index
  exact (milnorNormAt q n).map_zero

/-- **Global reciprocity on `F(t)`.** The sum of the normed finite residues
is the negative of the residue at infinity. -/
theorem milnorPolynomialTotalResidue_reciprocity (n : ℕ)
    (y : MilnorKDeg (RatFunc F) n.succ) :
    milnorPolynomialTotalNorm (F := F) n
      (milnorPolynomialTotalResidue (F := F) n y) + milnorResidueInfty n y = 0 := by
  classical
  have hmain : ∀ z : MilnorPolynomialTotalResidueTarget (F := F) n,
      ∀ y : MilnorKDeg (RatFunc F) n.succ,
        milnorPolynomialTotalResidue (F := F) n y = z →
          milnorPolynomialTotalNorm (F := F) n z = -milnorResidueInfty n y := by
    intro z
    induction z using DFinsupp.induction with
    | h0 =>
        intro y hy
        have hraw : ∀ q : MonicIrred F,
            milnorResidue (polyResidueData q.2.1) n.succ y = 0 := by
          apply (milnorPolynomialTotalResidue_mem_ker_iff (F := F) n y).mp
          exact hy
        have hinfty : milnorResidueInfty n y = 0 := by
          have h := milnorResidueInfty_eq_of_residues_eq (F := F) (n := n)
            (y := y) (y' := 0) (fun q => by rw [hraw q, map_zero])
          simpa using h
        rw [map_zero, hinfty, neg_zero]
    | @ha q b f hqzero hb hih =>
        intro y hy
        obtain ⟨u, huq, huother⟩ := exists_lift_single q n b
        have htotalu : milnorPolynomialTotalResidue (F := F) n u = DFinsupp.single q b := by
          ext q'
          rw [milnorPolynomialTotalResidue_apply]
          by_cases hqq' : q = q'
          · subst q'
            rw [DFinsupp.single_eq_same]
            change milnorDegCongr (Nat.succ_sub_one n)
              (milnorResidue (polyResidueData q.2.1) n.succ u) = b
            rw [huq]
            rfl
          · rw [DFinsupp.single_eq_of_ne (Ne.symm hqq')]
            change milnorDegCongr (Nat.succ_sub_one n)
              (milnorResidue (polyResidueData q'.2.1) n.succ u) = 0
            rw [huother q' (Ne.symm hqq')]
            exact map_zero _
        have htotaldiff : milnorPolynomialTotalResidue (F := F) n (y - u) = f := by
          rw [map_sub, hy, htotalu, add_sub_cancel_left]
        have hdiff := hih (y - u) htotaldiff
        have hsingle := milnorNormAt_spec q n huq huother
        calc
          milnorPolynomialTotalNorm (F := F) n (DFinsupp.single q b + f) =
              milnorPolynomialTotalNorm (F := F) n (DFinsupp.single q b) +
                milnorPolynomialTotalNorm (F := F) n f := by
                  exact (milnorPolynomialTotalNorm (F := F) n).map_add _ _
          _ = milnorNormAt q n b + milnorPolynomialTotalNorm (F := F) n f := by
                rw [milnorPolynomialTotalNorm_single]
          _ = -milnorResidueInfty n u + -milnorResidueInfty n (y - u) := by
                rw [hsingle, hdiff]
          _ = -milnorResidueInfty n y := by
                rw [map_sub]
                abel
  rw [hmain (milnorPolynomialTotalResidue (F := F) n y) y rfl]
  exact neg_add_cancel _

/-- The global finite-and-infinite residue sum. -/
noncomputable def milnorPolynomialGlobalResidue (n : ℕ) :
    MilnorKDeg (RatFunc F) n.succ →+ MilnorKDeg F n :=
  (milnorPolynomialTotalNorm (F := F) n).comp
    (milnorPolynomialTotalResidue (F := F) n) + milnorResidueInfty n

/-- The global finite-and-infinite Milnor residue homomorphism vanishes. -/
theorem milnorPolynomialGlobalResidue_eq_zero (n : ℕ) :
    milnorPolynomialGlobalResidue (F := F) n = 0 := by
  ext y
  exact milnorPolynomialTotalResidue_reciprocity n y

/-- The residue map recording all finite residues and the residue at infinity. -/
noncomputable def milnorPolynomialAllResidue (n : ℕ) :
    MilnorKDeg (RatFunc F) n.succ →+
      MilnorPolynomialTotalResidueTarget (F := F) n × MilnorKDeg F n :=
  (milnorPolynomialTotalResidue (F := F) n).prod (milnorResidueInfty n)

/-- The global norm-sum on finite-and-infinite residue data. -/
noncomputable def milnorPolynomialGlobalSum (n : ℕ) :
    MilnorPolynomialTotalResidueTarget (F := F) n × MilnorKDeg F n →+ MilnorKDeg F n :=
  (milnorPolynomialTotalNorm (F := F) n).comp (AddMonoidHom.fst _ _) + AddMonoidHom.snd _ _

/-- Evaluation of the all-place residue map. -/
theorem milnorPolynomialAllResidue_apply (n : ℕ)
    (y : MilnorKDeg (RatFunc F) n.succ) :
    milnorPolynomialAllResidue (F := F) n y =
      (milnorPolynomialTotalResidue (F := F) n y, milnorResidueInfty n y) := rfl

/-- Evaluation of the global norm-sum. -/
theorem milnorPolynomialGlobalSum_apply (n : ℕ)
    (z : MilnorPolynomialTotalResidueTarget (F := F) n × MilnorKDeg F n) :
    milnorPolynomialGlobalSum (F := F) n z =
      milnorPolynomialTotalNorm (F := F) n z.1 + z.2 := rfl

/-- **The global image condition.** All-place residue data come from a class
of `F(t)` exactly when their global norm-sum vanishes. -/
theorem milnorPolynomialAllResidue_range_eq_globalSum_ker (n : ℕ) :
    AddMonoidHom.range (milnorPolynomialAllResidue (F := F) n) =
      (milnorPolynomialGlobalSum (F := F) n).ker := by
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    change milnorPolynomialTotalNorm (F := F) n
      (milnorPolynomialTotalResidue (F := F) n y) + milnorResidueInfty n y = 0
    exact milnorPolynomialTotalResidue_reciprocity n y
  · intro z hz
    obtain ⟨y, hy⟩ := milnorPolynomialTotalResidue_surjective (F := F) n z.1
    refine ⟨y, Prod.ext hy ?_⟩
    have hsum : milnorPolynomialTotalNorm (F := F) n z.1 + z.2 = 0 := hz
    have hrec : milnorPolynomialTotalNorm (F := F) n z.1 + milnorResidueInfty n y = 0 := by
      rw [← hy]
      exact milnorPolynomialTotalResidue_reciprocity n y
    exact (eq_neg_of_add_eq_zero_right hrec).trans (eq_neg_of_add_eq_zero_right hsum).symm

/-- The all-place residue map is exact with the global norm-sum. -/
theorem milnorPolynomialAllResidue_exact (n : ℕ) :
    Function.Exact (milnorPolynomialAllResidue (F := F) n)
      (milnorPolynomialGlobalSum (F := F) n) := by
  rw [AddMonoidHom.exact_iff]
  exact (milnorPolynomialAllResidue_range_eq_globalSum_ker n).symm

/-- The global norm-sum is surjective, through the infinite coordinate. -/
theorem milnorPolynomialGlobalSum_surjective (n : ℕ) :
    Function.Surjective (milnorPolynomialGlobalSum (F := F) n) := by
  intro x
  refine ⟨(0, x), ?_⟩
  change milnorPolynomialTotalNorm (F := F) n 0 + x = x
  rw [map_zero, zero_add]

/-- Every constant class has zero all-place residue. -/
theorem milnorPolynomialAllResidue_const_eq_zero (n : ℕ)
    (x : MilnorKDeg F n.succ) :
    milnorPolynomialAllResidue (F := F) n
      (milnorKDegMap (ratFuncConstHom (F := F)) n.succ x) = 0 := by
  apply Prod.ext
  · exact milnorPolynomialTotalResidue_const_eq_zero n x
  · exact milnorResidueInfty_const n x

/-- The all-place residue kernel is exactly the image of the constant field. -/
theorem milnorPolynomialAllResidue_ker_eq_constRange (n : ℕ) :
    (milnorPolynomialAllResidue (F := F) n).ker =
      AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n.succ) := by
  apply le_antisymm
  · intro y hy
    apply milnorPolynomialTotalResidue_mem_ker_implies_mem_constRange n y
    have htotal : milnorPolynomialTotalResidue (F := F) n y = 0 := by
      simpa [milnorPolynomialAllResidue_apply] using congrArg Prod.fst hy
    exact htotal
  · rintro y ⟨x, rfl⟩
    exact milnorPolynomialAllResidue_const_eq_zero n x

/-- The constant-field map and all-place residue map are exact. -/
theorem milnorPolynomialConst_allResidue_exact (n : ℕ) :
    Function.Exact (milnorKDegMap (ratFuncConstHom (F := F)) n.succ)
      (milnorPolynomialAllResidue (F := F) n) := by
  rw [AddMonoidHom.exact_iff]
  exact milnorPolynomialAllResidue_ker_eq_constRange n

/-- **Projective-line Hasse exact sequence for Milnor `K`-theory.** -/
theorem milnorPolynomialProjectiveLine_exact (n : ℕ) :
    Function.Injective (milnorKDegMap (ratFuncConstHom (F := F)) n.succ) ∧
      Function.Exact (milnorKDegMap (ratFuncConstHom (F := F)) n.succ)
        (milnorPolynomialAllResidue (F := F) n) ∧
      Function.Exact (milnorPolynomialAllResidue (F := F) n)
        (milnorPolynomialGlobalSum (F := F) n) ∧
      Function.Surjective (milnorPolynomialGlobalSum (F := F) n) := by
  exact ⟨milnorKDegMap_ratFuncConstHom_injective n.succ,
    milnorPolynomialConst_allResidue_exact n,
    milnorPolynomialAllResidue_exact n,
    milnorPolynomialGlobalSum_surjective n⟩

end

end GaloisForLFunctions.HTGeometry
