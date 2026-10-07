import GaloisForLFunctions.RHTower.XiGlobalKummerSquareClasses
import GaloisForLFunctions.HTGeometry.MeromorphicPlaneAlgebra
import GaloisForLFunctions.HTGeometry.QuadraticTowerSquareClasses
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Persistence of the global Xi class on the joint marked tower

Adjoin square roots of `xi * (1 - (n+2)^(-s) * xi)` for every natural index. The independent
base square classes imply that Xi stays nonsquare at every finite stage and in their directed
union. Each marked factor has the same surviving nonzero square class as Xi on this union.
-/

noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

local instance : CharZero MeromorphicPlane :=
  charZero_of_injective_algebraMap constPlane_injective

abbrev K := MeromorphicPlane
abbrev Ω := AlgebraicClosure K

def base : Subfield Ω := baseRange K Ω

def radicand (n : ℕ) : K := xiElement * factorElement (n + 2)

/-- A chosen radical in an algebraic closure of the global meromorphic plane field. -/
def root (n : ℕ) : Ω :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (radicand n)) (by decide : 0 < 2))

theorem root_sq (n : ℕ) : root n * root n = algebraMap K Ω (radicand n) := by
  simpa only [root, pow_two] using
    (Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (radicand n))
      (by decide : 0 < 2)))

theorem isSqIn_base_iff (a : K) : IsSqIn base (algebraMap K Ω a) ↔ IsSquare a := by
  constructor
  · rintro ⟨r, hr, h⟩
    change ∃ b, algebraMap K Ω b = r at hr
    obtain ⟨b, rfl⟩ := hr
    refine ⟨b, (algebraMap K Ω).injective ?_⟩
    simpa only [map_mul] using h
  · rintro ⟨r, hr⟩
    refine ⟨algebraMap K Ω r, RingHom.mem_fieldRange_self _ r, ?_⟩
    rw [hr, map_mul]

theorem xi_pow_mul_shifted_factors_not_isSquare (T : Finset ℕ) (e : ℕ)
    (hne : T.Nonempty) :
    ¬ IsSquare (xiElement ^ e * ∏ n ∈ T, factorElement (n + 2)) := by
  have hn := xi_pow_mul_prod_factors_not_isSquare (T.image (fun n => n + 2)) e
    (hne.image _) (by
      intro n hn
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hn
      omega)
  rw [Finset.prod_image] at hn
  · exact hn
  · intro a _ b _ hab
    dsimp at hab
    omega

theorem prod_radicand (T : Finset ℕ) :
    ∏ n ∈ T, radicand n = xiElement ^ T.card * ∏ n ∈ T, factorElement (n + 2) := by
  simp only [radicand, Finset.prod_mul_distrib, Finset.prod_const]

theorem prod_radicand_not_isSquare (T : Finset ℕ) (hne : T.Nonempty) :
    ¬ IsSquare (∏ n ∈ T, radicand n) := by
  rw [prod_radicand]
  exact xi_pow_mul_shifted_factors_not_isSquare T T.card hne

theorem xi_mul_prod_radicand_not_isSquare (T : Finset ℕ) :
    ¬ IsSquare (xiElement * ∏ n ∈ T, radicand n) := by
  by_cases hne : T.Nonempty
  · have he : xiElement * ∏ n ∈ T, radicand n =
        xiElement ^ (T.card + 1) * ∏ n ∈ T, factorElement (n + 2) := by
      rw [prod_radicand, pow_succ]
      ring
    rw [he]
    exact xi_pow_mul_shifted_factors_not_isSquare T (T.card + 1) hne
  · have ht : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa [ht] using xiElement_not_isSquare

def stage (k : ℕ) : Subfield Ω := radicalStage base root k

theorem root_sq_mem_base (n : ℕ) : root n * root n ∈ base := by
  rw [root_sq]
  exact RingHom.mem_fieldRange_self _ _

theorem root_radicands_independent (T : Finset ℕ) (hne : T.Nonempty) :
    ¬ IsSqIn base (∏ n ∈ T, root n * root n) := by
  simp_rw [root_sq]
  rw [← map_prod, isSqIn_base_iff]
  exact prod_radicand_not_isSquare T hne

/-- Xi remains nonsquare after every finite initial segment of marked roots. -/
theorem xi_not_isSqIn_stage (k : ℕ) : ¬ IsSqIn (stage k) (algebraMap K Ω xiElement) := by
  let C := independentTower base root k (by norm_num : (2 : Ω) ≠ 0)
    (fun n _ => root_sq_mem_base n) (fun T _ hT => root_radicands_independent T hT)
  have hb : C.M 0 = base := radicalStage_zero base root
  have hi : ∀ T : Finset ℕ, T ⊆ Finset.range k → T.Nonempty →
      ¬ IsSqIn (C.M 0) (∏ n ∈ T, C.d n) := by
    intro T _ hT
    rw [hb]
    exact root_radicands_independent T hT
  intro hsq
  obtain ⟨T, _, hT⟩ := C.exists_twist_isSq (by norm_num) hi k le_rfl
    (algebraMap K Ω xiElement) (by rw [hb]; exact RingHom.mem_fieldRange_self _ _) hsq
  rw [hb] at hT
  change IsSqIn base (algebraMap K Ω xiElement * ∏ n ∈ T, root n * root n) at hT
  simp_rw [root_sq] at hT
  rw [← map_prod, ← map_mul, isSqIn_base_iff] at hT
  exact xi_mul_prod_radicand_not_isSquare T hT

theorem stage_mono : Monotone stage := by
  apply monotone_nat_of_le_succ
  exact radicalStage_mono base root

/-- The joint marked field, as the directed union of all finite radical stages. -/
def markedField : Subfield Ω := ⨆ k, stage k

/-- Xi remains nonsquare in the full infinite marked field. -/
theorem xi_not_isSqIn_markedField :
    ¬ IsSqIn markedField (algebraMap K Ω xiElement) := by
  rintro ⟨r, hr, hsq⟩
  obtain ⟨k, hk⟩ := (Subfield.mem_iSup_of_directed stage_mono.directed_le).mp hr
  exact xi_not_isSqIn_stage k ⟨r, hk, hsq⟩

theorem root_mem_markedField (n : ℕ) : root n ∈ markedField :=
  (le_iSup stage (n + 1)) (root_mem_radicalStage_succ base root n)

theorem base_le_markedField : base ≤ markedField :=
  le_trans (base_le_radicalStage base root 0) (le_iSup stage 0)

/-- Every integer-labelled factor remains nonsquare on the full marked field. -/
theorem factor_not_isSqIn_markedField (n : ℕ) :
    ¬ IsSqIn markedField (algebraMap K Ω (factorElement (n + 2))) := by
  rintro ⟨r, hr, hsq⟩
  have hf0 : algebraMap K Ω (factorElement (n + 2)) ≠ 0 :=
    (map_ne_zero (algebraMap K Ω)).mpr (factorElement_ne_zero (by omega))
  have hr0 : r ≠ 0 := by
    intro hz
    apply hf0
    simpa [hz] using hsq
  apply xi_not_isSqIn_markedField
  refine ⟨root n / r, markedField.div_mem (root_mem_markedField n) hr, ?_⟩
  have hroot := root_sq n
  rw [radicand, map_mul, hsq] at hroot
  field_simp [hr0]
  linear_combination -hroot


/-- The same marked field with its canonical base-field algebra structure. -/
def markedExtension : IntermediateField K Ω :=
  markedField.toIntermediateField (fun a =>
    base_le_markedField (RingHom.mem_fieldRange_self (algebraMap K Ω) a))

/-- The original global Xi class survives on the actual joint marked extension. -/
theorem xi_not_isSquare_markedExtension :
    ¬ IsSquare (algebraMap K markedExtension xiElement) := by
  rintro ⟨r, hr⟩
  apply xi_not_isSqIn_markedField
  exact ⟨r.val, r.property, congrArg (fun x : markedExtension => (x : Ω)) hr⟩

def markedRoot (n : ℕ) : markedExtension := ⟨root n, root_mem_markedField n⟩

theorem markedRoot_sq (n : ℕ) :
    markedRoot n * markedRoot n = algebraMap K markedExtension (radicand n) := by
  apply Subtype.ext
  exact root_sq n

/-- Every marked factor retains a nonzero square class on the joint extension. -/
theorem factor_not_isSquare_markedExtension (n : ℕ) :
    ¬ IsSquare (algebraMap K markedExtension (factorElement (n + 2))) := by
  rintro ⟨r, hr⟩
  apply factor_not_isSqIn_markedField n
  exact ⟨r.val, r.property, congrArg (fun x : markedExtension => (x : Ω)) hr⟩


/-- All marked factors represent the same square class as Xi on the joint extension. -/
theorem xi_mul_factor_isSquare_markedExtension (n : ℕ) :
    IsSquare (algebraMap K markedExtension xiElement *
      algebraMap K markedExtension (factorElement (n + 2))) := by
  refine ⟨markedRoot n, ?_⟩
  rw [markedRoot_sq, radicand, map_mul]

end RHTower.XiGlobalKummer
