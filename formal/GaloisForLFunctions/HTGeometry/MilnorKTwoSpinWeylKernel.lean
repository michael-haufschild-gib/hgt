import GaloisForLFunctions.HTGeometry.MilnorKTwoSpinWeylAction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Tactic

/-!
# Exact kernel of the rank-four Spin vector representation

Clifford contraction identifies vector commutators with exterior derivatives.  The exterior
Euler operator acts by degree, so an even Clifford element commuting with every vector is scalar.
Spin unitarity then forces that scalar to be `1` or `-1`, giving the exact two-element kernel.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorSpinWeyl

open CliffordAlgebra

abbrev V := Fin 4 → ℝ
abbrev Exterior := ExteriorAlgebra ℝ V

noncomputable def vectorBasis : Module.Basis (Fin 4) ℝ V :=
  Pi.basisFun ℝ (Fin 4)

noncomputable def exteriorBasis : Module.Basis (Finset (Fin 4)) ℝ Exterior :=
  vectorBasis.ExteriorAlgebra

/-- Clifford commutator with a vector is contraction after parity twisting. -/
theorem vector_mul_sub_involute_mul (Q : QuadraticForm ℝ V) (m : V)
    (x : CliffordAlgebra Q) :
    CliffordAlgebra.ι Q m * x - CliffordAlgebra.involute x * CliffordAlgebra.ι Q m =
      CliffordAlgebra.contractLeft (QuadraticMap.polarBilin Q m) x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [show CliffordAlgebra.involute
          (algebraMap ℝ (CliffordAlgebra Q) r) =
          algebraMap ℝ (CliffordAlgebra Q) r by
            rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one],
        CliffordAlgebra.contractLeft_algebraMap]
      exact sub_eq_zero.mpr
        (Algebra.commutes r (CliffordAlgebra.ι Q m)).symm
  | add x y hx hy =>
      simp only [mul_add, map_add, add_mul]
      rw [← hx, ← hy]
      abel
  | ι_mul x n hx =>
      rw [map_mul, CliffordAlgebra.involute_ι,
        CliffordAlgebra.contractLeft_ι_mul]
      rw [show CliffordAlgebra.ι Q m * (CliffordAlgebra.ι Q n * x) -
          (-CliffordAlgebra.ι Q n * CliffordAlgebra.involute x) *
            CliffordAlgebra.ι Q m =
          (CliffordAlgebra.ι Q m * CliffordAlgebra.ι Q n) * x +
            CliffordAlgebra.ι Q n *
              (CliffordAlgebra.involute x * CliffordAlgebra.ι Q m) by
            noncomm_ring]
      rw [CliffordAlgebra.ι_mul_ι_comm]
      rw [show (algebraMap ℝ (CliffordAlgebra Q)
              (QuadraticMap.polar Q m n) -
            CliffordAlgebra.ι Q n * CliffordAlgebra.ι Q m) * x +
            CliffordAlgebra.ι Q n *
              (CliffordAlgebra.involute x * CliffordAlgebra.ι Q m) =
          QuadraticMap.polar Q m n • x -
            CliffordAlgebra.ι Q n *
              (CliffordAlgebra.ι Q m * x -
                CliffordAlgebra.involute x * CliffordAlgebra.ι Q m) by
            rw [Algebra.smul_def]
            noncomm_ring]
      rw [hx]
      rfl

def coordinateDual (i : Fin 4) : Module.Dual ℝ V :=
  LinearMap.proj i

@[simp] theorem coordinateDual_basisVector (i j : Fin 4) :
    coordinateDual i (basisVector j) = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [coordinateDual, basisVector]
  · simp [coordinateDual, basisVector, h]

def exteriorEuler : Exterior →ₗ[ℝ] Exterior :=
  ∑ i : Fin 4,
    (LinearMap.mulLeft ℝ (ExteriorAlgebra.ι ℝ (basisVector i))).comp
      (CliffordAlgebra.contractLeft (coordinateDual i))

theorem sum_coordinate_basis (v : V) :
    ∑ i : Fin 4, coordinateDual i v • basisVector i = v := by
  classical
  funext j
  fin_cases j <;>
    simp [coordinateDual, basisVector, Fin.sum_univ_four]

theorem exterior_ι_anti (u v : V) :
    ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v =
      -(ExteriorAlgebra.ι ℝ v * ExteriorAlgebra.ι ℝ u) := by
  rw [CliffordAlgebra.ι_mul_ι_comm]
  simp [QuadraticMap.polar]

theorem exteriorEuler_ιMulti : ∀ (n : ℕ) (v : Fin n → V),
    exteriorEuler (ExteriorAlgebra.ιMulti ℝ n v) =
      n • ExteriorAlgebra.ιMulti ℝ n v := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [exteriorEuler]
  | succ n ih =>
      intro v
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp only [exteriorEuler, LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, CliffordAlgebra.contractLeft_ι_mul,
        Finset.sum_sub_distrib, mul_sub]
      simp_rw [Algebra.mul_smul_comm]
      simp_rw [← smul_mul_assoc]
      rw [← Finset.sum_mul]
      have hι := congrArg (ExteriorAlgebra.ι ℝ) (sum_coordinate_basis (v 0))
      simp only [map_sum, map_smul] at hι
      rw [hι]
      conv in (∑ i : Fin 4, _) =>
        enter [2, i]
        rw [← mul_assoc, exterior_ι_anti (basisVector i) (v 0),
          neg_mul, mul_assoc]
      rw [Finset.sum_neg_distrib, sub_neg_eq_add, ← Finset.mul_sum]
      change ExteriorAlgebra.ι ℝ (v 0) *
          ExteriorAlgebra.ιMulti ℝ n (Matrix.vecTail v) +
          ExteriorAlgebra.ι ℝ (v 0) *
            exteriorEuler (ExteriorAlgebra.ιMulti ℝ n (Matrix.vecTail v)) =
          ((n + 1) • ExteriorAlgebra.ι ℝ (v 0)) *
            ExteriorAlgebra.ιMulti ℝ n (Matrix.vecTail v)
      rw [ih]
      noncomm_ring
      simpa [add_comm] using
        (succ_nsmul
          (ExteriorAlgebra.ι ℝ (v 0) *
            ExteriorAlgebra.ιMulti ℝ n (Matrix.vecTail v)) n).symm

theorem exteriorEuler_basis (s : Finset (Fin 4)) :
    exteriorEuler (exteriorBasis s) =
      (s.card : ℝ) • exteriorBasis s := by
  rw [exteriorBasis, ExteriorAlgebra.basis_apply,
    exteriorEuler_ιMulti]
  exact (Nat.cast_smul_eq_nsmul ℝ s.card _).symm

theorem exteriorEuler_repr (y : Exterior) (s : Finset (Fin 4)) :
    exteriorBasis.repr (exteriorEuler y) s =
      (s.card : ℝ) • exteriorBasis.repr y s := by
  classical
  conv_lhs =>
    rw [← exteriorBasis.sum_repr y]
  simp only [map_sum, map_smul, exteriorEuler_basis]
  simp [Finsupp.single_apply, mul_comm]

theorem exterior_eq_scalar_of_contractLeft_eq_zero (y : Exterior)
    (hy : ∀ i : Fin 4,
      CliffordAlgebra.contractLeft (coordinateDual i) y = 0) :
    ∃ c : ℝ, y = algebraMap ℝ Exterior c := by
  have hEuler : exteriorEuler y = 0 := by
    simp [exteriorEuler, hy]
  have hcoeff : ∀ s : Finset (Fin 4), s ≠ ∅ →
      exteriorBasis.repr y s = 0 := by
    intro s hs
    have hcoord := congrArg (fun z => exteriorBasis.repr z s) hEuler
    rw [exteriorEuler_repr] at hcoord
    simp only [map_zero, Finsupp.zero_apply] at hcoord
    have hcard : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs))
    exact (smul_eq_zero.mp hcoord).resolve_left hcard
  let c := exteriorBasis.repr y ∅
  refine ⟨c, ?_⟩
  have hybasis : y = c • exteriorBasis ∅ := by
    apply exteriorBasis.repr.injective
    ext s
    by_cases hs : s = ∅
    · subst s
      simp [c]
    · simp [hcoeff s hs, hs]
  rw [hybasis]
  have hempty : exteriorBasis ∅ = 1 := by
    rw [exteriorBasis, ExteriorAlgebra.basis_apply]
    exact ExteriorAlgebra.ιMulti_zero_apply _
  rw [hempty, Algebra.smul_def, mul_one]

theorem spinQ_polarBilin_basisVector (i : Fin 4) :
    QuadraticMap.polarBilin spinQ (basisVector i) =
      (-2 : ℝ) • coordinateDual i := by
  ext v
  fin_cases i <;>
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      spinQ, basisVector, coordinateDual, Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
      Fin.sum_univ_four]
  <;> ring

/-- An even rank-four Clifford element commuting with every vector generator is scalar. -/
theorem clifford_eq_scalar_of_even_commutes_basis (x : Clifford)
    (heven : CliffordAlgebra.involute x = x)
    (hcomm : ∀ i : Fin 4, basisClifford i * x = x * basisClifford i) :
    ∃ c : ℝ, x = algebraMap ℝ Clifford c := by
  have hpolar : ∀ i : Fin 4,
      CliffordAlgebra.contractLeft
        (QuadraticMap.polarBilin spinQ (basisVector i)) x = 0 := by
    intro i
    rw [← vector_mul_sub_involute_mul spinQ (basisVector i) x,
      heven]
    exact sub_eq_zero.mpr (hcomm i)
  have hcoordinate : ∀ i : Fin 4,
      CliffordAlgebra.contractLeft (coordinateDual i) x = 0 := by
    intro i
    have hi := hpolar i
    rw [spinQ_polarBilin_basisVector] at hi
    rw [LinearMap.map_smul, LinearMap.smul_apply] at hi
    exact (smul_eq_zero.mp hi).resolve_left (by norm_num)
  let y : Exterior := CliffordAlgebra.equivExterior spinQ x
  have hy : ∀ i : Fin 4,
      CliffordAlgebra.contractLeft (coordinateDual i) y = 0 := by
    intro i
    change CliffordAlgebra.contractLeft (coordinateDual i)
      (CliffordAlgebra.changeForm
        (CliffordAlgebra.changeForm.associated_neg_proof (Q := spinQ)) x) = 0
    rw [← CliffordAlgebra.changeForm_contractLeft,
      hcoordinate i, map_zero]
  obtain ⟨c, hc⟩ := exterior_eq_scalar_of_contractLeft_eq_zero y hy
  refine ⟨c, ?_⟩
  apply (CliffordAlgebra.equivExterior spinQ).injective
  change y = CliffordAlgebra.equivExterior spinQ (algebraMap ℝ Clifford c)
  rw [hc]
  change algebraMap ℝ Exterior c =
    CliffordAlgebra.changeForm
      (CliffordAlgebra.changeForm.associated_neg_proof (Q := spinQ))
        (algebraMap ℝ Clifford c)
  rw [CliffordAlgebra.changeForm_algebraMap]

theorem spin_eq_one_or_centralNegOne_of_scalar (s : spinGroup spinQ)
    (c : ℝ) (hc : (s : Clifford) = algebraMap ℝ Clifford c) :
    s = 1 ∨ s = centralNegOne := by
  have hunit := pinGroup.star_mul_self_of_mem
    (spinGroup.mem_pin s.property)
  rw [hc] at hunit
  have hc2map : algebraMap ℝ Clifford (c * c) =
      algebraMap ℝ Clifford 1 := by
    simpa only [CliffordAlgebra.star_algebraMap, map_mul, map_one] using hunit
  have hc2 : c * c = 1 :=
    FaithfulSMul.algebraMap_injective ℝ Clifford hc2map
  rcases (mul_self_eq_one_iff.mp hc2) with hc_one | hc_neg
  · left
    apply Subtype.ext
    rw [hc, hc_one, map_one]
    rfl
  · right
    apply Subtype.ext
    rw [hc, hc_neg, map_neg, map_one, centralNegOne_val]

theorem spinVectorLinearEquiv_centralNegOne :
    spinVectorLinearEquiv centralNegOne = 1 := by
  have hsq : centralNegOne * centralNegOne = 1 := by
    apply Subtype.ext
    simp
  have hinv : centralNegOne⁻¹ = centralNegOne :=
    (eq_inv_of_mul_eq_one_left hsq).symm
  apply LinearEquiv.ext
  intro p
  apply spinCliffordIota_injective
  rw [spinCliffordIota_spinVectorLinearEquiv]
  simp only [spinConjugation, MulSemiringAction.toAlgEquiv_apply]
  rw [@ConjAct.units_smul_def, @ConjAct.ofConjAct_toConjAct]
  change (centralNegOne : Clifford) * CliffordAlgebra.ι spinQ p *
      ((centralNegOne⁻¹ : spinGroup spinQ) : Clifford) =
    CliffordAlgebra.ι spinQ ((1 : V ≃ₗ[ℝ] V) p)
  rw [hinv, centralNegOne_val]
  simp

/-- Exact kernel of the rank-four Spin vector representation. -/
theorem spinVectorRepresentation_eq_one_iff (s : spinGroup spinQ) :
    spinVectorRepresentation s = 1 ↔ s = 1 ∨ s = centralNegOne := by
  constructor
  · intro hs
    have hs' : spinVectorLinearEquiv s = 1 := hs
    have hcomm : ∀ i : Fin 4,
        basisClifford i * (s : Clifford) =
          (s : Clifford) * basisClifford i := by
      intro i
      have hfix := LinearEquiv.congr_fun hs' (basisVector i)
      have hconj := spinCliffordIota_spinVectorLinearEquiv s (basisVector i)
      rw [hfix] at hconj
      simp at hconj
      have hconj' :
          (s : Clifford) * basisClifford i *
              ((s⁻¹ : spinGroup spinQ) : Clifford) = basisClifford i := by
        simpa [spinConjugation, basisClifford,
          @ConjAct.units_smul_def, @ConjAct.ofConjAct_toConjAct] using hconj.symm
      have hright := congrArg (fun z : Clifford => z * (s : Clifford)) hconj'
      have hinv_mul : ((s⁻¹ : spinGroup spinQ) : Clifford) *
          (s : Clifford) = 1 := by
        exact congrArg Subtype.val (inv_mul_cancel s)
      simpa only [mul_assoc, hinv_mul, mul_one] using hright.symm
    obtain ⟨c, hc⟩ := clifford_eq_scalar_of_even_commutes_basis
      (s : Clifford) (spinGroup.involute_eq s.property) hcomm
    exact spin_eq_one_or_centralNegOne_of_scalar s c hc
  · rintro (rfl | rfl)
    · exact map_one spinVectorRepresentation
    · exact spinVectorLinearEquiv_centralNegOne

example (s : Finset (Fin 4)) :
    exteriorBasis s = ExteriorAlgebra.ιMulti_family ℝ s.card vectorBasis
      (Set.powersetCard.prodEquiv.symm s).2 := by
  exact ExteriorAlgebra.basis_apply vectorBasis s

end MilnorSpinWeyl
end GaloisForLFunctions.HTGeometry
