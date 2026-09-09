import GaloisForLFunctions.HTGeometry.ConservativeDissipativeQuantum

set_option autoImplicit false

/-!
# Conservative–dissipative pauligraph laws

Applications of Schaffer–Exl, arXiv:2609.04530, to constructed operators
and the existing mathematical objects used below.
-/

open scoped Matrix InnerProductSpace
open Matrix QuantumAlg
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Hamiltonian circulation combined with the existing physical graph edge Casimir. -/
def pauliGraphField (G : SimpleGraph V) (H X : FiniteTwoReplicaMatrix V) : FiniteTwoReplicaMatrix V :=
  Complex.I • ringCommutator (hermitianPart H) X - finiteTwoReplicaPhysicalGraphCasimir G X

/-- Physical graph-edge energy is exactly the damping power of graph-coupled quantum motion. -/
theorem pauliGraphField_power (G : SimpleGraph V) (H X : FiniteTwoReplicaMatrix V) :
    (hsInner X (pauliGraphField G H X)).re = -finiteTwoReplicaPhysicalGraphEnergy G X := by
  rw [pauliGraphField, hsInner_sub_right, hsInner_smul_right, Complex.sub_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    commutator_expectation_im, sub_self, zero_sub]
  congr 1
  rw [← inner_finiteMatrixHilbertEquiv_eq_hsInner]
  exact re_inner_finiteTwoReplicaPhysicalGraphCasimir_eq_energy G X

/-- Graph Casimir energy is nonnegative for every graph, including disconnected and empty graphs. -/
theorem pauliGraphEnergy_nonneg (G : SimpleGraph V) (X : FiniteTwoReplicaMatrix V) :
    0 ≤ finiteTwoReplicaPhysicalGraphEnergy G X := by
  classical
  unfold finiteTwoReplicaPhysicalGraphEnergy
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  · exact le_rfl

theorem pauliGraphField_power_nonpos (G : SimpleGraph V) (H X : FiniteTwoReplicaMatrix V) :
    (hsInner X (pauliGraphField G H X)).re ≤ 0 := by
  rw [pauliGraphField_power]
  exact neg_nonpos.mpr (pauliGraphEnergy_nonneg G X)

/-- Lossless graph observables commute with every literal interacting edge channel. -/
theorem pauliGraphField_lossless_iff (G : SimpleGraph V) (H X : FiniteTwoReplicaMatrix V) :
    (hsInner X (pauliGraphField G H X)).re = 0 ↔
      ∀ u v, G.Adj u v → ∀ a b : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear (finiteEdgePauliLabel u v a b) X = 0 := by
  classical
  rw [pauliGraphField_power, neg_eq_zero]
  unfold finiteTwoReplicaPhysicalGraphEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ => by
    split_ifs
    · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    · exact le_rfl)]
  simp only [Finset.mem_univ, forall_true_left, Prod.forall]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro v
  by_cases he : G.Adj u v
  · rw [if_pos he]
    simp only [he, forall_true_left]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    simp only [Finset.mem_univ, forall_true_left]
    apply forall_congr'
    intro a
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
    simp only [Finset.mem_univ, forall_true_left, sq_eq_zero_iff, norm_eq_zero,
      finiteMatrixHilbertEquiv.map_eq_zero_iff]
  · simp [he]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
