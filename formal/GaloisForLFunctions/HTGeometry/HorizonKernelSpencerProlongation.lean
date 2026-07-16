import GaloisForLFunctions.HTGeometry.CommutingPrincipalSymbolProlongation
import Mathlib.RingTheory.Derivation.Lie

/-!
# Commutator kernels impose Spencer prolongation laws

A linear relation among law commutators is not only a relation in exterior degree two.  Applying
it one step beyond a terminal principal symbol forces a corresponding first-prolongation identity
among the tail derivatives.  For a free first tail and a skew coefficient matrix, the relation
must annihilate the terminal symbol matrix.  This is the first higher compatibility law for a
prescribed commutator kernel.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {L : Type v} {ι η : Type w}
  [Field K] [Field L] [Algebra K L] [Fintype ι] [Fintype η]

/-- The first Spencer obstruction produced by a matrix of commutator coefficients and a terminal
principal-symbol matrix. -/
def principalSymbolSpencerObstruction
    (δ : ι → Derivation K L L) (a : ι → η → K) (y : η → L)
    (q : ι → ι → K) : L :=
  ∑ i, ∑ k, q i k •
    ((∑ j, a k j • δ i (y j)) - (∑ j, a i j • δ k (y j)))

/-- A commutator relation forces the associated first Spencer obstruction to vanish. -/
theorem principalSymbolSpencerObstruction_eq_zero_of_commutatorRelation
    (δ : ι → Derivation K L L) (z : L) (a : ι → η → K) (y : η → L)
    (q : ι → ι → K)
    (hboundary : ∀ i, δ i z = ∑ j, a i j • y j)
    (hrelation : ∑ i, ∑ k, q i k • ⁅δ i, δ k⁆ = 0) :
    principalSymbolSpencerObstruction δ a y q = 0 := by
  classical
  let ev : Derivation K L L →ₗ[K] L :=
    { toFun := fun D ↦ D z
      map_add' := by simp
      map_smul' := by simp }
  have hrelz := congrArg ev hrelation
  simp only [map_sum, map_smul, map_zero] at hrelz
  change (∑ i, ∑ k, q i k • ((δ i) ((δ k) z) - (δ k) ((δ i) z))) = 0 at hrelz
  simpa only [principalSymbolSpencerObstruction, hboundary, map_sum,
    Derivation.map_smul] using hrelz

/-- Coefficient of the free first-tail state indexed by `(s,j)` in the Spencer obstruction. -/
def principalSymbolSpencerCoefficient
    (q : ι → ι → K) (a : ι → η → K) (p : ι × η) : K :=
  (∑ k, q p.1 k * a k p.2) - (∑ i, q i p.1 * a i p.2)

/-- The Spencer obstruction is the linear combination of first-tail states with the displayed
matrix coefficient. -/
theorem principalSymbolSpencerObstruction_eq_linearCombination
    (δ : ι → Derivation K L L) (a : ι → η → K) (y : η → L)
    (q : ι → ι → K) :
    principalSymbolSpencerObstruction δ a y q =
      Fintype.linearCombination K (fun p : ι × η ↦ δ p.1 (y p.2))
        (principalSymbolSpencerCoefficient q a) := by
  classical
  unfold principalSymbolSpencerObstruction
  rw [Fintype.linearCombination_apply, Fintype.sum_prod_type]
  simp only [principalSymbolSpencerCoefficient]
  simp_rw [smul_sub, sub_smul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  simp_rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]

/-- With a linearly independent first tail, every commutator relation satisfies the corresponding
matrix first-prolongation equations. -/
theorem commutatorRelation_freeTail_forces_spencerCoefficients_zero
    (δ : ι → Derivation K L L) (z : L) (a : ι → η → K) (y : η → L)
    (q : ι → ι → K)
    (hboundary : ∀ i, δ i z = ∑ j, a i j • y j)
    (hrelation : ∑ i, ∑ k, q i k • ⁅δ i, δ k⁆ = 0)
    (htail : LinearIndependent K (fun p : ι × η ↦ δ p.1 (y p.2))) :
    ∀ p, principalSymbolSpencerCoefficient q a p = 0 := by
  classical
  have hzero := principalSymbolSpencerObstruction_eq_zero_of_commutatorRelation
    δ z a y q hboundary hrelation
  have hcomb : Fintype.linearCombination K (fun p : ι × η ↦ δ p.1 (y p.2))
      (principalSymbolSpencerCoefficient q a) =
      Fintype.linearCombination K (fun p : ι × η ↦ δ p.1 (y p.2)) 0 := by
    rw [← principalSymbolSpencerObstruction_eq_linearCombination δ a y q, hzero]
    simp
  have hcoeff := htail.fintypeLinearCombination_injective hcomb
  intro p
  exact congrFun hcoeff p

/-- For skew commutator coefficients in characteristic zero, a free first tail forces the
coefficient matrix `q` to annihilate every terminal-symbol column. -/
theorem skewCommutatorRelation_freeTail_forces_symbolKernel
    [CharZero K]
    (δ : ι → Derivation K L L) (z : L) (a : ι → η → K) (y : η → L)
    (q : ι → ι → K)
    (hq : ∀ i k, q k i = -q i k)
    (hboundary : ∀ i, δ i z = ∑ j, a i j • y j)
    (hrelation : ∑ i, ∑ k, q i k • ⁅δ i, δ k⁆ = 0)
    (htail : LinearIndependent K (fun p : ι × η ↦ δ p.1 (y p.2))) :
    ∀ i j, ∑ k, q i k * a k j = 0 := by
  intro i j
  have hcoeff := commutatorRelation_freeTail_forces_spencerCoefficients_zero
    δ z a y q hboundary hrelation htail (i, j)
  simp only [principalSymbolSpencerCoefficient] at hcoeff
  have htranspose : (∑ k, q k i * a k j) = -(∑ k, q i k * a k j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hq k i]
    ring
  rw [htranspose, sub_neg_eq_add] at hcoeff
  have htwo : (2 : K) * (∑ k, q i k * a k j) = 0 := by
    simpa [two_mul] using hcoeff
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end

end GaloisForLFunctions.HTGeometry
