import GaloisForLFunctions.RHTower.WeilLogShiftOrderedPrefix
import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalParity
import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalQuadrature

/-! Strictly positive edge masses determined by canonical probability prefixes. -/

open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalCluster_prefix_pos (r k : ℕ) (i : Fin (r + 1)) :
    0 < finiteWeilBinomialParity r i.castSucc *
      ∑ j ∈ Finset.Iic i.castSucc, finiteWeilCanonicalCluster r k j := by
  exact finiteWeilNormalizedMomentDual_prefix_pos (finiteWeilClusterLogNodes r k)
    (finiteWeilClusterLogNodes_strictMono r k) i

def finiteWeilCanonicalPrefixDifference (r k : ℕ) (i : Fin (r + 1)) : ℝ :=
  ∑ j ∈ Finset.Iic i.castSucc,
    (finiteWeilCanonicalPositiveProfile r k j - finiteWeilCanonicalNegativeProfile r k j)

def finiteWeilCanonicalEdgeMass (r k : ℕ) (i : Fin (r + 1)) : ℝ :=
  |finiteWeilCanonicalPrefixDifference r k i|

theorem finiteWeilCanonicalPrefixDifference_eq (r k : ℕ) (i : Fin (r + 1)) :
    finiteWeilCanonicalPrefixDifference r k i =
      (2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) *
        ∑ j ∈ Finset.Iic i.castSucc, finiteWeilCanonicalCluster r k j := by
  unfold finiteWeilCanonicalPrefixDifference finiteWeilCanonicalPositiveProfile
    finiteWeilCanonicalNegativeProfile
  simp only [finiteWeil_profile_difference, Finset.mul_sum]

theorem finiteWeilCanonicalPrefixDifference_pos (r k : ℕ) (i : Fin (r + 1)) :
    0 < finiteWeilBinomialParity r i.castSucc * finiteWeilCanonicalPrefixDifference r k i := by
  rw [finiteWeilCanonicalPrefixDifference_eq]
  have hscale := (finiteWeil_profile_scale_bounds (finiteWeilCanonicalCluster r k)
    (finiteWeilCanonicalCluster_spec r k).1 (finiteWeilCanonicalCluster_sum_zero r k)).1
  have hp := mul_pos hscale (finiteWeilCanonicalCluster_prefix_pos r k i)
  simpa only [mul_left_comm] using hp

theorem finiteWeilCanonicalEdgeMass_pos (r k : ℕ) (i : Fin (r + 1)) :
    0 < finiteWeilCanonicalEdgeMass r k i := by
  apply abs_pos.mpr
  intro he
  have hp := finiteWeilCanonicalPrefixDifference_pos r k i
  rw [he, mul_zero] at hp
  exact (lt_irrefl 0) hp

theorem finiteWeilCanonicalPrefixDifference_signed_mass (r k : ℕ) (i : Fin (r + 1)) :
    finiteWeilCanonicalPrefixDifference r k i =
      finiteWeilBinomialParity r i.castSucc * finiteWeilCanonicalEdgeMass r k i := by
  have hp := finiteWeilCanonicalPrefixDifference_pos r k i
  have habs : finiteWeilCanonicalEdgeMass r k i =
      finiteWeilBinomialParity r i.castSucc * finiteWeilCanonicalPrefixDifference r k i := by
    simpa only [abs_mul, finiteWeilBinomialParity_abs, one_mul,
      finiteWeilCanonicalEdgeMass] using abs_of_pos hp
  have hsq := finiteWeilBinomialParity_sq r i.castSucc
  rw [habs, ← mul_assoc, ← pow_two, hsq, one_mul]

end RHTower
