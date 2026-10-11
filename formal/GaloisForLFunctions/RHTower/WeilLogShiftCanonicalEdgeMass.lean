import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalPrefixMass
import GaloisForLFunctions.RHTower.WeilLogShiftPrefixPairing

/-! Canonical adjacent edge masses form a strictly positive probability vector. -/

open scoped BigOperators
namespace RHTower

theorem finiteWeilBinomialParity_adjacent (r : ℕ) (i : Fin (r + 1)) :
    finiteWeilBinomialParity r i.succ = -finiteWeilBinomialParity r i.castSucc := by
  unfold finiteWeilBinomialParity
  have he : r + 1 - (i.castSucc : ℕ) = r + 1 - (i.succ : ℕ) + 1 := by
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  rw [he, pow_succ]
  ring

theorem finiteWeilCanonicalProfiles_parity (r k : ℕ) (j : Fin (r + 2)) :
    finiteWeilCanonicalPositiveProfile r k j - finiteWeilCanonicalNegativeProfile r k j =
      finiteWeilBinomialParity r j *
        |finiteWeilCanonicalPositiveProfile r k j - finiteWeilCanonicalNegativeProfile r k j| := by
  have hscale := (finiteWeil_profile_scale_bounds (finiteWeilCanonicalCluster r k)
    (finiteWeilCanonicalCluster_spec r k).1 (finiteWeilCanonicalCluster_sum_zero r k)).1
  change finiteWeilPositiveProfile (finiteWeilCanonicalCluster r k) j -
      finiteWeilNegativeProfile (finiteWeilCanonicalCluster r k) j =
    finiteWeilBinomialParity r j *
      |finiteWeilPositiveProfile (finiteWeilCanonicalCluster r k) j -
        finiteWeilNegativeProfile (finiteWeilCanonicalCluster r k) j|
  simp only [finiteWeil_profile_difference]
  rw [abs_mul, abs_of_pos hscale]
  calc
    _ = (2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) *
        (finiteWeilBinomialParity r j * |finiteWeilCanonicalCluster r k j|) :=
      congrArg (fun x => (2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) * x)
        (finiteWeilCanonicalCluster_parity r k j)
    _ = _ := by ring

theorem finiteWeilCanonicalProfiles_parity_pairing (r k : ℕ) :
    (∑ j, (finiteWeilCanonicalPositiveProfile r k j - finiteWeilCanonicalNegativeProfile r k j) *
      finiteWeilBinomialParity r j) = 2 := by
  have hpoint (j : Fin (r + 2)) :
      (finiteWeilCanonicalPositiveProfile r k j - finiteWeilCanonicalNegativeProfile r k j) *
        finiteWeilBinomialParity r j =
        |finiteWeilCanonicalPositiveProfile r k j - finiteWeilCanonicalNegativeProfile r k j| := by
    calc
      _ = (finiteWeilBinomialParity r j *
          |finiteWeilCanonicalPositiveProfile r k j - finiteWeilCanonicalNegativeProfile r k j|) *
          finiteWeilBinomialParity r j :=
        congrArg (fun x => x * finiteWeilBinomialParity r j) (finiteWeilCanonicalProfiles_parity r k j)
      _ = finiteWeilBinomialParity r j ^ 2 *
          |finiteWeilCanonicalPositiveProfile r k j - finiteWeilCanonicalNegativeProfile r k j| := by ring
      _ = _ := by rw [finiteWeilBinomialParity_sq, one_mul]
  simp_rw [hpoint]
  exact (finiteWeilCanonicalProfiles_spec r k).2.2.2.1

theorem finiteWeilCanonicalEdgeMass_sum (r k : ℕ) :
    (∑ i, finiteWeilCanonicalEdgeMass r k i) = 1 := by
  have hzero : (∑ j, (finiteWeilCanonicalPositiveProfile r k j -
      finiteWeilCanonicalNegativeProfile r k j)) = 0 := by
    rw [Finset.sum_sub_distrib, (finiteWeilCanonicalProfiles_spec r k).2.1,
      (finiteWeilCanonicalProfiles_spec r k).2.2.1]
    norm_num
  have hp := finiteWeil_prefix_pairing_zero
    (fun j => finiteWeilCanonicalPositiveProfile r k j - finiteWeilCanonicalNegativeProfile r k j)
    (finiteWeilBinomialParity r) hzero
  rw [finiteWeilCanonicalProfiles_parity_pairing r k] at hp
  have hedge (i : Fin (r + 1)) :
      (∑ j ∈ Finset.Iic i.castSucc,
        (finiteWeilCanonicalPositiveProfile r k j - finiteWeilCanonicalNegativeProfile r k j)) *
        (finiteWeilBinomialParity r i.castSucc - finiteWeilBinomialParity r i.succ) =
          2 * finiteWeilCanonicalEdgeMass r k i := by
    change finiteWeilCanonicalPrefixDifference r k i *
      (finiteWeilBinomialParity r i.castSucc - finiteWeilBinomialParity r i.succ) = _
    rw [finiteWeilCanonicalPrefixDifference_signed_mass, finiteWeilBinomialParity_adjacent]
    calc
      _ = 2 * finiteWeilBinomialParity r i.castSucc ^ 2 * finiteWeilCanonicalEdgeMass r k i := by ring
      _ = _ := by rw [finiteWeilBinomialParity_sq, mul_one]
  simp_rw [hedge] at hp
  rw [← Finset.mul_sum] at hp
  linarith

end RHTower
