import GaloisForLFunctions.RHTower.Deninger.DeningerCharacteristicZeroTensorReduced
import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelPairTensorEquiv
import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelUniversalQuotient

/-!
# Reduction of Hazewinkel multiplication to one-stage primeness

The characteristic-zero tensor theorem removes Hazewinkel's tensor-reducedness obligation.  For
positive stages, primeness of the two individual Hankel determinantal ideals makes their quotient
rings characteristic-zero domains; their tensor product over `ℤ` is therefore reduced.  The
explicit pair-quotient equivalence then supplies reducedness of the universal multiplication
quotient and hence corrected multiplication over every commutative target ring, including rings
with nilpotents.

Thus the only remaining external input is the one-stage theorem
`(deningerHazewinkelIdeal n).IsPrime`.
-/

namespace RHTower

noncomputable section

/-- Positive Hazewinkel stage tensors are reduced as soon as the two one-stage ideals are prime. -/
theorem deningerHazewinkelStageTensor_isReduced_of_isPrime
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hpn : (deningerHazewinkelIdeal n).IsPrime)
    (hpm : (deningerHazewinkelIdeal m).IsPrime) :
    IsReduced (DeningerHazewinkelStageTensor n m) := by
  letI : (deningerHazewinkelIdeal n).IsPrime := hpn
  letI : (deningerHazewinkelIdeal m).IsPrime := hpm
  letI : IsDomain (DeningerHazewinkelStageQuotient n) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hpn
  letI : IsDomain (DeningerHazewinkelStageQuotient m) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hpm
  letI : CharZero (DeningerHazewinkelStageQuotient n) :=
    deningerHazewinkelQuotient_charZero n hn
  letI : CharZero (DeningerHazewinkelStageQuotient m) :=
    deningerHazewinkelQuotient_charZero m hm
  exact deningerCharZeroDomainTensorInt_isReduced

/-- Positive universal pair quotients are reduced under the two one-stage primeness statements. -/
theorem deningerHazewinkelPairQuotient_isReduced_of_isPrime
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hpn : (deningerHazewinkelIdeal n).IsPrime)
    (hpm : (deningerHazewinkelIdeal m).IsPrime) :
    IsReduced (DeningerHazewinkelPairQuotient n m) := by
  rw [deningerHazewinkelPairQuotient_isReduced_iff_stageTensor]
  exact deningerHazewinkelStageTensor_isReduced_of_isPrime n m hn hm hpn hpm

/-- Under one-stage Hazewinkel primeness, corrected multiplication holds over every commutative
target ring; no reducedness assumption is imposed on the target. -/
theorem deninger_hankelRankLT_mul_corrected_of_hazewinkel_isPrime
    {A : Type*} [CommRing A] {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hpn : (deningerHazewinkelIdeal n).IsPrime)
    (hpm : (deningerHazewinkelIdeal m).IsPrime)
    {u v : DeningerBigWittAdditive A}
    (hu : DeningerBigWittHankelRankLT (n + 1) u)
    (hv : DeningerBigWittHankelRankLT (m + 1) v) :
    DeningerBigWittHankelRankLT
      (deningerCorrectedWittMulStageBound n m + 1)
      (deningerBigWittMul u v) := by
  letI : IsReduced (DeningerHazewinkelPairQuotient n m) :=
    deningerHazewinkelPairQuotient_isReduced_of_isPrime n m hn hm hpn hpm
  exact deninger_hankelRankLT_mul_corrected_of_pairQuotient_isReduced hu hv

end

end RHTower
