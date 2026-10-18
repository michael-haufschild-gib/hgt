import GaloisForLFunctions.BiScaleUncertainty.PrimeFamilyPhaseRecovery
import GaloisForLFunctions.BiScaleUncertainty.ThreePrimeMomentCollision

/-!
# Scalar sixth-moment ambiguity and explicit sixth-lag separation

At every cutoff at least fourteen, actual divisor weights supported on the
three odd-prime atoms have the same affine data, all through-five translated
moments, and the zero-lag sixth moment without sharing one common sign. A
selected sixth Fourier readout differs by exactly ten times the sixth power
of the factorial period, and some literal sixth lag therefore separates them.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
open GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Three supported coefficients inside any sufficiently large actual prime family. -/
def threePrimeCoefficients (a b c : ℝ) (p : ℕ) : ℝ :=
  (if p = 3 then a else 0) + (if p = 5 then b else 0) + (if p = 7 then c else 0)

private def primeThree (N : ℕ) : oddPrimeModes (N+14) :=
  ⟨3,by norm_num [mem_oddPrimeModes]⟩
private def primeFive (N : ℕ) : oddPrimeModes (N+14) :=
  ⟨5,by norm_num [mem_oddPrimeModes]⟩
private def primeSeven (N : ℕ) : oddPrimeModes (N+14) :=
  ⟨7,by norm_num [mem_oddPrimeModes]⟩

private theorem three_coeff_weight (N : ℕ) (a b c : ℝ) (d : ℕ) :
    primeFamilyWeight (N+14) (threePrimeCoefficients a b c) d =
      a*oddPrimeAtom 3 d+b*oddPrimeAtom 5 d+c*oddPrimeAtom 7 d := by
  have h3 (p : oddPrimeModes (N+14)) : ((p : ℕ) = 3) ↔ p = primeThree N := by
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  have h5 (p : oddPrimeModes (N+14)) : ((p : ℕ) = 5) ↔ p = primeFive N := by
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  have h7 (p : oddPrimeModes (N+14)) : ((p : ℕ) = 7) ↔ p = primeSeven N := by
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  unfold primeFamilyWeight threePrimeCoefficients
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul]
  simp_rw [h3,h5,h7]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

private theorem three_coeff_response (N : ℕ) (a b c : ℝ) (n : ℕ) :
    sieveSeq (N+14) (primeFamilyWeight (N+14) (threePrimeCoefficients a b c)) n =
      (if 2 ∣ n then 1 else -1) *
        (a*residueRow 3 (n : ZMod 3)+b*residueRow 5 (n : ZMod 5)+c*residueRow 7 (n : ZMod 7)) := by
  simp only [sieveSeq,three_coeff_weight,Finset.sum_add_distrib,← Finset.mul_sum]
  change a*sieveSeq (N+14) (oddPrimeAtom 3) n+b*sieveSeq (N+14) (oddPrimeAtom 5) n+
    c*sieveSeq (N+14) (oddPrimeAtom 7) n = _
  rw [sieveSeq_oddPrimeAtom (by decide : Nat.Prime 3) (by decide : Odd 3) (by omega),
    sieveSeq_oddPrimeAtom (by decide : Nat.Prime 5) (by decide : Odd 5) (by omega),
    sieveSeq_oddPrimeAtom (by decide : Nat.Prime 7) (by decide : Odd 7) (by omega)]
  ring

private def threePrimeModulus : Fin 3 → ℕ := ![3,5,7]

local instance (i : Fin 3) : NeZero (threePrimeModulus i) := by
  fin_cases i
  · change NeZero 3; infer_instance
  · change NeZero 5; infer_instance
  · change NeZero 7; infer_instance

private theorem three_residue_average (N : ℕ) (F : ZMod 3 → ZMod 5 → ZMod 7 → ℝ) :
    (∑ n ∈ Finset.range (N+14).factorial, F n n n) / ((N+14).factorial : ℝ) =
      (∑ x : ZMod 3, ∑ y : ZMod 5, ∑ z : ZMod 7, F x y z) / 105 := by
  have hc : Pairwise (fun i j => Nat.Coprime (threePrimeModulus i) (threePrimeModulus j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [threePrimeModulus] at *
  have hd : (∏ i, threePrimeModulus i) ∣ (N+14).factorial := by
    apply coprime_prod_dvd _ hc
    intro i
    fin_cases i
    · change 3 ∣ (N+14).factorial
      exact Nat.dvd_factorial (by decide : 0 < 3) (by omega)
    · change 5 ∣ (N+14).factorial
      exact Nat.dvd_factorial (by decide : 0 < 5) (by omega)
    · change 7 ∣ (N+14).factorial
      exact Nat.dvd_factorial (by decide : 0 < 7) (by omega)
  let e : (∀ i : Fin 3, ZMod (threePrimeModulus i)) ≃ ZMod 3 × ZMod 5 × ZMod 7 := {
    toFun := fun x => (x 0,x 1,x 2)
    invFun := fun y => Fin.cons y.1 (Fin.cons y.2.1 (Fin.cons y.2.2 (fun i => Fin.elim0 i)))
    left_inv := by intro x; funext i; fin_cases i <;> rfl
    right_inv := by intro x; rcases x with ⟨a,b,c⟩; rfl }
  have hs : (∑ x : ∀ i : Fin 3, ZMod (threePrimeModulus i), F (x 0) (x 1) (x 2)) =
      ∑ x : ZMod 3, ∑ y : ZMod 5, ∑ z : ZMod 7, F x y z := by
    calc
      _ = ∑ y : ZMod 3 × ZMod 5 × ZMod 7, F y.1 y.2.1 y.2.2 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        rw [Fintype.sum_prod_type]
  have hp : (∏ i, threePrimeModulus i) = 105 := by rw [Fin.prod_univ_three]; rfl
  have h := period_average_crt threePrimeModulus hc (N+14).factorial
    (Nat.factorial_pos _) hd (fun x => F (x 0) (x 1) (x 2))
  rw [hs,hp] at h
  exact h

/-- Literal zero-lag sixth moments of three actual prime atoms have the exact CRT formula. -/
theorem threePrime_zero_lag_sixth (N : ℕ) (a b c : ℝ) :
    translatedMoment (N+14) (primeFamilyWeight (N+14) (threePrimeCoefficients a b c))
      (fun _ : Fin 6 => 0) =
      (∑ x : ZMod 3, ∑ y : ZMod 5, ∑ z : ZMod 7,
        (a*residueRow 3 x+b*residueRow 5 y+c*residueRow 7 z)^6) / 105 := by
  have hs (n : ℕ) : (sieveSeq (N+14)
      (primeFamilyWeight (N+14) (threePrimeCoefficients a b c)) n)^6 =
      (a*residueRow 3 (n : ZMod 3)+b*residueRow 5 (n : ZMod 5)+c*residueRow 7 (n : ZMod 7))^6 := by
    rw [three_coeff_response,mul_pow]
    split_ifs <;> norm_num
  calc
    _ = (∑ n ∈ Finset.range (N+14).factorial,
        (a*residueRow 3 (n : ZMod 3)+b*residueRow 5 (n : ZMod 5)+
          c*residueRow 7 (n : ZMod 7))^6) / ((N+14).factorial : ℝ) := by
      unfold translatedMoment
      apply congrArg (fun x : ℝ => x / ((N+14).factorial : ℝ))
      apply Finset.sum_congr rfl
      intro n _
      simpa only [Nat.add_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hs n
    _ = _ := three_residue_average N
      (fun x y z => (a*residueRow 3 x+b*residueRow 5 y+c*residueRow 7 z)^6)

/-- Fixed left coefficients of the three-prime scalar-collision witness. -/
def scalarCollisionLeft : ℕ → ℝ :=
  threePrimeCoefficients 1 ((5 : ℝ)^(3 : ℝ)⁻¹) (-((2 : ℝ)^(3 : ℝ)⁻¹))

/-- Fixed right coefficients; the last two signs are reversed. -/
def scalarCollisionRight : ℕ → ℝ :=
  threePrimeCoefficients 1 (-((5 : ℝ)^(3 : ℝ)⁻¹)) ((2 : ℝ)^(3 : ℝ)⁻¹)

private theorem collision_coeff_squares (N : ℕ) (p : oddPrimeModes (N+14)) :
    scalarCollisionLeft p ^ 2 = scalarCollisionRight p ^ 2 := by
  by_cases h3 : (p : ℕ) = 3 <;> by_cases h5 : (p : ℕ) = 5 <;> by_cases h7 : (p : ℕ) = 7 <;>
    simp_all [scalarCollisionLeft,scalarCollisionRight,threePrimeCoefficients]

/-- All affine data, all through-five lags, and one zero-lag sixth observation can coincide. -/
theorem threePrime_scalar_collision (N : ℕ) :
    (∀ r s, affineMoment (N+14) (primeFamilyWeight (N+14) scalarCollisionLeft) r s =
      affineMoment (N+14) (primeFamilyWeight (N+14) scalarCollisionRight) r s) ∧
    (∀ m, m ≤ 5 → ∀ h : Fin m → ℕ,
      translatedMoment (N+14) (primeFamilyWeight (N+14) scalarCollisionLeft) h =
        translatedMoment (N+14) (primeFamilyWeight (N+14) scalarCollisionRight) h) ∧
    translatedMoment (N+14) (primeFamilyWeight (N+14) scalarCollisionLeft) (fun _ : Fin 6 => 0) =
      translatedMoment (N+14) (primeFamilyWeight (N+14) scalarCollisionRight) (fun _ : Fin 6 => 0) := by
  refine ⟨(primeFamily_affine_iff_sq _ _ _).mpr (collision_coeff_squares N),
    fun m hm h => primeFamily_through_five_eq_of_sq_eq _ _ _ (collision_coeff_squares N) m hm h,?_⟩
  unfold scalarCollisionLeft scalarCollisionRight
  rw [threePrime_zero_lag_sixth,threePrime_zero_lag_sixth]
  have hc := positive_cubic_cancellation_constants
  have h := congrArg (fun x : ℝ => x / 105)
    (three_prime_sixth_collision _ _ hc.2.2.1 hc.2.2.2)
  simpa only [one_mul,neg_mul,← sub_eq_add_neg] using h

/-- These fixed actual-family coefficients are not related by one common sign. -/
theorem threePrime_collision_not_common_sign (N : ℕ) :
    ¬((∀ p : oddPrimeModes (N+14), scalarCollisionLeft p = scalarCollisionRight p) ∨
      (∀ p : oddPrimeModes (N+14), scalarCollisionLeft p = -scalarCollisionRight p)) := by
  rintro (h | h)
  · have h5 := h (primeFive N)
    simp only [scalarCollisionLeft,scalarCollisionRight,threePrimeCoefficients,primeFive] at h5
    norm_num at h5
    have hp := positive_cubic_cancellation_constants.1
    linarith
  · have h3 := h (primeThree N)
    norm_num [scalarCollisionLeft,scalarCollisionRight,threePrimeCoefficients,primeThree] at h3

/-- The positive survivor is explicit: a chosen sixth Fourier readout separates the witnesses. -/
theorem threePrime_collision_readout_gap (N : ℕ) :
    sixthPairReadout (N+14) (primeFamilyWeight (N+14) scalarCollisionLeft) 1 3 5 -
      sixthPairReadout (N+14) (primeFamilyWeight (N+14) scalarCollisionRight) 1 3 5 =
        10*((N+14).factorial : ℝ)^6 := by
  have hL := primeFamily_sixth_readout (N+14) scalarCollisionLeft (primeThree N) (primeFive N)
  have hR := primeFamily_sixth_readout (N+14) scalarCollisionRight (primeThree N) (primeFive N)
  change sixthPairReadout (N+14) (primeFamilyWeight (N+14) scalarCollisionLeft) 1 3 5 = _ at hL
  change sixthPairReadout (N+14) (primeFamilyWeight (N+14) scalarCollisionRight) 1 3 5 = _ at hR
  rw [hL,hR]
  have hu := positive_cubic_cancellation_constants.2.2.1
  norm_num at hu
  norm_num [scalarCollisionLeft,scalarCollisionRight,threePrimeCoefficients,primeThree,primeFive]
  linear_combination (2*((N+14).factorial : ℝ)^6) * hu

/-- At least one literal sixth lag observation separates this pair that all lower degrees miss. -/
theorem threePrime_some_sixth_lag_separates (N : ℕ) :
    ∃ h : Fin 6 → ℕ,
      translatedMoment (N+14) (primeFamilyWeight (N+14) scalarCollisionLeft) h ≠
        translatedMoment (N+14) (primeFamilyWeight (N+14) scalarCollisionRight) h := by
  by_contra h
  push Not at h
  exact threePrime_collision_not_common_sign N
    ((primeFamily_sixth_iff_common_sign _ _ _).mp h)

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
