import GaloisForLFunctions.HTGeometry.PolynomialSignedPoissonSourceTransform
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomScalePolynomials
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Literal theta atoms in the exact signed Poisson clock

Every atom index and every derivative order use the same source transform.
The literal pair energy is its seeded polynomial-square moment; the exact
seed becomes three shifted square moments. Both unequal pairs remain in
the retained two-atom energy. These identities leave its quantitative sign open.
-/

open Polynomial
namespace HTGeometry.SignedPoisson
noncomputable section

/-- A literal Gaussian theta-clock frame, for every polynomial clock observable. -/
def atomMomentFrame (p : ℝ) (P : ℝ[X]) (x : ℝ) : ℝ :=
  Real.exp (x/2-p*Real.exp (2*x))*(negativePoissonPolynomial P).eval (p*Real.exp (2*x))

/-- Theta differentiation is exactly multiplication by 2 J + 1/2 in the signed clock. -/
theorem hasDerivAt_atomMomentFrame (p : ℝ) (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (atomMomentFrame p P) (atomMomentFrame p (thetaClockMultiply P) x) x := by
  have hq : HasDerivAt (fun y : ℝ => p*Real.exp (2*y)) (2*(p*Real.exp (2*x))) x := by
    simpa only [mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm,id_eq] using
      (((hasDerivAt_id x).const_mul (2 : ℝ)).exp.const_mul p)
  have hg := (((hasDerivAt_id x).div_const 2).sub hq).exp
  have hp := ((negativePoissonPolynomial P).hasDerivAt (p*Real.exp (2*x))).comp x hq
  have hm := hg.mul hp
  convert hm using 1
  all_goals try rfl
  all_goals simp only [atomMomentFrame,thetaClockMultiply]
  all_goals rw [map_add,map_smul,map_smul,negativePoissonPolynomial_X_mul]
  all_goals simp only [eval_add,eval_smul,eval_mul,eval_sub,eval_X,smul_eq_mul,Pi.sub_apply,Function.comp_apply,id_eq]
  all_goals ring

/-- Every derivative retains the same polynomial clock, with no finite-order truncation. -/
theorem iteratedDeriv_atomMomentFrame (p : ℝ) (P : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (atomMomentFrame p P) = atomMomentFrame p ((thetaClockMultiply^[n]) P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih,Function.iterate_succ_apply']
    funext x
    exact (hasDerivAt_atomMomentFrame p ((thetaClockMultiply^[n]) P) x).deriv

/-- The clock construction is the actual nth theta source atom, including its full seed. -/
theorem atomMomentFrame_thetaClockSeed_eq_source (n : ℕ) (x : ℝ) :
    atomMomentFrame (Real.pi*(n : ℝ)^(2 : ℕ)) thetaClockSeed x = RHTower.thetaCuspSourceTerm x n := by
  have he : Real.exp (2*x) = Real.exp x^(2 : ℕ) := by
    rw [show 2*x=x+x by ring,Real.exp_add]
    ring
  have hq : (Real.pi*(n : ℝ)^(2 : ℕ))*Real.exp (2*x) = Real.pi*((n : ℝ)*Real.exp x)^(2 : ℕ) := by
    rw [he]
    ring
  unfold atomMomentFrame thetaClockSeed
  rw [negativePoissonPolynomial_thetaSeed]
  simp only [eval_sub,eval_mul,eval_pow,eval_ofNat,eval_X]
  rw [hq,sub_eq_add_neg,Real.exp_add]
  unfold RHTower.thetaCuspSourceTerm RHTower.thetaCuspSeed
  simp only [neg_mul]
  ring

/-- All literal theta-atom jets admit the same source-identified signed-clock formula. -/
theorem iteratedDeriv_thetaCuspSourceTerm_eq_atomMomentFrame (n k : ℕ) :
    iteratedDeriv k (fun x : ℝ => RHTower.thetaCuspSourceTerm x n) =
      atomMomentFrame (Real.pi*(n : ℝ)^(2 : ℕ)) ((thetaClockMultiply^[k]) thetaClockSeed) := by
  have he : (fun x : ℝ => RHTower.thetaCuspSourceTerm x n) =
      atomMomentFrame (Real.pi*(n : ℝ)^(2 : ℕ)) thetaClockSeed := by
    funext x
    exact (atomMomentFrame_thetaClockSeed_eq_source n x).symm
  rw [he]
  exact iteratedDeriv_atomMomentFrame _ _ _


open scoped TensorProduct ContDiff

/-- The unrestricted moment evaluated at a physical negative clock parameter. -/
def negativePoissonEvaluation (p : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  (Polynomial.leval p).comp negativePoissonPolynomial

/-- The two physical clocks remain independent in the exact paired functional. -/
def pairedNegativePoissonEvaluation (p r : ℝ) : (ℝ[X] ⊗[ℝ] ℝ[X]) →ₗ[ℝ] ℝ :=
  TensorProduct.lift
    { toFun := fun P => negativePoissonEvaluation p P • negativePoissonEvaluation r
      map_add' := fun P Q => by simp only [map_add,add_smul]
      map_smul' := fun c P => by simp only [map_smul,smul_smul,RingHom.id_apply,smul_eq_mul] }

@[simp] theorem pairedNegativePoissonEvaluation_tmul (p r : ℝ) (P Q : ℝ[X]) :
    pairedNegativePoissonEvaluation p r (P ⊗ₜ[ℝ] Q) =
      (negativePoissonPolynomial P).eval p*(negativePoissonPolynomial Q).eval r := rfl

/-- The literal theta derivative multiplier, before applying the moment. -/
def thetaClockPolynomial : ℝ[X] := (2 : ℝ) • X+(1/2 : ℝ) • 1

private theorem thetaClockMultiply_eq_mul (P : ℝ[X]) :
    thetaClockMultiply P = thetaClockPolynomial*P := by
  simp only [thetaClockMultiply,thetaClockPolynomial,smul_eq_C_mul]
  ring

/-- Iterating the actual derivative clock is ordinary polynomial multiplication. -/
theorem iterate_thetaClockMultiply (k : ℕ) (P : ℝ[X]) :
    (thetaClockMultiply^[k]) P = thetaClockPolynomial^k*P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',thetaClockMultiply_eq_mul,ih,pow_succ']
    ring

/-- Reflection subtracts the two derivative clocks. -/
def thetaPairClock : ℝ[X] ⊗[ℝ] ℝ[X] :=
  thetaClockPolynomial ⊗ₜ[ℝ] (1 : ℝ[X])-(1 : ℝ[X]) ⊗ₜ[ℝ] thetaClockPolynomial

private theorem thetaPairClock_pow_mul (n : ℕ) (P Q : ℝ[X]) :
    thetaPairClock^n*(P ⊗ₜ[ℝ] Q) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) •
        ((thetaClockPolynomial^k*P) ⊗ₜ[ℝ]
          ((-1 : ℝ)^(n-k) • (thetaClockPolynomial^(n-k)*Q))) := by
  unfold thetaPairClock
  rw [sub_eq_add_neg,← TensorProduct.tmul_neg,add_pow,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = (n.choose k : ℝ) •
        (((thetaClockPolynomial ⊗ₜ[ℝ] (1 : ℝ[X]))^k*
          ((1 : ℝ[X]) ⊗ₜ[ℝ] (-thetaClockPolynomial))^(n-k))*(P ⊗ₜ[ℝ] Q)) := by
      rw [Nat.cast_smul_eq_nsmul ℝ,nsmul_eq_mul]
      ring
    _ = _ := by
      rw [Algebra.TensorProduct.tmul_pow,Algebra.TensorProduct.tmul_pow]
      simp only [one_pow,Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
      have hpow : (-thetaClockPolynomial)^(n-k) =
          (-1 : ℝ)^(n-k) • thetaClockPolynomial^(n-k) := by
        rw [← _root_.smul_pow,neg_one_smul]
      rw [hpow,smul_mul_assoc]

/-- The reflected moment is exactly the binomial of the two physical derivative clocks. -/
theorem pairedNegativePoissonEvaluation_clock_pow (n : ℕ) (P Q : ℝ[X]) (p r : ℝ) :
    pairedNegativePoissonEvaluation p r (thetaPairClock^n*(P ⊗ₜ[ℝ] Q)) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ)*(-1 : ℝ)^(n-k)*
        (negativePoissonPolynomial ((thetaClockMultiply^[k]) P)).eval p*
        (negativePoissonPolynomial ((thetaClockMultiply^[n-k]) Q)).eval r := by
  rw [thetaPairClock_pow_mul,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [map_smul,pairedNegativePoissonEvaluation_tmul,eval_smul,
    smul_eq_mul,iterate_thetaClockMultiply]
  ring

/-- Literal reflection jet for an ordered pair of theta atoms. -/
def thetaCuspAtomPairReflectionJet (n a b : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv n (fun t : ℝ => RHTower.thetaCuspSourceTerm (x+t) a*
    RHTower.thetaCuspSourceTerm (x-t) b) 0

/-- All unequal and equal theta-atom pairs have an exact source-identified clock moment. -/
theorem thetaCuspAtomPairReflectionJet_eq_moment (n a b : ℕ) (x : ℝ) :
    thetaCuspAtomPairReflectionJet n a b x =
      Real.exp (x-RHTower.thetaCuspSingleAtomReflectionScale a x-
        RHTower.thetaCuspSingleAtomReflectionScale b x)*
      pairedNegativePoissonEvaluation
        (RHTower.thetaCuspSingleAtomReflectionScale a x)
        (RHTower.thetaCuspSingleAtomReflectionScale b x)
        (thetaPairClock^n*(thetaClockSeed ⊗ₜ[ℝ] thetaClockSeed)) := by
  have ha : ContDiff ℝ n (fun y : ℝ => RHTower.thetaCuspSourceTerm y a) :=
    (RHTower.contDiff_thetaCuspSourceAtom a).of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hb : ContDiff ℝ n (fun y : ℝ => RHTower.thetaCuspSourceTerm y b) :=
    (RHTower.contDiff_thetaCuspSourceAtom b).of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hl : ContDiffAt ℝ n (fun t : ℝ => RHTower.thetaCuspSourceTerm (x+t) a) 0 :=
    (ha.comp (contDiff_const.add contDiff_id)).contDiffAt
  have hr : ContDiffAt ℝ n (fun t : ℝ => RHTower.thetaCuspSourceTerm (x-t) b) 0 :=
    (hb.comp (contDiff_const.sub contDiff_id)).contDiffAt
  unfold thetaCuspAtomPairReflectionJet
  rw [iteratedDeriv_fun_mul hl hr,pairedNegativePoissonEvaluation_clock_pow]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hleft := congrFun (iteratedDeriv_comp_const_add k
    (fun y : ℝ => RHTower.thetaCuspSourceTerm y a) x) 0
  have hright := congrFun (iteratedDeriv_comp_const_sub (n-k)
    (fun y : ℝ => RHTower.thetaCuspSourceTerm y b) x) 0
  simp only [add_zero,sub_zero] at hleft hright
  rw [hleft,hright,iteratedDeriv_thetaCuspSourceTerm_eq_atomMomentFrame,
    iteratedDeriv_thetaCuspSourceTerm_eq_atomMomentFrame]
  simp only [atomMomentFrame,smul_eq_mul,RHTower.thetaCuspSingleAtomReflectionScale]
  have he : Real.exp (x-(Real.pi*(a : ℝ)^(2 : ℕ))*Real.exp (2*x)-
      (Real.pi*(b : ℝ)^(2 : ℕ))*Real.exp (2*x)) =
      Real.exp (x/2-(Real.pi*(a : ℝ)^(2 : ℕ))*Real.exp (2*x))*
        Real.exp (x/2-(Real.pi*(b : ℝ)^(2 : ℕ))*Real.exp (2*x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- The even test polynomial in the exact reflected clock, at any finite rank. -/
def thetaPairEvenPolynomial {N : ℕ} (c : Fin N → ℝ) : ℝ[X] ⊗[ℝ] ℝ[X] :=
  ∑ i, (c i*(-1 : ℝ)^i.val) • thetaPairClock^(2*i.val)

/-- Every literal atom-pair even quadratic form is a seeded polynomial-square moment. -/
theorem thetaCuspAtomPairEvenEnergy_eq_moment {N : ℕ} (c : Fin N → ℝ)
    (a b : ℕ) (x : ℝ) :
    (∑ i, ∑ j, c i*((-1 : ℝ)^(i.val+j.val)*
      thetaCuspAtomPairReflectionJet (2*(i.val+j.val)) a b x)*c j) =
      Real.exp (x-RHTower.thetaCuspSingleAtomReflectionScale a x-
        RHTower.thetaCuspSingleAtomReflectionScale b x)*
      pairedNegativePoissonEvaluation
        (RHTower.thetaCuspSingleAtomReflectionScale a x)
        (RHTower.thetaCuspSingleAtomReflectionScale b x)
        (thetaPairEvenPolynomial c^(2 : ℕ)*(thetaClockSeed ⊗ₜ[ℝ] thetaClockSeed)) := by
  simp_rw [thetaCuspAtomPairReflectionJet_eq_moment]
  unfold thetaPairEvenPolynomial
  rw [pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum,Finset.sum_mul,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_mul_smul_comm,smul_mul_assoc,map_smul,← pow_add]
  rw [show 2*i.val+2*j.val = 2*(i.val+j.val) by omega,pow_add]
  simp only [smul_eq_mul]
  ring

/-- Shift each of the two independent polynomial clocks. -/
def thetaPairShift (u v : ℝ) :
    (ℝ[X] ⊗[ℝ] ℝ[X]) →ₐ[ℝ] (ℝ[X] ⊗[ℝ] ℝ[X]) :=
  Algebra.TensorProduct.map (Polynomial.taylorAlgHom u) (Polynomial.taylorAlgHom v)

@[simp] theorem thetaPairShift_tmul (u v : ℝ) (P Q : ℝ[X]) :
    thetaPairShift u v (P ⊗ₜ[ℝ] Q) =
      Polynomial.taylor u P ⊗ₜ[ℝ] Polynomial.taylor v Q := rfl

/-- The full pair seed has four exact shifts, retaining both negative mixed terms. -/
theorem pairedNegativePoissonEvaluation_seed_mul (p r : ℝ) (Z : ℝ[X] ⊗[ℝ] ℝ[X]) :
    pairedNegativePoissonEvaluation p r ((thetaClockSeed ⊗ₜ[ℝ] thetaClockSeed)*Z) =
      16*p^(2 : ℕ)*r^(2 : ℕ)*pairedNegativePoissonEvaluation p r (thetaPairShift 2 2 Z)-
        24*p^(2 : ℕ)*r*pairedNegativePoissonEvaluation p r (thetaPairShift 2 1 Z)-
        24*p*r^(2 : ℕ)*pairedNegativePoissonEvaluation p r (thetaPairShift 1 2 Z)+
        36*p*r*pairedNegativePoissonEvaluation p r (thetaPairShift 1 1 Z) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp
  | tmul P Q =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul,pairedNegativePoissonEvaluation_tmul,
      thetaPairShift_tmul,negativePoissonPolynomial_thetaSeed_mul,
      eval_sub,eval_mul,eval_pow,eval_ofNat,eval_X]
    ring
  | add Z T hZ hT =>
    simp only [mul_add,map_add] at *
    linarith only [hZ,hT]

noncomputable local instance (n : ℕ) : AddCommGroup (PolyBelow n) := inferInstance

/-- A finite separated square in the source functional is exactly the proved signed square sum. -/
theorem pairedNegativePoissonEvaluation_separated_square {N : ℕ} (n m : ℕ)
    (p r : ℝ) (P : Fin N → PolyBelow n) (Q : Fin N → PolyBelow m) :
    pairedNegativePoissonEvaluation p r ((∑ i, (P i : ℝ[X]) ⊗ₜ[ℝ] (Q i : ℝ[X]))^(2 : ℕ)) =
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range m, weight (-p) k*weight (-r) l*
        (∑ i, moment n (-p) (((difference n)^k) (P i))*
          moment m (-r) (((difference m)^l) (Q i)))^(2 : ℕ) := by
  rw [← pairSquare_eq_difference_squares]
  unfold pairSquare
  rw [pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum,map_sum,Algebra.TensorProduct.tmul_mul_tmul,
    pairedNegativePoissonEvaluation_tmul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (negativePoissonPolynomial (mulBelow n n (P i) (P j) : ℝ[X])).eval p*
      (negativePoissonPolynomial (mulBelow m m (Q i) (Q j) : ℝ[X])).eval r = _
  rw [negativePoissonPolynomial_eval_eq_moment,negativePoissonPolynomial_eval_eq_moment]

private theorem thetaClockPolynomial_taylor (u : ℝ) :
    Polynomial.taylor u thetaClockPolynomial = thetaClockPolynomial+(2*u) • (1 : ℝ[X]) := by
  simp only [thetaClockPolynomial,map_add,map_smul,Polynomial.taylor_X,Polynomial.taylor_one]
  simp only [smul_eq_C_mul,map_one,C_mul,C_ofNat]
  ring

/-- Only the relative clock shift enters reflection. -/
theorem thetaPairShift_clock (u v : ℝ) :
    thetaPairShift u v thetaPairClock = thetaPairClock+(2*(u-v)) • 1 := by
  simp only [thetaPairClock,map_sub,thetaPairShift_tmul,thetaClockPolynomial_taylor,
    Polynomial.taylor_one,map_one,TensorProduct.add_tmul,TensorProduct.tmul_add,
    ← TensorProduct.smul_tmul',TensorProduct.tmul_smul,Algebra.TensorProduct.one_def]
  module

/-- Any even test has the same shifted polynomial under equal clock translations. -/
theorem thetaPairShift_evenPolynomial {N : ℕ} (c : Fin N → ℝ) (u v : ℝ) :
    thetaPairShift u v (thetaPairEvenPolynomial c) =
      ∑ i, (c i*(-1 : ℝ)^i.val) • (thetaPairClock+(2*(u-v)) • 1)^(2*i.val) := by
  simp only [thetaPairEvenPolynomial,map_sum,map_smul,map_pow,thetaPairShift_clock]

/-- The exact shifted even test uses the physical reflection-clock increment. -/
def thetaPairShiftedEvenPolynomial {N : ℕ} (c : Fin N → ℝ) (h : ℝ) :
    ℝ[X] ⊗[ℝ] ℝ[X] :=
  ∑ i, (c i*(-1 : ℝ)^i.val) • (thetaPairClock+h • 1)^(2*i.val)

/-- The literal pair seed reduces to three shifted square moments, with both signs retained. -/
theorem pairedNegativePoissonEvaluation_seed_even_square {N : ℕ}
    (c : Fin N → ℝ) (p r : ℝ) :
    pairedNegativePoissonEvaluation p r
        (thetaPairEvenPolynomial c^(2 : ℕ)*(thetaClockSeed ⊗ₜ[ℝ] thetaClockSeed)) =
      (16*p^(2 : ℕ)*r^(2 : ℕ)+36*p*r)*pairedNegativePoissonEvaluation p r (thetaPairEvenPolynomial c^(2 : ℕ))-
        24*p^(2 : ℕ)*r*pairedNegativePoissonEvaluation p r (thetaPairShiftedEvenPolynomial c 2^(2 : ℕ))-
        24*p*r^(2 : ℕ)*pairedNegativePoissonEvaluation p r (thetaPairShiftedEvenPolynomial c (-2)^(2 : ℕ)) := by
  rw [mul_comm,pairedNegativePoissonEvaluation_seed_mul]
  simp only [map_pow,thetaPairShift_evenPolynomial]
  norm_num only [sub_self,mul_zero,zero_smul,add_zero,show (2*(2-1) : ℝ) = 2 by ring,
    show (2*(1-2) : ℝ) = -2 by ring]
  change 16*p^(2 : ℕ)*r^(2 : ℕ)*pairedNegativePoissonEvaluation p r (thetaPairEvenPolynomial c^(2 : ℕ))-
      24*p^(2 : ℕ)*r*pairedNegativePoissonEvaluation p r (thetaPairShiftedEvenPolynomial c 2^(2 : ℕ))-
      24*p*r^(2 : ℕ)*pairedNegativePoissonEvaluation p r (thetaPairShiftedEvenPolynomial c (-2)^(2 : ℕ))+
      36*p*r*pairedNegativePoissonEvaluation p r (thetaPairEvenPolynomial c^(2 : ℕ)) = _
  ring

private theorem atomPair_contDiffAt (n a b : ℕ) (x : ℝ) :
    ContDiffAt ℝ n (fun t : ℝ => RHTower.thetaCuspSourceTerm (x+t) a*
      RHTower.thetaCuspSourceTerm (x-t) b) 0 := by
  have ha : ContDiff ℝ n (fun y : ℝ => RHTower.thetaCuspSourceTerm y a) :=
    (RHTower.contDiff_thetaCuspSourceAtom a).of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hb : ContDiff ℝ n (fun y : ℝ => RHTower.thetaCuspSourceTerm y b) :=
    (RHTower.contDiff_thetaCuspSourceAtom b).of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  exact ((ha.comp (contDiff_const.add contDiff_id)).mul
    (hb.comp (contDiff_const.sub contDiff_id))).contDiffAt

/-- The retained two-atom reflection contains exactly its four ordered source pairs. -/
theorem thetaCuspTwoAtomReflectionJet_eq_pairs (n : ℕ) (x : ℝ) :
    RHTower.thetaCuspTwoAtomReflectionJet n x =
      thetaCuspAtomPairReflectionJet n 1 1 x+thetaCuspAtomPairReflectionJet n 1 2 x+
        (thetaCuspAtomPairReflectionJet n 2 1 x+thetaCuspAtomPairReflectionJet n 2 2 x) := by
  have he : (fun t : ℝ => RHTower.thetaCuspTwoAtomSource (x+t)*RHTower.thetaCuspTwoAtomSource (x-t)) =
      fun t : ℝ =>
        (RHTower.thetaCuspSourceTerm (x+t) 1*RHTower.thetaCuspSourceTerm (x-t) 1+
          RHTower.thetaCuspSourceTerm (x+t) 1*RHTower.thetaCuspSourceTerm (x-t) 2)+
        (RHTower.thetaCuspSourceTerm (x+t) 2*RHTower.thetaCuspSourceTerm (x-t) 1+
          RHTower.thetaCuspSourceTerm (x+t) 2*RHTower.thetaCuspSourceTerm (x-t) 2) := by
    funext t
    unfold RHTower.thetaCuspTwoAtomSource
    ring
  unfold RHTower.thetaCuspTwoAtomReflectionJet thetaCuspAtomPairReflectionJet
  rw [he,iteratedDeriv_fun_add ((atomPair_contDiffAt n 1 1 x).add (atomPair_contDiffAt n 1 2 x))
      ((atomPair_contDiffAt n 2 1 x).add (atomPair_contDiffAt n 2 2 x)),
    iteratedDeriv_fun_add (atomPair_contDiffAt n 1 1 x) (atomPair_contDiffAt n 1 2 x),
    iteratedDeriv_fun_add (atomPair_contDiffAt n 2 1 x) (atomPair_contDiffAt n 2 2 x)]

/-- The seeded clock square with its literal pair Gaussian normalization. -/
def thetaPairSourceEvenEnergy {N : ℕ} (c : Fin N → ℝ) (a b : ℕ) (x : ℝ) : ℝ :=
  Real.exp (x-RHTower.thetaCuspSingleAtomReflectionScale a x-
    RHTower.thetaCuspSingleAtomReflectionScale b x)*
  pairedNegativePoissonEvaluation
    (RHTower.thetaCuspSingleAtomReflectionScale a x)
    (RHTower.thetaCuspSingleAtomReflectionScale b x)
    (thetaPairEvenPolynomial c^(2 : ℕ)*(thetaClockSeed ⊗ₜ[ℝ] thetaClockSeed))

/-- Exact two-atom even energy, retaining both unequal pairs at every finite rank. -/
theorem thetaCuspTwoAtomEvenEnergy_eq_four_pair_moments {N : ℕ} (c : Fin N → ℝ) (x : ℝ) :
    (∑ i, ∑ j, c i*((-1 : ℝ)^(i.val+j.val)*
      RHTower.thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*c j) =
      thetaPairSourceEvenEnergy c 1 1 x+thetaPairSourceEvenEnergy c 1 2 x+
        (thetaPairSourceEvenEnergy c 2 1 x+thetaPairSourceEvenEnergy c 2 2 x) := by
  unfold thetaPairSourceEvenEnergy
  rw [← thetaCuspAtomPairEvenEnergy_eq_moment c 1 1 x,
    ← thetaCuspAtomPairEvenEnergy_eq_moment c 1 2 x,
    ← thetaCuspAtomPairEvenEnergy_eq_moment c 2 1 x,
    ← thetaCuspAtomPairEvenEnergy_eq_moment c 2 2 x]
  simp only [thetaCuspTwoAtomReflectionJet_eq_pairs,mul_add,add_mul,Finset.sum_add_distrib]

end
end HTGeometry.SignedPoisson

