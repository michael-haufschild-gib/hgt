import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTwoAtomAffineEvenFour
import GaloisForLFunctions.HTGeometry.TwoAtomAffineEvenFourReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomCentralFactorial
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeFluxSplit
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSignedPoissonAtoms

/-!
# Literal two-atom affine energy

Exact atom dilation makes the pure second-atom energy a nonnegative shifted
first-atom energy. The other three ordered pairs give the affine radial
moments at every even order, preserving their literal Gaussian normalization.
-/
namespace RHTower
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
open HTGeometry.SignedPoisson

private theorem shifted_second_scale (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 (x+Real.log 2) =
      4*thetaCuspSingleAtomReflectionScale 1 x := by
  have he : Real.exp (2*Real.log 2) = 4 := by
    rw [show (2 : ℝ)*Real.log 2=Real.log 2+Real.log 2 by ring,Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  unfold thetaCuspSingleAtomReflectionScale
  rw [show (2 : ℝ)*(x+Real.log 2)=2*x+2*Real.log 2 by ring,Real.exp_add,he]
  norm_num
  ring

private theorem atom_two_shift (x : ℝ) :
    thetaCuspSourceTerm x 2 = (2 : ℝ)^(-(1/2 : ℝ))*thetaCuspSourceTerm (x+Real.log 2) 1 := by
  have h := invSqrt_mul_thetaCuspSourceTerm_shift (q:=2) (by norm_num) 1 x
  simpa only [Nat.mul_one,Nat.cast_ofNat] using h.symm

/-- Exact shifted first-atom formula for the full pure second-atom reflection jet. -/
theorem thetaCuspSecondPairReflectionJet_eq_shift (n : ℕ) (x : ℝ) :
    thetaCuspAtomPairReflectionJet n 2 2 x =
      ((2 : ℝ)^(-(1/2 : ℝ)))^(2 : ℕ)*thetaCuspFirstAtomReflectionJet n (x+Real.log 2) := by
  have hf : (fun t : ℝ => thetaCuspSourceTerm (x+t) 2*thetaCuspSourceTerm (x-t) 2) =
      fun t : ℝ => ((2 : ℝ)^(-(1/2 : ℝ)))^(2 : ℕ)*
        (thetaCuspSourceTerm ((x+Real.log 2)+t) 1*thetaCuspSourceTerm ((x+Real.log 2)-t) 1) := by
    funext t
    rw [atom_two_shift,atom_two_shift,
      show x+t+Real.log 2=(x+Real.log 2)+t by ring,
      show x-t+Real.log 2=(x+Real.log 2)-t by ring]
    ring
  unfold thetaCuspAtomPairReflectionJet thetaCuspFirstAtomReflectionJet
  rw [hf,iteratedDeriv_const_mul_field]

/-- The complete pure second atom contributes a nonnegative degree-six energy. -/
theorem thetaCuspSecondPairEvenEnergy_nonneg {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4,
      c i*((-1 : ℝ)^(i.val+j.val)*thetaCuspAtomPairReflectionJet (2*(i.val+j.val)) 2 2 x)*c j := by
  have hscale : 7/2 ≤ thetaCuspSingleAtomReflectionScale 1 (x+Real.log 2) := by
    rw [shifted_second_scale]
    linarith
  have hE := firstAtomEvenEnergy_lower_of_seven_halves_le hscale c
  have hnon : 0 ≤ (196 : ℝ)*thetaCuspSourceTerm (x+Real.log 2) 1^(2 : ℕ)*
      (8*thetaCuspSingleAtomReflectionScale 1 (x+Real.log 2))^(6 : ℕ)*(c 3)^(2 : ℕ) := by positivity
  have hn : 0 ≤ firstAtomEvenEnergy (x+Real.log 2) c := hnon.trans hE
  have he : (∑ i : Fin 4, ∑ j : Fin 4,
      c i*((-1 : ℝ)^(i.val+j.val)*thetaCuspAtomPairReflectionJet (2*(i.val+j.val)) 2 2 x)*c j) =
      ((2 : ℝ)^(-(1/2 : ℝ)))^(2 : ℕ)*firstAtomEvenEnergy (x+Real.log 2) c := by
    unfold firstAtomEvenEnergy firstAtomSignedMoment
    simp only [thetaCuspSecondPairReflectionJet_eq_shift,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact mul_nonneg (sq_nonneg _) hn


private theorem signed_pair_eq_radial (a b k : ℕ) (x : ℝ) :
    (-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) a b x =
      4*(thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x)*
        Real.exp (x-thetaCuspSingleAtomReflectionScale a x-thetaCuspSingleAtomReflectionScale b x)*
        (thetaPairRadialEvenPolynomial
          (thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x) k).eval
          (thetaCuspSingleAtomReflectionScale a x+thetaCuspSingleAtomReflectionScale b x) := by
  unfold thetaCuspAtomPairReflectionJet
  rw [thetaCuspAtomPairEvenJet_eq_radial]
  have he : (-1 : ℝ)^k*(-1 : ℝ)^k = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℝ)^k*(-1 : ℝ)^k)*
      (4*(thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x)*
        Real.exp (x-thetaCuspSingleAtomReflectionScale a x-thetaCuspSingleAtomReflectionScale b x)*
        (thetaPairRadialEvenPolynomial
          (thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x) k).eval
          (thetaCuspSingleAtomReflectionScale a x+thetaCuspSingleAtomReflectionScale b x)) := by ring
    _ = _ := by rw [he,one_mul]

/-- The affine moment retains exactly the first pair and both unequal pairs at every order. -/
theorem thetaCuspTwoAtomSignedEvenJet_eq_affine_add_second (k : ℕ) (x : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    (-1 : ℝ)^k*thetaCuspTwoAtomReflectionJet (2*k) x =
      4*q^(2 : ℕ)*Real.exp (x-2*q)*thetaCuspTwoAtomAffineEvenMoment k q (Real.exp (-3*q))+
        (-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) 2 2 x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hs : thetaCuspSingleAtomReflectionScale 2 x = 4*q := by
    dsimp [thetaCuspSingleAtomReflectionScale,q]
    norm_num
    ring
  have h11 := signed_pair_eq_radial 1 1 k x
  have h12 := signed_pair_eq_radial 1 2 k x
  have h21 := signed_pair_eq_radial 2 1 k x
  change (-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) 1 1 x =
    4*(q*q)*Real.exp (x-q-q)*(thetaPairRadialEvenPolynomial (q*q) k).eval (q+q) at h11
  rw [hs] at h12 h21
  change (-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) 1 2 x =
    4*(q*(4*q))*Real.exp (x-q-4*q)*(thetaPairRadialEvenPolynomial (q*(4*q)) k).eval (q+4*q) at h12
  change (-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) 2 1 x =
    4*((4*q)*q)*Real.exp (x-4*q-q)*(thetaPairRadialEvenPolynomial ((4*q)*q) k).eval (4*q+q) at h21
  rw [show q*q=q^(2 : ℕ) by ring,show q+q=2*q by ring,show x-q-q=x-2*q by ring] at h11
  rw [show q*(4*q)=4*q^(2 : ℕ) by ring,show q+4*q=5*q by ring,
    show x-q-4*q=x-5*q by ring] at h12
  rw [show (4*q)*q=4*q^(2 : ℕ) by ring,show 4*q+q=5*q by ring,
    show x-4*q-q=x-5*q by ring] at h21
  have he : Real.exp (x-5*q) = Real.exp (x-2*q)*Real.exp (-3*q) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [thetaCuspTwoAtomReflectionJet_eq_pairs]
  simp only [mul_add]
  rw [h11,h12,h21,he]
  change _ = 4*q^(2 : ℕ)*Real.exp (x-2*q)*thetaCuspTwoAtomAffineEvenMoment k q (Real.exp (-3*q))+_
  unfold thetaCuspTwoAtomAffineEvenMoment
  ring


/-- The Gaussian normalization times its seed square equals the literal first-atom mass. -/
theorem thetaCuspAffineGaussian_mul_seedSquare (x : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    4*q^(2 : ℕ)*Real.exp (x-2*q)*(2*q-3)^(2 : ℕ) = thetaCuspSourceTerm x 1^(2 : ℕ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have he : Real.exp (x/2-q)^(2 : ℕ) = Real.exp (x-2*q) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp only
  change 4*q^(2 : ℕ)*Real.exp (x-2*q)*(2*q-3)^(2 : ℕ) = (Real.exp (x/2-q)*(4*q^(2 : ℕ)-6*q))^(2 : ℕ)
  rw [mul_pow,he]
  ring

/-- The literal two-atom energy dominates the entire corrected affine form. -/
theorem thetaCuspTwoAtomAffineCorrectedEnergy_le {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    4*q^(2 : ℕ)*Real.exp (x-2*q)*HTGeometry.twoAtomAffineEvenFourCorrectedQuadratic
      q (Real.exp (-3*q)) (c 0) (c 1) (c 2) (c 3) ≤
    (∑ i : Fin 4, ∑ j : Fin 4,
      c i*((-1 : ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*c j)+
      1000000000000*(11/2-q)*thetaCuspSourceTerm x 1^(2 : ℕ)*(c 3)^(2 : ℕ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let z := Real.exp (-3*q)
  let C := 4*q^(2 : ℕ)*Real.exp (x-2*q)
  let S := ∑ i : Fin 4, ∑ j : Fin 4, c i*thetaCuspTwoAtomAffineEvenMoment (i.val+j.val) q z*c j
  let E := ∑ i : Fin 4, ∑ j : Fin 4,
    c i*((-1 : ℝ)^(i.val+j.val)*thetaCuspAtomPairReflectionJet (2*(i.val+j.val)) 2 2 x)*c j
  have hE : 0 ≤ E := thetaCuspSecondPairEvenEnergy_nonneg hq c
  have hsplit : (∑ i : Fin 4, ∑ j : Fin 4,
      c i*((-1 : ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)*c j) = C*S+E := by
    calc
      _ = ∑ i : Fin 4, ∑ j : Fin 4,
          (C*(c i*thetaCuspTwoAtomAffineEvenMoment (i.val+j.val) q z*c j)+
            c i*((-1 : ℝ)^(i.val+j.val)*thetaCuspAtomPairReflectionJet (2*(i.val+j.val)) 2 2 x)*c j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [thetaCuspTwoAtomSignedEvenJet_eq_affine_add_second]
        dsimp [C,q,z]
        ring
      _ = _ := by
        dsimp [S,E]
        simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have hQ : HTGeometry.twoAtomAffineEvenFourCorrectedQuadratic q z (c 0) (c 1) (c 2) (c 3) =
      S+1000000000000*(11/2-q)*(2*q-3)^(2 : ℕ)*(c 3)^(2 : ℕ) := by
    dsimp [S]
    norm_num [Fin.sum_univ_succ,HTGeometry.twoAtomAffineEvenFourCorrectedQuadratic,
      thetaCuspTwoAtomAffineEvenMoment_0_eq,thetaCuspTwoAtomAffineEvenMoment_1_eq,
      thetaCuspTwoAtomAffineEvenMoment_2_eq,thetaCuspTwoAtomAffineEvenMoment_3_eq,
      thetaCuspTwoAtomAffineEvenMoment_4_eq,thetaCuspTwoAtomAffineEvenMoment_5_eq,
      thetaCuspTwoAtomAffineEvenMoment_6_eq]
    simp only [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by rfl]
    ring
  have hmass : C*(2*q-3)^(2 : ℕ) = thetaCuspSourceTerm x 1^(2 : ℕ) := thetaCuspAffineGaussian_mul_seedSquare x
  dsimp only
  change C*HTGeometry.twoAtomAffineEvenFourCorrectedQuadratic q z (c 0) (c 1) (c 2) (c 3) ≤ _
  rw [hsplit,hQ]
  calc
    _ = C*S+1000000000000*(11/2-q)*(C*(2*q-3)^(2 : ℕ))*(c 3)^(2 : ℕ) := by ring
    _ = C*S+1000000000000*(11/2-q)*thetaCuspSourceTerm x 1^(2 : ℕ)*(c 3)^(2 : ℕ) := by rw [hmass]
    _ ≤ _ := by nlinarith only [hE]

end
end RHTower
