import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCuspMetricSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularMasterCurrent
import GaloisForLFunctions.RHTower.ZetaInverseHorizontal
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullLinearEinsteinEquation

/-!
# Reflection of the literal cusp metric and its Einstein source

Divisor complement preserves the completed Fourier coefficient, and evenness of
Bessel order preserves every signed Fourier mode. The completed functional equation
exchanges the two Weyl terms. Thus the full nonreal scalar cusp field is even in its
centered spectral parameter, as are its coexact covector and complete metric recipe.

At every actual Xi occurrence, reflection exchanges the original fundamental decay
rates. The frequency conversion `omega = I*s` agrees with the original QNM recipe.
For independent unchanged scalar/vector amplitudes, the two on-shell metric families
and all coefficients of their full Einstein sources are exchanged exactly.

This supplies concrete source-exchange data. It does not identify a normalized
Peierls candidate with the physical causal action, establish nonzero source coupling,
or prove fixed-clock extinction or RH.
-/

open Complex Real Finset
open scoped BigOperators
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

private theorem divisor_reflection_atom (u : ℂ) (n : D4BMPositiveIndex)
    {d : ℕ} (hd : d ∈ n.1.divisors) :
    (n.1 : ℂ)^(-u) * ((n.1 / d : ℕ) : ℂ)^(-2*(-u)) =
      (n.1 : ℂ)^u * (d : ℂ)^(-2*u) := by
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_dvd_of_pos hdvd n.2
  have hqpos := Nat.div_pos (Nat.le_of_dvd n.2 hdvd) hdpos
  have hd0 : (d : ℂ)^u ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hdpos.ne'))
  have hq0 : (((n.1 / d : ℕ) : ℂ)^u) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hqpos.ne'))
  have hn : (n.1 : ℂ) = ((n.1/d : ℕ) : ℂ)*(d : ℂ) := by
    exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  rw [hn, Complex.natCast_mul_natCast_cpow, Complex.natCast_mul_natCast_cpow]
  rw [show -2*(-u) = (2:ℂ)*u by ring, show -2*u = -((2:ℂ)*u) by ring]
  simp only [Complex.cpow_neg, Complex.cpow_ofNat_mul]
  field_simp

/-- Divisor complement preserves the actual completed Fourier coefficient. -/
theorem d4BMCompletedEisensteinWhittakerCoefficient_neg
    (u : ℂ) (n : D4BMPositiveIndex) :
    d4BMCompletedEisensteinWhittakerCoefficient (-u) n =
      d4BMCompletedEisensteinWhittakerCoefficient u n := by
  unfold d4BMCompletedEisensteinWhittakerCoefficient
  rw [← Nat.sum_div_divisors n.1 (fun d => (d : ℂ)^(-2*(-u)))]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun d hd => divisor_reflection_atom u n hd)

/-- Both spectral parameters may be reflected in the full signed zero word. -/
theorem d4BMCompletedEisensteinFullSignedZeroWord_neg
    (u nu : ℂ) (x Y : ℝ) :
    d4BMCompletedEisensteinFullSignedZeroWord (-u) (-nu) x Y =
      d4BMCompletedEisensteinFullSignedZeroWord u nu x Y := by
  simp only [d4BMCompletedEisensteinFullSignedZeroWord,
    d4BMCompletedEisensteinSignedSqrtWhittakerTail,
    d4BMCompletedEisensteinWhittakerCoefficient_neg, modifiedBesselKOrder_neg]

private theorem lambda_eq_completed_nonreal {s : ℂ} (hs : s.im ≠ 0) :
    reflectedCompletedLambda s = completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by intro h; exact hs (by rw [h]; rfl)
  rw [reflectedCompletedLambda, riemannZeta_def_of_ne_zero hs0]
  field_simp [gammaR_ne_zero_of_im_ne hs]

private theorem lambda_one_sub_nonreal {s : ℂ} (hs : s.im ≠ 0) :
    reflectedCompletedLambda (1-s) = reflectedCompletedLambda s := by
  rw [lambda_eq_completed_nonreal (by simpa using hs),
    lambda_eq_completed_nonreal hs, completedRiemannZeta_one_sub]

/-- The full literal scalar, including both Weyl terms and the infinite tail,
respects spectral reflection at every nonreal parameter. -/
theorem d4BMCompletedEisensteinScalarCuspLeg_neg (u : ℂ) (hu : u.im ≠ 0)
    (x Y : ℝ) :
    d4BMCompletedEisensteinCuspLeg .scalar (-u) x Y =
      d4BMCompletedEisensteinCuspLeg .scalar u x Y := by
  have h2 : (2*u).im ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hu
  have h12 : (1+2*u).im ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hu
  have hm := lambda_one_sub_nonreal h12
  have hp := lambda_one_sub_nonreal h2
  rw [show 1-(1+2*u) = 2*(-u) by ring] at hm
  rw [show 1-2*u = 1+2*(-u) by ring] at hp
  simp only [d4BMCompletedEisensteinCuspLeg, d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm, d4BMCompletedEisensteinCuspConstantCoefficient,
    d4BMCompletedEisensteinCuspConstantMaassFactor,
    d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign,
    Bool.false_eq_true, ite_false, ite_true, Int.cast_neg, Int.cast_one,
    mul_one, neg_one_mul, one_mul, neg_neg, d4BMCompletedEisensteinCuspTailPart,
    d4BMCompletedEisensteinFullSignedZeroWord_neg, hm, hp]
  ring

namespace D4BMLiteralCusp

theorem scalar_neg (u : ℂ) (hu : u.im ≠ 0) : scalar (-u) = scalar u := by
  funext z
  exact d4BMCompletedEisensteinScalarCuspLeg_neg u hu (z 0) (z 1)

theorem vector_neg (u : ℂ) (hu : u.im ≠ 0) : vector (-u) = vector u := by
  rw [vector, scalar_neg u hu]
  rfl

theorem perturbation_neg (omega u aS aV : ℂ) (hu : u.im ≠ 0) :
    perturbation omega (-u) aS aV = perturbation omega u aS aV := by
  simp only [perturbation, scalar_neg u hu, vector_neg u hu, scalarQ, neg_sq]


/-- The original metric recipe at the original fundamental frequency `omega = I*s`.
The scalar and vector amplitudes remain independent and unchanged. -/
def physicalPerturbation (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ) :
    D4BMActualMetricSource.MetricField :=
  perturbation (Complex.I * D4BMModularCore.physicalRate q branch)
    (D4BMGlobalAngularResponse.center q) aS aV

private theorem center_reflect (q : XiZeroCopy) :
    D4BMGlobalAngularResponse.center (xiZeroCopyReflectEquiv q) =
      -D4BMGlobalAngularResponse.center q := by
  change 1-(q.1:ℂ)-1/2 = -((q.1:ℂ)-1/2)
  ring

private theorem center_nonreal (q : XiZeroCopy) :
    (D4BMGlobalAngularResponse.center q).im ≠ 0 := by
  simpa [D4BMGlobalAngularResponse.center] using xi_divisor_support_im_ne_zero q.1

/-- Reflection exchanges the original damped time rates. -/
theorem physicalRate_reflect (q : XiZeroCopy) (branch : Bool) :
    D4BMModularCore.physicalRate (xiZeroCopyReflectEquiv q) branch =
      D4BMModularCore.physicalRate q (!branch) := by
  cases branch <;>
    simp only [D4BMModularCore.physicalRate, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true]
  · change -(1-(q.1:ℂ))-1 = (q.1:ℂ)-2
    ring
  · change 1-(q.1:ℂ)-2 = -(q.1:ℂ)-1
    ring

/-- Exact branch exchange of the complete literal metric field, not only a period. -/
theorem physicalPerturbation_reflect (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ) :
    physicalPerturbation (xiZeroCopyReflectEquiv q) branch aS aV =
      physicalPerturbation q (!branch) aS aV := by
  unfold physicalPerturbation
  rw [physicalRate_reflect, center_reflect, perturbation_neg _ _ _ _ (center_nonreal q)]

/-- The frequency conversion agrees with the original plus/minus QNM recipe. -/
theorem physicalPerturbation_eq_qnm (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ) :
    physicalPerturbation q branch aS aV =
      perturbation
        (if branch then d4BMCausalQNMMinus 0
          (radialMomentum (D4BMGlobalAngularResponse.center q))
         else d4BMCausalQNMPlus 0
          (radialMomentum (D4BMGlobalAngularResponse.center q)))
        (D4BMGlobalAngularResponse.center q) aS aV := by
  unfold physicalPerturbation
  congr 1
  cases branch <;>
    simp only [D4BMModularCore.physicalRate, Bool.false_eq_true, ite_false, ite_true,
      d4BMCausalQNMPlus, d4BMCausalQNMMinus, d4BMCausalDecay, radialMomentum,
      D4BMGlobalAngularResponse.center, Nat.cast_zero]
  all_goals ring

/-- Both concrete exchanged metric families satisfy the original linear Einstein equation. -/
theorem physicalPerturbation_first_source_zero (q : XiZeroCopy) (branch : Bool)
    (aS aV : ℂ) (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    deriv (D4BMActualMetricSource.source p (physicalPerturbation q branch aS aV) i j) 0 = 0 := by
  rw [physicalPerturbation_eq_qnm]
  cases branch
  · exact D4BMFullLinearEquation.literal_plus_source_first_zero _ _ _ p i j
  · exact D4BMFullLinearEquation.literal_minus_source_first_zero _ _ _ p i j

/-- Reflection exchanges the complete original Einstein source as a function of amplitude. -/
theorem physicalSource_reflect (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    D4BMActualMetricSource.source p
        (physicalPerturbation (xiZeroCopyReflectEquiv q) branch aS aV) i j =
      D4BMActualMetricSource.source p (physicalPerturbation q (!branch) aS aV) i j := by
  rw [physicalPerturbation_reflect]

/-- All nonlinear source coefficients inherit the same exact exchange. -/
theorem physicalSource_coefficient_reflect (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) (k : ℕ) :
    iteratedDeriv k (D4BMActualMetricSource.source p
        (physicalPerturbation (xiZeroCopyReflectEquiv q) branch aS aV) i j) 0 =
      iteratedDeriv k (D4BMActualMetricSource.source p
        (physicalPerturbation q (!branch) aS aV) i j) 0 := by
  rw [physicalSource_reflect]

end D4BMLiteralCusp
end
end RHTower
