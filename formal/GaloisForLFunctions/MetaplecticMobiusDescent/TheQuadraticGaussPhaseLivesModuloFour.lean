/-
Portions adapted from OpenAI’s Gauss-sum formalization, Apache-2.0.
See LICENSE and NOTICE in this directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticTraceCoordinates
import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinResidueGaussianMass
import GaloisForLFunctions.MetaplecticMobiusDescent.TheDualGaussianPhaseFreezes

/-!
# The quadratic trace Gauss sum is a residue invariant modulo four

Poisson summation identifies the original and dual Gaussian Abel limits.
The dual phase is periodic modulo two, so only four residues remain.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein
open Coordinates

/-- The dual frequency lattice in the integral Eisenstein basis. -/
def dualFrequencyEquiv : ℤ × ℤ ≃ O :=
  ({ toFun := fun z => (z.1+z.2,z.1)
     invFun := fun z => (z.2,z.1-z.2)
     left_inv := by rintro ⟨k,l⟩; simp
     right_inv := by rintro ⟨k,l⟩; simp } : (ℤ × ℤ) ≃ (ℤ × ℤ)).trans
    coordinateEquiv.symm

theorem dualFrequencyEquiv_apply (z : ℤ × ℤ) :
    dualFrequencyEquiv z = eval (z.1+z.2) z.1 := rfl

theorem dualFrequency_norm_sq (z : ℤ × ℤ) :
    ‖ringComplex (dualFrequencyEquiv z)‖ ^ 2 = OscSpecial.dualQ z := by
  rw [dualFrequencyEquiv_apply, complex_norm_eval_sq]
  dsimp [OscSpecial.dualQ]
  push_cast
  ring

/-- The fixed phase of the inverse quadratic form is the trace phase modulo four. -/
theorem dualFrequency_phase (a b : ℤ) (z : ℤ × ℤ) :
    fixedDualPhase (eval a b) (dualFrequencyEquiv z) =
      Complex.exp (Complex.I * (OscSpecial.phaseAngle (a : ℝ) (b : ℝ) z : ℂ)) := by
  rw [dualFrequencyEquiv_apply, fixedDualPhase_eval]
  conv_lhs => rw [← Complex.exp_pi_div_two_mul_I, ← Complex.exp_int_mul]
  congr 1
  dsimp [OscSpecial.phaseAngle, OscSpecial.dualTrace]
  push_cast
  ring

/-- Reindexing the fixed dual Gaussian exposes its period-two residue classes. -/
theorem fixed_dual_sum_eq (a b : ℤ) (η : ℝ) :
    (∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z) =
      ∑' y : O, fixedDualPhase (eval a b) y *
        Complex.exp (-(Real.pi : ℂ) * (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
          (‖ringComplex y‖ ^ 2 : ℂ)) := by
  rw [← dualFrequencyEquiv.tsum_eq (fun y : O => fixedDualPhase (eval a b) y *
    Complex.exp (-(Real.pi : ℂ) * (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
      (‖ringComplex y‖ ^ 2 : ℂ)))]
  apply tsum_congr
  intro z
  have hnorm : (‖ringComplex (dualFrequencyEquiv z)‖ : ℂ) ^ 2 =
      (OscSpecial.dualQ z : ℂ) := by exact_mod_cast dualFrequency_norm_sq z
  rw [dualFrequency_phase, hnorm]
  dsimp [OscSpecial.dualFixedTerm, OscSpecial.dualAmp, OscSpecial.dualScale]
  rw [Complex.ofReal_exp]
  push_cast
  ring

/-- The actual quadratic trace kernel is the oscillatory binary Gaussian. -/
theorem original_kernel_eq_binary (a b x y : ℤ) (hc : eval a b ≠ 0) (η : ℝ) :
    principalTraceChar (eval a b) hc
        (Ideal.Quotient.mk (Ideal.span {eval a b}) (eval x y) ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) * (‖ringComplex (eval x y)‖ ^ 2 : ℂ)) =
      RankTwoComplex.binaryGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ)) (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (x,y) := by
  have hnorm : (‖ringComplex (eval x y)‖ : ℂ) ^ 2 =
      (x : ℂ) ^ 2 - (x : ℂ) * (y : ℂ) + (y : ℂ) ^ 2 := by
    exact_mod_cast complex_norm_eval_sq x y
  rw [principalTraceChar_square, hnorm, ← Complex.exp_add]
  dsimp [RankTwoComplex.binaryGaussian, OscSpecial.A, OscSpecial.B, OscSpecial.D,
    OscSpecial.q]
  congr 1
  push_cast
  ring

theorem original_sum_eq_binary (a b : ℤ) (hc : eval a b ≠ 0) (η : ℝ) :
    (∑' z : O, principalTraceChar (eval a b) hc
        (Ideal.Quotient.mk (Ideal.span {eval a b}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) * (‖ringComplex z‖ ^ 2 : ℂ))) =
      ∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ)) (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) z := by
  rw [← coordinateEquiv.symm.tsum_eq (fun z : O =>
    principalTraceChar (eval a b) hc (Ideal.Quotient.mk (Ideal.span {eval a b}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) * (‖ringComplex z‖ ^ 2 : ℂ)))]
  exact tsum_congr fun z => original_kernel_eq_binary a b z.1 z.2 hc η

private theorem finite_mod_two : Finite (O ⧸ Ideal.span {(2 : O)}) :=
  (Ideal.span {(2 : O)}).finiteQuotientOfFreeOfNeBot
    (fun h => (by norm_num : (2 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))

/-- Equal Abel mass in the four classes leaves their fixed phase average. -/
theorem fixed_phase_abel_limit (c : O) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      (∑' y : O, fixedDualPhase c y *
        Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (‖ringComplex y‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / (Real.sqrt 3 : ℂ)) * fixedDualAverage c)) := by
  letI : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_mod_two
  letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let rep := GaussianShiftedPartition.representative (2 : O)
  let P : O ⧸ Ideal.span {(2 : O)} → ℂ := fun r => fixedDualPhase c (rep r)
  let W (t : ℝ) (y : O) : ℂ :=
    Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (‖ringComplex y‖ ^ 2 : ℂ))
  have hP (y : O) : P (Ideal.Quotient.mk (Ideal.span {(2 : O)}) y) =
      fixedDualPhase c y :=
    fixedDualPhase_eq_of_mod_two c _ _
      (GaussianShiftedPartition.representative_spec 2 _)
  have hfiber (r : O ⧸ Ideal.span {(2 : O)}) :
      Tendsto (fun t : ℝ => (t : ℂ) * (∑' y : O, W t (rep r + 2*y)))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / (2 * (Real.sqrt 3 : ℂ)))) := by
    have h := actual_O_fiber_gaussian_mass (2 : O) (rep r) (by norm_num)
    have hcoords : coords (2 : O) = (2,0) := by
      rw [← show eval 2 0 = (2 : O) by norm_num [eval], coords_eval]
    simp only [hcoords] at h
    convert h using 1
    dsimp [W]
    push_cast
    ring
  have hsum := tendsto_finsetSum Finset.univ (fun r _ => (hfiber r).const_mul (P r))
  have hpoint (t : ℝ) (ht : 0 < t) :
      (t : ℂ) * (∑' y : O, fixedDualPhase c y * W t y) =
      ∑ r : O ⧸ Ideal.span {(2 : O)}, P r *
        ((t : ℂ) * (∑' y : O, W t (rep r + 2*y))) := by
    have hconv : Summable (fun y : O => P (Ideal.Quotient.mk (Ideal.span {(2 : O)}) y) * W t y) := by
      apply (eis_gaussian_summable ht).norm.of_norm_bounded
      intro y
      simpa only [norm_mul, hP, fixedDualPhase_norm, one_mul] using (le_refl ‖W t y‖)
    have hp := GaussianAbelPartition.tsum_periodic_weighted_partition
      (Ideal.Quotient.mk (Ideal.span {(2 : O)})) P (W t) hconv
    simp only [hP] at hp
    rw [hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [GaussianFiberEquiv.fiber_tsum 2 (by norm_num) r (rep r)
      (GaussianShiftedPartition.representative_spec 2 r) (W t)]
    ring
  have heq : (fun t : ℝ => (t : ℂ) * (∑' y : O, fixedDualPhase c y * W t y)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ∑ r : O ⧸ Ideal.span {(2 : O)}, P r *
        ((t : ℂ) * (∑' y : O, W t (rep r + 2*y)))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpoint t ht
  have hlim := hsum.congr' heq.symm
  convert hlim using 1
  congr 1
  unfold fixedDualAverage
  change (1 / (Real.sqrt 3 : ℂ)) * ((∑ r, P r) / 2) = _
  rw [← Finset.sum_mul]
  ring

/-- The fixed dual sum has its residue average as its rescaled Abel limit. -/
theorem fixed_dual_abel_limit (a b : ℤ) (hc : eval a b ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) *
        ((1 / (Real.sqrt 3 : ℂ)) * fixedDualAverage (eval a b)))) := by
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    dsimp [OscSpecial.q]
    exact_mod_cast coordinate_norm_pos a b hc
  have h := OscSpecial.abel_mass_dual_scale (a : ℝ) (b : ℝ) hq
    (fun t : ℝ => ∑' y : O, fixedDualPhase (eval a b) y *
      Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (‖ringComplex y‖ ^ 2 : ℂ)))
    _ (fixed_phase_abel_limit (eval a b))
  simpa only [fixed_dual_sum_eq] using h

/-- Poisson summation and the vanishing phase error give the dual limit of the original kernel. -/
theorem original_dual_abel_limit (a b : ℤ) (hc : eval a b ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O, principalTraceChar (eval a b) hc
        (Ideal.Quotient.mk (Ideal.span {eval a b}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) * (‖ringComplex z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ)) *
        (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) *
          ((1 / (Real.sqrt 3 : ℂ)) * fixedDualAverage (eval a b))))) := by
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    dsimp [OscSpecial.q]
    exact_mod_cast coordinate_norm_pos a b hc
  have h := abel_transfer
    (fun η : ℝ => 1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ)))
    (fun η : ℝ => ∑' z : ℤ × ℤ, OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z)
    (fun η : ℝ => ∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z)
    _ _ (OscSpecial.prefactor_tendsto hq) (fixed_dual_abel_limit a b hc)
    (OscSpecial.normalized_dual_phase_sum_error_tendsto_zero hq)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [original_sum_eq_binary, OscSpecial.oscillatory_gaussian_poisson hη hq]
  congr 2
  exact tsum_congr fun z => (OscSpecial.dualGaussian_eq_dualVarTerm hη hq z).symm

/-- The normalized quadratic trace Gauss sum is the four-residue dual average. -/
theorem normalizedQuadraticTraceGauss_eq_average (a b : ℤ) (hc : eval a b ≠ 0) :
    normalizedQuadraticTraceGauss (eval a b) hc = fixedDualAverage (eval a b) := by
  have ho := original_abel_gauss_limit (eval a b) hc
  simp only [coords_eval] at ho
  have hd := original_dual_abel_limit a b hc
  have heq := tendsto_nhds_unique ho hd
  let n := ‖ringComplex (eval a b)‖
  have hn : 0 < n := norm_pos_iff.mpr
    (fun h => hc (ringComplex_injective (by simpa using h)))
  have hq : OscSpecial.q (a : ℝ) (b : ℝ) = n ^ 2 :=
    (complex_norm_eval_sq a b).symm
  have hsqrt : Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) = n := by
    rw [hq, Real.sqrt_sq hn.le]
  have hi : (((a*a-a*b+b*b : ℤ) : ℝ)) = n ^ 2 := by
    simpa only [OscSpecial.q, Int.cast_add, Int.cast_sub, Int.cast_mul, pow_two] using hq
  change ((2 / (Real.sqrt 3 * (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ) *
      quadraticTraceGauss (eval a b) hc = _ at heq
  rw [hi, hsqrt, hq] at heq
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  change quadraticTraceGauss (eval a b) hc / (n : ℂ) = _
  apply mul_left_cancel₀ (show (2 / ((Real.sqrt 3 : ℂ) * (n : ℂ))) ≠ 0 by
    exact div_ne_zero (by norm_num) (mul_ne_zero hsC hnC))
  convert heq using 1 <;> push_cast <;> field_simp [hnC, hsC]
  all_goals ring

/-- Every nonzero modulus has an explicit quadratic trace Gauss phase modulo four. -/
theorem normalizedQuadraticTraceGauss_formula (a b : ℤ) (hc : eval a b ≠ 0) :
    normalizedQuadraticTraceGauss (eval a b) hc =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  rw [normalizedQuadraticTraceGauss_eq_average, fixedDualAverage_formula]

/-- The intrinsic normalized sum is the dual average, independently of coordinate choices. -/
theorem normalizedQuadraticTraceGauss_eq_fixedDualAverage (c : O) (hc : c ≠ 0) :
    normalizedQuadraticTraceGauss c hc = fixedDualAverage c := by
  obtain ⟨a,b,hab⟩ := exists_coordinates c
  change c = eval a b at hab
  subst c
  exact normalizedQuadraticTraceGauss_eq_average a b hc

/-- The normalized quadratic trace sum depends only on the modulus modulo four. -/
theorem normalizedQuadraticTraceGauss_eq_of_mod_four (c d : O) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) :
    normalizedQuadraticTraceGauss c hc = normalizedQuadraticTraceGauss d hd := by
  rw [normalizedQuadraticTraceGauss_eq_fixedDualAverage,
    normalizedQuadraticTraceGauss_eq_fixedDualAverage,
    fixedDualAverage_eq_of_mod_four c d h]

/-- The quadratic trace Gauss sum is positive on the principal class modulo four. -/
theorem quadraticTraceGauss_eq_norm (c : O) (hc : c ≠ 0)
    (hfour : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c = 1) :
    quadraticTraceGauss c hc = (‖ringComplex c‖ : ℂ) := by
  have h := normalizedQuadraticTraceGauss_eq_fixedDualAverage c hc
  rw [fixedDualAverage_eq_one _ hfour] at h
  have hn : (‖ringComplex c‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr
      (fun h => hc (ringComplex_injective (by simpa using h)))
  exact (div_eq_one_iff_eq hn).mp h

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.fixed_phase_abel_limit

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.original_dual_abel_limit

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.normalizedQuadraticTraceGauss_formula

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.normalizedQuadraticTraceGauss_eq_of_mod_four

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.quadraticTraceGauss_eq_norm
