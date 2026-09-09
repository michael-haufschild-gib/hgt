import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovFibers

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix
noncomputable section

/-- Evolving a real input and then embedding in complex coordinates equals the complex matrix action. -/
theorem egbFixedChargeACriticalMarkov_complex_lift (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalMarkovMatrix n ^ m) *ᵥ (fun i => (f i : ℂ)) = fun i =>
      ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f i : ℂ) := by
  funext i
  apply Complex.ext
  · have h := congrFun (egbFixedChargeACriticalMarkov_real_action n m (fun j => (f j : ℂ))) i
    simpa only [Complex.ofReal_re] using h.symm
  · change (∑ j, (egbFixedChargeACriticalMarkovMatrix n ^ m) i j * (f j : ℂ)).im = 0
    rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro j _
    simp only [Complex.mul_im, egbFixedChargeACriticalMarkovMatrix_pow_im_zero,
      Complex.ofReal_im, mul_zero, zero_mul, add_zero]

/-- Five complex Fourier coordinates completely classify coincident outputs for real inputs. -/
theorem egbFixedChargeACriticalMarkov_real_fiber_iff (n m : ℕ)
    (f g : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal f =
      (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal g ↔
        ∀ k : Fin 5,
          egbFixedChargeACriticalFourierCoordinates n (fun i => (f i : ℂ)) (egbFixedChargeAFiveFourierModes n k) =
            egbFixedChargeACriticalFourierCoordinates n (fun i => (g i : ℂ)) (egbFixedChargeAFiveFourierModes n k) := by
  have hlift :
      (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal f =
        (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal g ↔
          (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) *ᵥ (fun i => (f i : ℂ)) =
            (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) *ᵥ (fun i => (g i : ℂ)) := by
    rw [egbFixedChargeACriticalMarkov_complex_lift, egbFixedChargeACriticalMarkov_complex_lift]
    constructor
    · intro h
      funext i
      rw [h]
    · intro h
      funext i
      have hi := congrArg Complex.re (congrFun h i)
      simpa only [Complex.ofReal_re] using hi
  exact hlift.trans (egbFixedChargeACriticalMarkovMatrix_fiber_iff n m
    (fun i => (f i : ℂ)) (fun i => (g i : ℂ)))

/-- Later finite times create no additional coincidences between real input profiles. -/
theorem egbFixedChargeACriticalMarkov_real_fiber_time_independent (n m : ℕ)
    (f g : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal f =
      (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal g ↔
        (egbFixedChargeACriticalMarkovIteratedKernel n 1).toFinitePositiveKernel.applyReal f =
          (egbFixedChargeACriticalMarkovIteratedKernel n 1).toFinitePositiveKernel.applyReal g :=
  (egbFixedChargeACriticalMarkov_real_fiber_iff n m f g).trans
    (egbFixedChargeACriticalMarkov_real_fiber_iff n 0 f g).symm

end
end GaloisForLFunctions.HTGeometry
