import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.LowValue
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.SignTarget
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare
def boundaryLowCore76 (h s : ℂ) : ℂ :=
  (((((h^(6-6:ℕ) * (s ^ Nat.rawCast 1 * NNRat.rawCast 104096251904 531441)) + (h^(6-6:ℕ) * (s ^ Nat.rawCast 2 * NNRat.rawCast 336723968 6561))) + ((h^(6-6:ℕ) * (s ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 1301807104) 531441)) + (h^(7-6:ℕ) * (s ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 1304204238848) 4782969)))) + (((h^(7-6:ℕ) * (s ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 47163277312) 1594323)) + (h^(7-6:ℕ) * (s ^ Nat.rawCast 3 * NNRat.rawCast 1592262656 1594323))) + ((h^(8-6:ℕ) * (s ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 23604740096) 4782969)) + ((h^(8-6:ℕ) * (s ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 3967516672) 1594323)) + (h^(8-6:ℕ) * (s ^ Nat.rawCast 4 * NNRat.rawCast 692584448 1594323)))))) + ((((h^(9-6:ℕ) * (s ^ Nat.rawCast 3 * NNRat.rawCast 40742912000 4782969)) + (h^(9-6:ℕ) * (s ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 4044161024) 4782969))) + ((h^(10-6:ℕ) * (s ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 51636723712) 14348907)) + (h^(10-6:ℕ) * (s ^ Nat.rawCast 4 * NNRat.rawCast 2856648704 14348907)))) + (((h^(10-6:ℕ) * (s ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 92569600) 4782969)) + (h^(11-6:ℕ) * (s ^ Nat.rawCast 4 * NNRat.rawCast 1094238208 4782969))) + ((h^(11-6:ℕ) * (s ^ Nat.rawCast 5 * NNRat.rawCast 323993600 4782969)) + ((h^(12-6:ℕ) * (s ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 1133977600) 14348907)) + (h^(13-6:ℕ) * (s ^ Nat.rawCast 5 * NNRat.rawCast 3968921600 129140163)))))))

theorem boundaryLowCore76_factor (h s : ℂ) :
    boundaryLowValue76 h s=h^6*boundaryLowCore76 h s := by
  rw [(boundaryLowValue76Norm h s).property]
  change (h ^ Nat.rawCast 6 * (s ^ Nat.rawCast 1 * NNRat.rawCast 104096251904 531441) +
      (h ^ Nat.rawCast 6 * (s ^ Nat.rawCast 2 * NNRat.rawCast 336723968 6561) +
        (h ^ Nat.rawCast 6 * (s ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 1301807104) 531441) +
          (h ^ Nat.rawCast 7 * (s ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 1304204238848) 4782969) +
            (h ^ Nat.rawCast 7 * (s ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 47163277312) 1594323) +
              (h ^ Nat.rawCast 7 * (s ^ Nat.rawCast 3 * NNRat.rawCast 1592262656 1594323) +
                (h ^ Nat.rawCast 8 * (s ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 23604740096) 4782969) +
                  (h ^ Nat.rawCast 8 * (s ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 3967516672) 1594323) +
                    (h ^ Nat.rawCast 8 * (s ^ Nat.rawCast 4 * NNRat.rawCast 692584448 1594323) +
                      (h ^ Nat.rawCast 9 * (s ^ Nat.rawCast 3 * NNRat.rawCast 40742912000 4782969) +
                        (h ^ Nat.rawCast 9 * (s ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 4044161024) 4782969) +
                          (h ^ Nat.rawCast 10 * (s ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 51636723712) 14348907) +
                            (h ^ Nat.rawCast 10 * (s ^ Nat.rawCast 4 * NNRat.rawCast 2856648704 14348907) +
                              (h ^ Nat.rawCast 10 * (s ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 92569600) 4782969) +
                                (h ^ Nat.rawCast 11 * (s ^ Nat.rawCast 4 * NNRat.rawCast 1094238208 4782969) +
                                  (h ^ Nat.rawCast 11 * (s ^ Nat.rawCast 5 * NNRat.rawCast 323993600 4782969) +
                                    (h ^ Nat.rawCast 12 *
                                        (s ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 1133977600) 14348907) +
                                      (h ^ Nat.rawCast 13 * (s ^ Nat.rawCast 5 * NNRat.rawCast 3968921600 129140163) +
                                        0))))))))))))))))))=h^6*boundaryLowCore76 h s
  dsimp only [boundaryLowCore76]
  norm_num
  ring

def boundaryRegularCore76 (h s : ℂ) : ℂ :=
  boundaryLowCore76 h s+boundaryReHigh76 h (nonlinearBoundaryR h s)+
    nonlinearBoundaryZ h s*boundaryImHigh76 h (nonlinearBoundaryR h s)

theorem boundaryCompact_regularization76 (h s : ℂ) :
    boundaryCompactA75 h (nonlinearBoundaryR h s)+
      h*nonlinearBoundaryZ h s*boundaryCompactB75 h (nonlinearBoundaryR h s)=
        h^6*boundaryRegularCore76 h s := by
  rw [boundaryReCompleteSplit76,boundaryImCompleteSplit76]
  have hl := boundaryLowCore76_factor h s
  dsimp only [boundaryLowValue76] at hl
  dsimp only [boundaryRegularCore76]
  linear_combination hl

theorem boundaryRegularCore76_source {h : ℂ} (hh : h≠0) (s u : ℂ)
    (hv : nonlinearBoundaryV h s≠0) :
    (((6:ℂ)^24*24^9)⁻¹)*eval (basePoint h s u) reducedNonlinearBoundaryCore=
      boundaryRegularCore76 h s := by
  apply mul_left_cancel₀ (pow_ne_zero 6 hh)
  have hc := reducedBoundaryCore_compact76 hh s u hv
  rw [boundaryCompact_regularization76] at hc
  simpa only [mul_assoc] using hc

end
end HTGeometry.ThetaRatioInfinity
