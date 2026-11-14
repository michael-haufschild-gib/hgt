import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.FiberwiseFloor

/-!
# The certificate matrix of a parity sector

`certMat S Bclean FC = 2Λ - Qtot - Bclean - diag(pertTot)`. Its quadratic form splits into the
fiberwise and archimedean pieces (`quadR_certMat`); positivity is certified by `ldlCheck`.
-/

open Real Finset
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

/-- The final certificate matrix of a parity sector. -/
def certMat (S : SectorData) (Bclean : List (List ℚ)) (FC : FiberCert) : List (List ℚ) :=
  tabQ S.K fun i j => 2 * matQ S.Λ i j - matQ (FC.Qtot S) i j - matQ Bclean i j -
    if i = j then FC.pertTot S i else 0

theorem quadR_certMat (S : SectorData) (Bclean : List (List ℚ)) (FC : FiberCert)
    (m : Fin S.K → ℝ) :
    quadR S.K (certMat S Bclean FC) m = 2 * quadR S.K S.Λ m - quadR S.K (FC.Qtot S) m -
      quadR S.K Bclean m - ∑ k : Fin S.K, (FC.pertTot S k : ℝ) * m k ^ 2 := by
  have hdiag : ∀ i : Fin S.K, ∑ j : Fin S.K,
      ((if (i : ℕ) = j then FC.pertTot S i else 0 : ℚ) : ℝ) * m i * m j =
      (FC.pertTot S i : ℝ) * m i ^ 2 := fun i => by
    rw [Finset.sum_eq_single i (fun j _ hji => by
      rw [if_neg (fun h => hji (Fin.ext h).symm)]; simp) (fun hi => absurd (Finset.mem_univ i) hi)]
    simp [sq]; ring
  simp only [quadR, certMat, matQ_tabQ _ (Fin.is_lt _) (Fin.is_lt _), Rat.cast_sub, Rat.cast_mul,
    Rat.cast_ofNat, sub_mul, Finset.sum_sub_distrib, ← hdiag, Finset.mul_sum]
  congr 1; congr 1; congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
