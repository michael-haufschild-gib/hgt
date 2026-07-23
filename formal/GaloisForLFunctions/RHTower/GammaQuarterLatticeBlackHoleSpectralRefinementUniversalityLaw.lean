import GaloisForLFunctions.HTGeometry.BlackHoleDressedLogSpectralClock
import GaloisForLFunctions.HTGeometry.PolygammaMultiplication
import GaloisForLFunctions.RHTower.GammaRealConnectionSpectralHankel

/-!
# Quarter-lattice spectral refinement between the central Gamma connection and black-hole clock

Gauss multiplication and the Gamma/Bose moment realization jointly give an exact refinement law:
the `n` shifted reciprocal-energy sectors sum to the `n`-dilated integer sector.  At `n = 4`,
the quarter-shift sector is the normalized central real-Gamma connection jet, while the integer
sector is the normalized Schwarzschild far-zone jet.  The other three residue sectors are a
positive, scale-independent complement.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- **Gamma/Bose lattice-refinement law.**  Every positive shifted reciprocal-energy moment
splits into `n` residue sectors, and their sum is the `n^(m+2)` dilation of the original moment. -/
theorem gammaBoseMoment_latticeRefinement
    (m : ℕ) {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    ∑ k ∈ Finset.range n,
        HTGeometry.gammaBoseMoment ((s + k) / n) m =
      (n : ℝ) ^ (m + 2) * HTGeometry.gammaBoseMoment s m := by
  have hregular : ∀ p : ℕ, (s : ℂ) ≠ -(p : ℂ) := by
    intro p hp
    have hre := congrArg Complex.re hp
    norm_num at hre
    have hpnonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith
  have hmul := GaloisForLFunctions.polygamma_multiplication m hn hregular
  let C : ℂ := (-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero (m + 1))
  have hleft :
      (∑ k ∈ Finset.range n,
          iteratedDeriv (m + 1) Complex.digamma (((s : ℂ) + k) / n)) =
        C * (∑ k ∈ Finset.range n,
          (HTGeometry.gammaBoseMoment ((s + k) / n) m : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have harg : 0 < (s + (k : ℝ)) / (n : ℝ) := by positivity
    have hvalue := HTGeometry.iteratedDeriv_digamma_eq_gammaBoseMoment harg m
    convert hvalue using 1
    all_goals push_cast
    all_goals ring
  have hright :
      (n : ℂ) ^ (m + 2) * iteratedDeriv (m + 1) Complex.digamma (s : ℂ) =
        C * ((n : ℂ) ^ (m + 2) *
          (HTGeometry.gammaBoseMoment s m : ℂ)) := by
    rw [HTGeometry.iteratedDeriv_digamma_eq_gammaBoseMoment hs m]
    dsimp [C]
    ring
  rw [hleft, hright] at hmul
  have hcomplex :
      (∑ k ∈ Finset.range n,
          (HTGeometry.gammaBoseMoment ((s + k) / n) m : ℂ)) =
        (n : ℂ) ^ (m + 2) * (HTGeometry.gammaBoseMoment s m : ℂ) :=
    mul_left_cancel₀ hC hmul
  exact_mod_cast hcomplex

/-- The three non-quarter residue sectors complementary to the central real-Gamma connection. -/
def gammaQuarterLatticeComplementMoment (m : ℕ) : ℝ :=
  HTGeometry.gammaBoseMoment (1 / 2) m +
    HTGeometry.gammaBoseMoment (3 / 4) m +
      HTGeometry.gammaBoseMoment 1 m

/-- **Central-Gamma/black-hole spectral-refinement universality law.**  At every jet order and
for every black-hole scale convention, the central real-Gamma connection plus its three positive
quarter-lattice complement sectors equals the four-dilated Schwarzschild far-zone clock. -/
theorem gammaRealConnection_add_quarterComplement_eq_dilatedBlackHoleClock
    (scaleLog : ℂ) (m : ℕ) :
    normalizedGammaRealConnectionJet m + gammaQuarterLatticeComplementMoment m =
      (4 : ℝ) ^ (m + 2) *
        HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m := by
  rw [normalizedGammaRealConnectionJet_eq_quarterMoment,
    HTGeometry.normalizedBlackHoleFarZoneJet_eq_gammaBoseMoment]
  have h := gammaBoseMoment_latticeRefinement m (n := 4) (s := 1)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  simpa [gammaQuarterLatticeComplementMoment, add_assoc] using h

end

end RHTower
