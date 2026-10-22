import GaloisForLFunctions.RHTower.CCM.CCMUniversalWeilSourceReconstruction
import GaloisForLFunctions.RHTower.XiWeilMultiOrbitInertia
import GaloisForLFunctions.HTGeometry.EventualNegDefFromEntrywise

/-!
# Finite-index transport from off-real Xi orbits to explicit source packets

Every fold-distinct finite family of off-real Xi sign vectors can be approximated simultaneously
by explicit, pairwise-separated continued-Cauchy prime--Gamma source packets. Their reflected
cross-Gram converges to the exact multiplicity-weighted negative diagonal of the divisor packet.
Finite-dimensional inertia stability therefore produces an eventually negative-definite source
packet block of the same prescribed size.

This upgrades one-vector source reconstruction to finite negative-index transport. It does not
assert semilocal compact-support realization of these continued-Cauchy packets.
-/

namespace RHTower

open scoped ComplexConjugate BigOperators Topology
open Complex Matrix Filter

noncomputable section

/-- Reflected Xi Weil cross-Gram of explicit separated continued-source packets. -/
def xiSeparatedPacketWeilGram {k : ℕ}
    (P : Fin k → XiSeparatedContinuedCauchyPacket) :
    Matrix (Fin k) (Fin k) ℂ := fun j l =>
  inner ℂ (xiWeilLineConjLp (P l).evaluation) (P j).evaluation

/-- Diagonal entries of the packet Gram are literal finite prime--Gamma source energies. -/
theorem xiSeparatedPacketWeilGram_diagonal_re
    {k : ℕ} (P : Fin k → XiSeparatedContinuedCauchyPacket) (j : Fin k) :
    (xiSeparatedPacketWeilGram P j j).re = (P j).sourceEnergy := by
  exact (P j).sourceEnergy_eq_hilbertQuadratic.symm

/-- `k` fold-distinct off-real Xi orbits force an eventually negative-definite `k`-packet block
made from explicit separated continued-Cauchy prime--Gamma sources. -/
theorem exists_xiSeparatedPacketWeilGram_eventually_negDef
    {k : ℕ} (s : Fin k → XiZeroCopy)
    (hfold : Function.Injective (fun j =>
      complexConjugationFold (xiSpectralPoint (s j))))
    (him : ∀ j, (xiSpectralPoint (s j)).im ≠ 0) :
    ∃ P : Fin k → ℕ → XiSeparatedContinuedCauchyPacket,
      (∀ j, Tendsto (fun n => (P j n).evaluation) atTop
        (nhds (xiWeilEvaluationLp
          (xiOffRealSignTest (xiSpectralPoint (s j)))
          (xiOffRealSignTest_squareSummable (xiSpectralPoint (s j)))))) ∧
      ∀ᶠ n in atTop, ∀ x : Fin k → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
          (xiSeparatedPacketWeilGram (fun j => P j n)).mulVec x).re < 0 := by
  have hex : ∀ j, ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (P n).evaluation) atTop
        (nhds (xiWeilEvaluationLp
          (xiOffRealSignTest (xiSpectralPoint (s j)))
          (xiOffRealSignTest_squareSummable (xiSpectralPoint (s j))))) := by
    intro j
    exact exists_separatedContinuedCauchyPackets_tendsto_evaluation
      (xiOffRealSignTest (xiSpectralPoint (s j)))
      (xiOffRealSignTest_squareSummable (xiSpectralPoint (s j)))
  choose P hP using hex
  refine ⟨P, hP, ?_⟩
  let c : Fin k → ℝ := fun j =>
    -(xiWeilOffRealOrbitMultiplicity (s j) : ℝ)
  have hc : ∀ j, c j ≤ -(1 : ℝ) := by
    intro j
    have hm : (1 : ℝ) ≤ xiWeilOffRealOrbitMultiplicity (s j) := by
      exact_mod_cast xiWeilOffRealOrbitMultiplicity_pos (s j)
    dsimp [c]
    linarith
  have htarget : xiWeilOffRealSignGram s =
      Matrix.diagonal (fun j => ((c j : ℝ) : ℂ)) := by
    rw [xiWeilOffRealSignGram_eq_diagonal s hfold him]
    congr 1
    funext j
    simp [c]
  have hentry : ∀ j l, Tendsto
      (fun n => xiSeparatedPacketWeilGram (fun i => P i n) j l)
      atTop (nhds ((Matrix.diagonal (fun i => ((c i : ℝ) : ℂ))) j l)) := by
    intro j l
    have hl := tendsto_xiWeilLineConjLp (hP l)
    have hinner : Tendsto
        (fun n => inner ℂ
          (xiWeilLineConjLp (P l n).evaluation) (P j n).evaluation)
        atTop
        (nhds (inner ℂ
          (xiWeilLineConjLp
            (xiWeilEvaluationLp
              (xiOffRealSignTest (xiSpectralPoint (s l)))
              (xiOffRealSignTest_squareSummable (xiSpectralPoint (s l)))))
          (xiWeilEvaluationLp
            (xiOffRealSignTest (xiSpectralPoint (s j)))
            (xiOffRealSignTest_squareSummable (xiSpectralPoint (s j)))))) :=
      hl.inner (hP j)
    have hlim : inner ℂ
        (xiWeilLineConjLp
          (xiWeilEvaluationLp
            (xiOffRealSignTest (xiSpectralPoint (s l)))
            (xiOffRealSignTest_squareSummable (xiSpectralPoint (s l)))))
        (xiWeilEvaluationLp
          (xiOffRealSignTest (xiSpectralPoint (s j)))
          (xiOffRealSignTest_squareSummable (xiSpectralPoint (s j)))) =
        xiWeilOffRealSignGram s j l := by
      exact inner_xiWeilLineConjLp_evaluation_eq_polarization
        (xiOffRealSignTest (xiSpectralPoint (s j)))
        (xiOffRealSignTest (xiSpectralPoint (s l)))
        (xiOffRealSignTest_squareSummable (xiSpectralPoint (s j)))
        (xiOffRealSignTest_squareSummable (xiSpectralPoint (s l)))
    rw [hlim, htarget] at hinner
    simpa only [xiSeparatedPacketWeilGram] using hinner
  have hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ j l,
      ‖xiSeparatedPacketWeilGram (fun i => P i n) j l -
        (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)) j l‖ ≤ ε := by
    intro ε hε
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro l
    filter_upwards [(hentry j l).eventually
      (Metric.ball_mem_nhds _ hε)] with n hn
    simpa [dist_eq_norm] using le_of_lt hn
  exact GaloisForLFunctions.HTGeometry.eventually_negDef_of_entrywise_tendsto_diagonal
    (fun n => xiSeparatedPacketWeilGram (fun j => P j n)) c
    zero_lt_one hc hconv

end

end RHTower
