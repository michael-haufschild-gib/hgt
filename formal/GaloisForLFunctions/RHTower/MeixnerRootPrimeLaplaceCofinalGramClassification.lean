import GaloisForLFunctions.RHTower.MeixnerRootPrimeLaplaceCofinalGramRigidity

open Filter Topology

namespace RHTower

noncomputable section

/-- A prime-Laplace seam admits packet-uniform finite interpolation bounds at every scale of a
positive cofinal root-time family exactly when its reflected seam lies on the critical line. -/
theorem meixnerPrimeSeamFiniteGram_cofinal_iff_re_eq_half
    {theta : ℕ → ℝ} (htheta_pos : ∀ n, 0 < theta n)
    (htheta_zero : Tendsto theta atTop (nhds 0))
    {rho : ℂ} (hrho : 0 < rho.re ∧ rho.re < 1) :
    (∀ n, ∃ B : ℝ,
      meixnerPrimeSeamFiniteGramBound (theta n) (htheta_pos n).le rho B) ↔
      rho.re = 1 / 2 := by
  constructor
  · exact meixnerPrimeSeamFiniteGram_cofinal_forces_re_eq_half
      htheta_pos htheta_zero hrho
  · intro hcritical n
    exact (exists_finiteGramBound_iff_meixnerRootThreshold
      (htheta_pos n) hrho).mpr (Or.inl hcritical)

end

end RHTower
