import GaloisForLFunctions.RHTower.MeixnerRootPrimeLaplaceValueFrame

open Filter Topology

namespace RHTower

noncomputable section

/-- A finite prime-Laplace Gram bound along any positive source scale converging to zero
forces the reflected seam root onto the critical line. -/
theorem meixnerPrimeSeamFiniteGram_cofinal_forces_re_eq_half
    {theta : ℕ → ℝ} (htheta_pos : ∀ n, 0 < theta n)
    (htheta_zero : Tendsto theta atTop (nhds 0))
    {rho : ℂ} (hrho : 0 < rho.re ∧ rho.re < 1)
    (hgram : ∀ n, ∃ B : ℝ,
      meixnerPrimeSeamFiniteGramBound (theta n) (htheta_pos n).le rho B) :
    rho.re = 1 / 2 := by
  by_contra hcritical
  let gap : ℝ := |2 * rho.re - 1|
  have hgap_ne : 2 * rho.re - 1 ≠ 0 := by
    intro hzero
    apply hcritical
    linarith
  have hgap_pos : 0 < gap := by
    exact abs_pos.mpr hgap_ne
  obtain ⟨n, hn⟩ :=
    (htheta_zero.eventually (eventually_lt_nhds hgap_pos)).exists
  obtain ⟨B, hB⟩ := hgram n
  have hthreshold :=
    (exists_finiteGramBound_iff_meixnerRootThreshold (htheta_pos n) hrho).mp ⟨B, hB⟩
  rcases hthreshold with hhalf | hwide
  · exact hcritical hhalf
  · exact (not_lt_of_ge hn.le) (by simpa [gap] using hwide)

end

end RHTower
