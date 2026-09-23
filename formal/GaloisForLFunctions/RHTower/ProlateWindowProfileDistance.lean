import GaloisForLFunctions.RHTower.ProlateGroundTotalMass

/-!
# Window distance of the normalized prolate profile to the Gaussian

The window comparison already available in the corpus is stated for the *square* of the profile,
because that is what the mass computation needs.  The transfer of the profile integral itself needs
the unsquared statement, which is the first half of the same argument: the Grönwall envelope
controls the sup distance on the half window, and evenness extends it to the full window.

* `prolateWindowDistEnvelope` : the Grönwall envelope alone, without the squaring and length factors.
* `prolateGround_windowDist_bound` : the profile is within that envelope of the Gaussian on the
  whole window.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The Grönwall envelope for the window distance of the profile to the Gaussian. -/
def prolateWindowDistEnvelope (c mu K : ℝ) : ℝ :=
  ((prolateWindowEpsP c mu K 0 + prolateWindowEpsQ c K) * prolateWindowPhaseBound K
      / max 1 (hermiteWindowBound K 0))
    * (Real.exp (max 1 (hermiteWindowBound K 0) * (K - 0)) - 1)

theorem tendsto_prolateWindowDistEnvelope {ι : Type*} {L : Filter ι} {mu c : ι → ℝ} {K : ℝ}
    (hmu : Tendsto mu L (𝓝 1)) (hc : Tendsto c L atTop) :
    Tendsto (fun i => prolateWindowDistEnvelope (c i) (mu i) K) L (𝓝 0) := by
  refine tendsto_prolateWindow_envelope (n := 0) (B := prolateWindowPhaseBound K) ?_ hc
  simpa using hmu

/-- **Window distance of the normalized profile to the Gaussian.**  On the whole window the
normalized prolate profile differs from `e^{−x²/2}` by at most the Grönwall envelope. -/
theorem prolateGround_windowDist_bound
    {c mu chi lam K : ℝ} {Phi : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hne : Phi ≠ 0) (heven : Function.Even Phi) (hlam : lam ≠ 0)
    (hband : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hmuval : mu = c * radialSeparationRatio c chi)
    (hP : prolateWindowEpsP c mu K 0 ≤ 1) (hQ : prolateWindowEpsQ c K ≤ 1) :
    ∀ x ∈ Icc (-K) K,
      |normalizedProlateProfile c Phi x - gaussianProfile x|
        ≤ prolateWindowDistEnvelope c mu K := by
  obtain ⟨hu, hu', hequ0, hval0, hval0'⟩ :=
    normalizedProlate_window_package (K := K) hK hcK hsm hne heven hlam hband heig
  have hequ : ∀ x ∈ Icc (0 : ℝ) K,
      normalizedProlateDeriv2 c Phi x
        = rescaledProlateP c mu x * normalizedProlateProfile c Phi x
          + rescaledProlateQ c x * normalizedProlateDeriv c Phi x := by
    rw [hmuval]
    exact hequ0
  have hB : ∀ x ∈ Icc (0 : ℝ) K,
      max |normalizedProlateProfile c Phi x| |normalizedProlateDeriv c Phi x|
        ≤ prolateWindowPhaseBound K :=
    normalizedProlate_phase_le hK hcK hu hu' hequ hval0 hval0' hP hQ
  have hgron := prolateProfile_window_gaussian_dist_le (c := c) (mu := mu) (K := K)
    (B := prolateWindowPhaseBound K) hK hcK hu hu' hequ hB hval0 hval0'
  have hdist0 : ∀ x ∈ Icc (0 : ℝ) K,
      |normalizedProlateProfile c Phi x - gaussianProfile x|
        ≤ prolateWindowDistEnvelope c mu K := by
    intro x hx
    exact le_trans (le_max_left _ _) (hgron x hx)
  have heu : Function.Even (normalizedProlateProfile c Phi) :=
    even_normalizedProlateProfile heven
  exact abs_sub_le_of_even_window heu hdist0

end GaloisForLFunctions.RHTower

end
