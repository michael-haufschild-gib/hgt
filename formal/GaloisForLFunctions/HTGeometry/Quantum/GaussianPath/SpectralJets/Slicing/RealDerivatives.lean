import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.CoordinateCalculus
import GaloisForLFunctions.HTGeometry.SortedEigenbranchAnalytic

/-! # Restriction of holomorphic mixed derivatives to real coordinates -/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n : ℕ}

/-- Vary the indicated real coordinate, holding all other couplings fixed. -/
def realLine (x : Fin n → ℝ) (i : Fin n) (t : ℝ) (j : Fin n) : ℝ := x j + if j=i then t else 0

private theorem realLine_tendsto (x : Fin n → ℝ) (i : Fin n) :
    Tendsto (realLine x i) (𝓝 0) (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hj : j=i
  · have h : Continuous (fun t : ℝ => x j + t) := continuous_const.add continuous_id
    simpa [realLine,hj] using h.tendsto 0
  · simp [realLine,hj]

private theorem realEmbed_realLine (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    realEmbed (realLine x i t) = coordLine (realEmbed x) i (t:ℂ) := by
  funext j
  by_cases hj : j=i <;> simp [realEmbed,realLine,coordLine,hj]

/-- Real coordinate derivatives with the outermost letter first. -/
def realMixed : List (Fin n) → ((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → ℝ
  | [], g => g
  | i::w, g => fun x => deriv (fun t => realMixed w g (realLine x i t)) 0

/-- All mixed derivatives agree when a holomorphic germ restricts to a real germ. -/
theorem mixed_of_real_germ {x : Fin n → ℝ} {f : (Fin n → ℂ) → ℂ} {g : (Fin n → ℝ) → ℝ}
    (hf : AnalyticAt ℂ f (realEmbed x))
    (hg : (fun y => f (realEmbed y)) =ᶠ[𝓝 x] fun y => (g y : ℂ)) (w : List (Fin n)) :
    mixed w f (realEmbed x) = (realMixed w g x : ℂ) := by
  induction w generalizing x with
  | nil => exact hg.self_of_nhds
  | cons i w ih =>
    let F (t : ℝ) := realMixed w g (realLine x i t)
    let A := mixed (i::w) f (realEmbed x)
    have he : ∀ᶠ y in 𝓝 x, mixed w f (realEmbed y) = (realMixed w g y : ℂ) := by
      filter_upwards [(continuous_realEmbed.tendsto x) hf.eventually_analyticAt,hg.eventually_nhds]
        with y hy hgen
      exact ih hy hgen
    have hC : HasDerivAt (fun t => (F t : ℂ)) A 0 := by
      have h := hasDerivAt_next_mixed hf i w
      have h₀ : HasDerivAt (fun t : ℝ => mixed w f (coordLine (realEmbed x) i (t:ℂ))) A 0 := by
        exact HasDerivAt.comp_ofReal (e := fun t : ℂ => mixed w f (coordLine (realEmbed x) i t))
          (z := 0) (by simpa only [Complex.ofReal_zero] using h)
      apply h₀.congr_of_eventuallyEq
      filter_upwards [(realLine_tendsto x i) he] with t ht
      exact (by simpa only [F,realEmbed_realLine] using ht.symm)
    have hR : HasDerivAt F A.re 0 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hC
    exact (hC.unique hR.ofReal_comp).trans (congrArg Complex.ofReal hR.deriv.symm)

#print axioms mixed_of_real_germ
end
end GaloisForLFunctions.HTGeometry.SpectralJets
