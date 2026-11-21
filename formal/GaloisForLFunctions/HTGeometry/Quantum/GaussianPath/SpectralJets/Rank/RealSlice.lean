import GaloisForLFunctions.HTGeometry.QubitPathRecurrenceCollisionCapstone

/-! # Linear independence of holomorphic gap branches on Pauli charts -/

open Set Metric Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- The real parameters inside complex coupling space. -/
def realPoint {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℂ := x i

/-- A relation between anchored branches on an open complex subchart extends to the
whole ball. On its real slice, the real and imaginary parts of its coefficients each
give a forbidden real gap relation. -/
theorem path_gap_chart_independent (k d : ℕ)
    (anchor : Fin (2^(k+3))) (ι : Fin d → Fin (2^(k+3)))
    (hi : Function.Injective ι) (ha : ∀ j, ι j ≠ anchor)
    (θ : Fin (Fintype.card (ChainLabel (k+3))) → ℝ) {r : ℝ} (hr : 0 < r)
    (f : Fin (2^(k+3)) → (Fin (Fintype.card (ChainLabel (k+3))) → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) (ball (realPoint θ) r))
    (hinj : ∀ z ∈ ball (realPoint θ) r, Function.Injective fun j => f j z)
    (hroot : ∀ z ∈ ball (realPoint θ) r, ∀ j,
      matrixCharpolyRelation (∑ a, z a • chainPauliFin (k+3) a,f j z) = 0)
    {V : Set (Fin (Fintype.card (ChainLabel (k+3))) → ℂ)}
    (hVU : V ⊆ ball (realPoint θ) r) (hV : IsOpen V) (hne : V.Nonempty)
    (c : Fin d → ℂ)
    (hrel : ∀ z ∈ V, ∑ j, (f (ι j) z - f anchor z)*c j = 0) : c = 0 := by
  let U := ball (realPoint θ) r
  let W := realPoint ⁻¹' U
  let e := fun x j => (f j (realPoint x)).re
  have hW : IsOpen W := isOpen_ball.preimage (continuous_pi fun i =>
    Complex.continuous_ofReal.comp (continuous_apply i))
  have hθ : θ ∈ W := mem_ball_self hr
  obtain ⟨z₀,hz₀⟩ := hne
  have hF : AnalyticOnNhd ℂ (fun z => ∑ j, (f (ι j) z - f anchor z)*c j) U :=
    fun z hz => Finset.analyticAt_fun_sum _ fun j _ =>
      ((hf _ z hz).sub (hf _ z hz)).mul analyticAt_const
  have hall := hF.eqOn_of_preconnected_of_eventuallyEq (g := fun _ => (0:ℂ))
    (fun _ _ => analyticAt_const) (convex_ball (realPoint θ) r).isPreconnected
    (hVU hz₀) (Filter.mem_of_superset (hV.mem_nhds hz₀) (fun z hz => hrel z hz))
  let P := chainPauliFin (k+3)
  have hreal (x) (hx : x ∈ W) (j) : (e x j : ℂ) = f j (realPoint x) := by
    have him := matrixCharpolyRelation_im_eq_zero_of_isHermitian (spectralEnsembleMatrix P x)
      (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian _) x) _ (hroot _ hx j)
    exact Complex.ext rfl (by simp [him])
  have hesc : SpectrumEscapesAffineRelations (range (realAffineMatrix 0 P)) := by
    simpa only [funext (realAffineMatrix_zero_eq_spectralEnsembleMatrix P)] using
      chainPauliFin_spectrumEscapesAffineRelations k
  have hzero (w : Fin d → ℝ) (hw : ∀ x ∈ W, ∑ j, w j * (e x (ι j) - e x anchor) = 0) :
      w = 0 := by
    apply no_constant_combination_anchoredGap 0 P hesc hi ha (scale := 1) one_ne_zero hW
      ⟨θ,hθ⟩ e _ _ w
    · intro x hx y hy
      simpa only [anchoredGapMap,div_one] using (hw x hx).trans (hw y hy).symm
    · intro x hx i j hij
      apply hinj _ hx
      exact (hreal x hx i).symm.trans ((congrArg Complex.ofReal hij).trans (hreal x hx j))
    · intro x hx j
      rw [realAffineMatrix_zero_eq_spectralEnsembleMatrix,hreal x hx]
      exact hroot _ hx j
  have heq (x) (hx : x ∈ W) :
      ∑ j, (((e x (ι j) - e x anchor : ℝ) : ℂ) * c j) = 0 := by
    simpa only [Complex.ofReal_sub,hreal x hx] using hall hx
  have hre := hzero (fun j => (c j).re) (fun x hx => by
    simpa [Complex.mul_re,mul_comm] using congrArg Complex.re (heq x hx))
  have him := hzero (fun j => (c j).im) (fun x hx => by
    simpa [Complex.mul_im,mul_comm] using congrArg Complex.im (heq x hx))
  funext j
  exact Complex.ext (congrFun hre j) (congrFun him j)

#print axioms path_gap_chart_independent
end
end GaloisForLFunctions.HTGeometry.SpectralJets
