import GaloisForLFunctions.HTGeometry.MassShiftFoldedObservation
import GaloisForLFunctions.HTGeometry.ShiftedMassJetSmoothness

/-!
# The data a shift-uniform descent needs

For each relation shape the transversality argument needs an evaluation-point packet with more rows
than columns, at distinct heights above the real axis, and a carrier whose jets vary smoothly with
the shift.

Both are explicit: the nodes may be taken on the imaginary axis at integer heights, and the carrier
jets are smooth because the carrier is analytic there.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Evaluation points -/

/-- Evaluation points on the imaginary axis at integer heights. -/
def gridNodes (N : ℕ) : Fin N → ℂ := fun b => Complex.I * ((((b : ℕ) + 1 : ℕ) : ℝ) : ℂ)

theorem gridNodes_im (N : ℕ) (b : Fin N) : (gridNodes N b).im = ((b : ℕ) + 1 : ℕ) := by
  simp [gridNodes, Complex.mul_im]

theorem gridNodes_upper (N : ℕ) (b : Fin N) : 0 < (gridNodes N b).im := by
  rw [gridNodes_im]
  positivity

theorem gridNodes_sep (N : ℕ) :
    ∀ b b' : Fin N, b ≠ b' → (gridNodes N b).im ≠ (gridNodes N b').im := by
  intro b b' hbb hEq
  rw [gridNodes_im, gridNodes_im] at hEq
  exact hbb (Fin.ext (by exact_mod_cast Nat.succ_injective (by exact_mod_cast hEq)))

theorem gridNodes_injective (N : ℕ) : Function.Injective (gridNodes N) := by
  intro b b' hEq
  by_contra hne
  exact gridNodes_sep N b b' hne (congrArg Complex.im hEq)

/-! ## Smoothness of the carrier jets -/

/-- The jets of an analytic carrier at a translated node are smooth in the translation tuple. -/
theorem contDiff_carrierJet {row : Type*} {z : row → ℂ} (hupper : ∀ b, 0 < (z b).im) {r : ℕ}
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A {ζ : ℂ | 0 < ζ.im}) (j : ℕ) (v : row × Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) fun t : Fin r → ℝ => iteratedDeriv j A (combinedNodes z t v) := by
  have hanal : AnalyticOnNhd ℂ (iteratedDeriv j A) {ζ : ℂ | 0 < ζ.im} :=
    analyticOnNhd_iteratedDeriv hA j
  rw [contDiff_iff_contDiffAt]
  intro t
  have hmem : combinedNodes z t v ∈ {ζ : ℂ | 0 < ζ.im} := im_combinedNodes_pos hupper t v
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (iteratedDeriv j A) (combinedNodes z t v) :=
    ((hanal _ hmem).contDiffAt).restrict_scalars ℝ
  exact hg.comp t (contDiff_combinedNodes z v).contDiffAt

/-- The carrier jets in the sigma-indexed coordinates. -/
def sigmaCarrierJets {row : Type} (r d D : ℕ) (h : r * (d + 1) = D) (z : row → ℂ)
    (c : ℂ) (A : ℂ → ℂ) (t : Fin r → ℝ) : (Σ _ : row × Fin r, Fin (d + 1)) → ℂ :=
  fun v => outerCarrierJets r d D h z t c A (sigmaJetIndexEquiv r d D h v)

theorem sigmaCarrierJets_fold {row : Type} [Fintype row] (r d D : ℕ) (h : r * (d + 1) = D)
    (z : row → ℂ) (c : ℂ) (A : ℂ → ℂ) (t : Fin r → ℝ) (p : row × Fin D) :
    sigmaCarrierJets r d D h z c A t ((sigmaJetIndexEquiv r d D h).symm p)
      = outerCarrierJets r d D h z t c A p := by
  rw [sigmaCarrierJets, Equiv.apply_symm_apply]

/-- **The carrier jets are smooth in the shift.** -/
theorem contDiff_sigmaCarrierJets {row : Type} [Fintype row] (r d D : ℕ) (h : r * (d + 1) = D)
    {z : row → ℂ} (hupper : ∀ b, 0 < (z b).im) (c : ℂ) {A : ℂ → ℂ}
    (hA : AnalyticOnNhd ℂ A {ζ : ℂ | 0 < ζ.im}) :
    ContDiff ℝ (⊤ : ℕ∞) (sigmaCarrierJets r d D h z c A) := by
  rw [contDiff_pi]
  intro v
  set p : row × Fin D := sigmaJetIndexEquiv r d D h v with hp
  have hval : (fun t : Fin r → ℝ => sigmaCarrierJets r d D h z c A t v)
      = fun t : Fin r → ℝ => c * iteratedDeriv
        ((finProdFinEquiv.symm ((finCongr h).symm p.2)).2 : ℕ) A
        (combinedNodes z t (p.1, (finProdFinEquiv.symm ((finCongr h).symm p.2)).1)) := rfl
  rw [hval]
  exact contDiff_const.mul (contDiff_carrierJet hupper hA _ _)

end

end GaloisForLFunctions.HTGeometry
