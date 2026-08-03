import GaloisForLFunctions.HTGeometry.OuterJetSigmaSubmersion
import GaloisForLFunctions.HTGeometry.ShiftedMassJetSubmersion

/-!
# The observation seen by a parametric transversality argument

The observation is the Cayley outer chart of the jets of an exponentially rescaled discrete mass, at
the combined nodes of a family of real translates, corrected by a fixed carrier.

It is smooth in the mass parameter and the shift tuple jointly, and its derivative in the mass
parameter is surjective wherever the mass columns span, because the chart is a submersion and a
fixed additive correction does not change a derivative.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Cayley outer jets of the shifted rescaled mass, corrected by a fixed carrier. -/
def outerShiftObservation {row : Type*} (z : row → ℂ) {r : ℕ} (d : ℕ) (x w : ℕ → ℝ)
    {K : ℕ} (a : Fin K → ℕ)
    (carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ))
    (p : (Fin K → ℝ) × (Fin r → ℝ)) : (Σ _ : row × Fin r, Fin (d + 1)) → ℂ :=
  outerJetSigma (fun _ : row × Fin r => d)
    (shiftedMassJetPacket z (fun _ : row × Fin r => d + 1) x w a p) + carrier p.2

/-- The zeroth jet of a nonnegative discrete mass never meets `-i` above the real axis. -/
theorem discreteJetPacket_zero_add_I_ne_zero {ι : Type*} [Fintype ι] (nodes : ι → ℂ)
    (hupper : ∀ i, 0 < (nodes i).im) (m : ι → ℕ) (x : ℕ → ℝ) {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable w) (i : ι) :
    discreteJetPacket nodes (fun i => m i + 1) x w ⟨i, 0⟩ + Complex.I ≠ 0 := by
  haveI := isFiniteMeasure_countableWeightedDirac (x := x) hw hsum
  have hzero : discreteJetPacket nodes (fun i => m i + 1) x w ⟨i, 0⟩
      = cauchyTransform (_root_.HTGeometry.countableWeightedDirac w x) (nodes i) := by
    simp [discreteJetPacket]
  rw [hzero]
  exact add_I_ne_zero_of_im_nonneg (im_cauchyTransform_nonneg _ (hupper i))

/-- The jets of a positive discrete mass always lie in the chart domain above the real axis. -/
theorem shiftedMassJetPacket_mem_outerJetSigmaDomain {row : Type*} [Fintype row] {z : row → ℂ}
    (hupper : ∀ b, 0 < (z b).im) {r : ℕ} (d : ℕ) (x : ℕ → ℝ) {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable w) {K : ℕ} (a : Fin K → ℕ) (p : (Fin K → ℝ) × (Fin r → ℝ)) :
    shiftedMassJetPacket z (fun _ : row × Fin r => d + 1) x w a p
      ∈ outerJetSigmaDomain (fun _ : row × Fin r => d) := by
  intro i
  exact discreteJetPacket_zero_add_I_ne_zero (combinedNodes z p.2)
    (fun v => im_combinedNodes_pos hupper p.2 v) (fun _ : row × Fin r => d) x
    (perturbedWeight_nonneg a p.1 hw) (summable_perturbedWeight a p.1 hsum) i

/-- **The observation is jointly smooth.** -/
theorem contDiffOn_outerShiftObservation {row : Type*} [Fintype row] {z : row → ℂ}
    (hupper : ∀ b, 0 < (z b).im) {r : ℕ} (d : ℕ) (x : ℕ → ℝ) {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable w) {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a)
    {carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ)}
    (hcarrier : ContDiff ℝ (⊤ : ℕ∞) carrier) {U : Set (Fin r → ℝ)} :
    ContDiffOn ℝ (⊤ : ℕ∞) (outerShiftObservation z d x w a carrier) (Set.univ ×ˢ U) := by
  have hJ : ContDiff ℝ (⊤ : ℕ∞) (shiftedMassJetPacket z (fun _ : row × Fin r => d + 1) x w a) :=
    contDiff_shiftedMassJetPacket hupper (fun _ : row × Fin r => d + 1) x hw hsum ha
  have hmaps : Set.MapsTo (shiftedMassJetPacket z (fun _ : row × Fin r => d + 1) x w a)
      (Set.univ ×ˢ U) (outerJetSigmaDomain (fun _ : row × Fin r => d)) := fun p _ =>
    shiftedMassJetPacket_mem_outerJetSigmaDomain hupper d x hw hsum a p
  have hchart : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p => outerJetSigma (fun _ : row × Fin r => d)
        (shiftedMassJetPacket z (fun _ : row × Fin r => d + 1) x w a p)) (Set.univ ×ˢ U) :=
    (contDiffOn_outerJetSigma (fun _ : row × Fin r => d)).comp hJ.contDiffOn hmaps
  exact hchart.add (hcarrier.comp contDiff_snd).contDiffOn

/-- **The observation is a submersion in the mass parameter.**  The chart is a submersion, the mass
parameter reaches every jet direction, and the fixed carrier does not change a derivative. -/
theorem surjective_fderiv_param_outerShiftObservation {row : Type*} [Fintype row] {z : row → ℂ}
    (hupper : ∀ b, 0 < (z b).im) {r : ℕ} (d : ℕ) (x : ℕ → ℝ) {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable w) {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a)
    (carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ))
    (t : Fin r → ℝ) (s₀ : Fin K → ℝ)
    (hspan : Submodule.span ℝ (Set.range fun k =>
      massJetColumn (combinedNodes z t) (fun _ : row × Fin r => d + 1) x w (a k)) = ⊤) :
    Function.Surjective
      (fderiv ℝ (fun s => outerShiftObservation z d x w a carrier (s, t)) s₀) := by
  set J : (Fin K → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ) :=
    fun s => shiftedMassJetPacket z (fun _ : row × Fin r => d + 1) x w a (s, t) with hJdef
  have hJcont : ContDiff ℝ (⊤ : ℕ∞) J :=
    (contDiff_shiftedMassJetPacket hupper (fun _ : row × Fin r => d + 1) x hw hsum ha).comp
      (contDiff_id.prodMk contDiff_const)
  have hJdiff : DifferentiableAt ℝ J s₀ := (hJcont.differentiable (by simp)).differentiableAt
  have hmem : J s₀ ∈ outerJetSigmaDomain (fun _ : row × Fin r => d) :=
    shiftedMassJetPacket_mem_outerJetSigmaDomain hupper d x hw hsum a (s₀, t)
  have hchartDiff : DifferentiableAt ℝ (outerJetSigma (fun _ : row × Fin r => d)) (J s₀) :=
    ((contDiffOn_outerJetSigma (fun _ : row × Fin r => d)).differentiableOn
      (by simp)).differentiableAt
        ((isOpen_outerJetSigmaDomain (fun _ : row × Fin r => d)).mem_nhds hmem)
  have hval : (fun s => outerShiftObservation z d x w a carrier (s, t))
      = fun s => carrier t + outerJetSigma (fun _ : row × Fin r => d) (J s) := by
    funext s
    rw [outerShiftObservation]
    exact add_comm _ _
  have hcompfun : (fun s => outerJetSigma (fun _ : row × Fin r => d) (J s))
      = (outerJetSigma (fun _ : row × Fin r => d)) ∘ J := rfl
  rw [hval, fderiv_const_add, hcompfun, fderiv_comp s₀ hchartDiff hJdiff]
  rw [ContinuousLinearMap.coe_comp]
  exact Function.Surjective.comp (surjective_fderiv_outerJetSigma hmem)
    (surjective_fderiv_shiftedMassJetPacket hupper (fun _ : row × Fin r => d + 1) x hw hsum
      ha t s₀ hspan)

end

end GaloisForLFunctions.HTGeometry
