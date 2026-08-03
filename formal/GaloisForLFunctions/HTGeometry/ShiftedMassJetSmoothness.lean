import GaloisForLFunctions.HTGeometry.FamilyOuterObservationJets
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogJets

/-!
# Joint smoothness of the shifted mass jet packet

The jets of a discrete Cauchy transform at the combined nodes of a family of real translates depend
on two parameters: the exponential rescaling of finitely many masses, and the translation tuple.

Rescaling splits the packet affinely along the mass columns, so the dependence is the sum of a fixed
analytic term evaluated at a translated node and finitely many explicit rational terms.  Real
translations never move a node onto the real axis, so both are smooth on the whole parameter space.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A real translation of a fixed node is a smooth function of the translation tuple. -/
theorem contDiff_combinedNodes {row : Type*} (z : row → ℂ) {r : ℕ} (u : row × Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) fun t : Fin r → ℝ => combinedNodes z t u := by
  refine contDiff_const.add ?_
  exact (Complex.ofRealCLM.contDiff).comp (contDiff_apply ℝ ℝ u.2)

theorem im_combinedNodes_pos {row : Type*} {z : row → ℂ} (hupper : ∀ b, 0 < (z b).im) {r : ℕ}
    (t : Fin r → ℝ) (u : row × Fin r) : 0 < (combinedNodes z t u).im := by
  rw [im_combinedNodes]
  exact hupper u.1

/-- The unperturbed jets at a translated node are smooth in the translation tuple. -/
theorem contDiff_baseJet {row : Type*} {z : row → ℂ} (hupper : ∀ b, 0 < (z b).im) {r : ℕ}
    (ν : Measure ℝ) [IsFiniteMeasure ν] (j : ℕ) (u : row × Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) fun t : Fin r → ℝ =>
      iteratedDeriv j (cauchyTransform ν) (combinedNodes z t u) := by
  have hanal : AnalyticOnNhd ℂ (iteratedDeriv j (cauchyTransform ν)) {ζ : ℂ | 0 < ζ.im} :=
    analyticOnNhd_iteratedDeriv
      (analyticOnNhd_cauchyTransform ν isOpen_upperHalfSet fun _ hζ => ne_of_gt hζ) j
  rw [contDiff_iff_contDiffAt]
  intro t
  have hmem : combinedNodes z t u ∈ {ζ : ℂ | 0 < ζ.im} := im_combinedNodes_pos hupper t u
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (iteratedDeriv j (cauchyTransform ν)) (combinedNodes z t u) :=
    ((hanal _ hmem).contDiffAt).restrict_scalars ℝ
  exact hg.comp t (contDiff_combinedNodes z u).contDiffAt

/-- The mass columns at a translated node are smooth in the translation tuple. -/
theorem contDiff_massJetColumn {row : Type*} {z : row → ℂ} (hupper : ∀ b, 0 < (z b).im) {r : ℕ}
    (ord : row × Fin r → ℕ) (x w : ℕ → ℝ) (n : ℕ) (u : Σ v : row × Fin r, Fin (ord v)) :
    ContDiff ℝ (⊤ : ℕ∞) fun t : Fin r → ℝ =>
      massJetColumn (combinedNodes z t) ord x w n u := by
  have hden : ContDiff ℝ (⊤ : ℕ∞) fun t : Fin r → ℝ =>
      ((x n : ℝ) : ℂ) - combinedNodes z t u.1 :=
    contDiff_const.sub (contDiff_combinedNodes z u.1)
  have hne : ∀ t : Fin r → ℝ, ((x n : ℝ) : ℂ) - combinedNodes z t u.1 ≠ 0 := by
    intro t hzero
    have him : (combinedNodes z t u.1).im = 0 := by
      have := congrArg Complex.im hzero
      simpa using this.symm
    exact absurd him (ne_of_gt (im_combinedNodes_pos hupper t u.1))
  have hinv : ContDiff ℝ (⊤ : ℕ∞) fun t : Fin r → ℝ =>
      (((x n : ℝ) : ℂ) - combinedNodes z t u.1)⁻¹ := hden.inv hne
  have hpow : ContDiff ℝ (⊤ : ℕ∞) fun t : Fin r → ℝ =>
      ((((x n : ℝ) : ℂ) - combinedNodes z t u.1)⁻¹) ^ ((u.2 : ℕ) + 1) := hinv.pow _
  have hval : (fun t : Fin r → ℝ => massJetColumn (combinedNodes z t) ord x w n u)
      = fun t : Fin r → ℝ => (w n : ℂ) * (((Nat.factorial (u.2 : ℕ) : ℕ) : ℂ)
        * ((((x n : ℝ) : ℂ) - combinedNodes z t u.1)⁻¹) ^ ((u.2 : ℕ) + 1)) := rfl
  rw [hval]
  exact contDiff_const.mul (contDiff_const.mul hpow)

/-- The jets of the exponentially rescaled discrete mass at the combined nodes. -/
def shiftedMassJetPacket {row : Type*} (z : row → ℂ) {r : ℕ} (ord : row × Fin r → ℕ)
    (x w : ℕ → ℝ) {K : ℕ} (a : Fin K → ℕ) (p : (Fin K → ℝ) × (Fin r → ℝ)) :
    (Σ v : row × Fin r, Fin (ord v)) → ℂ :=
  discreteJetPacket (combinedNodes z p.2) ord x (perturbedWeight a p.1 w)

/-- **The shifted mass jet packet is jointly smooth.**  Rescaling splits it affinely along the mass
columns, and every term is smooth in the translation tuple because a real translation keeps the node
above the real axis. -/
theorem contDiff_shiftedMassJetPacket {row : Type*} [Fintype row] {z : row → ℂ}
    (hupper : ∀ b, 0 < (z b).im) {r : ℕ} (ord : row × Fin r → ℕ) (x : ℕ → ℝ) {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (hsum : Summable w) {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a) :
    ContDiff ℝ (⊤ : ℕ∞) (shiftedMassJetPacket z ord x w a) := by
  haveI := isFiniteMeasure_countableWeightedDirac (x := x) hw hsum
  rw [contDiff_pi]
  intro u
  have hsplit : ∀ p : (Fin K → ℝ) × (Fin r → ℝ),
      shiftedMassJetPacket z ord x w a p u
        = discreteJetPacket (combinedNodes z p.2) ord x w u
          + ∑ k, (Real.exp (p.1 k) - 1) • massJetColumn (combinedNodes z p.2) ord x w (a k) u := by
    intro p
    have hdiff := discreteJetPacket_perturbedWeight_sub ha p.1 hw hsum (combinedNodes z p.2)
      (fun v => (im_combinedNodes_pos hupper p.2 v).ne') ord x u
    have hsumapply : (∑ k, (Real.exp (p.1 k) - 1) • massJetColumn (combinedNodes z p.2) ord x w
        (a k)) u = ∑ k, (Real.exp (p.1 k) - 1) • massJetColumn (combinedNodes z p.2) ord x w
        (a k) u := by
      simp
    show discreteJetPacket (combinedNodes z p.2) ord x (perturbedWeight a p.1 w) u = _
    rw [← hdiff]
    ring
  simp only [hsplit]
  refine ContDiff.add ?_ ?_
  · exact (contDiff_baseJet hupper _ (u.2 : ℕ) u.1).comp contDiff_snd
  · refine ContDiff.sum fun k _ => ?_
    have hexp : ContDiff ℝ (⊤ : ℕ∞) fun p : (Fin K → ℝ) × (Fin r → ℝ) =>
        ((Real.exp (p.1 k) - 1 : ℝ) : ℂ) := by
      refine Complex.ofRealCLM.contDiff.comp ?_
      exact (Real.contDiff_exp.comp ((contDiff_apply ℝ ℝ k).comp contDiff_fst)).sub contDiff_const
    have hcol : ContDiff ℝ (⊤ : ℕ∞) fun p : (Fin K → ℝ) × (Fin r → ℝ) =>
        massJetColumn (combinedNodes z p.2) ord x w (a k) u :=
      (contDiff_massJetColumn hupper ord x w (a k) u).comp contDiff_snd
    have hval : (fun p : (Fin K → ℝ) × (Fin r → ℝ) =>
        (Real.exp (p.1 k) - 1) • massJetColumn (combinedNodes z p.2) ord x w (a k) u)
        = fun p : (Fin K → ℝ) × (Fin r → ℝ) => ((Real.exp (p.1 k) - 1 : ℝ) : ℂ)
          * massJetColumn (combinedNodes z p.2) ord x w (a k) u := by
      funext p
      rw [Complex.real_smul]
    rw [hval]
    exact hexp.mul hcol

end

end GaloisForLFunctions.HTGeometry
