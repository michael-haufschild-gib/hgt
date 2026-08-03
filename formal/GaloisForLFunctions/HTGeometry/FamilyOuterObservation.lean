import GaloisForLFunctions.HTGeometry.ShapeOuterObservation

/-!
# The outer jets of a translated family, in evaluation-matrix coordinates

A relation among finitely many real translates of one function, evaluated at a packet of points, sees
the jets of that function at the *combined* nodes: evaluation point plus shift.  Its expanded
evaluation matrix indexes those jets by (point, folded order), the fold running over member and order
together.

Composing the outer jet observation at the combined nodes with that fold gives the observation of the
mass parameter in exactly the coordinates a relation among the translates is written in.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The combined node packet of a family of real translates: evaluation point plus shift. -/
def combinedNodes {row : Type*} {r : ℕ} (z : row → ℂ) (t : Fin r → ℝ) : row × Fin r → ℂ :=
  fun p => z p.1 + (t p.2 : ℂ)

theorem im_combinedNodes {row : Type*} {r : ℕ} (z : row → ℂ) (t : Fin r → ℝ) (p : row × Fin r) :
    (combinedNodes z t p).im = (z p.1).im := by
  simp [combinedNodes]

/-- The outer jets of the translated family, folded into the coordinates of the evaluation
matrix. -/
def familyOuterObservation {row : Type*} (r d : ℕ) (z : row → ℂ) (t : Fin r → ℝ) (x ε : ℕ → ℝ)
    (u : MassParameter) : row × Fin (r * (d + 1)) → ℂ :=
  sigmaJetHomeomorph r d
    (outerJetSigma (fun _ : row × Fin r => d)
      (discreteJetPacket (combinedNodes z t) (fun _ => d + 1) x fun n => ε n * Real.exp (u n)))

/-- **The family observation is continuous.** -/
theorem continuous_familyOuterObservation {row : Type*} [Fintype row] (r d : ℕ) (z : row → ℂ)
    (t : Fin r → ℝ) (hupper : ∀ b, 0 < (z b).im) (x : ℕ → ℝ) {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Summable ε) :
    Continuous (familyOuterObservation r d z t x ε) := by
  have hup : ∀ p : row × Fin r, 0 < (combinedNodes z t p).im := by
    intro p
    rw [im_combinedNodes]
    exact hupper p.1
  have hbase : Continuous fun u : MassParameter =>
      discreteJetPacket (combinedNodes z t) (fun _ : row × Fin r => d + 1) x
        fun n => ε n * Real.exp (u n) :=
    continuous_discreteJetPacket_expParameter _ hup _ x hεpos hε
  have hmaps : ∀ u : MassParameter,
      (discreteJetPacket (combinedNodes z t) (fun _ : row × Fin r => d + 1) x
        fun n => ε n * Real.exp (u n))
        ∈ {y : (Σ _ : row × Fin r, Fin (d + 1)) → ℂ | ∀ i, y ⟨i, 0⟩ + Complex.I ≠ 0} := fun u =>
    discreteJetPacket_mem_chartDomain _ hup (fun _ => d) x hεpos hε u
  have hcomp : Continuous fun u : MassParameter =>
      outerJetSigma (fun _ : row × Fin r => d)
        (discreteJetPacket (combinedNodes z t) (fun _ => d + 1) x
          fun n => ε n * Real.exp (u n)) :=
    (continuousOn_outerJetSigma _).comp_continuous hbase hmaps
  exact (sigmaJetHomeomorph r d).continuous.comp hcomp

/-- **The family observation is locally surjective.** -/
theorem locallySurjective_familyOuterObservation {row : Type*} [Fintype row] [DecidableEq row]
    (r d : ℕ) (z : row → ℂ) (t : Fin r → ℝ)
    (hnodesinj : Function.Injective (combinedNodes z t)) (hupper : ∀ b, 0 < (z b).im)
    {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Summable ε) :
    LocallySurjectiveObservation (familyOuterObservation r d z t x ε) := by
  have hup : ∀ p : row × Fin r, 0 < (combinedNodes z t p).im := by
    intro p
    rw [im_combinedNodes]
    exact hupper p.1
  exact (locallySurjective_outerJetObservation (combinedNodes z t) hnodesinj hup
    (fun _ => d) x hx hεpos hε).congr_homeomorph (sigmaJetHomeomorph r d)

end

end GaloisForLFunctions.HTGeometry
