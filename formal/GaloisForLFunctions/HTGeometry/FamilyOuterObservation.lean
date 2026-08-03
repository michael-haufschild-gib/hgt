import GaloisForLFunctions.HTGeometry.ShapeOuterObservation
import GaloisForLFunctions.HTGeometry.FamilyJetRelationExpansion

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
def familyOuterObservation {row : Type*} (r d D : ℕ) (h : r * (d + 1) = D) (z : row → ℂ)
    (t : Fin r → ℝ) (x ε : ℕ → ℝ) (u : MassParameter) : row × Fin D → ℂ :=
  sigmaJetHomeomorph r d D h
    (outerJetSigma (fun _ : row × Fin r => d)
      (discreteJetPacket (combinedNodes z t) (fun _ => d + 1) x fun n => ε n * Real.exp (u n)))

/-- **The family observation is continuous.** -/
theorem continuous_familyOuterObservation {row : Type*} [Fintype row] (r d D : ℕ)
    (h : r * (d + 1) = D) (z : row → ℂ) (t : Fin r → ℝ) (hupper : ∀ b, 0 < (z b).im) (x : ℕ → ℝ)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Summable ε) :
    Continuous (familyOuterObservation r d D h z t x ε) := by
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
  exact (sigmaJetHomeomorph r d D h).continuous.comp hcomp

/-- **The family observation is locally surjective.** -/
theorem locallySurjective_familyOuterObservation {row : Type*} [Fintype row] [DecidableEq row]
    (r d D : ℕ) (h : r * (d + 1) = D) (z : row → ℂ) (t : Fin r → ℝ)
    (hnodesinj : Function.Injective (combinedNodes z t)) (hupper : ∀ b, 0 < (z b).im)
    {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Summable ε) :
    LocallySurjectiveObservation (familyOuterObservation r d D h z t x ε) := by
  have hup : ∀ p : row × Fin r, 0 < (combinedNodes z t p).im := by
    intro p
    rw [im_combinedNodes]
    exact hupper p.1
  exact (locallySurjective_outerJetObservation (combinedNodes z t) hnodesinj hup
    (fun _ => d) x hx hεpos hε).congr_homeomorph (sigmaJetHomeomorph r d D h)

/-! ## Jets of a translate -/

/-- The jets of a translate are the jets at the translated point. -/
theorem iteratedDeriv_translate (F : ℂ → ℂ) (c : ℂ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => F (w + c)) z = iteratedDeriv k F (z + c) :=
  congrFun (iteratedDeriv_comp_add_const k F c) z

/-- **The jets of a family of real translates are the jets of the function at the combined nodes.**
This is why a relation among translates, evaluated at a packet of points, reads off the jets of one
function at the points shifted by the translation parameters. -/
theorem familyJet_translate {r n : ℕ} (F : ℂ → ℂ) (t : Fin r → ℝ) {row : Type*} (z : row → ℂ)
    (b : row) (k : FamilyJetVariables r n) :
    iteratedDeriv (k.2 : ℕ) (fun w => F (w + (t k.1 : ℂ))) (z b)
      = iteratedDeriv (k.2 : ℕ) F (combinedNodes z t (b, k.1)) :=
  iteratedDeriv_translate F _ _ (z b)

/-! ## Residual rigidity for the translated family -/

/-- Reduced shapes whose jet depth is that of a family of `m' + 1` translates differentiated to
order `n`. -/
abbrev FamilyShape (m' n : ℕ) : Type := {S : ReducedShape // S.1.depthPred = m' * (n + 1) + n}

theorem familyShape_mul (m' n : ℕ) (S : FamilyShape m' n) :
    (m' + 1) * (n + 1) = S.1.1.depthPred + 1 := by
  rw [S.2]
  ring

/-- **Residual rigidity for the translated family.**  For a residual set of mass parameters, at the
given node packets, the only coefficient vector annihilated by the evaluation matrix of any shape of
the family's depth is zero -- with the fixed carrier jets included. -/
theorem residual_familyOuterJet_rigidity {m' n : ℕ} (t : Fin (m' + 1) → ℝ)
    {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε)
    (carrier : ∀ S : FamilyShape m' n, ShapeJetIndex S.1.1 → ℂ)
    (nodeOf : ∀ S : FamilyShape m' n,
      Fin S.1.1.monomialCount × Fin (S.1.1.spectralDegree + 1) → ℂ)
    (hnodesinj : ∀ S, Function.Injective (combinedNodes (nodeOf S) t))
    (hupper : ∀ S b, 0 < (nodeOf S b).im)
    (hD : ∀ S : FamilyShape m' n,
      shapeDeterminant S.1.1.spectralDegree S.1.1.jetDepth S.1.1.exponent (nodeOf S) ≠ 0) :
    {u : MassParameter | ∀ (S : FamilyShape m' n)
        (c : Fin S.1.1.monomialCount × Fin (S.1.1.spectralDegree + 1) → ℂ),
        (expandedDifferentialEvaluationMatrix S.1.1.spectralDegree S.1.1.jetDepth (nodeOf S)
          S.1.1.exponent
          (familyOuterObservation (m' + 1) n (S.1.1.depthPred + 1) (familyShape_mul m' n S)
            (nodeOf S) t x ε u + carrier S)).mulVec c = 0 → c = 0}
      ∈ residual MassParameter :=
  residual_forall_shape_coeff_eq_zero (Sh := FamilyShape m' n) (sh := fun S => S.1.1)
    (nodeOf := nodeOf)
    (jetOf := fun S u =>
      familyOuterObservation (m' + 1) n (S.1.1.depthPred + 1) (familyShape_mul m' n S)
        (nodeOf S) t x ε u + carrier S)
    (fun S => (continuous_familyOuterObservation (m' + 1) n (S.1.1.depthPred + 1)
      (familyShape_mul m' n S) (nodeOf S) t (hupper S) x hεpos hε).add continuous_const)
    (fun S => (locallySurjective_familyOuterObservation (m' + 1) n (S.1.1.depthPred + 1)
      (familyShape_mul m' n S) (nodeOf S) t (hnodesinj S) (hupper S) hx hεpos hε).add_const _) hD

end

end GaloisForLFunctions.HTGeometry
