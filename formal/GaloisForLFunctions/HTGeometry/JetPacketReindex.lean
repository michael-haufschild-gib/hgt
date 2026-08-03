import GaloisForLFunctions.HTGeometry.JetObservationGenericity
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Jet packets in the coordinates of the evaluation matrix

The jet packet of a finite family of translates, observed at a packet of evaluation points, is
indexed by triples (point, member, order).  The expanded evaluation matrix indexes its jet variables
by pairs (point, folded order), the fold running over member and order together.

Those index sets are equivalent, so the two coordinate systems are homeomorphic, and a locally
surjective observation in one is a locally surjective observation in the other.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Folding (member, order) into a single jet index. -/
def sigmaJetIndexEquiv {row : Type*} (r d D : ℕ) (h : r * (d + 1) = D) :
    (Σ _ : row × Fin r, Fin (d + 1)) ≃ row × Fin D where
  toFun t := (t.1.1, finCongr h (finProdFinEquiv (t.1.2, t.2)))
  invFun p := ⟨(p.1, (finProdFinEquiv.symm ((finCongr h).symm p.2)).1),
    (finProdFinEquiv.symm ((finCongr h).symm p.2)).2⟩
  left_inv := by
    rintro ⟨⟨b, j⟩, o⟩
    simp
  right_inv := by
    rintro ⟨b, m⟩
    show (b, finCongr h (finProdFinEquiv ((finProdFinEquiv.symm ((finCongr h).symm m)).1,
      (finProdFinEquiv.symm ((finCongr h).symm m)).2))) = (b, m)
    rw [Prod.mk.eta, finProdFinEquiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The two coordinate systems for a jet packet are homeomorphic. -/
def sigmaJetHomeomorph {row : Type*} (r d D : ℕ) (h : r * (d + 1) = D) :
    ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ) ≃ₜ ((row × Fin D) → ℂ) where
  toFun y := fun p => y ((sigmaJetIndexEquiv r d D h).symm p)
  invFun w := fun t => w (sigmaJetIndexEquiv r d D h t)
  left_inv := by
    intro y
    funext t
    simp
  right_inv := by
    intro w
    funext p
    simp
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

/-- **A locally surjective observation stays one after a homeomorphic change of coordinates.** -/
theorem LocallySurjectiveObservation.congr_homeomorph {P : Type*} [TopologicalSpace P]
    {σ τ : Type*} {J : P → (σ → ℂ)} (hJ : LocallySurjectiveObservation J)
    (e : (σ → ℂ) ≃ₜ (τ → ℂ)) :
    LocallySurjectiveObservation fun p => e (J p) := by
  intro p N hN
  have himg : (fun p => e (J p)) '' N = e '' (J '' N) := by
    rw [← Set.image_comp]
    rfl
  rw [himg]
  exact e.isOpenMap.image_mem_nhds (hJ p N hN)

/-- **A locally surjective observation stays one after a fixed translation of the target.**  This is
what makes a fixed additive perturbation invisible to a transversality argument. -/
theorem LocallySurjectiveObservation.add_const {P : Type*} [TopologicalSpace P] {σ : Type*}
    {J : P → (σ → ℂ)} (hJ : LocallySurjectiveObservation J) (v : σ → ℂ) :
    LocallySurjectiveObservation fun p => J p + v := by
  intro p N hN
  have himg : (fun p => J p + v) '' N = (fun y : σ → ℂ => y + v) '' (J '' N) := by
    rw [← Set.image_comp]
    rfl
  rw [himg]
  exact (Homeomorph.addRight v).isOpenMap.image_mem_nhds (hJ p N hN)

/-- The jet packet of a family of translates, read in the coordinates of the evaluation matrix. -/
theorem locallySurjectiveObservation_reindex {P : Type*} [TopologicalSpace P] {row : Type*}
    (r d D : ℕ) (h : r * (d + 1) = D) {J : P → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ)}
    (hJ : LocallySurjectiveObservation J) :
    LocallySurjectiveObservation fun p => sigmaJetHomeomorph r d D h (J p) :=
  hJ.congr_homeomorph _

end

end GaloisForLFunctions.HTGeometry
