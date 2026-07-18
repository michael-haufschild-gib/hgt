import GaloisForLFunctions.HTGeometry.MultivariateEntireFrechetJet
import GaloisForLFunctions.HTGeometry.SymmetricMultilinearPolarization
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Polarized mixed jets of compact-open multivariate entire sources

An order-`n` directional derivative is the diagonal of the symmetric order-`n` jet.  The standard
finite-difference polarization formula recovers an ordered mixed jet from those diagonals.  Since
every directional jet is a continuous linear observation of the source, the polarized observation
is automatically continuous and linear as well.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Sum the directions selected by a subset of the `n` jet slots. -/
def jetSubsetDirection {d n : ℕ} (dirs : Fin n → (Fin d → ℂ))
    (s : Finset (Fin n)) : Fin d → ℂ :=
  ∑ j ∈ s, dirs j

/-- Coefficient in the finite-difference polarization identity. -/
def jetPolarizationCoeff (n : ℕ) (s : Finset (Fin n)) : ℂ :=
  (-1 : ℂ) ^ (n - s.card) / (n.factorial : ℂ)

/-- The polarized order-`n` mixed jet in the ordered directions `dirs`, bundled as a continuous
complex-linear observation of the entire source. -/
def polarizedJetEvalCLM {d n : ℕ} (x : Fin d → ℂ)
    (dirs : Fin n → (Fin d → ℂ)) : MultivariateEntire d →L[ℂ] ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
    jetPolarizationCoeff n s • directionalJetEvalCLM n x (jetSubsetDirection dirs s)

@[simp]
theorem polarizedJetEvalCLM_apply {d n : ℕ} (x : Fin d → ℂ)
    (dirs : Fin n → (Fin d → ℂ)) (f : MultivariateEntire d) :
    polarizedJetEvalCLM x dirs f =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        jetPolarizationCoeff n s •
          directionalJetEval n x (jetSubsetDirection dirs s) f := by
  simp only [polarizedJetEvalCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, directionalJetEvalCLM_apply]

/-- For a genuinely Frechet-holomorphic source, the polarized continuous observation is exactly
the ordinary ordered mixed Frechet jet. -/
theorem polarizedJetEvalCLM_eq_iteratedFDeriv {d n : ℕ}
    (x : Fin d → ℂ) (dirs : Fin n → (Fin d → ℂ))
    (f : MultivariateEntire d) (hf : ContDiff ℂ (⊤ : WithTop ℕ∞) f.1) :
    polarizedJetEvalCLM x dirs f =
      iteratedFDeriv ℂ n f.1 x dirs := by
  have hsymm : ∀ σ : Equiv.Perm (Fin n),
      iteratedFDeriv ℂ n f.1 x (fun i ↦ dirs (σ i)) =
        iteratedFDeriv ℂ n f.1 x dirs := by
    intro σ
    simpa [Function.comp_def] using
      (hf.contDiffAt.iteratedFDeriv_comp_perm dirs σ)
  rw [polarizedJetEvalCLM_apply]
  simp_rw [directionalJetEval_eq_iteratedFDeriv _ _ f hf]
  simpa [jetPolarizationCoeff, jetSubsetDirection] using
    continuousMultilinearMap_symmetric_polarization
      (iteratedFDeriv ℂ n f.1 x) dirs hsymm

theorem continuousLinearMap_jetSubsetDirection {d n : ℕ}
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ))
    (dirs : Fin n → (Fin d → ℂ)) (s : Finset (Fin n)) :
    L (jetSubsetDirection dirs s) =
      jetSubsetDirection (fun j ↦ L (dirs j)) s := by
  simp [jetSubsetDirection]

/-- Polarized mixed jets satisfy the exact affine chain rule, with every ordered tangent direction
transported by the linear part of the affine automorphism. -/
theorem polarizedJetEvalCLM_affinePullback {d n : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (f : MultivariateEntire d) (x : Fin d → ℂ)
    (dirs : Fin n → (Fin d → ℂ)) :
    polarizedJetEvalCLM x dirs (multivariateEntireAffinePullback e f) =
      polarizedJetEvalCLM (e x)
        (fun j ↦ e.toContinuousAffineMap.contLinear (dirs j)) f := by
  simp [polarizedJetEvalCLM_apply, directionalJetEval_affinePullback,
    continuousLinearMap_jetSubsetDirection]

/-- The coordinate direction corresponding to one partial-derivative slot. -/
def coordinateJetDirection {d : ℕ} (i : Fin d) : Fin d → ℂ :=
  Pi.single i 1

/-- An ordered coordinate word determines a continuous mixed-partial jet observation.  Permuting
the word will later be identified by symmetry of the analytic jet. -/
def orderedPartialJetEvalCLM {d n : ℕ} (x : Fin d → ℂ)
    (word : Fin n → Fin d) : MultivariateEntire d →L[ℂ] ℂ :=
  polarizedJetEvalCLM x (fun j ↦ coordinateJetDirection (word j))

@[simp]
theorem orderedPartialJetEvalCLM_apply {d n : ℕ} (x : Fin d → ℂ)
    (word : Fin n → Fin d) (f : MultivariateEntire d) :
    orderedPartialJetEvalCLM x word f =
      polarizedJetEvalCLM x (fun j ↦ coordinateJetDirection (word j)) f :=
  rfl

/-- Ordered coordinate observations are the ordinary ordered coordinate values of the iterated
Frechet derivative on every Frechet-holomorphic source. -/
theorem orderedPartialJetEvalCLM_eq_iteratedFDeriv {d n : ℕ}
    (x : Fin d → ℂ) (word : Fin n → Fin d)
    (f : MultivariateEntire d) (hf : ContDiff ℂ (⊤ : WithTop ℕ∞) f.1) :
    orderedPartialJetEvalCLM x word f =
      iteratedFDeriv ℂ n f.1 x
        (fun j ↦ coordinateJetDirection (word j)) := by
  exact polarizedJetEvalCLM_eq_iteratedFDeriv x
    (fun j ↦ coordinateJetDirection (word j)) f hf

end

end GaloisForLFunctions.HTGeometry
