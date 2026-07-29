import GaloisForLFunctions.HTGeometry.CountableConstraintBlockAperture
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite-constraint Hilbert-cube apertures in `L∞`

Pairwise-disjoint positive measurable blocks give explicit indicator atoms in `L∞`, normalized
`L¹` coordinate functionals, and bounded projections isolating each block.  The finite block
kernel law then produces a closed Hilbert cube in every exact finite continuous-linear constraint
fiber.

This module keeps the genuinely measure-theoretic input explicit: the required countable positive
partition is an assumption, rather than being conflated with mathlib's weaker singleton-null
`NoAtoms` predicate.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

/-- The `L∞` class of the indicator of a measurable set. -/
noncomputable def linftyIndicatorAtom (s : Set α) (hs : MeasurableSet s) : Lp ℝ ∞ μ :=
  indicatorConstLp ∞ hs (measure_ne_top μ s) 1

/-- The normalized `L¹` indicator used to read an `L∞` indicator coefficient by Hölder
pairing. -/
noncomputable def normalizedL1Indicator (s : Set α) (hs : MeasurableSet s) : Lp ℝ 1 μ :=
  (μ.real s)⁻¹ • indicatorConstLp 1 hs (measure_ne_top μ s) 1

/-- Normalized averaging over a measurable set, as a continuous functional on `L∞`. -/
noncomputable def linftyIndicatorCoordinate (s : Set α) (hs : MeasurableSet s) :
    Lp ℝ ∞ μ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 1 ∞) (normalizedL1Indicator μ s hs)

theorem linftyIndicatorCoordinate_apply_atom
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    linftyIndicatorCoordinate μ s hs (linftyIndicatorAtom μ t ht) =
      (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  rw [linftyIndicatorCoordinate, ContinuousLinearMap.lpPairing_eq_integral]
  calc
    ∫ (x : α),
        ((ContinuousLinearMap.mul ℝ ℝ) (⇑(normalizedL1Indicator μ s hs) x))
          (⇑(linftyIndicatorAtom μ t ht) x) ∂μ =
        ∫ x : α, (s ∩ t).indicator (fun _ => (μ.real s)⁻¹) x ∂μ := by
      apply integral_congr_ae
      have hsmul : ⇑((μ.real s)⁻¹ •
          indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)) =ᵐ[μ]
          (μ.real s)⁻¹ • ⇑(indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)) :=
        Lp.coeFn_smul (μ.real s)⁻¹ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ))
      have hscoe : ⇑(indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)) =ᵐ[μ]
          s.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
      have htcoe : ⇑(indicatorConstLp ∞ ht (measure_ne_top μ t) (1 : ℝ)) =ᵐ[μ]
          t.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
      filter_upwards [hsmul, hscoe, htcoe] with x hx hxs hxt
      change ⇑(normalizedL1Indicator μ s hs) x * ⇑(linftyIndicatorAtom μ t ht) x = _
      simp only [normalizedL1Indicator, linftyIndicatorAtom]
      rw [hx]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hxs, hxt]
      by_cases hxs' : x ∈ s <;> by_cases hxt' : x ∈ t <;> simp [hxs', hxt']
    _ = μ.real (s ∩ t) • (μ.real s)⁻¹ :=
      integral_indicator_const (μ.real s)⁻¹ (hs.inter ht)
    _ = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
      simp [smul_eq_mul, mul_comm]

theorem linftyIndicatorCoordinate_self
    (s : Set α) (hs : MeasurableSet s) (hspos : μ s ≠ 0) :
    linftyIndicatorCoordinate μ s hs (linftyIndicatorAtom μ s hs) = 1 := by
  rw [linftyIndicatorCoordinate_apply_atom, Set.inter_self]
  exact inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hspos, measure_ne_top μ s⟩)

theorem linftyIndicatorCoordinate_disjoint
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) :
    linftyIndicatorCoordinate μ s hs (linftyIndicatorAtom μ t ht) = 0 := by
  rw [linftyIndicatorCoordinate_apply_atom, Set.disjoint_iff_inter_eq_empty.mp hst]
  simp

variable {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsFiniteMeasure ν]

noncomputable def linftyBlockAtom {k : ℕ}
    (A : ℕ → Fin (k + 1) → Set β)
    (hAmeas : ∀ j l, MeasurableSet (A j l))
    (j : ℕ) (l : Fin (k + 1)) : Lp ℝ ∞ ν :=
  linftyIndicatorAtom ν (A j l) (hAmeas j l)

noncomputable def linftyBlockCoordinate {k : ℕ}
    (A : ℕ → Fin (k + 1) → Set β)
    (hAmeas : ∀ j l, MeasurableSet (A j l))
    (j : ℕ) (l : Fin (k + 1)) : Lp ℝ ∞ ν →L[ℝ] ℝ :=
  linftyIndicatorCoordinate ν (A j l) (hAmeas j l)

noncomputable def linftyBlockProjection {k : ℕ}
    (A : ℕ → Fin (k + 1) → Set β)
    (hAmeas : ∀ j l, MeasurableSet (A j l))
    (j : ℕ) : Lp ℝ ∞ ν →L[ℝ] Lp ℝ ∞ ν :=
  ∑ l, (linftyBlockCoordinate ν A hAmeas j l).smulRight
    (linftyBlockAtom ν A hAmeas j l)

theorem linftyBlockCoordinate_apply_atom {k : ℕ}
    (A : ℕ → Fin (k + 1) → Set β)
    (hAmeas : ∀ j l, MeasurableSet (A j l))
    (hApos : ∀ j l, ν (A j l) ≠ 0)
    (hAdisj : ∀ j l m r, (j, l) ≠ (m, r) → Disjoint (A j l) (A m r))
    (j m : ℕ) (l r : Fin (k + 1)) :
    linftyBlockCoordinate ν A hAmeas j l (linftyBlockAtom ν A hAmeas m r) =
      if (j, l) = (m, r) then 1 else 0 := by
  split_ifs with h
  · cases h
    exact linftyIndicatorCoordinate_self ν _ _ (hApos j l)
  · exact linftyIndicatorCoordinate_disjoint ν _ _ _ _ (hAdisj j l m r h)

theorem linftyBlockAtom_linearIndependent {k : ℕ}
    (A : ℕ → Fin (k + 1) → Set β)
    (hAmeas : ∀ j l, MeasurableSet (A j l))
    (hApos : ∀ j l, ν (A j l) ≠ 0)
    (hAdisj : ∀ j l m r, (j, l) ≠ (m, r) → Disjoint (A j l) (A m r))
    (j : ℕ) : LinearIndependent ℝ (linftyBlockAtom ν A hAmeas j) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have h := congrArg (linftyBlockCoordinate ν A hAmeas j l) hg
  simp only [map_sum, map_smul, map_zero] at h
  simp_rw [linftyBlockCoordinate_apply_atom ν A hAmeas hApos hAdisj] at h
  simpa using h

theorem linftyBlockProjection_apply_atom {k : ℕ}
    (A : ℕ → Fin (k + 1) → Set β)
    (hAmeas : ∀ j l, MeasurableSet (A j l))
    (hApos : ∀ j l, ν (A j l) ≠ 0)
    (hAdisj : ∀ j l m r, (j, l) ≠ (m, r) → Disjoint (A j l) (A m r))
    (j m : ℕ) (r : Fin (k + 1)) :
    linftyBlockProjection ν A hAmeas j (linftyBlockAtom ν A hAmeas m r) =
      if j = m then linftyBlockAtom ν A hAmeas m r else 0 := by
  simp only [linftyBlockProjection, _root_.sum_apply,
    ContinuousLinearMap.smulRight_apply]
  simp_rw [linftyBlockCoordinate_apply_atom ν A hAmeas hApos hAdisj]
  split_ifs with hjm
  · subst m
    simp
  · have hpair : ∀ l : Fin (k + 1), (j, l) ≠ (m, r) := by
      intro l h
      exact hjm (congrArg Prod.fst h)
    simp [hpair]

/-- A countable family of pairwise-disjoint positive measurable `(k+1)`-blocks in a finite
measure space forces a closed Hilbert cube in every exact `k`-constraint fiber of `L∞`. -/
theorem exists_closedEmbeddedHilbertCube_in_linfty_finiteConstraintFiber
    {k : ℕ} (T : (Lp ℝ ∞ ν) →L[ℝ] (Fin k → ℝ)) (base : Lp ℝ ∞ ν)
    {delta : ℝ} (hdelta : 0 < delta)
    (A : ℕ → Fin (k + 1) → Set β)
    (hAmeas : ∀ j l, MeasurableSet (A j l))
    (hApos : ∀ j l, ν (A j l) ≠ 0)
    (hAdisj : ∀ j l m r, (j, l) ≠ (m, r) → Disjoint (A j l) (A m r)) :
    ∃ v : ℕ → Lp ℝ ∞ ν, ∃ ell : ℕ → (Lp ℝ ∞ ν) →L[ℝ] ℝ,
      (∀ n, ‖v n‖ = 1) ∧ (∀ n, T (v n) = 0) ∧
      (∀ n m, ell n (v m) = if n = m then 1 else 0) ∧
      Topology.IsClosedEmbedding (affinePositiveHilbertCubeMap base delta v) ∧
      ∀ t : SignedHilbertCube,
        T (affinePositiveHilbertCubeMap base delta v t) = T base := by
  exact exists_closedEmbeddedHilbertCube_in_finiteConstraintFiber T base hdelta
    (linftyBlockAtom ν A hAmeas)
    (fun j => linftyBlockAtom_linearIndependent ν A hAmeas hApos hAdisj j)
    (linftyBlockProjection ν A hAmeas)
    (linftyBlockProjection_apply_atom ν A hAmeas hApos hAdisj)

end

end GaloisForLFunctions.HTGeometry
