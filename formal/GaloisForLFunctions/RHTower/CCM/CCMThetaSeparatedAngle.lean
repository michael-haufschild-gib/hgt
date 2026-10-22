import GaloisForLFunctions.RHTower.CCM.CCMThetaArithmeticLocalization
import GaloisForLFunctions.RHTower.CCM.CCMThetaModulusObstruction
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Compact smooth angles separating actual source supports

A positive gap between supports persists at their closures. Smooth Urysohn
separation then gives a compact Schwartz angle equal to zero on one source
and to any prescribed phase on the other. No discontinuous source cutoff
or assumed smooth separator is needed in the arithmetic applications.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped SchwartzMap Manifold ContDiff

namespace RHTower

open ThetaSourceWard

theorem disjoint_tsupport_of_positive_gap (f g : ℝ → ℝ) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ Function.support g, ∀ y ∈ Function.support f, d ≤ x - y) :
    Disjoint (tsupport f) (tsupport g) := by
  have hg (x : ℝ) (hx : x ∈ Function.support g) :
      ∀ y ∈ tsupport f, d ≤ x - y := by
    exact closure_minimal (hgap x hx)
      (isClosed_le continuous_const (continuous_const.sub continuous_id))
  have hfg (y : ℝ) (hy : y ∈ tsupport f) :
      ∀ x ∈ tsupport g, d ≤ x - y := by
    exact closure_minimal (fun x hx => hg x hx y hy)
      (isClosed_le continuous_const (continuous_id.sub continuous_const))
  exact Set.disjoint_left.mpr fun x hx hxg => by
    have := hfg x hx x hxg
    linarith

/-- A real Schwartz phase separates any closed set from a disjoint compact set. -/
theorem exists_schwartz_separating_angle {s t : Set ℝ}
    (hs : IsClosed s) (ht : IsCompact t) (hd : Disjoint s t) (phase : ℝ) :
    ∃ theta : 𝓢(ℝ, ℝ), HasCompactSupport theta ∧
      (∀ x ∈ s, theta x = 0) ∧ (∀ x ∈ t, theta x = phase) := by
  obtain ⟨d, hdp, hsub⟩ := ht.exists_cthickening_subset_open hs.isOpen_compl
    (Set.disjoint_right.mp hd)
  have hdisj : Disjoint (Metric.thickening d t)ᶜ t := by
    exact Set.disjoint_left.mpr fun x hx hxt => hx (Metric.self_subset_thickening hdp t hxt)
  obtain ⟨f, hf0, hf1, _⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (I := 𝓘(ℝ, ℝ)) (M := ℝ) (n := (⊤ : ℕ∞))
    Metric.isOpen_thickening.isClosed_compl ht.isClosed hdisj
  have hfs : Function.support (f : ℝ → ℝ) ⊆ Metric.thickening d t := by
    intro x hx
    by_contra hout
    exact hx (hf0 hout)
  have hft : tsupport (f : ℝ → ℝ) ⊆ Metric.cthickening d t :=
    (closure_mono hfs).trans (Metric.closure_thickening_subset_cthickening _ _)
  have hfc : HasCompactSupport (f : ℝ → ℝ) :=
    (ht.cthickening).of_isClosed_subset (isClosed_tsupport _) hft
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℝ) :=
    contMDiff_iff_contDiff.mp f.contMDiff
  have htc : HasCompactSupport (fun x : ℝ => phase * f x) :=
    hfc.comp_left (g := fun z : ℝ => phase * z) (mul_zero phase)
  let theta : 𝓢(ℝ, ℝ) := htc.toSchwartzMap (contDiff_const.mul hfd)
  refine ⟨theta, htc, ?_, ?_⟩
  · intro x hx
    have hx0 : f x = 0 := by
      apply hf0
      intro hxt
      exact hsub (Metric.thickening_subset_cthickening _ _ hxt) hx
    change phase * f x = 0
    rw [hx0, mul_zero]
  · intro x hx
    change phase * f x = phase
    rw [hf1 hx, Pi.one_apply, mul_one]

/-- The actual positive continuous-coupling witnesses admit a compact smooth phase separator. -/
theorem exists_separated_thetaArithmetic_phase_pair :
    ∃ phi psi : 𝓢(ℝ, ℝ),
      HasCompactSupport phi ∧ HasCompactSupport psi ∧
      (∀ x, 0 ≤ phi x) ∧ (∀ x, 0 ≤ psi x) ∧
      Disjoint (tsupport phi) (tsupport psi) ∧
      (∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y) ∧
      (∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
        ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n) ∧
      0 < thetaGammaPolarGroundCrossPairing phi psi ∧
      ∀ phase : ℝ, ∃ theta : 𝓢(ℝ, ℝ), HasCompactSupport theta ∧
        (∀ x ∈ tsupport phi, theta x = 0) ∧
        (∀ x ∈ tsupport psi, theta x = phase) := by
  obtain ⟨phi, psi, hp, hq, _, hg, _, hc, hpc, hqc⟩ :=
    exists_disjoint_positive_compact_thetaGammaPolarGroundCrossPairing
  have hd := disjoint_tsupport_of_positive_gap phi psi
    GaloisForLFunctions.RHTower.screwSignThreshold_pos
    (fun x hx y hy => (hg x hx y hy).1.le)
  refine ⟨phi, psi, hpc, hqc, hp, hq, hd, ?_, ?_, hc, ?_⟩
  · exact fun x hx y hy => GaloisForLFunctions.RHTower.screwSignThreshold_pos.trans
      (hg x hx y hy).1
  · exact fun x hx y hy => (hg x hx y hy).2
  · exact fun phase => exists_schwartz_separating_angle (isClosed_tsupport _) hqc hd phase

end RHTower
