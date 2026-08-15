import GaloisForLFunctions.SelbergClass.MultipleStandardTwistInitialHolomorphy
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex

/-!
# Uniqueness from the initial multiple-twist domain

The initial domain of a multiple standard twist is a nonempty open convex
product of right half-planes.  Hence two globally analytic functions that
agree with the initial tensor there agree on all of `ℂ^N`.  This is a
uniqueness statement only: it constructs no analytic or meromorphic
continuation.
-/

open Complex Filter Set
open scoped Topology

namespace GaloisForLFunctions.SelbergClass

/-- The initial multiple-twist domain is open. -/
theorem isOpen_multipleStandardTwistInitialDomain (N : ℕ) :
    IsOpen (multipleStandardTwistInitialDomain N) := by
  rw [multipleStandardTwistInitialDomain]
  rw [show {s : Fin N → ℂ | ∀ i, 1 < (s i).re} =
      ⋂ i : Fin N, (fun s : Fin N → ℂ => s i) ⁻¹' {z : ℂ | 1 < z.re} by
    ext s
    simp]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_Ioi.preimage (continuous_re.comp (continuous_apply i))

/-- The initial multiple-twist domain contains the constant point `2`. -/
theorem multipleStandardTwistInitialDomain_nonempty (N : ℕ) :
    (multipleStandardTwistInitialDomain N).Nonempty := by
  refine ⟨fun _ => (2 : ℂ), ?_⟩
  simp [multipleStandardTwistInitialDomain]

/-- The initial multiple-twist domain is convex over the reals. -/
theorem convex_multipleStandardTwistInitialDomain (N : ℕ) :
    Convex ℝ (multipleStandardTwistInitialDomain N) := by
  rw [multipleStandardTwistInitialDomain]
  rw [show {s : Fin N → ℂ | ∀ i, 1 < (s i).re} =
      Set.univ.pi fun _ : Fin N => {z : ℂ | 1 < z.re} by
    ext s
    simp]
  exact convex_pi fun _ _ => convex_halfSpace_re_gt 1

/-- The initial multiple-twist domain is preconnected. -/
theorem isPreconnected_multipleStandardTwistInitialDomain (N : ℕ) :
    IsPreconnected (multipleStandardTwistInitialDomain N) :=
  (convex_multipleStandardTwistInitialDomain N).isPreconnected

/-- Globally analytic functions on `ℂ^N` are uniquely determined by their
values on the initial multiple-twist domain. -/
theorem eq_of_analyticOnNhd_eqOn_multipleStandardTwistInitialDomain
    {N : ℕ} (f g : (Fin N → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfg : EqOn f g (multipleStandardTwistInitialDomain N)) : f = g := by
  let z0 : Fin N → ℂ := fun _ => 2
  have hz0 : z0 ∈ multipleStandardTwistInitialDomain N := by
    simp [z0, multipleStandardTwistInitialDomain]
  apply AnalyticOnNhd.eq_of_eventuallyEq hf hg
  filter_upwards [isOpen_multipleStandardTwistInitialDomain N |>.mem_nhds hz0] with z hz
  exact hfg hz

/-- A globally analytic candidate agreeing with the initial tensor is unique
among globally analytic candidates.  This does not assert that any candidate
exists. -/
theorem MultipleStandardTwistData.eq_of_analyticOnNhd_eqOn_initial
    {N : ℕ} (D : MultipleStandardTwistData N) (f g : (Fin N → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hf_initial : EqOn f D.initial (multipleStandardTwistInitialDomain N))
    (hg_initial : EqOn g D.initial (multipleStandardTwistInitialDomain N)) : f = g := by
  apply eq_of_analyticOnNhd_eqOn_multipleStandardTwistInitialDomain f g hf hg
  intro s hs
  exact (hf_initial hs).trans (hg_initial hs).symm

end GaloisForLFunctions.SelbergClass
