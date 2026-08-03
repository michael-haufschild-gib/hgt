import GaloisForLFunctions.HTGeometry.BarnesConeProduct
import GaloisForLFunctions.HTGeometry.MeromorphicMultipleEllipticGamma

/-!
# The Barnes source in the global meromorphic differential field

The cone product is entire and takes the value one at the origin, because every elementary factor
does.  So it is a nonzero element of the analytic germ domain, hence a nonzero element of the
global meromorphic field, and its logarithmic derivative is a genuine element of that differential
field.

That logarithmic derivative is the Barnes source up to the linear factor and the normalization
exponential.  Both of those are differentially algebraic, so they are invisible to every
annihilator statement taken modulo the differentially algebraic sector — which is the only way the
Barnes translation-annihilator theorem uses the source.
-/

open Filter Topology Set Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι]

local instance barnesUnivDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

/-! ## The product is nonzero -/

omit [Nonempty ι] in
@[simp] theorem barnesConeFactor_zero_arg (ω : ι → ℂ) (n : ι → ℕ) :
    barnesConeFactor ω n 0 = 1 := by
  rw [barnesConeFactor]
  split_ifs with h
  · rfl
  · rw [zero_div, neg_zero, weierstrassFactor_zero_arg]

omit [Nonempty ι] in
theorem barnesConeProduct_zero_arg (ω : ι → ℂ) : barnesConeProduct ω 0 = 1 := by
  rw [barnesConeProduct]
  simp only [barnesConeFactor_zero_arg]
  exact tprod_one

omit [Nonempty ι] in
theorem barnesConeProduct_ne_zero (ω : ι → ℂ) : barnesConeProduct ω ≠ 0 := by
  intro hzero
  have h0 := congrFun hzero 0
  rw [barnesConeProduct_zero_arg] at h0
  exact one_ne_zero h0

/-! ## The entire germ -/

/-- The Barnes cone product in the global analytic germ domain. -/
def barnesConeAnalytic (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    analyticSubring (Set.univ : Set ℂ) :=
  ⟨Germ.coeRingHom (𝓟 Set.univ) (barnesConeProduct ω),
    ⟨_, by
      rw [Complex.analyticOnNhd_univ_iff_differentiable]
      exact differentiable_barnesConeProduct ω hω, rfl⟩⟩

theorem barnesConeAnalytic_ne_zero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    barnesConeAnalytic ω hω ≠ 0 := by
  intro hzero
  have hv := congrArg Subtype.val hzero
  simp only [barnesConeAnalytic, ZeroMemClass.coe_zero] at hv
  change Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ)) (barnesConeProduct ω) =
    Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ)) (fun _ : ℂ => 0) at hv
  rw [Germ.coe_eq] at hv
  have h0 := eventually_principal.mp hv 0 (Set.mem_univ 0)
  rw [barnesConeProduct_zero_arg] at h0
  exact one_ne_zero h0

/-! ## The meromorphic source -/

/-- The Barnes cone product as an element of the global meromorphic field. -/
def barnesConeMero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) : meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
    (barnesConeAnalytic ω hω)

theorem barnesConeMero_ne_zero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    barnesConeMero ω hω ≠ 0 := by
  rw [barnesConeMero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    (barnesConeAnalytic_ne_zero ω hω)

/-- **The Barnes source.**  The logarithmic derivative of the cone product in the global
meromorphic differential field: the Barnes multiple-gamma logarithmic derivative up to the linear
factor and the normalization exponential, both of which are differentially algebraic. -/
def barnesSourceLogDerivMero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    meroField (Set.univ : Set ℂ) := by
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  exact Differential.logDeriv (barnesConeMero ω hω)

end

end GaloisForLFunctions
