import GaloisForLFunctions.HTGeometry.MeroRankThreeIncrementCollapse
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationDerivative
import GaloisForLFunctions.HTGeometry.AllDepthCarrierJets

/-!
# Transporting function identities into the meromorphic field

A meromorphic germ is determined by the function it realizes, up to agreement on punctured
neighbourhoods: if the realized functions agree off their poles, the germs are equal.  Together with
additivity, scalar multiples and the realization of constants this moves an identity proved about
functions into the global meromorphic differential field, where the elliptic-gamma matroid lives.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- **A germ realizing a function that vanishes off its poles is zero.** -/
theorem eq_zero_of_realizesMero_eventually_zero {x : meroField (Set.univ : Set ℂ)} {h : ℂ → ℂ}
    (hx : RealizesMero x h) (hz : ∀ z, ∀ᶠ w in 𝓝[≠] z, h w = 0) : x = 0 := by
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hxab, hfAB⟩ := hx
  have hBne : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, B w ≠ 0 := by
    intro z
    exact eventually_nhdsNE_ne_zero_of_germ_ne_zero hb0 hB hBb z
  have hAz : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, A w = 0 := by
    intro z
    filter_upwards [hBne z, hz z] with w hw1 hw2
    have hval := hfAB w hw1
    rw [hw2] at hval
    have hdiv : A w / B w = 0 := hval.symm
    exact (div_eq_zero_iff.mp hdiv).resolve_right hw1
  have hA0 : ∀ z, A z = 0 := by
    intro z
    have hcont : Tendsto A (𝓝[≠] z) (𝓝 (A z)) :=
      ((hA z (Set.mem_univ z)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hzero : Tendsto A (𝓝[≠] z) (𝓝 0) := by
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℂ)))
      filter_upwards [hAz z] with w hw
      exact hw.symm
    exact tendsto_nhds_unique hcont hzero
  have ha0 : a = 0 := by
    apply Subtype.ext
    rw [← hAa, show A = 0 from funext hA0]
    simp
  rw [hxab, ha0, map_zero, zero_div]

/-- The complex constants are realized by the constant functions. -/
theorem realizesMero_algebraMap_complex (c : ℂ) :
    RealizesMero (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) (fun _ : ℂ => c) := by
  refine ⟨constToAnalytic Set.univ c, 1, (fun _ : ℂ => c), 1, one_ne_zero,
    analyticOnNhd_const, analyticOnNhd_const, rfl, ?_, ?_, fun z _ => ?_⟩
  · show Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (1 : ℂ → ℂ)
      = ((1 : analyticSubring (Set.univ : Set ℂ)) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
    simp
  · rw [map_one, div_one, algebraMap_complex_eq_constToAnalytic]
  · simp

/-- Negatives of realized functions are realized. -/
theorem realizesMero_neg {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (hx : RealizesMero x f) : RealizesMero (-x) (fun z => -f z) := by
  have h := realizesMero_const_mul (-1) hx
  rw [algebraMap_complex_eq_constToAnalytic] at h
  have hx1 : algebraMap ℂ (meroField (Set.univ : Set ℂ)) (-1) * x = -x := by
    rw [map_neg, map_one, neg_mul, one_mul]
  have hf1 : (fun z => (-1 : ℂ) * f z) = fun z => -f z := by
    funext z
    ring
  rwa [hx1, hf1] at h

/-- **Realization is faithful up to punctured agreement.** -/
theorem realizesMero_eq_of_eventuallyEq {x y : meroField (Set.univ : Set ℂ)} {f g : ℂ → ℂ}
    (hx : RealizesMero x f) (hy : RealizesMero y g)
    (heq : ∀ z, ∀ᶠ w in 𝓝[≠] z, f w = g w) : x = y := by
  have hsub := realizesMero_sub hx hy
  have hzero : ∀ z, ∀ᶠ w in 𝓝[≠] z, f w - g w = 0 := by
    intro z
    filter_upwards [heq z] with w hw
    rw [hw, sub_self]
  have := eq_zero_of_realizesMero_eventually_zero hsub hzero
  linear_combination this

end

end GaloisForLFunctions.HTGeometry
