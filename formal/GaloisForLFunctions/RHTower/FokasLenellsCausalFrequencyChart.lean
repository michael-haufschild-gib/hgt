import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedFrequencyMeans
/-! Exact redundancy of normalized boundary-frequency charts.
Positive raw-rate rescaling preserves the actual normalized rate, rational datum,
whole derivative chain and frequency mean. Equality of actual rates, data and chains
is classified by the same cross-multiplied frequency invariant. -/
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalFrequencyChartLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalFrequencyChartChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalFrequencyChartChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalFrequencyChartChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalFrequencyChartEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedRing

private theorem normalize_positive_mul (a : ℝ) (ha : 0 < a) (z : ℂ) :
    ((a : ℂ) * z) / (‖(a : ℂ) * z‖ : ℂ) = z / (‖z‖ : ℂ) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le, Complex.ofReal_mul]
  exact mul_div_mul_left z (‖z‖ : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt ha))

private theorem unit_eigenvalue_unique
    {D E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S J : D → E) (v w : D) (hv : ‖J v‖ = 1) (z t : ℂ)
    (hz : S v = z • J v) (ht : S w = t • J w) (hvw : v = w) : z = t := by
  have hn : J v ≠ 0 := by intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  apply smul_left_injective ℂ hn
  exact hz.symm.trans ((congrArg S hvw).trans
    (ht.trans (congrArg (fun x : D => t • J x) hvw.symm)))

private theorem exp_rescale (b c : ℝ) : Real.exp (c-b) * Real.exp b = Real.exp c := by
  rw [← Real.exp_add, sub_add_cancel]

private theorem boundary_rate_rescale (b c ω : ℝ) :
    (causalBoundaryRate c (Real.exp (c-b)*ω)).val =
      (Real.exp (c-b) : ℂ) * (causalBoundaryRate b ω).val := by
  have he := congrArg (fun r : ℝ => (r : ℂ)) (exp_rescale b c)
  rw [Complex.ofReal_mul] at he
  change -(Real.exp c : ℂ) + ((Real.exp (c-b)*ω : ℝ) : ℂ)*I =
    (Real.exp (c-b) : ℂ) * (-(Real.exp b : ℂ) + (ω : ℂ)*I)
  rw [← he, Complex.ofReal_mul]
  ring

private theorem scaled_frequency_eq_iff (b c ω η : ℝ) :
    Real.exp (c-b)*ω = η ↔ ω*Real.exp c = η*Real.exp b := by
  have he := exp_rescale b c
  constructor
  · intro h
    calc
      ω*Real.exp c = (Real.exp (c-b)*ω)*Real.exp b := by rw [← he]; ring
      _ = η*Real.exp b := congrArg (fun x : ℝ => x*Real.exp b) h
  · intro h
    apply mul_right_cancel₀ (Real.exp_ne_zero b)
    calc
      (Real.exp (c-b)*ω)*Real.exp b = ω*Real.exp c := by rw [← he]; ring
      _ = η*Real.exp b := h

/-- Positive relabeling between any two damping charts preserves the actual normalized rate. -/
theorem causalUnitBoundaryRate_rescale (b c ω : ℝ) :
    causalUnitBoundaryRate c (Real.exp (c-b)*ω) = causalUnitBoundaryRate b ω := by
  apply Subtype.ext
  change (causalBoundaryRate c (Real.exp (c-b)*ω)).val /
      (‖(causalBoundaryRate c (Real.exp (c-b)*ω)).val‖ : ℂ) =
    (causalBoundaryRate b ω).val / (‖(causalBoundaryRate b ω).val‖ : ℂ)
  rw [boundary_rate_rescale b c ω]
  exact normalize_positive_mul (Real.exp (c-b)) (Real.exp_pos _) (causalBoundaryRate b ω).val

/-- Complete classification of duplicate normalized-rate labels across different charts. -/
theorem causalUnitBoundaryRate_eq_iff (b c ω η : ℝ) :
    (causalUnitBoundaryRate b ω).val = (causalUnitBoundaryRate c η).val ↔
      ω*Real.exp c = η*Real.exp b := by
  have hr := congrArg Subtype.val (causalUnitBoundaryRate_rescale b c ω)
  constructor
  · intro h
    exact (scaled_frequency_eq_iff b c ω η).mp ((causalUnitBoundaryRate_injective c) (hr.trans h))
  · intro h
    exact hr.symm.trans (congrArg (fun t : ℝ => (causalUnitBoundaryRate c t).val)
      ((scaled_frequency_eq_iff b c ω η).mpr h))

/-- The original normalized rational datum is unchanged by the exact frequency relabeling. -/
theorem causalUnitBoundaryEigenvector_rescale (b c ω : ℝ) :
    causalUnitBoundaryEigenvector c (Real.exp (c-b)*ω) = causalUnitBoundaryEigenvector b ω := by
  unfold causalUnitBoundaryEigenvector
  rw [causalUnitBoundaryRate_rescale b c ω]

/-- Equality of original normalized rational data is exactly equality of the reduced frequency. -/
theorem causalUnitBoundaryEigenvector_eq_iff (b c ω η : ℝ) :
    causalUnitBoundaryEigenvector b ω = causalUnitBoundaryEigenvector c η ↔
      ω*Real.exp c = η*Real.exp b := by
  constructor
  · intro h
    have hr := unit_eigenvalue_unique causalGenerator (fun u : causalGeneratorDomain => u.val)
      (causalUnitBoundaryEigenvector b ω) (causalUnitBoundaryEigenvector c η)
      (norm_causalUnitBoundaryEigenvector b ω)
      (causalUnitBoundaryRate b ω).val (causalUnitBoundaryRate c η).val
      (causalGenerator_unitBoundaryEigenvector b ω) (causalGenerator_unitBoundaryEigenvector c η) h
    exact (causalUnitBoundaryRate_eq_iff b c ω η).mp hr
  · intro h
    exact (causalUnitBoundaryEigenvector_rescale b c ω).symm.trans
      (congrArg (causalUnitBoundaryEigenvector c) ((scaled_frequency_eq_iff b c ω η).mpr h))

/-- Every genuine derivative coordinate is preserved by relabeling the normalized frequency chart. -/
theorem causalBoundedUnitEigenchain_rescale (b c ω : ℝ) :
    causalBoundedUnitEigenchain c (Real.exp (c-b)*ω) = causalBoundedUnitEigenchain b ω := by
  apply Subtype.ext
  apply lp.ext
  funext j
  change (causalUnitBoundaryRate c (Real.exp (c-b)*ω)).val^j •
      (causalUnitBoundaryEigenvector c (Real.exp (c-b)*ω)).val =
    (causalUnitBoundaryRate b ω).val^j • (causalUnitBoundaryEigenvector b ω).val
  rw [causalUnitBoundaryRate_rescale b c ω, causalUnitBoundaryEigenvector_rescale b c ω]

/-- Actual unit derivative chains coincide exactly at the same reduced frequency. -/
theorem causalBoundedUnitEigenchain_eq_iff (b c ω η : ℝ) :
    causalBoundedUnitEigenchain b ω = causalBoundedUnitEigenchain c η ↔
      ω*Real.exp c = η*Real.exp b := by
  constructor
  · intro h
    have hr := unit_eigenvalue_unique causalBoundedChainShift (fun u : causalBoundedChain => u)
      (causalBoundedUnitEigenchain b ω) (causalBoundedUnitEigenchain c η)
      (norm_causalBoundedUnitEigenchain b ω)
      (causalUnitBoundaryRate b ω).val (causalUnitBoundaryRate c η).val
      (causalBoundedChainShift_unitEigenchain b ω) (causalBoundedChainShift_unitEigenchain c η) h
    exact (causalUnitBoundaryRate_eq_iff b c ω η).mp hr
  · intro h
    exact (causalBoundedUnitEigenchain_rescale b c ω).symm.trans
      (congrArg (causalBoundedUnitEigenchain c) ((scaled_frequency_eq_iff b c ω η).mpr h))

/-- The actual bounded frequency-mean operator is independent of the chosen chart after relabeling. -/
theorem causalBoundedFrequencyMean_rescale (b c ω : ℝ) (N : ℕ) :
    causalBoundedFrequencyMean c (Real.exp (c-b)*ω) N = causalBoundedFrequencyMean b ω N := by
  exact congrArg (fun r : {z : ℂ // z.re < 0} =>
    (((N : ℝ)⁻¹ : ℂ)) • ∑ j ∈ Finset.range N,
      (r.val⁻¹)^j • causalBoundedChainShift^j) (causalUnitBoundaryRate_rescale b c ω)
end
end RHTower.FokasLenells
