import GaloisForLFunctions.RHTower.RealCoronaHolomorphicReflectionCrossedProduct
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianResidueNonadmission
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# The actual Riemann-Xi Real corona is not endpoint-holomorphically smooth

This file closes the first unconditional automorphic case of P3.  Center the completed Riemann
zeta divisor at the functional-equation fixed point and use the projective coordinate
`(rho - 1/2)⁻¹`.  Both height ends then accumulate at the single finite endpoint `0`, while the
functional equation `rho ↦ 1-rho` becomes the holomorphic involution `w ↦ -w`.

The upper/lower characteristic idempotent exists in the full divisor function algebra, but the
identity theorem excludes it from the natural dense algebra of restrictions of entire functions.
The same exclusion holds in the honest order-two skew crossed product.  No zero-density estimate,
RH, or unproved automorphic input is used: infinitude and local finiteness of the actual Xi divisor
already imply unbounded ordinates.
-/

noncomputable section

open Complex Set Metric

namespace RHTower

open DeningerMeyerGaussianGreen
open GaloisForLFunctions.RHTower

/-- Projective coordinate centered at the Riemann-Xi functional-equation fixed point. -/
def xiCenteredReciprocal (rho : ℂ) : ℂ :=
  (rho - 1 / 2)⁻¹

@[simp] theorem xiCenteredReciprocal_one_sub (rho : ℂ) :
    xiCenteredReciprocal (1 - rho) = -xiCenteredReciprocal rho := by
  simp only [xiCenteredReciprocal]
  rw [show 1 - rho - 1 / 2 = -(rho - 1 / 2) by ring, inv_neg]

/-- The compactified positive-height Xi divisor. -/
def xiCompactifiedUpperZeroSector : Set ℂ :=
  {w | ∃ rho : ℂ, xi rho = 0 ∧ 0 < rho.im ∧ w = xiCenteredReciprocal rho}

/-- The compactified negative-height Xi divisor. -/
def xiCompactifiedLowerZeroSector : Set ℂ :=
  {w | ∃ rho : ℂ, xi rho = 0 ∧ rho.im < 0 ∧ w = xiCenteredReciprocal rho}

theorem xiCenteredReciprocal_ne_zero_of_xi_zero {rho : ℂ} (hrho : xi rho = 0) :
    xiCenteredReciprocal rho ≠ 0 := by
  let q : XiDivisorSupport := ⟨rho, mem_xi_divisor_support_of_eq_zero hrho⟩
  exact inv_ne_zero (sub_ne_zero.mpr (xi_divisor_support_ne_half q))

/-- Every positive height threshold is crossed by an actual Xi zero in the upper half-plane. -/
theorem exists_xi_zero_im_gt {T : ℝ} (hT : 0 ≤ T) :
    ∃ rho : ℂ, xi rho = 0 ∧ 0 < rho.im ∧ T < rho.im := by
  obtain ⟨rho, hrho, hheight⟩ := exists_xiZero_im_gt T
  change xi rho = 0 at hrho
  by_cases him : 0 < rho.im
  · refine ⟨rho, hrho, him, ?_⟩
    simpa [abs_of_pos him] using hheight
  · have himle : rho.im ≤ 0 := le_of_not_gt him
    have himlt : rho.im < 0 := by
      have habspos : 0 < |rho.im| := lt_of_le_of_lt hT hheight
      exact lt_of_le_of_ne himle (fun heq => by simpa [heq] using habspos)
    refine ⟨1 - rho, ?_, ?_, ?_⟩
    · simpa [xi_one_sub] using hrho
    · simp only [Complex.sub_im, Complex.one_im]
      linarith
    · rw [abs_of_neg himlt] at hheight
      simp only [Complex.sub_im, Complex.one_im]
      linarith

/-- Functional-equation reflection exchanges the two compactified height sectors. -/
theorem neg_mem_xiCompactifiedUpper_iff_mem_lower (w : ℂ) :
    -w ∈ xiCompactifiedUpperZeroSector ↔
      w ∈ xiCompactifiedLowerZeroSector := by
  constructor
  · rintro ⟨rho, hrho, him, hcoord⟩
    refine ⟨1 - rho, ?_, ?_, ?_⟩
    · simpa [xi_one_sub] using hrho
    · simp only [Complex.sub_im, Complex.one_im]
      linarith
    · rw [xiCenteredReciprocal_one_sub, ← hcoord]
      simp
  · rintro ⟨rho, hrho, him, hcoord⟩
    refine ⟨1 - rho, ?_, ?_, ?_⟩
    · simpa [xi_one_sub] using hrho
    · simp only [Complex.sub_im, Complex.one_im]
      linarith
    · rw [xiCenteredReciprocal_one_sub, ← hcoord]

theorem neg_mem_xiCompactifiedLower_iff_mem_upper (w : ℂ) :
    -w ∈ xiCompactifiedLowerZeroSector ↔
      w ∈ xiCompactifiedUpperZeroSector := by
  simpa using (neg_mem_xiCompactifiedUpper_iff_mem_lower (-w)).symm

/-- Upper and lower compactified sectors are disjoint. -/
theorem xiCompactifiedZeroSectors_disjoint :
    Disjoint xiCompactifiedUpperZeroSector xiCompactifiedLowerZeroSector := by
  rw [Set.disjoint_left]
  intro w hwUpper hwLower
  rcases hwUpper with ⟨rho, hrho, hrhoIm, hwRho⟩
  rcases hwLower with ⟨sigma, hsigma, hsigmaIm, hwSigma⟩
  have hinv : (rho - 1 / 2)⁻¹ = (sigma - 1 / 2)⁻¹ := by
    simpa only [xiCenteredReciprocal] using hwRho.symm.trans hwSigma
  have hcenter : rho - 1 / 2 = sigma - 1 / 2 := inv_injective hinv
  have hrs : rho = sigma := by
    calc
      rho = (rho - 1 / 2) + 1 / 2 := by ring
      _ = (sigma - 1 / 2) + 1 / 2 := congrArg (fun z : ℂ => z + 1 / 2) hcenter
      _ = sigma := by ring
  have himEq : rho.im = sigma.im := congrArg Complex.im hrs
  linarith

theorem zero_not_mem_xiCompactifiedUpperZeroSector :
    (0 : ℂ) ∉ xiCompactifiedUpperZeroSector := by
  rintro ⟨rho, hrho, _, hcoord⟩
  exact xiCenteredReciprocal_ne_zero_of_xi_zero hrho hcoord.symm

theorem zero_not_mem_xiCompactifiedLowerZeroSector :
    (0 : ℂ) ∉ xiCompactifiedLowerZeroSector := by
  rintro ⟨rho, hrho, _, hcoord⟩
  exact xiCenteredReciprocal_ne_zero_of_xi_zero hrho hcoord.symm

/-- The positive-height compactified divisor accumulates at its projective endpoint. -/
theorem zero_mem_closure_xiCompactifiedUpperZeroSector :
    (0 : ℂ) ∈ closure (xiCompactifiedUpperZeroSector \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro epsilon hepsilon
  obtain ⟨rho, hrho, hrhoIm, hheight⟩ :=
    exists_xi_zero_im_gt (T := 1 / epsilon) (by positivity)
  let w := xiCenteredReciprocal rho
  have hwne : w ≠ 0 := xiCenteredReciprocal_ne_zero_of_xi_zero hrho
  refine ⟨w, ⟨⟨rho, hrho, hrhoIm, rfl⟩, ?_⟩, ?_⟩
  · simpa only [Set.mem_singleton_iff] using hwne
  · change dist 0 (xiCenteredReciprocal rho) < epsilon
    rw [dist_zero_left, xiCenteredReciprocal, norm_inv]
    have himNorm : rho.im ≤ ‖rho - 1 / 2‖ := by
      have h := Complex.abs_im_le_norm (rho - 1 / 2)
      simpa [abs_of_pos hrhoIm] using h
    calc
      ‖rho - 1 / 2‖⁻¹ ≤ 1 / rho.im :=
        by simpa only [one_div] using one_div_le_one_div_of_le hrhoIm himNorm
      _ < epsilon := (one_div_lt hepsilon hrhoIm).mp hheight

/-- The negative-height compactified divisor has the same projective endpoint. -/
theorem zero_mem_closure_xiCompactifiedLowerZeroSector :
    (0 : ℂ) ∈ closure (xiCompactifiedLowerZeroSector \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro epsilon hepsilon
  obtain ⟨w, hw, hdist⟩ :=
    (Metric.mem_closure_iff.mp zero_mem_closure_xiCompactifiedUpperZeroSector)
      epsilon hepsilon
  refine ⟨-w, ?_, ?_⟩
  · constructor
    · exact (neg_mem_xiCompactifiedLower_iff_mem_upper w).mpr hw.1
    · simpa only [Set.mem_singleton_iff, neg_eq_zero] using hw.2
  · simpa [dist_zero_left] using hdist

/-- Each compactified height sector is genuinely infinite. -/
theorem xiCompactifiedUpperZeroSector_infinite :
    xiCompactifiedUpperZeroSector.Infinite := by
  intro hfinite
  have hclosed : IsClosed (xiCompactifiedUpperZeroSector \ {0}) :=
    hfinite.sdiff.isClosed
  have hmem : (0 : ℂ) ∈ xiCompactifiedUpperZeroSector \ {0} := by
    rw [← hclosed.closure_eq]
    exact zero_mem_closure_xiCompactifiedUpperZeroSector
  exact hmem.2 rfl

theorem xiCompactifiedLowerZeroSector_infinite :
    xiCompactifiedLowerZeroSector.Infinite := by
  intro hfinite
  have hclosed : IsClosed (xiCompactifiedLowerZeroSector \ {0}) :=
    hfinite.sdiff.isClosed
  have hmem : (0 : ℂ) ∈ xiCompactifiedLowerZeroSector \ {0} := by
    rw [← hclosed.closure_eq]
    exact zero_mem_closure_xiCompactifiedLowerZeroSector
  exact hmem.2 rfl

/-- Negation preserves the complete compactified divisor. -/
theorem xiCompactifiedZeroSectors_neg_mapsTo :
    MapsTo (-·)
      (xiCompactifiedUpperZeroSector ∪ xiCompactifiedLowerZeroSector)
      (xiCompactifiedUpperZeroSector ∪ xiCompactifiedLowerZeroSector) := by
  intro w hw
  rcases hw with hw | hw
  · exact Or.inr ((neg_mem_xiCompactifiedLower_iff_mem_upper w).mpr hw)
  · exact Or.inl ((neg_mem_xiCompactifiedUpper_iff_mem_lower w).mpr hw)

/-- Honest holomorphic order-two reflection induced by the Xi functional equation. -/
def xiCompactifiedHolomorphicReflection :
    GaloisForLFunctions.RHTower.HolomorphicDivisorReflection Set.univ
      (xiCompactifiedUpperZeroSector ∪ xiCompactifiedLowerZeroSector) :=
  GaloisForLFunctions.RHTower.negationHolomorphicDivisorReflection _
    xiCompactifiedZeroSectors_neg_mapsTo

/-- The actual Xi corona has the expected odd Real parity under functional-equation reflection. -/
theorem xiCompactified_odd_smul_corona_eq_complement :
    let R := xiCompactifiedHolomorphicReflection
    letI := R.functionAction
    ReflectionParity.odd •
        endpointRealCoronaIdempotent
          xiCompactifiedUpperZeroSector xiCompactifiedLowerZeroSector =
      1 - endpointRealCoronaIdempotent
          xiCompactifiedUpperZeroSector xiCompactifiedLowerZeroSector := by
  let R := xiCompactifiedHolomorphicReflection
  letI := R.functionAction
  apply R.odd_smul_endpointRealCoronaIdempotent_eq_complement
    xiCompactifiedZeroSectors_disjoint
  intro w
  change -(w : ℂ) ∈ xiCompactifiedUpperZeroSector ↔
    (w : ℂ) ∈ xiCompactifiedLowerZeroSector
  exact neg_mem_xiCompactifiedUpper_iff_mem_lower w

/-- Exact actual-automorphic P3 classification in the holomorphic reflection crossed product. -/
theorem xiCompactifiedCorona_crossedProduct_iff_finite :
    let R := xiCompactifiedHolomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((xiCompactifiedUpperZeroSector ∪ xiCompactifiedLowerZeroSector : Set ℂ) → ℂ)) :=
      R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent
          xiCompactifiedUpperZeroSector xiCompactifiedLowerZeroSector) ∈
      Set.range
        (InvariantSubalgebra.crossedProductInclusion
          (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) ↔
      xiCompactifiedUpperZeroSector.Finite ∧
        xiCompactifiedLowerZeroSector.Finite := by
  let R := xiCompactifiedHolomorphicReflection
  letI := R.functionAction
  letI : SMulCommClass ReflectionParity ℂ
      (((xiCompactifiedUpperZeroSector ∪ xiCompactifiedLowerZeroSector : Set ℂ) → ℂ)) :=
    R.functionSmulCommClass
  exact
    GaloisForLFunctions.RHTower.HolomorphicDivisorReflection.reflectedEndpointCorona_crossedProduct_iff_finite
        R isPreconnected_univ (Set.subset_univ _) (Set.subset_univ _)
        xiCompactifiedUpperZeroSector_infinite.nonempty
        xiCompactifiedLowerZeroSector_infinite.nonempty
        (Set.mem_univ 0) (Set.mem_univ 0)
        (fun _ => zero_mem_closure_xiCompactifiedUpperZeroSector)
        (fun _ => zero_mem_closure_xiCompactifiedLowerZeroSector)
        xiCompactifiedZeroSectors_disjoint

/-- **P3, actual completed automorphic instance.**  The Riemann-Xi Real-corona idempotent is not
smooth in the natural dense endpoint-entire crossed product. -/
theorem xiCompactifiedCorona_not_mem_smoothCrossedProductRange :
    let R := xiCompactifiedHolomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((xiCompactifiedUpperZeroSector ∪ xiCompactifiedLowerZeroSector : Set ℂ) → ℂ)) :=
      R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent
          xiCompactifiedUpperZeroSector xiCompactifiedLowerZeroSector) ∉
      Set.range
        (InvariantSubalgebra.crossedProductInclusion
          (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) := by
  dsimp only
  let R := xiCompactifiedHolomorphicReflection
  letI := R.functionAction
  letI : SMulCommClass ReflectionParity ℂ
      (((xiCompactifiedUpperZeroSector ∪ xiCompactifiedLowerZeroSector : Set ℂ) → ℂ)) :=
    R.functionSmulCommClass
  intro hmem
  have hiff :
      SkewMonoidAlgebra.single (1 : ReflectionParity)
          (endpointRealCoronaIdempotent
            xiCompactifiedUpperZeroSector xiCompactifiedLowerZeroSector) ∈
        Set.range
          (InvariantSubalgebra.crossedProductInclusion
            (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) ↔
        xiCompactifiedUpperZeroSector.Finite ∧
          xiCompactifiedLowerZeroSector.Finite :=
    xiCompactifiedCorona_crossedProduct_iff_finite
  have hfinite := hiff.mp hmem
  exact xiCompactifiedUpperZeroSector_infinite hfinite.1

end RHTower
