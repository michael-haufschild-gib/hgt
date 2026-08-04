import GaloisForLFunctions.RHTower.RealCoronaHolomorphicReflectionCrossedProduct

/-!
# Universal complete-strip Real-corona compactification law

This is the divisor-geometric core of automorphic P3.  Any infinite locally finite divisor in the
open unit strip, stable under the functional-equation reflection `rho ↦ 1-rho`, has unbounded
ordinates.  In the centered reciprocal coordinate `(rho-1/2)⁻¹`, its two height sectors are
infinite, disjoint, accumulate at `0`, and are exchanged by holomorphic negation.

Consequently the Real-corona idempotent is bounded in the full divisor algebra but is never smooth
in the natural dense endpoint-entire algebra or its honest order-two crossed product.  This theorem
isolates the universal law; separate modules verify its hypotheses for actual completed
automorphic L-functions.
-/

noncomputable section

open Complex Metric Set Filter

namespace GaloisForLFunctions.RHTower

/-- Minimal dependency-closed divisor interface forced by a positive-degree completed
functional equation.  Local finiteness is stated on closed discs so no hidden meromorphic-divisor
API is required by downstream compactification results. -/
structure CompleteStripReflectionDivisor where
  completed : ℂ → ℂ
  zeroSetInfinite : {z : ℂ | completed z = 0}.Infinite
  zero_mem_openUnitStrip : ∀ {z : ℂ}, completed z = 0 → 0 < z.re ∧ z.re < 1
  zero_reflect : ∀ {z : ℂ}, completed z = 0 → completed (1 - z) = 0
  zeros_closedBall_finite : ∀ (c : ℂ) (R : ℝ),
    {z ∈ Metric.closedBall c R | completed z = 0}.Finite

namespace CompleteStripReflectionDivisor

variable (D : CompleteStripReflectionDivisor)

def zeroSet : Set ℂ := {z | D.completed z = 0}

def centeredReciprocal (_D : CompleteStripReflectionDivisor) (rho : ℂ) : ℂ :=
  (rho - 1 / 2)⁻¹

@[simp] theorem centeredReciprocal_one_sub (rho : ℂ) :
    D.centeredReciprocal (1 - rho) = -D.centeredReciprocal rho := by
  simp only [centeredReciprocal]
  rw [show 1 - rho - 1 / 2 = -(rho - 1 / 2) by ring, inv_neg]

def upperSector : Set ℂ :=
  {w | ∃ rho : ℂ, D.completed rho = 0 ∧ 0 < rho.im ∧
    w = D.centeredReciprocal rho}

def lowerSector : Set ℂ :=
  {w | ∃ rho : ℂ, D.completed rho = 0 ∧ rho.im < 0 ∧
    w = D.centeredReciprocal rho}

theorem exists_zero_im_abs_gt (T : ℝ) :
    ∃ rho, D.completed rho = 0 ∧ T < |rho.im| := by
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_and, not_lt] at hcon
  have hsub : D.zeroSet ⊆
      {z ∈ Metric.closedBall (0 : ℂ) (1 + |T|) | D.completed z = 0} := by
    intro z hz
    have hstrip := D.zero_mem_openUnitStrip hz
    have him := hcon z hz
    refine ⟨?_, hz⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |T| := by
        have h1 : |z.re| ≤ 1 := by
          rw [abs_of_pos hstrip.1]
          linarith [hstrip.2]
        have h2 : |z.im| ≤ |T| := le_trans him (le_abs_self T)
        linarith
  exact D.zeroSetInfinite ((D.zeros_closedBall_finite 0 (1 + |T|)).subset hsub)

theorem centeredReciprocal_ne_zero_of_im_ne_zero {rho : ℂ}
    (him : rho.im ≠ 0) : D.centeredReciprocal rho ≠ 0 := by
  apply inv_ne_zero
  apply sub_ne_zero.mpr
  intro hhalf
  apply him
  have := congrArg Complex.im hhalf
  simpa using this

theorem exists_upper_zero_im_gt {T : ℝ} (hT : 0 ≤ T) :
    ∃ rho, D.completed rho = 0 ∧ 0 < rho.im ∧ T < rho.im := by
  obtain ⟨rho, hrho, hheight⟩ := D.exists_zero_im_abs_gt T
  by_cases him : 0 < rho.im
  · exact ⟨rho, hrho, him, by simpa [abs_of_pos him] using hheight⟩
  · have himle : rho.im ≤ 0 := le_of_not_gt him
    have himlt : rho.im < 0 := by
      have habspos : 0 < |rho.im| := lt_of_le_of_lt hT hheight
      exact lt_of_le_of_ne himle (fun heq => by simpa [heq] using habspos)
    refine ⟨1 - rho, D.zero_reflect hrho, ?_, ?_⟩
    · simp only [Complex.sub_im, Complex.one_im]
      linarith
    · rw [abs_of_neg himlt] at hheight
      simp only [Complex.sub_im, Complex.one_im]
      linarith

theorem neg_mem_upper_iff_mem_lower (w : ℂ) :
    -w ∈ D.upperSector ↔ w ∈ D.lowerSector := by
  constructor
  · rintro ⟨rho, hrho, him, hcoord⟩
    refine ⟨1 - rho, D.zero_reflect hrho, ?_, ?_⟩
    · simp only [Complex.sub_im, Complex.one_im]
      linarith
    · rw [D.centeredReciprocal_one_sub, ← hcoord]
      simp
  · rintro ⟨rho, hrho, him, hcoord⟩
    refine ⟨1 - rho, D.zero_reflect hrho, ?_, ?_⟩
    · simp only [Complex.sub_im, Complex.one_im]
      linarith
    · rw [D.centeredReciprocal_one_sub, ← hcoord]

theorem neg_mem_lower_iff_mem_upper (w : ℂ) :
    -w ∈ D.lowerSector ↔ w ∈ D.upperSector := by
  simpa using (D.neg_mem_upper_iff_mem_lower (-w)).symm

theorem sectors_disjoint : Disjoint D.upperSector D.lowerSector := by
  rw [Set.disjoint_left]
  intro w hwUpper hwLower
  rcases hwUpper with ⟨rho, hrho, hrhoIm, hwRho⟩
  rcases hwLower with ⟨sigma, hsigma, hsigmaIm, hwSigma⟩
  have hinv : (rho - 1 / 2)⁻¹ = (sigma - 1 / 2)⁻¹ := by
    simpa only [centeredReciprocal] using hwRho.symm.trans hwSigma
  have hcenter : rho - 1 / 2 = sigma - 1 / 2 := inv_injective hinv
  have hrs : rho = sigma := by
    calc
      rho = (rho - 1 / 2) + 1 / 2 := by ring
      _ = (sigma - 1 / 2) + 1 / 2 := congrArg (fun z : ℂ => z + 1 / 2) hcenter
      _ = sigma := by ring
  have himEq : rho.im = sigma.im := congrArg Complex.im hrs
  linarith

theorem zero_mem_closure_upper : (0 : ℂ) ∈ closure (D.upperSector \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro epsilon hepsilon
  obtain ⟨rho, hrho, hrhoIm, hheight⟩ :=
    D.exists_upper_zero_im_gt (T := 1 / epsilon) (by positivity)
  let w := D.centeredReciprocal rho
  have hwne : w ≠ 0 := D.centeredReciprocal_ne_zero_of_im_ne_zero (ne_of_gt hrhoIm)
  refine ⟨w, ⟨⟨rho, hrho, hrhoIm, rfl⟩, ?_⟩, ?_⟩
  · simpa only [Set.mem_singleton_iff] using hwne
  · change dist 0 (D.centeredReciprocal rho) < epsilon
    rw [dist_zero_left, centeredReciprocal, norm_inv]
    have himNorm : rho.im ≤ ‖rho - 1 / 2‖ := by
      have h := Complex.abs_im_le_norm (rho - 1 / 2)
      simpa [abs_of_pos hrhoIm] using h
    calc
      ‖rho - 1 / 2‖⁻¹ ≤ 1 / rho.im := by
        simpa only [one_div] using one_div_le_one_div_of_le hrhoIm himNorm
      _ < epsilon := (one_div_lt hepsilon hrhoIm).mp hheight

theorem zero_mem_closure_lower : (0 : ℂ) ∈ closure (D.lowerSector \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro epsilon hepsilon
  obtain ⟨w, hw, hdist⟩ :=
    (Metric.mem_closure_iff.mp D.zero_mem_closure_upper) epsilon hepsilon
  refine ⟨-w, ?_, ?_⟩
  · exact ⟨(D.neg_mem_lower_iff_mem_upper w).mpr hw.1,
      by simpa only [Set.mem_singleton_iff, neg_eq_zero] using hw.2⟩
  · simpa [dist_zero_left] using hdist

theorem upperSector_infinite : D.upperSector.Infinite := by
  intro hfinite
  have hclosed : IsClosed (D.upperSector \ {0}) := hfinite.sdiff.isClosed
  have hmem : (0 : ℂ) ∈ D.upperSector \ {0} := by
    rw [← hclosed.closure_eq]
    exact D.zero_mem_closure_upper
  exact hmem.2 rfl

theorem lowerSector_infinite : D.lowerSector.Infinite := by
  intro hfinite
  have hclosed : IsClosed (D.lowerSector \ {0}) := hfinite.sdiff.isClosed
  have hmem : (0 : ℂ) ∈ D.lowerSector \ {0} := by
    rw [← hclosed.closure_eq]
    exact D.zero_mem_closure_lower
  exact hmem.2 rfl

theorem sectors_neg_mapsTo : MapsTo (-·) (D.upperSector ∪ D.lowerSector)
    (D.upperSector ∪ D.lowerSector) := by
  intro w hw
  rcases hw with hw | hw
  · exact Or.inr ((D.neg_mem_lower_iff_mem_upper w).mpr hw)
  · exact Or.inl ((D.neg_mem_upper_iff_mem_lower w).mpr hw)

def holomorphicReflection :
    HolomorphicDivisorReflection Set.univ (D.upperSector ∪ D.lowerSector) :=
  negationHolomorphicDivisorReflection _ D.sectors_neg_mapsTo

theorem odd_smul_corona_eq_complement :
    let R := D.holomorphicReflection
    letI := R.functionAction
    ReflectionParity.odd • endpointRealCoronaIdempotent D.upperSector D.lowerSector =
      1 - endpointRealCoronaIdempotent D.upperSector D.lowerSector := by
  let R := D.holomorphicReflection
  letI := R.functionAction
  apply R.odd_smul_endpointRealCoronaIdempotent_eq_complement D.sectors_disjoint
  intro w
  change -(w : ℂ) ∈ D.upperSector ↔ (w : ℂ) ∈ D.lowerSector
  exact D.neg_mem_upper_iff_mem_lower w

theorem corona_crossedProduct_iff_finite :
    let R := D.holomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((D.upperSector ∪ D.lowerSector : Set ℂ) → ℂ)) := R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent D.upperSector D.lowerSector) ∈
      Set.range (InvariantSubalgebra.crossedProductInclusion
        (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) ↔
      D.upperSector.Finite ∧ D.lowerSector.Finite := by
  let R := D.holomorphicReflection
  letI := R.functionAction
  letI : SMulCommClass ReflectionParity ℂ
      (((D.upperSector ∪ D.lowerSector : Set ℂ) → ℂ)) := R.functionSmulCommClass
  exact HolomorphicDivisorReflection.reflectedEndpointCorona_crossedProduct_iff_finite
    R isPreconnected_univ (Set.subset_univ _) (Set.subset_univ _)
    D.upperSector_infinite.nonempty D.lowerSector_infinite.nonempty
    (Set.mem_univ 0) (Set.mem_univ 0)
    (fun _ => D.zero_mem_closure_upper) (fun _ => D.zero_mem_closure_lower)
    D.sectors_disjoint

/-- Universal P3 no-go for every infinite locally finite complete-strip reflection divisor. -/
theorem corona_not_mem_smoothCrossedProductRange :
    let R := D.holomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((D.upperSector ∪ D.lowerSector : Set ℂ) → ℂ)) := R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent D.upperSector D.lowerSector) ∉
      Set.range (InvariantSubalgebra.crossedProductInclusion
        (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) := by
  dsimp only
  let R := D.holomorphicReflection
  letI := R.functionAction
  letI : SMulCommClass ReflectionParity ℂ
      (((D.upperSector ∪ D.lowerSector : Set ℂ) → ℂ)) := R.functionSmulCommClass
  intro hmem
  have hiff :
      SkewMonoidAlgebra.single (1 : ReflectionParity)
          (endpointRealCoronaIdempotent D.upperSector D.lowerSector) ∈
        Set.range (InvariantSubalgebra.crossedProductInclusion
          (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) ↔
        D.upperSector.Finite ∧ D.lowerSector.Finite := D.corona_crossedProduct_iff_finite
  exact D.upperSector_infinite (hiff.mp hmem).1

end CompleteStripReflectionDivisor
end GaloisForLFunctions.RHTower
