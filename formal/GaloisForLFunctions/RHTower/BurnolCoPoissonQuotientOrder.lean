import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinFaithful
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinReflection

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace RHTower

theorem burnolCoPoissonQuotientSpace_map_cosine (b : ℝ) :
    (burnolCoPoissonQuotientSpace b).map
        soninCosineUnitary.toLinearIsometry.toLinearMap =
      burnolCoPoissonQuotientSpace b := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact soninCosineUnitary_mem_coPoissonQuotientSpace hx
  · intro y hy
    refine ⟨soninCosineUnitary y,
      soninCosineUnitary_mem_coPoissonQuotientSpace hy, ?_⟩
    exact soninCosineUnitary_involutive y

theorem evenFourierTransform_burnolCoPoissonQuotientProjection
    (b : ℝ) (hb : 0 < b) (f : evenSubspace) :
    evenFourierTransform (burnolCoPoissonQuotientProjection b hb f) =
      burnolCoPoissonQuotientProjection b hb (evenFourierTransform f) := by
  letI : CompleteSpace (burnolCoPoissonQuotientSpace b) :=
    (isClosed_burnolCoPoissonQuotientSpace hb).completeSpace_coe
  let Q := burnolCoPoissonQuotientSpace b
  change soninCosineUnitary (Q.starProjection f) =
    Q.starProjection (soninCosineUnitary f)
  symm
  apply Q.eq_starProjection_of_mem_of_inner_eq_zero
  · exact soninCosineUnitary_mem_coPoissonQuotientSpace (Q.coe_mem _)
  · intro w hw
    have hJw : soninCosineUnitary w ∈ Q :=
      soninCosineUnitary_mem_coPoissonQuotientSpace hw
    calc
      ⟪soninCosineUnitary f - soninCosineUnitary (Q.starProjection f), w⟫_ℂ =
          ⟪soninCosineUnitary (f - Q.starProjection f),
            soninCosineUnitary (soninCosineUnitary w)⟫_ℂ := by
              rw [map_sub, soninCosineUnitary_involutive]
      _ = ⟪f - Q.starProjection f, soninCosineUnitary w⟫_ℂ :=
        soninCosineUnitary.inner_map_map _ _
      _ = 0 := Q.starProjection_inner_eq_zero f _ hJw

theorem evenFourierTransform_mul_burnolCoPoissonQuotientProjection
    (b : ℝ) (hb : 0 < b) :
    evenFourierTransform * burnolCoPoissonQuotientProjection b hb =
      burnolCoPoissonQuotientProjection b hb * evenFourierTransform := by
  apply ContinuousLinearMap.ext
  exact evenFourierTransform_burnolCoPoissonQuotientProjection b hb

theorem adjoint_burnolCoPoissonQuotientProjection
    (b : ℝ) (hb : 0 < b) :
    ContinuousLinearMap.adjoint (burnolCoPoissonQuotientProjection b hb) =
      burnolCoPoissonQuotientProjection b hb := by
  letI : CompleteSpace (burnolCoPoissonQuotientSpace b) :=
    (isClosed_burnolCoPoissonQuotientSpace hb).completeSpace_coe
  change ContinuousLinearMap.adjoint
      (burnolCoPoissonQuotientSpace b).starProjection =
    (burnolCoPoissonQuotientSpace b).starProjection
  exact (isSelfAdjoint_starProjection
    (burnolCoPoissonQuotientSpace b)).adjoint_eq

/-- Actual compression of the finite aperture holonomy to Burnol's source quotient. -/
def burnolCoPoissonCompressedHolonomy
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    evenSubspace →L[ℂ] evenSubspace :=
  burnolCoPoissonQuotientProjection b hb *
    burnolExtendedBilateralApertureHolonomy a ha r hr *
      burnolCoPoissonQuotientProjection b hb

/-- The compressed holonomy remains Fourier odd. -/
theorem burnolCoPoissonCompressedHolonomy_fourier_odd
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    evenFourierTransform *
        burnolCoPoissonCompressedHolonomy b hb a ha r hr *
      evenFourierTransform =
        -burnolCoPoissonCompressedHolonomy b hb a ha r hr := by
  let J := evenFourierTransform
  let E := burnolCoPoissonQuotientProjection b hb
  let H := burnolExtendedBilateralApertureHolonomy a ha r hr
  have hJE : J * E = E * J := by
    simpa only [J, E] using
      evenFourierTransform_mul_burnolCoPoissonQuotientProjection b hb
  have hJHJ : J * H * J = -H := by
    simpa only [J, H] using
      burnolExtendedBilateralApertureHolonomy_fourier_odd a ha r hr
  change J * (E * H * E) * J = -(E * H * E)
  calc
    J * (E * H * E) * J = (J * E) * H * (E * J) := by noncomm_ring
    _ = (E * J) * H * (J * E) := by rw [hJE]
    _ = E * (J * H * J) * E := by noncomm_ring
    _ = E * (-H) * E := by rw [hJHJ]
    _ = -(E * H * E) := by
      apply ContinuousLinearMap.ext
      intro x
      simp

theorem adjoint_burnolExtendedSoninProjection
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.adjoint (burnolExtendedSoninProjection a ha) =
      burnolExtendedSoninProjection a ha := by
  letI : Fact (0 < a) := ⟨ha⟩
  change ContinuousLinearMap.adjoint (soninExtendedSpace a).starProjection =
    (soninExtendedSpace a).starProjection
  exact (isSelfAdjoint_starProjection (soninExtendedSpace a)).adjoint_eq

theorem burnolExtendedBilateralApertureHolonomy_isSelfAdjoint
    (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    IsSelfAdjoint (burnolExtendedBilateralApertureHolonomy a ha r hr) := by
  let U := evenDilationCLM r (zero_lt_one.trans hr)
  let P := burnolExtendedSoninProjection a ha
  have hP : ContinuousLinearMap.adjoint P = P := by
    simpa only [P] using adjoint_burnolExtendedSoninProjection a ha
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
  change ContinuousLinearMap.adjoint
      (U * P * ContinuousLinearMap.adjoint U -
        ContinuousLinearMap.adjoint U * P * U) = _
  simp only [adjoint_sub_clm, adjoint_mul_clm,
    ContinuousLinearMap.adjoint_adjoint, hP]
  rfl

theorem burnolCoPoissonCompressedHolonomy_isSelfAdjoint
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    IsSelfAdjoint (burnolCoPoissonCompressedHolonomy b hb a ha r hr) := by
  let E := burnolCoPoissonQuotientProjection b hb
  let H := burnolExtendedBilateralApertureHolonomy a ha r hr
  have hE : ContinuousLinearMap.adjoint E = E := by
    simpa only [E] using adjoint_burnolCoPoissonQuotientProjection b hb
  have hH : ContinuousLinearMap.adjoint H = H := by
    exact (burnolExtendedBilateralApertureHolonomy_isSelfAdjoint
      a ha r hr).adjoint_eq
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
  change ContinuousLinearMap.adjoint (E * H * E) = E * H * E
  simp only [adjoint_mul_clm, hE, hH]
  exact (mul_assoc E H E).symm

/-- A Fourier-odd operator cannot be one-sided semidefinite unless it vanishes. -/
theorem eq_zero_of_fourierOdd_of_neg_isPositive
    {T : evenSubspace →L[ℂ] evenSubspace}
    (hodd : evenFourierTransform * T * evenFourierTransform = -T)
    (hneg : (-T).IsPositive) :
    T = 0 := by
  have hconj := hneg.conj_adjoint evenFourierTransform
  have hJadj : ContinuousLinearMap.adjoint evenFourierTransform = evenFourierTransform :=
    adjoint_evenFourierTransform
  have hpos : T.IsPositive := by
    rw [hJadj] at hconj
    have heq : evenFourierTransform * (-T) * evenFourierTransform = T := by
      calc
        evenFourierTransform * (-T) * evenFourierTransform =
            -(evenFourierTransform * T * evenFourierTransform) := by
              apply ContinuousLinearMap.ext
              intro x
              simp
        _ = -(-T) := by rw [hodd]
        _ = T := neg_neg T
    change (evenFourierTransform * (-T) * evenFourierTransform).IsPositive at hconj
    rwa [heq] at hconj
  apply le_antisymm
  · change (0 - T).IsPositive
    simpa using hneg
  · change (T - 0).IsPositive
    simpa using hpos

/-- On the actual source quotient, nonpositive order, flatness, and nonnegative order coincide. -/
theorem burnolCoPoissonCompressedHolonomy_order_flatness
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    ((-burnolCoPoissonCompressedHolonomy b hb a ha r hr).IsPositive ↔
      burnolCoPoissonCompressedHolonomy b hb a ha r hr = 0) ∧
    ((burnolCoPoissonCompressedHolonomy b hb a ha r hr).IsPositive ↔
      burnolCoPoissonCompressedHolonomy b hb a ha r hr = 0) := by
  let T := burnolCoPoissonCompressedHolonomy b hb a ha r hr
  have hodd : evenFourierTransform * T * evenFourierTransform = -T :=
    burnolCoPoissonCompressedHolonomy_fourier_odd b hb a ha r hr
  constructor
  · constructor
    · exact eq_zero_of_fourierOdd_of_neg_isPositive hodd
    · intro h
      rw [h]
      simp
  · constructor
    · intro hpos
      have hoddNeg : evenFourierTransform * (-T) * evenFourierTransform = -(-T) := by
        calc
          evenFourierTransform * (-T) * evenFourierTransform =
              -(evenFourierTransform * T * evenFourierTransform) := by
                apply ContinuousLinearMap.ext
                intro x
                simp
          _ = -(-T) := by rw [hodd]
      have hnegneg : (-(-T)).IsPositive := by simpa using hpos
      have := eq_zero_of_fourierOdd_of_neg_isPositive hoddNeg hnegneg
      simpa using congrArg Neg.neg this
    · intro h
      rw [h]
      simp

/-- Unnormalized even-to-odd block of an operator relative to an involution.  Its zero set is
identical to that of the block formed with the normalized projections `(1 ± J)/2`. -/
def involutionEvenOddBlock
    (J T : evenSubspace →L[ℂ] evenSubspace) :
    evenSubspace →L[ℂ] evenSubspace :=
  (1 + J) * T * (1 - J)

theorem fourierOdd_eq_zero_iff_even_odd_block_eq_zero
    {T : evenSubspace →L[ℂ] evenSubspace}
    (hT : IsSelfAdjoint T)
    (hodd : evenFourierTransform * T * evenFourierTransform = -T) :
    T = 0 ↔
      involutionEvenOddBlock evenFourierTransform T = 0 := by
  let J := evenFourierTransform
  let P : evenSubspace →L[ℂ] evenSubspace := 1 + J
  let Q : evenSubspace →L[ℂ] evenSubspace := 1 - J
  have hJ2 : J * J = 1 := evenFourierTransform_mul_self
  have hJadj : ContinuousLinearMap.adjoint J = J := by
    simpa only [J] using adjoint_evenFourierTransform
  have hJsymm (u v : evenSubspace) : ⟪J u, v⟫_ℂ = ⟪u, J v⟫_ℂ := by
    calc
      ⟪J u, v⟫_ℂ = ⟪u, (ContinuousLinearMap.adjoint J) v⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_right J u v).symm
      _ = ⟪u, J v⟫_ℂ := by rw [hJadj]
  have hTsymm (u v : evenSubspace) : ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ := by
    calc
      ⟪T u, v⟫_ℂ = ⟪u, (ContinuousLinearMap.adjoint T) v⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_right T u v).symm
      _ = ⟪u, T v⟫_ℂ := by rw [hT.adjoint_eq]
  have hPsymm (u v : evenSubspace) : ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ := by
    simp [P, hJsymm]
  have hQsymm (u v : evenSubspace) : ⟪Q u, v⟫_ℂ = ⟪u, Q v⟫_ℂ := by
    simp [Q, hJsymm]
  have hdecomp : T + T + T + T = P * T * Q + Q * T * P := by
    apply ContinuousLinearMap.ext
    intro x
    have hoddx := congrArg (fun A : evenSubspace →L[ℂ] evenSubspace => A x) hodd
    change J (T (J x)) = -T x at hoddx
    simp [P, Q, hoddx]
    module
  constructor
  · intro h
    simp [involutionEvenOddBlock, h]
  · intro hblock
    change P * T * Q = 0 at hblock
    have hother : Q * T * P = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      apply ext_inner_left ℂ
      intro y
      have hblocky := congrArg
        (fun A : evenSubspace →L[ℂ] evenSubspace => A y) hblock
      change P (T (Q y)) = 0 at hblocky
      calc
        ⟪y, (Q * T * P) x⟫_ℂ = ⟪y, Q (T (P x))⟫_ℂ := rfl
        _ = ⟪Q y, T (P x)⟫_ℂ := (hQsymm y (T (P x))).symm
        _ = ⟪T (Q y), P x⟫_ℂ := (hTsymm (Q y) (P x)).symm
        _ = ⟪P (T (Q y)), x⟫_ℂ := (hPsymm (T (Q y)) x).symm
        _ = ⟪0, x⟫_ℂ := by rw [hblocky]
        _ = ⟪y, (0 : evenSubspace)⟫_ℂ := by simp
    have hsum : T + T + T + T = 0 := by
      rw [hdecomp, hblock, hother, add_zero]
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun A : evenSubspace →L[ℂ] evenSubspace => A x) hsum
    change T x + T x + T x + T x = 0 at hx
    calc
      T x = (1 / 4 : ℂ) • (T x + T x + T x + T x) := by module
      _ = 0 := by rw [hx]; simp

/-- Burnol's concrete source-quotient compression vanishes exactly when its parity-changing
block vanishes. -/
theorem burnolCoPoissonCompressedHolonomy_eq_zero_iff_even_odd_block_eq_zero
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    burnolCoPoissonCompressedHolonomy b hb a ha r hr = 0 ↔
      involutionEvenOddBlock evenFourierTransform
        (burnolCoPoissonCompressedHolonomy b hb a ha r hr) = 0 :=
  fourierOdd_eq_zero_iff_even_odd_block_eq_zero
    (burnolCoPoissonCompressedHolonomy_isSelfAdjoint b hb a ha r hr)
    (burnolCoPoissonCompressedHolonomy_fourier_odd b hb a ha r hr)

end RHTower
