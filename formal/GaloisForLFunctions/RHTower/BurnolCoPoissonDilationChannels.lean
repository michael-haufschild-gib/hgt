import GaloisForLFunctions.RHTower.BurnolCoPoissonParityChannels

open Complex Real
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A contraction has positive adjoint defect `1 - C C†`. -/
theorem one_sub_comp_adjoint_isPositive_of_norm_le_one
    (C : H →L[ℂ] H) (hC : ‖C‖ ≤ 1) :
    (1 - C * ContinuousLinearMap.adjoint C).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  constructor
  · exact (IsSelfAdjoint.one (H →L[ℂ] H)).sub
      (ContinuousLinearMap.isPositive_self_comp_adjoint C).isSelfAdjoint
  · intro x
    have hnorm : ‖ContinuousLinearMap.adjoint C x‖ ≤ ‖x‖ := by
      calc
        ‖ContinuousLinearMap.adjoint C x‖ ≤
            ‖ContinuousLinearMap.adjoint C‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ = ‖C‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg x)
        _ = ‖x‖ := one_mul _
    have hinner :
        ⟪(C * ContinuousLinearMap.adjoint C) x, x⟫_ℂ =
          ⟪ContinuousLinearMap.adjoint C x,
            ContinuousLinearMap.adjoint C x⟫_ℂ := by
      change ⟪C (ContinuousLinearMap.adjoint C x), x⟫_ℂ = _
      exact (ContinuousLinearMap.adjoint_inner_right C _ _).symm
    have hxinner : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) x
    have hadjinner :
        (⟪ContinuousLinearMap.adjoint C x,
          ContinuousLinearMap.adjoint C x⟫_ℂ).re =
            ‖ContinuousLinearMap.adjoint C x‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) _
    change 0 ≤ (⟪(1 - C * ContinuousLinearMap.adjoint C) x, x⟫_ℂ).re
    rw [sub_apply, one_apply_eq_self, inner_sub_left, hinner, Complex.sub_re,
      hxinner, hadjinner]
    nlinarith [norm_nonneg x, norm_nonneg (ContinuousLinearMap.adjoint C x)]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Contractive right factorization reverses the order of the two range Gram operators. -/
theorem gram_sub_gram_isPositive_of_contractive_factorization
    (A B : H →L[ℂ] K) (C : H →L[ℂ] H)
    (hC : ‖C‖ ≤ 1) (hfactor : A = B ∘L C) :
    (B ∘L ContinuousLinearMap.adjoint B -
      A ∘L ContinuousLinearMap.adjoint A).IsPositive := by
  have hpos :=
    (one_sub_comp_adjoint_isPositive_of_norm_le_one C hC).conj_adjoint B
  rw [hfactor]
  convert hpos using 1
  apply ContinuousLinearMap.ext
  intro x
  simp

/-- Forward-dilation channel from the extended Sonine carrier to the full co-Poisson quotient. -/
def burnolCoPoissonFullForwardChannel
    (b : ℝ) (hb : 0 < b) (a : ℝ) (r : ℝ) (hr : 1 < r) :
    soninExtendedSpace a →L[ℂ] evenSubspace :=
  burnolCoPoissonQuotientProjection b hb ∘L
    evenDilationCLM r (zero_lt_one.trans hr) ∘L
      (soninExtendedSpace a).subtypeL

/-- Inverse-dilation channel from the extended Sonine carrier to the full co-Poisson quotient. -/
def burnolCoPoissonFullInverseChannel
    (b : ℝ) (hb : 0 < b) (a : ℝ) (r : ℝ) (hr : 1 < r) :
    soninExtendedSpace a →L[ℂ] evenSubspace :=
  burnolCoPoissonQuotientProjection b hb ∘L
    ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) ∘L
      (soninExtendedSpace a).subtypeL

/-- Explicit Hilbert adjoint of the full forward channel. -/
def burnolCoPoissonFullForwardChannelAdjoint
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    evenSubspace →L[ℂ] soninExtendedSpace a := by
  exact burnolExtendedSoninInclusionAdjoint a ha ∘L
    ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) ∘L
      burnolCoPoissonQuotientProjection b hb

/-- Explicit Hilbert adjoint of the full inverse channel. -/
def burnolCoPoissonFullInverseChannelAdjoint
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    evenSubspace →L[ℂ] soninExtendedSpace a := by
  exact burnolExtendedSoninInclusionAdjoint a ha ∘L
    evenDilationCLM r (zero_lt_one.trans hr) ∘L
      burnolCoPoissonQuotientProjection b hb

set_option maxHeartbeats 400000 in
theorem adjoint_burnolCoPoissonFullForwardChannel
    (b : ℝ) (hb : 0 < b) (a : ℝ) [Fact (0 < a)]
    (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    ContinuousLinearMap.adjoint (𝕜 := ℂ)
        (E := soninExtendedSpace a) (F := evenSubspace)
        (burnolCoPoissonFullForwardChannel b hb a r hr) =
      burnolCoPoissonFullForwardChannelAdjoint b hb a ha r hr := by
  rw [burnolCoPoissonFullForwardChannel, burnolCoPoissonFullForwardChannelAdjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_burnolCoPoissonQuotientProjection]
  let Iadj := ContinuousLinearMap.adjoint (𝕜 := ℂ)
    (E := soninExtendedSpace a) (F := evenSubspace)
    ((soninExtendedSpace a).subtypeL)
  let Uadj := ContinuousLinearMap.adjoint
    (evenDilationCLM r (zero_lt_one.trans hr))
  let E := burnolCoPoissonQuotientProjection b hb
  change (Iadj ∘L Uadj) ∘L E = Iadj ∘L (Uadj ∘L E)
  exact ContinuousLinearMap.comp_assoc Iadj Uadj E

set_option maxHeartbeats 400000 in
theorem adjoint_burnolCoPoissonFullInverseChannel
    (b : ℝ) (hb : 0 < b) (a : ℝ) [Fact (0 < a)]
    (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    ContinuousLinearMap.adjoint (𝕜 := ℂ)
        (E := soninExtendedSpace a) (F := evenSubspace)
        (burnolCoPoissonFullInverseChannel b hb a r hr) =
      burnolCoPoissonFullInverseChannelAdjoint b hb a ha r hr := by
  rw [burnolCoPoissonFullInverseChannel, burnolCoPoissonFullInverseChannelAdjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_burnolCoPoissonQuotientProjection,
    ContinuousLinearMap.adjoint_adjoint]
  let Iadj := ContinuousLinearMap.adjoint (𝕜 := ℂ)
    (E := soninExtendedSpace a) (F := evenSubspace)
    ((soninExtendedSpace a).subtypeL)
  let U := evenDilationCLM r (zero_lt_one.trans hr)
  let E := burnolCoPoissonQuotientProjection b hb
  change (Iadj ∘L U) ∘L E = Iadj ∘L (U ∘L E)
  exact ContinuousLinearMap.comp_assoc Iadj U E

theorem burnolCoPoissonFullForwardChannel_gram
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    burnolCoPoissonFullForwardChannel b hb a r hr ∘L
        burnolCoPoissonFullForwardChannelAdjoint b hb a ha r hr =
      burnolCoPoissonQuotientProjection b hb *
        evenDilationCLM r (zero_lt_one.trans hr) *
          burnolExtendedSoninProjection a ha *
            ContinuousLinearMap.adjoint
              (evenDilationCLM r (zero_lt_one.trans hr)) *
                burnolCoPoissonQuotientProjection b hb := by
  letI : Fact (0 < a) := ⟨ha⟩
  rw [burnolCoPoissonFullForwardChannel, burnolCoPoissonFullForwardChannelAdjoint,
    burnolExtendedSoninProjection_eq_subtype_comp_adjoint a ha]
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem burnolCoPoissonFullInverseChannel_gram
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    burnolCoPoissonFullInverseChannel b hb a r hr ∘L
        burnolCoPoissonFullInverseChannelAdjoint b hb a ha r hr =
      burnolCoPoissonQuotientProjection b hb *
        ContinuousLinearMap.adjoint
          (evenDilationCLM r (zero_lt_one.trans hr)) *
            burnolExtendedSoninProjection a ha *
              evenDilationCLM r (zero_lt_one.trans hr) *
                burnolCoPoissonQuotientProjection b hb := by
  letI : Fact (0 < a) := ⟨ha⟩
  rw [burnolCoPoissonFullInverseChannel, burnolCoPoissonFullInverseChannelAdjoint,
    burnolExtendedSoninProjection_eq_subtype_comp_adjoint a ha]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- Exact range-Gram decomposition of the quotient-compressed bilateral aperture holonomy. -/
theorem burnolCoPoissonCompressedHolonomy_eq_fullChannel_gram_sub
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    burnolCoPoissonCompressedHolonomy b hb a ha r hr =
      burnolCoPoissonFullForwardChannel b hb a r hr ∘L
          burnolCoPoissonFullForwardChannelAdjoint b hb a ha r hr -
        burnolCoPoissonFullInverseChannel b hb a r hr ∘L
          burnolCoPoissonFullInverseChannelAdjoint b hb a ha r hr := by
  rw [burnolCoPoissonFullForwardChannel_gram, burnolCoPoissonFullInverseChannel_gram]
  change burnolCoPoissonQuotientProjection b hb *
      (evenDilationCLM r (zero_lt_one.trans hr) *
          burnolExtendedSoninProjection a ha *
            ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) -
        ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) *
          burnolExtendedSoninProjection a ha *
            evenDilationCLM r (zero_lt_one.trans hr)) *
        burnolCoPoissonQuotientProjection b hb = _
  apply ContinuousLinearMap.ext
  intro x
  simp

/-- A contractive inverse-channel factorization makes compressed holonomy nonpositive. -/
theorem burnolCoPoissonCompressedHolonomy_neg_isPositive_of_contractive_factorization
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r)
    (C : soninExtendedSpace a →L[ℂ] soninExtendedSpace a)
    (hC : ‖C‖ ≤ 1)
    (hfactor : burnolCoPoissonFullForwardChannel b hb a r hr =
      burnolCoPoissonFullInverseChannel b hb a r hr ∘L C) :
    (-burnolCoPoissonCompressedHolonomy b hb a ha r hr).IsPositive := by
  letI : Fact (0 < a) := ⟨ha⟩
  have hpos := gram_sub_gram_isPositive_of_contractive_factorization
    (H := soninExtendedSpace a) (K := evenSubspace)
    (burnolCoPoissonFullForwardChannel b hb a r hr)
    (burnolCoPoissonFullInverseChannel b hb a r hr) C hC hfactor
  rw [adjoint_burnolCoPoissonFullForwardChannel b hb a ha r hr,
    adjoint_burnolCoPoissonFullInverseChannel b hb a ha r hr] at hpos
  rw [burnolCoPoissonCompressedHolonomy_eq_fullChannel_gram_sub]
  convert hpos using 1
  apply ContinuousLinearMap.ext
  intro x
  simp

/-- Fourier oddness upgrades contractive channel factorization to exact quotient flatness. -/
theorem burnolCoPoissonCompressedHolonomy_eq_zero_of_contractive_factorization
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r)
    (C : soninExtendedSpace a →L[ℂ] soninExtendedSpace a)
    (hC : ‖C‖ ≤ 1)
    (hfactor : burnolCoPoissonFullForwardChannel b hb a r hr =
      burnolCoPoissonFullInverseChannel b hb a r hr ∘L C) :
    burnolCoPoissonCompressedHolonomy b hb a ha r hr = 0 :=
  (burnolCoPoissonCompressedHolonomy_order_flatness b hb a ha r hr).1.1
    (burnolCoPoissonCompressedHolonomy_neg_isPositive_of_contractive_factorization
      b hb a ha r hr C hC hfactor)

/-- Contractive full-channel factorization forces even/odd quotient-channel decorrelation. -/
theorem burnolCoPoissonForwardParityCrossGram_eq_zero_of_contractive_factorization
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r)
    (C : soninExtendedSpace a →L[ℂ] soninExtendedSpace a)
    (hC : ‖C‖ ≤ 1)
    (hfactor : burnolCoPoissonFullForwardChannel b hb a r hr =
      burnolCoPoissonFullInverseChannel b hb a r hr ∘L C) :
    burnolCoPoissonForwardParityCrossGram b hb a ha r hr = 0 :=
  (burnolCoPoissonCompressedHolonomy_eq_zero_iff_crossGram_eq_zero
    b hb a ha r hr).1
      (burnolCoPoissonCompressedHolonomy_eq_zero_of_contractive_factorization
        b hb a ha r hr C hC hfactor)

end RHTower
