import GaloisForLFunctions.RHTower.BurnolCoPoissonQuotientOrder

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexOrder

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

/-- Orthogonal projector onto the `+1` Fourier eigenspace. -/
def burnolFourierEvenProjection : evenSubspace →L[ℂ] evenSubspace :=
  (2 : ℂ)⁻¹ • (1 + evenFourierTransform)

/-- Orthogonal projector onto the `-1` Fourier eigenspace. -/
def burnolFourierOddProjection : evenSubspace →L[ℂ] evenSubspace :=
  (2 : ℂ)⁻¹ • (1 - evenFourierTransform)

theorem burnolFourierEvenProjection_mul_evenFourierTransform :
    burnolFourierEvenProjection * evenFourierTransform =
      burnolFourierEvenProjection := by
  apply ContinuousLinearMap.ext
  intro x
  have hJ2 := congrArg
    (fun A : evenSubspace →L[ℂ] evenSubspace => A x)
    evenFourierTransform_mul_self
  change evenFourierTransform (evenFourierTransform x) = x at hJ2
  simp [burnolFourierEvenProjection, hJ2]
  module

theorem burnolFourierOddProjection_mul_evenFourierTransform :
    burnolFourierOddProjection * evenFourierTransform =
      -burnolFourierOddProjection := by
  apply ContinuousLinearMap.ext
  intro x
  have hJ2 := congrArg
    (fun A : evenSubspace →L[ℂ] evenSubspace => A x)
    evenFourierTransform_mul_self
  change evenFourierTransform (evenFourierTransform x) = x at hJ2
  simp [burnolFourierOddProjection, hJ2]
  module

theorem evenFourierTransform_mul_burnolFourierEvenProjection :
    evenFourierTransform * burnolFourierEvenProjection =
      burnolFourierEvenProjection := by
  apply ContinuousLinearMap.ext
  intro x
  have hJ2 := congrArg
    (fun A : evenSubspace →L[ℂ] evenSubspace => A x)
    evenFourierTransform_mul_self
  change evenFourierTransform (evenFourierTransform x) = x at hJ2
  simp [burnolFourierEvenProjection, hJ2]
  module

theorem evenFourierTransform_mul_burnolFourierOddProjection :
    evenFourierTransform * burnolFourierOddProjection =
      -burnolFourierOddProjection := by
  apply ContinuousLinearMap.ext
  intro x
  have hJ2 := congrArg
    (fun A : evenSubspace →L[ℂ] evenSubspace => A x)
    evenFourierTransform_mul_self
  change evenFourierTransform (evenFourierTransform x) = x at hJ2
  simp [burnolFourierOddProjection, hJ2]
  module

theorem adjoint_burnolFourierEvenProjection :
    ContinuousLinearMap.adjoint burnolFourierEvenProjection =
      burnolFourierEvenProjection := by
  rw [burnolFourierEvenProjection,
    ContinuousLinearMap.adjoint.map_smulₛₗ, adjoint_add_clm,
    ContinuousLinearMap.adjoint_one, adjoint_evenFourierTransform]
  rw [map_inv₀]
  rw [Complex.conj_ofNat]

theorem adjoint_burnolFourierOddProjection :
    ContinuousLinearMap.adjoint burnolFourierOddProjection =
      burnolFourierOddProjection := by
  rw [burnolFourierOddProjection,
    ContinuousLinearMap.adjoint.map_smulₛₗ, adjoint_sub_clm,
    ContinuousLinearMap.adjoint_one, adjoint_evenFourierTransform]
  rw [map_inv₀]
  rw [Complex.conj_ofNat]

/-- Fourier-even part of the canonical co-Poisson quotient projection. -/
def burnolCoPoissonEvenQuotientProjection (b : ℝ) (hb : 0 < b) :
    evenSubspace →L[ℂ] evenSubspace :=
  burnolFourierEvenProjection * burnolCoPoissonQuotientProjection b hb

/-- Fourier-odd part of the canonical co-Poisson quotient projection. -/
def burnolCoPoissonOddQuotientProjection (b : ℝ) (hb : 0 < b) :
    evenSubspace →L[ℂ] evenSubspace :=
  burnolFourierOddProjection * burnolCoPoissonQuotientProjection b hb

theorem burnolCoPoissonQuotientProjection_mul_burnolFourierEvenProjection
    (b : ℝ) (hb : 0 < b) :
    burnolCoPoissonQuotientProjection b hb * burnolFourierEvenProjection =
      burnolFourierEvenProjection * burnolCoPoissonQuotientProjection b hb := by
  apply ContinuousLinearMap.ext
  intro x
  have hcomm := congrArg
    (fun A : evenSubspace →L[ℂ] evenSubspace => A x)
    (evenFourierTransform_mul_burnolCoPoissonQuotientProjection b hb)
  change evenFourierTransform (burnolCoPoissonQuotientProjection b hb x) =
    burnolCoPoissonQuotientProjection b hb (evenFourierTransform x) at hcomm
  simp [burnolFourierEvenProjection, hcomm]

theorem burnolCoPoissonQuotientProjection_mul_burnolFourierOddProjection
    (b : ℝ) (hb : 0 < b) :
    burnolCoPoissonQuotientProjection b hb * burnolFourierOddProjection =
      burnolFourierOddProjection * burnolCoPoissonQuotientProjection b hb := by
  apply ContinuousLinearMap.ext
  intro x
  have hcomm := congrArg
    (fun A : evenSubspace →L[ℂ] evenSubspace => A x)
    (evenFourierTransform_mul_burnolCoPoissonQuotientProjection b hb)
  change evenFourierTransform (burnolCoPoissonQuotientProjection b hb x) =
    burnolCoPoissonQuotientProjection b hb (evenFourierTransform x) at hcomm
  simp [burnolFourierOddProjection, hcomm]

theorem adjoint_burnolCoPoissonEvenQuotientProjection
    (b : ℝ) (hb : 0 < b) :
    ContinuousLinearMap.adjoint (burnolCoPoissonEvenQuotientProjection b hb) =
      burnolCoPoissonEvenQuotientProjection b hb := by
  rw [burnolCoPoissonEvenQuotientProjection, adjoint_mul_clm,
    adjoint_burnolCoPoissonQuotientProjection,
    adjoint_burnolFourierEvenProjection,
    burnolCoPoissonQuotientProjection_mul_burnolFourierEvenProjection]

theorem adjoint_burnolCoPoissonOddQuotientProjection
    (b : ℝ) (hb : 0 < b) :
    ContinuousLinearMap.adjoint (burnolCoPoissonOddQuotientProjection b hb) =
      burnolCoPoissonOddQuotientProjection b hb := by
  rw [burnolCoPoissonOddQuotientProjection, adjoint_mul_clm,
    adjoint_burnolCoPoissonQuotientProjection,
    adjoint_burnolFourierOddProjection,
    burnolCoPoissonQuotientProjection_mul_burnolFourierOddProjection]

theorem burnolCoPoissonEvenQuotientProjection_mul_evenFourierTransform
    (b : ℝ) (hb : 0 < b) :
    burnolCoPoissonEvenQuotientProjection b hb * evenFourierTransform =
      burnolCoPoissonEvenQuotientProjection b hb := by
  rw [burnolCoPoissonEvenQuotientProjection]
  have hEJ : burnolCoPoissonQuotientProjection b hb * evenFourierTransform =
      evenFourierTransform * burnolCoPoissonQuotientProjection b hb :=
    (evenFourierTransform_mul_burnolCoPoissonQuotientProjection b hb).symm
  calc
    burnolFourierEvenProjection * burnolCoPoissonQuotientProjection b hb *
        evenFourierTransform =
      burnolFourierEvenProjection * evenFourierTransform *
        burnolCoPoissonQuotientProjection b hb := by
          noncomm_ring [hEJ]
    _ = burnolFourierEvenProjection *
        burnolCoPoissonQuotientProjection b hb := by
      rw [burnolFourierEvenProjection_mul_evenFourierTransform]

theorem evenFourierTransform_mul_burnolCoPoissonOddQuotientProjection
    (b : ℝ) (hb : 0 < b) :
    evenFourierTransform * burnolCoPoissonOddQuotientProjection b hb =
      -burnolCoPoissonOddQuotientProjection b hb := by
  rw [burnolCoPoissonOddQuotientProjection]
  calc
    evenFourierTransform *
        (burnolFourierOddProjection * burnolCoPoissonQuotientProjection b hb) =
      (evenFourierTransform * burnolFourierOddProjection) *
        burnolCoPoissonQuotientProjection b hb := by noncomm_ring
    _ = (-burnolFourierOddProjection) *
        burnolCoPoissonQuotientProjection b hb := by
      rw [evenFourierTransform_mul_burnolFourierOddProjection]
    _ = -(burnolFourierOddProjection *
        burnolCoPoissonQuotientProjection b hb) := by
      apply ContinuousLinearMap.ext
      intro x
      simp

theorem evenFourierTransform_mul_burnolExtendedSoninProjection
    (a : ℝ) (ha : 0 < a) :
    evenFourierTransform * burnolExtendedSoninProjection a ha =
      burnolExtendedSoninProjection a ha * evenFourierTransform := by
  apply ContinuousLinearMap.ext
  exact soninCosineUnitary_burnolExtendedSoninProjection a ha

theorem evenFourierTransform_conj_burnolExtendedSoninProjection
    (a : ℝ) (ha : 0 < a) :
    evenFourierTransform * burnolExtendedSoninProjection a ha *
        evenFourierTransform = burnolExtendedSoninProjection a ha := by
  calc
    evenFourierTransform * burnolExtendedSoninProjection a ha *
        evenFourierTransform =
      burnolExtendedSoninProjection a ha *
        (evenFourierTransform * evenFourierTransform) := by
      rw [evenFourierTransform_mul_burnolExtendedSoninProjection]
      noncomm_ring
    _ = burnolExtendedSoninProjection a ha := by
      rw [evenFourierTransform_mul_self, mul_one]

/-- Forward-dilation channel from the extended Sonine carrier to the even quotient parity. -/
def burnolCoPoissonForwardEvenChannel
    (b : ℝ) (hb : 0 < b) (a : ℝ) (r : ℝ) (hr : 1 < r) :
    soninExtendedSpace a →L[ℂ] evenSubspace :=
  burnolCoPoissonEvenQuotientProjection b hb ∘L
    evenDilationCLM r (zero_lt_one.trans hr) ∘L
      (soninExtendedSpace a).subtypeL

/-- Forward-dilation channel from the extended Sonine carrier to the odd quotient parity. -/
def burnolCoPoissonForwardOddChannel
    (b : ℝ) (hb : 0 < b) (a : ℝ) (r : ℝ) (hr : 1 < r) :
    soninExtendedSpace a →L[ℂ] evenSubspace :=
  burnolCoPoissonOddQuotientProjection b hb ∘L
    evenDilationCLM r (zero_lt_one.trans hr) ∘L
      (soninExtendedSpace a).subtypeL

/-- Adjoint of the extended-Sonine inclusion, with completeness discharged by closedness. -/
def burnolExtendedSoninInclusionAdjoint (a : ℝ) (ha : 0 < a) :
    evenSubspace →L[ℂ] soninExtendedSpace a := by
  letI : Fact (0 < a) := ⟨ha⟩
  exact ContinuousLinearMap.adjoint (𝕜 := ℂ)
    (E := soninExtendedSpace a) (F := evenSubspace)
    ((soninExtendedSpace a).subtypeL)

/-- Adjoint of the odd forward channel, with carrier completeness discharged by `ha`. -/
def burnolCoPoissonForwardOddChannelAdjoint
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    evenSubspace →L[ℂ] soninExtendedSpace a :=
  burnolExtendedSoninInclusionAdjoint a ha ∘L
    ContinuousLinearMap.adjoint
      (evenDilationCLM r (zero_lt_one.trans hr)) ∘L
        burnolCoPoissonOddQuotientProjection b hb

/-- The explicit reverse odd channel is the Hilbert adjoint of the forward odd channel. -/
theorem burnolCoPoissonForwardOddChannel_adjoint_pair
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r)
    (x : soninExtendedSpace a) (y : evenSubspace) :
    ⟪burnolCoPoissonForwardOddChannel b hb a r hr x, y⟫_ℂ =
      ⟪x, burnolCoPoissonForwardOddChannelAdjoint b hb a ha r hr y⟫_ℂ := by
  letI : Fact (0 < a) := ⟨ha⟩
  let Eminus := burnolCoPoissonOddQuotientProjection b hb
  let U := evenDilationCLM r (zero_lt_one.trans hr)
  let I := (soninExtendedSpace a).subtypeL
  have hE : ContinuousLinearMap.adjoint Eminus = Eminus := by
    simpa only [Eminus] using
      adjoint_burnolCoPoissonOddQuotientProjection b hb
  have hIadj : burnolExtendedSoninInclusionAdjoint a ha =
      ContinuousLinearMap.adjoint (𝕜 := ℂ)
        (E := soninExtendedSpace a) (F := evenSubspace) I := by
    rfl
  change ⟪Eminus (U (I x)), y⟫_ℂ =
    ⟪x, burnolExtendedSoninInclusionAdjoint a ha
      (ContinuousLinearMap.adjoint U (Eminus y))⟫_ℂ
  calc
    ⟪Eminus (U (I x)), y⟫_ℂ =
        ⟪U (I x), ContinuousLinearMap.adjoint Eminus y⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right Eminus (U (I x)) y).symm
    _ = ⟪U (I x), Eminus y⟫_ℂ := by rw [hE]
    _ = ⟪I x, ContinuousLinearMap.adjoint U (Eminus y)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right U (I x) (Eminus y)).symm
    _ = ⟪x, burnolExtendedSoninInclusionAdjoint a ha
          (ContinuousLinearMap.adjoint U (Eminus y))⟫_ℂ := by
      rw [hIadj]
      exact (ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ) I x
        (ContinuousLinearMap.adjoint U (Eminus y))).symm

/-- Static even/odd cross-Gram of the actual forward quotient channels. -/
def burnolCoPoissonForwardParityCrossGram
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    evenSubspace →L[ℂ] evenSubspace :=
  burnolCoPoissonForwardEvenChannel b hb a r hr ∘L
    burnolCoPoissonForwardOddChannelAdjoint b hb a ha r hr

theorem burnolExtendedSoninProjection_eq_subtype_comp_adjoint
    (a : ℝ) (ha : 0 < a) :
    burnolExtendedSoninProjection a ha =
      (soninExtendedSpace a).subtypeL ∘L
        burnolExtendedSoninInclusionAdjoint a ha := by
  letI : Fact (0 < a) := ⟨ha⟩
  change (soninExtendedSpace a).starProjection =
    (soninExtendedSpace a).subtypeL ∘L
      ContinuousLinearMap.adjoint (𝕜 := ℂ)
        (E := soninExtendedSpace a) (F := evenSubspace)
        ((soninExtendedSpace a).subtypeL)
  rw [(soninExtendedSpace a).adjoint_subtypeL]
  rfl

theorem burnolCoPoissonForwardParityCrossGram_eq
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    burnolCoPoissonForwardParityCrossGram b hb a ha r hr =
      burnolCoPoissonEvenQuotientProjection b hb *
        evenDilationCLM r (zero_lt_one.trans hr) *
          burnolExtendedSoninProjection a ha *
            ContinuousLinearMap.adjoint
              (evenDilationCLM r (zero_lt_one.trans hr)) *
                burnolCoPoissonOddQuotientProjection b hb := by
  letI : Fact (0 < a) := ⟨ha⟩
  rw [burnolCoPoissonForwardParityCrossGram,
    burnolCoPoissonForwardEvenChannel,
    burnolCoPoissonForwardOddChannelAdjoint,
    burnolExtendedSoninProjection_eq_subtype_comp_adjoint a ha]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- Exact `R8` identity: the quotient parity block of the finite holonomy is twice the forward
channel cross-Gram. -/
theorem burnolCoPoissonParityBlock_eq_two_crossGram
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    burnolCoPoissonEvenQuotientProjection b hb *
        burnolExtendedBilateralApertureHolonomy a ha r hr *
          burnolCoPoissonOddQuotientProjection b hb =
      (2 : ℂ) • burnolCoPoissonForwardParityCrossGram b hb a ha r hr := by
  let Eplus := burnolCoPoissonEvenQuotientProjection b hb
  let Eminus := burnolCoPoissonOddQuotientProjection b hb
  let J := evenFourierTransform
  let U := evenDilationCLM r (zero_lt_one.trans hr)
  let V := ContinuousLinearMap.adjoint U
  let P := burnolExtendedSoninProjection a ha
  let G := burnolCoPoissonForwardParityCrossGram b hb a ha r hr
  have hEplusJ : Eplus * J = Eplus := by
    simpa only [Eplus, J] using
      burnolCoPoissonEvenQuotientProjection_mul_evenFourierTransform b hb
  have hJEminus : J * Eminus = -Eminus := by
    simpa only [Eminus, J] using
      evenFourierTransform_mul_burnolCoPoissonOddQuotientProjection b hb
  have hJ2 : J * J = 1 := by
    simpa only [J] using evenFourierTransform_mul_self
  have hV : V = J * U * J := by
    symm
    calc
      J * U * J = V * (J * J) := by
        rw [show J * U = V * J by
          simpa only [J, U, V] using
            evenFourierTransform_mul_evenDilationCLM r hr]
        noncomm_ring
      _ = V := by rw [hJ2, mul_one]
  have hU : U = J * V * J := by
    symm
    calc
      J * V * J = U * (J * J) := by
        rw [show J * V = U * J by
          simpa only [J, U, V] using
            evenFourierTransform_mul_adjoint_evenDilationCLM r hr]
        noncomm_ring
      _ = U := by rw [hJ2, mul_one]
  have hP : P = J * P * J := by
    symm
    simpa only [P, J] using
      evenFourierTransform_conj_burnolExtendedSoninProjection a ha
  have hsecond : Eplus * V * P * U * Eminus =
      -(Eplus * U * P * V * Eminus) := by
    calc
      Eplus * V * P * U * Eminus =
          Eplus * (J * U * J) * P * U * Eminus :=
        congrArg (fun X => Eplus * X * P * U * Eminus) hV
      _ = Eplus * (J * U * J) * (J * P * J) * U * Eminus :=
        congrArg (fun X => Eplus * (J * U * J) * X * U * Eminus) hP
      _ = Eplus * (J * U * J) * (J * P * J) * (J * V * J) * Eminus := by
        exact congrArg
          (fun X => Eplus * (J * U * J) * (J * P * J) * X * Eminus) hU
      _ =
          (Eplus * J) * U * P * V * (J * Eminus) := by
        calc
          Eplus * (J * U * J) * (J * P * J) * (J * V * J) * Eminus =
              Eplus * J * U * (J * J) * P * (J * J) * V * J * Eminus := by
            noncomm_ring
          _ = Eplus * J * U * P * V * J * Eminus := by rw [hJ2]; simp
          _ = (Eplus * J) * U * P * V * (J * Eminus) := by noncomm_ring
      _ = Eplus * U * P * V * (-Eminus) := by
        rw [hEplusJ, hJEminus]
      _ = -(Eplus * U * P * V * Eminus) := by
        apply ContinuousLinearMap.ext
        intro x
        simp
  have hG : G = Eplus * U * P * V * Eminus := by
    simpa only [G, Eplus, Eminus, U, V, P] using
      burnolCoPoissonForwardParityCrossGram_eq b hb a ha r hr
  change Eplus * (U * P * V - V * P * U) * Eminus = (2 : ℂ) • G
  rw [mul_sub, sub_mul]
  have hsecond' : Eplus * (V * P * U) * Eminus =
      -(Eplus * U * P * V * Eminus) := by
    rw [show Eplus * (V * P * U) * Eminus =
      Eplus * V * P * U * Eminus by noncomm_ring]
    exact hsecond
  have hfirst : Eplus * (U * P * V) * Eminus = G := by
    rw [hG]
    noncomm_ring
  rw [hsecond', hfirst, ← hG]
  apply ContinuousLinearMap.ext
  intro x
  simp
  module

theorem involutionEvenOddBlock_eq_four_smul_normalized
    (T : evenSubspace →L[ℂ] evenSubspace) :
    involutionEvenOddBlock evenFourierTransform T =
      (4 : ℂ) •
        (burnolFourierEvenProjection * T * burnolFourierOddProjection) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [involutionEvenOddBlock, burnolFourierEvenProjection,
    burnolFourierOddProjection]
  module

theorem burnolNormalizedParityBlock_compressedHolonomy
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    burnolFourierEvenProjection *
        burnolCoPoissonCompressedHolonomy b hb a ha r hr *
          burnolFourierOddProjection =
      burnolCoPoissonEvenQuotientProjection b hb *
        burnolExtendedBilateralApertureHolonomy a ha r hr *
          burnolCoPoissonOddQuotientProjection b hb := by
  let E := burnolCoPoissonQuotientProjection b hb
  let H := burnolExtendedBilateralApertureHolonomy a ha r hr
  have hEminus : E * burnolFourierOddProjection =
      burnolFourierOddProjection * E :=
    burnolCoPoissonQuotientProjection_mul_burnolFourierOddProjection b hb
  change burnolFourierEvenProjection * (E * H * E) *
      burnolFourierOddProjection =
    (burnolFourierEvenProjection * E) * H *
      (burnolFourierOddProjection * E)
  noncomm_ring [hEminus]

/-- Exact `R5 ↔ R9` reduction on the actual co-Poisson quotient: flat compressed holonomy is
equivalent to even/odd forward-channel decorrelation. -/
theorem burnolCoPoissonCompressedHolonomy_eq_zero_iff_crossGram_eq_zero
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    burnolCoPoissonCompressedHolonomy b hb a ha r hr = 0 ↔
      burnolCoPoissonForwardParityCrossGram b hb a ha r hr = 0 := by
  rw [burnolCoPoissonCompressedHolonomy_eq_zero_iff_even_odd_block_eq_zero]
  rw [involutionEvenOddBlock_eq_four_smul_normalized]
  rw [burnolNormalizedParityBlock_compressedHolonomy]
  rw [burnolCoPoissonParityBlock_eq_two_crossGram]
  constructor
  · intro h
    have houter : (4 : ℂ) = 0 ∨
        (2 : ℂ) • burnolCoPoissonForwardParityCrossGram b hb a ha r hr = 0 :=
      smul_eq_zero.mp h
    have h2 := houter.resolve_left (by norm_num)
    have hinner : (2 : ℂ) = 0 ∨
        burnolCoPoissonForwardParityCrossGram b hb a ha r hr = 0 :=
      smul_eq_zero.mp h2
    exact hinner.resolve_left (by norm_num)
  · intro h
    rw [h]
    apply ContinuousLinearMap.ext
    intro x
    simp

end RHTower
