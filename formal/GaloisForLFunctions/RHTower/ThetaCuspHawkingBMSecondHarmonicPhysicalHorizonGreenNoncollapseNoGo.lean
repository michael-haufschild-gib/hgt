import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonIncidence

/-!
# Canonical physical BM Green equality no-go

The normalizable AdS branch has unit square-root boundary residue, so it is nonzero at some
interior radial point.  At that point the exact rank-one ingoing-minus-outgoing Green identity has
nonzero Frobenius coefficient and nonzero canonical denominators.  Its diagonal value is therefore
nonzero.

Consequently the physical ingoing and outgoing frequency-domain Green blocks are unequal on every
Xi fibre, including critical-line fibres.  Equality of these canonical propagators cannot select
RH.  The positive survivor is an explicit one-point source with nonzero rank-one normalizable-AdS
response on every Xi fibre.

`[NO-GO] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Unit square-root boundary residue forces the normalizable branch to be nonzero eventually
near the AdS boundary. -/
theorem eventually_d4BMPlusPlusAdSNormalizableSolution_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ∀ᶠ z in 𝓝[<] (1 : ℝ),
      0 < z ∧ z < 1 ∧ d4BMPlusPlusAdSNormalizableSolution n chi z ≠ 0 := by
  have hratio :=
    tendsto_d4BMPlusPlusAdSNormalizableSolution_div_sqrt_one_sub n chi hchi
  have hratio_ne : ∀ᶠ z in 𝓝[<] (1 : ℝ),
      d4BMPlusPlusAdSNormalizableSolution n chi z /
        (Real.sqrt (1 - z) : ℂ) ≠ 0 :=
    hratio.eventually_ne one_ne_zero
  have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)
  filter_upwards [hpos, self_mem_nhdsWithin, hratio_ne] with z hz0 hz1 hratioz
  exact ⟨hz0, hz1, fun hV => hratioz (by simp [hV])⟩

/-- There is an interior point where the normalizable AdS branch does not vanish. -/
theorem exists_d4BMPlusPlusAdSNormalizableSolution_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ∃ z : ℝ, 0 < z ∧ z < 1 ∧ d4BMPlusPlusAdSNormalizableSolution n chi z ≠ 0 := by
  exact (eventually_d4BMPlusPlusAdSNormalizableSolution_ne_zero n chi hchi).exists

/-- Physical ingoing-minus-outgoing Green kernel has a nonzero interior diagonal value. -/
theorem exists_d4BMPlusPlusIngoing_sub_outgoingRightEndpointGreenKernel_diag_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      d4BMPlusPlusIngoingAdSNormalizableRightEndpointGreenKernel n chi t t -
        d4BMPlusPlusOutgoingAdSNormalizableRightEndpointGreenKernel n chi t t ≠ 0 := by
  obtain ⟨t, ht0, ht1, hV⟩ :=
    exists_d4BMPlusPlusAdSNormalizableSolution_ne_zero n chi hchi
  refine ⟨t, ht0, ht1, ?_⟩
  rw [d4BMPlusPlusIngoing_sub_outgoingRightEndpointGreenKernel n chi hchi ht0 ht1]
  exact div_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (neg_ne_zero.mpr
          (d4BMPlusPlusComplementaryFrobeniusExponent_ne_zero n chi hchi))
        hV)
      hV)
    (mul_ne_zero
      (d4BMPlusPlusRegularAdSNormalizableGreenDenominator_ne_zero
        n chi hchi ht0 ht1)
      (d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_ne_zero
        n chi hchi ht0 ht1))

/-- Every Xi fibre has a nonzero interior diagonal Green difference. -/
theorem exists_d4BMXiPlusPlusIngoing_sub_outgoingRightEndpointGreenKernel_diag_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      d4BMPlusPlusIngoingAdSNormalizableRightEndpointGreenKernel n
          (d4BMXiMixedHorizonAngularMomentum q) t t -
        d4BMPlusPlusOutgoingAdSNormalizableRightEndpointGreenKernel n
          (d4BMXiMixedHorizonAngularMomentum q) t t ≠ 0 :=
  exists_d4BMPlusPlusIngoing_sub_outgoingRightEndpointGreenKernel_diag_ne_zero n
    (d4BMXiMixedHorizonAngularMomentum q)
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

/-- Canonical physical ingoing and outgoing Green kernels are unequal on every Xi fibre. -/
theorem d4BMXiPlusPlusIngoingRightEndpointGreenKernel_ne_outgoing
    (n : ℕ) (q : XiZeroCopy) :
    (fun p : ℝ × ℝ =>
      d4BMPlusPlusIngoingAdSNormalizableRightEndpointGreenKernel n
        (d4BMXiMixedHorizonAngularMomentum q) p.1 p.2) ≠
    (fun p : ℝ × ℝ =>
      d4BMPlusPlusOutgoingAdSNormalizableRightEndpointGreenKernel n
        (d4BMXiMixedHorizonAngularMomentum q) p.1 p.2) := by
  obtain ⟨t, _ht0, _ht1, hne⟩ :=
    exists_d4BMXiPlusPlusIngoing_sub_outgoingRightEndpointGreenKernel_diag_ne_zero n q
  intro h
  have ht := congrFun h (t, t)
  exact hne (sub_eq_zero.mpr ht)

/-- Unit point source propagated through the physical ingoing Green block. -/
def d4BMPlusPlusPointIngoingAdSNormalizableGreenResponse
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusFiniteIngoingAdSNormalizableRightEndpointGreenResponse
    ({()} : Finset Unit) (fun _ => t) (fun _ => 1) n chi z

/-- Unit point source propagated through the physical outgoing Green block. -/
def d4BMPlusPlusPointOutgoingAdSNormalizableGreenResponse
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusFiniteOutgoingAdSNormalizableRightEndpointGreenResponse
    ({()} : Finset Unit) (fun _ => t) (fun _ => 1) n chi z

@[simp]
theorem d4BMPlusPlusPointIngoingAdSNormalizableGreenResponse_eq_kernel
    (n : ℕ) (chi : ℂ) (t z : ℝ) :
    d4BMPlusPlusPointIngoingAdSNormalizableGreenResponse n chi t z =
      d4BMPlusPlusIngoingAdSNormalizableRightEndpointGreenKernel n chi t z := by
  simp [d4BMPlusPlusPointIngoingAdSNormalizableGreenResponse,
    d4BMPlusPlusFiniteIngoingAdSNormalizableRightEndpointGreenResponse,
    d4BMPlusPlusFiniteRegularAdSNormalizableRightEndpointGreenResponse,
    d4BMPlusPlusIngoingAdSNormalizableRightEndpointGreenKernel]

@[simp]
theorem d4BMPlusPlusPointOutgoingAdSNormalizableGreenResponse_eq_kernel
    (n : ℕ) (chi : ℂ) (t z : ℝ) :
    d4BMPlusPlusPointOutgoingAdSNormalizableGreenResponse n chi t z =
      d4BMPlusPlusOutgoingAdSNormalizableRightEndpointGreenKernel n chi t z := by
  simp [d4BMPlusPlusPointOutgoingAdSNormalizableGreenResponse,
    d4BMPlusPlusFiniteOutgoingAdSNormalizableRightEndpointGreenResponse,
    d4BMPlusPlusFiniteComplementaryAdSNormalizableRightEndpointGreenResponse,
    d4BMPlusPlusOutgoingAdSNormalizableRightEndpointGreenKernel]

/-- Positive survivor: every Xi fibre has an interior one-point source with nonzero physical
ingoing-minus-outgoing response. -/
theorem exists_d4BMXiPlusPlusPointIngoing_sub_outgoingGreenResponse_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      d4BMPlusPlusPointIngoingAdSNormalizableGreenResponse n
          (d4BMXiMixedHorizonAngularMomentum q) t t -
        d4BMPlusPlusPointOutgoingAdSNormalizableGreenResponse n
          (d4BMXiMixedHorizonAngularMomentum q) t t ≠ 0 := by
  simpa using
    exists_d4BMXiPlusPlusIngoing_sub_outgoingRightEndpointGreenKernel_diag_ne_zero n q

end

end RHTower
