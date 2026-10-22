import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskyMediatorHorizonMonodromy

/-!
# Source incidence for the Hawking--Teukolsky mediator determinant

The exact fundamental chiral radial kernel is nonzero on both virtual mediator channels: the
functional channel has `Q=-3/4`, while the reflected real-pair channel has `-2<Q<0`.  A common
bright completed-Eisenstein angular input therefore gives two nonzero separated source factors.
Multiplying these by the exponential-peeling Hawking block preserves its critical-line determinant
criterion.  The resulting object is the controlled factorized EKG--Teukolsky component, not the
uncomputed sum of all second-order gravitational return terms.
-/

open Complex Real Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Fundamental chiral radial response is nonzero in the universal mediator channel. -/
theorem d4BMFunctionalMediatorChiralSourceKernel_ne_zero :
    d4FundamentalQNMChiralSourceKernel
      d4BMFunctionalReflectionMediatorSpectralPoint ≠ 0 := by
  have hQ : d4ThetaTeukolskyAngularQ
      d4BMFunctionalReflectionMediatorSpectralPoint ≠ 0 := by
    unfold d4ThetaTeukolskyAngularQ
    rw [d4BMFunctionalReflectionMediatorSpectralPoint_angularEigenvalue]
    norm_num
  have hQ2 : d4ThetaTeukolskyAngularQ
      d4BMFunctionalReflectionMediatorSpectralPoint + 2 ≠ 0 := by
    unfold d4ThetaTeukolskyAngularQ
    rw [d4BMFunctionalReflectionMediatorSpectralPoint_angularEigenvalue]
    norm_num
  rw [d4FundamentalQNMChiralSourceKernel_eq _ hQ hQ2]
  exact div_ne_zero (by norm_num) (mul_ne_zero hQ hQ2)

/-- Fundamental chiral radial response is nonzero in every real-pair mediator channel. -/
theorem d4BMXiReflectedRealPairMediatorChiralSourceKernel_ne_zero
    (q : XiZeroCopy) :
    d4FundamentalQNMChiralSourceKernel
      (d4BMXiReflectedRealPairMediatorSpectralPoint q) ≠ 0 := by
  have hmem := d4BMXiReflectedRealPairMediatorAngularQ_mem_Ioo q
  have hQ : d4ThetaTeukolskyAngularQ
      (d4BMXiReflectedRealPairMediatorSpectralPoint q) ≠ 0 := by
    unfold d4ThetaTeukolskyAngularQ
    rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularEigenvalue]
    exact_mod_cast (ne_of_lt hmem.2)
  have hQ2 : d4ThetaTeukolskyAngularQ
      (d4BMXiReflectedRealPairMediatorSpectralPoint q) + 2 ≠ 0 := by
    unfold d4ThetaTeukolskyAngularQ
    rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularEigenvalue]
    exact_mod_cast (ne_of_gt (by linarith [hmem.1] :
      0 < d4BMXiReflectedRealPairMediatorAngularQ q + 2))
  rw [d4FundamentalQNMChiralSourceKernel_eq _ hQ hQ2]
  exact div_ne_zero (by norm_num) (mul_ne_zero hQ hQ2)

/-- Chiral radial factor times completed-Eisenstein angular incidence in the real-pair row. -/
def d4BMXiReflectedMediatorChiralEisensteinScale
    (q : XiZeroCopy) (r t : ℝ) : ℂ :=
  d4FundamentalQNMChiralSourceKernel
      (d4BMXiReflectedRealPairMediatorSpectralPoint q) *
    thetaCuspHawkingCompletedEisensteinPhysicalVertex
      (d4BMXiReflectedRealPairMediatorSpectralPoint q) r t

/-- Chiral radial factor times completed-Eisenstein angular incidence in the universal row. -/
def d4BMFunctionalMediatorChiralEisensteinScale (r t : ℝ) : ℂ :=
  d4FundamentalQNMChiralSourceKernel
      d4BMFunctionalReflectionMediatorSpectralPoint *
    thetaCuspHawkingCompletedEisensteinPhysicalVertex
      d4BMFunctionalReflectionMediatorSpectralPoint r t

/-- Both separated EKG--Teukolsky row factors are simultaneously nonzero. -/
theorem exists_d4BMXiMediatorCommonBrightChiralEisensteinInput
    (q : XiZeroCopy) (t : ℝ) :
    ∃ r : ℝ,
      d4BMXiReflectedMediatorChiralEisensteinScale q r t ≠ 0 ∧
        d4BMFunctionalMediatorChiralEisensteinScale r t ≠ 0 := by
  obtain ⟨r, hreflected, hfunctional⟩ :=
    exists_d4BMXiMediatorCommonBrightEisensteinInput q t
  exact ⟨r,
    mul_ne_zero
      (d4BMXiReflectedRealPairMediatorChiralSourceKernel_ne_zero q) hreflected,
    mul_ne_zero d4BMFunctionalMediatorChiralSourceKernel_ne_zero hfunctional⟩

/-- Factorized EKG--Teukolsky source determinant at two incoming affine frequencies. -/
def d4BMXiMediatorSourceHorizonDeterminant
    (inverseSurfaceGravity logIncoming₁ logIncoming₂ : ℝ)
    (q : XiZeroCopy) (r t : ℝ) : ℂ :=
  let K := exponentialKernel
    (thermalHorizonPhaseExponent (inverseSurfaceGravity : ℂ))
  (d4BMXiReflectedMediatorChiralEisensteinScale q r t *
      K (d4BMXiReflectedRealPairFrequency 0 q) (logIncoming₁ : ℂ)) *
    (d4BMFunctionalMediatorChiralEisensteinScale r t *
      K (d4BMFunctionalReflectionMediatorFrequency 0 0) (logIncoming₂ : ℂ)) -
  (d4BMXiReflectedMediatorChiralEisensteinScale q r t *
      K (d4BMXiReflectedRealPairFrequency 0 q) (logIncoming₂ : ℂ)) *
    (d4BMFunctionalMediatorChiralEisensteinScale r t *
      K (d4BMFunctionalReflectionMediatorFrequency 0 0) (logIncoming₁ : ℂ))

/-- One common bright input detects critical-line placement by the full factorized determinant. -/
theorem exists_d4BMXiMediatorSourceHorizonDeterminant_eq_zero_iff
    {inverseSurfaceGravity logIncoming₁ logIncoming₂ : ℝ}
    (hinverse : inverseSurfaceGravity ≠ 0)
    (hlog : logIncoming₁ ≠ logIncoming₂)
    (q : XiZeroCopy) (t : ℝ) :
    ∃ r : ℝ,
      d4BMXiReflectedMediatorChiralEisensteinScale q r t ≠ 0 ∧
      d4BMFunctionalMediatorChiralEisensteinScale r t ≠ 0 ∧
      (d4BMXiMediatorSourceHorizonDeterminant
          inverseSurfaceGravity logIncoming₁ logIncoming₂ q r t = 0 ↔
        (q.1 : ℂ).re = 1 / 2) := by
  obtain ⟨r, hreflected, hfunctional⟩ :=
    exists_d4BMXiMediatorCommonBrightChiralEisensteinInput q t
  refine ⟨r, hreflected, hfunctional, ?_⟩
  simpa [d4BMXiMediatorSourceHorizonDeterminant] using
    (d4BMXiMediatorHorizonDeterminant_separableScale_eq_zero_iff
      (inputScale₁ := (1 : ℂ)) (inputScale₂ := (1 : ℂ))
      hinverse hlog 0 q hreflected hfunctional (by norm_num) (by norm_num))

/-- Every tilted divisor has a bright factorized EKG--Teukolsky Hawking mixing block. -/
theorem exists_d4BMXiMediatorSourceHorizonDeterminant_ne_zero_of_tilt
    {inverseSurfaceGravity logIncoming₁ logIncoming₂ : ℝ}
    (hinverse : inverseSurfaceGravity ≠ 0)
    (hlog : logIncoming₁ ≠ logIncoming₂)
    (q : XiZeroCopy) (t : ℝ)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ r : ℝ,
      d4BMXiReflectedMediatorChiralEisensteinScale q r t ≠ 0 ∧
      d4BMFunctionalMediatorChiralEisensteinScale r t ≠ 0 ∧
      d4BMXiMediatorSourceHorizonDeterminant
        inverseSurfaceGravity logIncoming₁ logIncoming₂ q r t ≠ 0 := by
  obtain ⟨r, hreflected, hfunctional, hdet⟩ :=
    exists_d4BMXiMediatorSourceHorizonDeterminant_eq_zero_iff
      hinverse hlog q t
  refine ⟨r, hreflected, hfunctional, ?_⟩
  exact fun hzero => htilt (hdet.1 hzero)

/-- Global bright-source confluence for one two-frequency horizon probe. -/
def D4BMXiMediatorSourceHorizonConfluent
    (inverseSurfaceGravity logIncoming₁ logIncoming₂ t : ℝ) : Prop :=
  ∀ q : XiZeroCopy,
    ∃ r : ℝ,
      d4BMXiReflectedMediatorChiralEisensteinScale q r t ≠ 0 ∧
      d4BMFunctionalMediatorChiralEisensteinScale r t ≠ 0 ∧
      d4BMXiMediatorSourceHorizonDeterminant
        inverseSurfaceGravity logIncoming₁ logIncoming₂ q r t = 0

/-- Global confluence of the bright factorized source block is exactly RH. -/
theorem riemannHypothesis_iff_d4BMXiMediatorSourceHorizonConfluent
    {inverseSurfaceGravity logIncoming₁ logIncoming₂ : ℝ}
    (hinverse : inverseSurfaceGravity ≠ 0)
    (hlog : logIncoming₁ ≠ logIncoming₂)
    (t : ℝ) :
    RiemannHypothesis ↔
      D4BMXiMediatorSourceHorizonConfluent
        inverseSurfaceGravity logIncoming₁ logIncoming₂ t := by
  constructor
  · intro hRH q
    obtain ⟨r, hreflected, hfunctional, hdet⟩ :=
      exists_d4BMXiMediatorSourceHorizonDeterminant_eq_zero_iff
        hinverse hlog q t
    exact ⟨r, hreflected, hfunctional,
      hdet.2 (xi_divisor_support_re_eq_half_of_rh hRH q.1)⟩
  · intro hconfluent
    exact (riemannHypothesis_iff_d4BMXiTwoChannelBackreactionIsConfluent).2
      (fun q => by
        obtain ⟨r, hreflected, hfunctional, hzero⟩ := hconfluent q
        exact (d4BMXiTwoChannelHelicityTransfer_eq_zero_iff q).2
          ((d4BMXiMediatorHorizonDeterminant_separableScale_eq_zero_iff
            (inputScale₁ := (1 : ℂ)) (inputScale₂ := (1 : ℂ))
            hinverse hlog 0 q hreflected hfunctional (by norm_num) (by norm_num)).1
            (by simpa [d4BMXiMediatorSourceHorizonDeterminant] using hzero)))

end

end RHTower
