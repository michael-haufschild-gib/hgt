import GaloisForLFunctions.RHTower.PolynomialFockAdaptedTangentPacketBessel

open scoped InnerProductSpace

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def besselFamilyAnalysisLinearMap
    (φ : ι → H)
    (hsummable : ∀ x, Summable fun i => ‖inner ℂ (φ i) x‖ ^ (2 : ℝ)) :
    H →ₗ[ℂ] HTGeometry.IndexedEllTwo ι where
  toFun x := ⟨fun i => inner ℂ (φ i) x, memℓp_gen (hsummable x)⟩
  map_add' := by
    intro x y
    ext i
    exact inner_add_right _ _ _
  map_smul' := by
    intro c x
    ext i
    simp

@[simp] theorem besselFamilyAnalysisLinearMap_apply
    (φ : ι → H)
    (hsummable : ∀ x, Summable fun i => ‖inner ℂ (φ i) x‖ ^ (2 : ℝ))
    (x : H) (i : ι) :
    besselFamilyAnalysisLinearMap φ hsummable x i = inner ℂ (φ i) x := rfl

theorem norm_besselFamilyAnalysisLinearMap_le
    (φ : ι → H)
    (hsummable : ∀ x, Summable fun i => ‖inner ℂ (φ i) x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' i, ‖inner ℂ (φ i) x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : H) :
    ‖besselFamilyAnalysisLinearMap φ hsummable x‖ ≤ C * ‖x‖ := by
  have hleft : 0 ≤ ‖besselFamilyAnalysisLinearMap φ hsummable x‖ := norm_nonneg _
  have hright : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  have hdiag :
      ‖besselFamilyAnalysisLinearMap φ hsummable x‖ ^ (2 : ℝ) =
        ∑' i, ‖inner ℂ (φ i) x‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ι => ℂ) (by norm_num)
      (besselFamilyAnalysisLinearMap φ hsummable x)
  have hpow :
      ‖besselFamilyAnalysisLinearMap φ hsummable x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ) := by
    rw [hdiag]
    exact hBessel x
  have hleft2 :
      ‖besselFamilyAnalysisLinearMap φ hsummable x‖ ^ (2 : ℝ) =
        ‖besselFamilyAnalysisLinearMap φ hsummable x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hright2 : (C * ‖x‖) ^ (2 : ℝ) = (C * ‖x‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hleft2, hright2] at hpow
  have hsqrt := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

def besselFamilyAnalysisOperator
    (φ : ι → H)
    (hsummable : ∀ x, Summable fun i => ‖inner ℂ (φ i) x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' i, ‖inner ℂ (φ i) x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    H →L[ℂ] HTGeometry.IndexedEllTwo ι :=
  LinearMap.mkContinuous (besselFamilyAnalysisLinearMap φ hsummable) C
    (norm_besselFamilyAnalysisLinearMap_le φ hsummable hC hBessel)

@[simp] theorem besselFamilyAnalysisOperator_apply
    (φ : ι → H)
    (hsummable : ∀ x, Summable fun i => ‖inner ℂ (φ i) x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' i, ‖inner ℂ (φ i) x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : H) (i : ι) :
    besselFamilyAnalysisOperator φ hsummable hC hBessel x i = inner ℂ (φ i) x := rfl

variable [CompleteSpace H]

def besselFamilySynthesisOperator
    (φ : ι → H)
    (hsummable : ∀ x, Summable fun i => ‖inner ℂ (φ i) x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' i, ‖inner ℂ (φ i) x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    HTGeometry.IndexedEllTwo ι →L[ℂ] H :=
  adjoint (besselFamilyAnalysisOperator φ hsummable hC hBessel)

theorem besselFamilySynthesisOperator_coordinateBasis
    [DecidableEq ι]
    (φ : ι → H)
    (hsummable : ∀ x, Summable fun i => ‖inner ℂ (φ i) x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' i, ‖inner ℂ (φ i) x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (i : ι) :
    besselFamilySynthesisOperator φ hsummable hC hBessel
        (HTGeometry.ellTwoCoordinateBasis ι i) = φ i := by
  apply ext_inner_left ℂ
  intro x
  rw [besselFamilySynthesisOperator, adjoint_inner_right,
    HTGeometry.ellTwoCoordinateBasis_apply, lp.inner_single_right,
    besselFamilyAnalysisOperator_apply]
  simp [RCLike.inner_apply]

def polynomialFockAdaptedTangentPacketSynthesis
    (m : ℝ) (hm : 4 < m) : MomentFock →L[ℂ] MomentFock := by
  let φ : ℕ → MomentFock :=
    polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le
  let Δ : ℝ := ∑' z : ℤ, polynomialFockAdaptedGramEnvelope m z.natAbs
  have hΔ : 0 ≤ Δ := tsum_nonneg fun z =>
    polynomialFockAdaptedGramEnvelope_nonneg m z.natAbs
  have hsum : ∀ x, Summable fun n => ‖inner ℂ (φ n) x‖ ^ (2 : ℝ) := by
    intro x
    simpa [Real.rpow_two] using
      summable_norm_inner_sq_polynomialFockShiftedAdaptedNormalizedTangentPacket hm x
  have hBessel : ∀ x,
      ∑' n, ‖inner ℂ (φ n) x‖ ^ (2 : ℝ) ≤
        (Real.sqrt Δ * ‖x‖) ^ (2 : ℝ) := by
    intro x
    have h :=
      tsum_norm_inner_sq_polynomialFockShiftedAdaptedNormalizedTangentPacket_le hm x
    simpa [Real.rpow_two, mul_pow, Real.sq_sqrt hΔ] using h
  exact besselFamilySynthesisOperator φ hsum (Real.sqrt_nonneg Δ) hBessel

theorem polynomialFockAdaptedTangentPacketSynthesis_coordinateBasis
    {m : ℝ} (hm : 4 < m) (n : ℕ) :
    polynomialFockAdaptedTangentPacketSynthesis m hm
        (HTGeometry.ellTwoCoordinateBasis ℕ n) =
      polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n := by
  unfold polynomialFockAdaptedTangentPacketSynthesis
  exact besselFamilySynthesisOperator_coordinateBasis _ _ _ _ n

end

end RHTower
