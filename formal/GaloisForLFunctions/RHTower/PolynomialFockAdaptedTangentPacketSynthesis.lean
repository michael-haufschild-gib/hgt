import GaloisForLFunctions.RHTower.PolynomialFockAdaptedTangentPacketBessel

/-!
# Synthesis operator of the adapted tangent packets

A family `φ : ι → H` in a complex inner product space satisfying a Bessel bound
`∑ |⟨φ_i, x⟩|² ≤ (C ‖x‖)²` has a bounded analysis operator `x ↦ (⟨φ_i, x⟩)_i` into `ℓ²(ι)` of
norm at most `C`; on a Hilbert space its adjoint is the synthesis operator, which maps the `i`-th
coordinate vector to `φ_i`. Applied to the shifted adapted normalized tangent packets of the
degree-`m` polynomial moment Fock space (using their Bessel bound for `m > 4`), this yields a bounded
operator on the moment Fock carrier `ℓ²(ℕ)` sending `e_n` to the `n`-th packet.

## Main results

- `norm_besselFamilyAnalysisLinearMap_le`: the analysis map has norm at most `C` under a Bessel bound.
- `besselFamilyAnalysisOperator`, `besselFamilySynthesisOperator`: the bounded analysis operator
  and its adjoint.
- `besselFamilySynthesisOperator_coordinateBasis`: the synthesis operator maps `e_i` to `φ_i`.
- `polynomialFockAdaptedTangentPacketSynthesis`: for `m > 4`, the bounded synthesis operator of the
  adapted packet family.
- `polynomialFockAdaptedTangentPacketSynthesis_coordinateBasis`: it maps `e_n` to the `n`-th shifted
  adapted packet.

## Hypotheses

The generic Bessel-family constructions take as arguments the summability of
`i ↦ |⟨φ_i, x⟩|²` for every `x` and a Bessel bound with constant `C ≥ 0`; these are inputs of the
general construction. For the polynomial Fock packets both inputs are proved in the imported Bessel
module, so `polynomialFockAdaptedTangentPacketSynthesis` and its coordinate formula are
unconditional, assuming only `4 < m`.
-/

open scoped InnerProductSpace

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Analysis map `x ↦ (⟨φ_i, x⟩)_i` of a family whose coefficient sequences are square summable,
as a linear map into `ℓ²(ι)`. -/
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

/-- Given a Bessel bound `∑ |⟨φ_i, x⟩|² ≤ (C ‖x‖)²` with `C ≥ 0`, the analysis map satisfies
`‖(⟨φ_i, x⟩)_i‖ ≤ C ‖x‖`. -/
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

/-- The analysis map of a Bessel family as a bounded operator `H → ℓ²(ι)` of norm at most `C`. -/
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

/-- Synthesis operator `ℓ²(ι) → H` of a Bessel family: the adjoint of its analysis operator. -/
def besselFamilySynthesisOperator
    (φ : ι → H)
    (hsummable : ∀ x, Summable fun i => ‖inner ℂ (φ i) x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' i, ‖inner ℂ (φ i) x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    HTGeometry.IndexedEllTwo ι →L[ℂ] H :=
  adjoint (besselFamilyAnalysisOperator φ hsummable hC hBessel)

/-- The synthesis operator of a Bessel family sends the `i`-th coordinate vector of `ℓ²(ι)` to `φ_i`. -/
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

/-- For `4 < m`, the bounded synthesis operator `ℓ²(ℕ) → MomentFock` of the shifted adapted
normalized tangent packets, with Bessel constant `sqrt (∑_{z ∈ ℤ} E_m(|z|))`. -/
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

/-- For `4 < m`, the packet synthesis operator maps the coordinate vector `e_n` to the `n`-th shifted
adapted normalized tangent packet. -/
theorem polynomialFockAdaptedTangentPacketSynthesis_coordinateBasis
    {m : ℝ} (hm : 4 < m) (n : ℕ) :
    polynomialFockAdaptedTangentPacketSynthesis m hm
        (HTGeometry.ellTwoCoordinateBasis ℕ n) =
      polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n := by
  unfold polynomialFockAdaptedTangentPacketSynthesis
  exact besselFamilySynthesisOperator_coordinateBasis _ _ _ _ n

end

end RHTower
