import GaloisForLFunctions.RHTower.NonvacuousWitnessBound

/-!
# A finite-index subgroup of `SL(2, ℤ)` with a Laplace eigenvalue in `(0, ¼)`

Take the smooth bump profile `φ` (`φ = 1` near `0`, support in `[−1, 1]`).  Its Selberg transform is
strictly increasing on `[½, ∞)`, so `δ = m_φ − h_φ(½) = h_φ(1) − h_φ(½) > 0`.  For the cyclic covers
`Γ_N = windingSubgroup N` the test field `F_{N,L}` has Dirichlet form below `2δ‖F‖²` once `L` and
then `N` are large (`exists_testField_dirichlet_lt`), and the test-field criterion produces a
`Γ_N`-equivariant Laplace eigenfunction with eigenvalue `λ ∈ (0, ¼)` orthogonal to the constants.
Reading off one coordinate gives a scalar statement (`exists_finiteIndex_small_eigenvalue`): a
nonconstant `Γ_N`-invariant `C²` eigenfunction `u` of the positive hyperbolic Laplacian,
`Δ⁺u = λu` with `0 < λ < ¼`, square-integrable on the `Γ_N`-cell `⋃_q g_q⁻¹ 𝒟`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped MatrixGroups InnerProductSpace ENNReal

namespace GaloisForLFunctions.RHTower.NonvacuousWitness

open GaloisForLFunctions.HTGeometry RepPointPair RepCoset ModularLambdaWinding

noncomputable section

/-- The unit bump: `1` on `[−½, ½]`, supported in `(−1, 1)`. -/
def unitBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The smooth bump profile. -/
def bumpSmoothProfile : SmoothProfile where
  toFun := unitBump
  radius := 1
  radius_nonneg := zero_le_one
  contDiff := unitBump.contDiff
  support := fun u hu => by
    have : u ∉ Function.support unitBump := by
      rw [unitBump.support_eq]
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
      exact hu.le
    simpa using this

theorem bumpSmoothProfile_nonneg (u : ℝ) : 0 ≤ bumpSmoothProfile.toFun u := unitBump.nonneg

theorem bumpSmoothProfile_zero : bumpSmoothProfile.toFun 0 = 1 :=
  unitBump.one_of_mem_closedBall (by simp [unitBump])

/-- **The spectral gap of the bump**: `h_φ(½) < m_φ`. -/
theorem halfTransform_lt_kernelMass_bump :
    halfTransform (fun u => |bumpSmoothProfile.toFun u|) < kernelMassR bumpSmoothProfile.toFun := by
  have hc := bumpSmoothProfile.contDiff.continuous
  have hR : DeckPointPair.KernelSupport bumpSmoothProfile.toFun 1 := bumpSmoothProfile.kernelSupport'
  have h := DeckPointPair.selbergRealTransform_lt hc bumpSmoothProfile_nonneg hR
    ⟨0, le_refl 0, by rw [bumpSmoothProfile_zero]; norm_num⟩ (le_refl (1 / 2 : ℝ))
    (show (1 / 2 : ℝ) < 1 by norm_num)
  rw [DeckPointPair.selbergRealTransform_one_eq_mass hc hR] at h
  rw [halfTransform_eq_selbergReal bumpSmoothProfile_nonneg]
  exact h


/-- **Existence of a small Laplace eigenvalue on a cyclic cover** (vector form). -/
theorem exists_testField_laplaceEigen : ∃ n : ℕ, ∃ lam : ℝ, 0 < lam ∧ lam < 1 / 4 ∧
    ∃ U : ℍ → EuclideanSpace ℂ (SL(2, ℤ) ⧸ windingSubgroup (n + 2)),
      ∃ hL : IsLaplaceEigen (cosetRep (windingSubgroup (n + 2))) lam U, (∃ z, U z ≠ 0) ∧
        toRepL2 U hL.memLp ∈ (invConst (cosetRep (windingSubgroup (n + 2))))ᗮ := by
  have hδ : 0 < kernelMassR bumpSmoothProfile.toFun -
      halfTransform (fun u => |bumpSmoothProfile.toFun u|) :=
    sub_pos.2 halfTransform_lt_kernelMass_bump
  obtain ⟨n, L, hL2, hD⟩ := exists_testField_dirichlet_lt bumpSmoothProfile
    bumpSmoothProfile_nonneg hδ
  obtain ⟨lam, h0, h1, U, hL, hU0, hUV⟩ := bumpSmoothProfile.exists_laplaceEigen_of_testField
    bumpSmoothProfile_nonneg (by rw [bumpSmoothProfile_zero]; norm_num)
    (continuous_testField (n + 2) L) (isEquivariant_testField (n + 2) L)
    (memLp_testField (n + 2) L) (fun z c hc => inner_testField_eq_zero (n + 2) L (by omega) z c hc)
    hD
  exact ⟨n, lam, h0, h1, U, hL, hU0, hUV⟩


/-- The cell has positive hyperbolic area. -/
theorem volume_fd_pos : 0 < volume fd :=
  volume_fd_inter_im_le_two_pos.trans_le (measure_mono Set.inter_subset_left)

/-- **From an equivariant eigenfield to a scalar eigenfunction.**  A nonzero `C²` Laplace eigenfield
for the coset representation of `Γ`, orthogonal to the invariant constants, has as its `Γ`-coordinate a
nonconstant `Γ`-invariant Maass eigenfunction, square-integrable on the `Γ`-cell. -/
theorem exists_maass_of_laplaceEigen {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {lam : ℝ}
    {U : ℍ → EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ)} (hL : IsLaplaceEigen (cosetRep Γ) lam U)
    {z₀ : ℍ} (hz₀ : U z₀ ≠ 0) (hUV : toRepL2 U hL.memLp ∈ (invConst (cosetRep Γ))ᗮ) :
    ∃ u : ℍ → ℂ, IsMaassEigenfunction lam u ∧ (∀ γ ∈ Γ, ∀ z, u (γ • z) = u z) ∧
      (¬ ∃ c : ℂ, ∀ z, u z = c) ∧
      Integrable (fun z => ∑ᶠ q : SL(2, ℤ) ⧸ Γ, ‖u ((Quotient.out q)⁻¹ • z)‖ ^ 2) cellMeasure := by
  set q₁ : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk 1
  set u : ℍ → ℂ := fun z => U z q₁
  have hinv : ∀ γ ∈ Γ, ∀ z, u (γ • z) = u z := invariant_eval_one hL.equivariant
  have hUeq : U = cosetLift u := eq_cosetLift_eval_one hL.equivariant
  have hUq : ∀ z q, U z q = u ((Quotient.out q)⁻¹ • z) := by
    intro z q
    rw [hUeq, cosetLift_apply]
  -- regularity
  have hsmooth : IsRealSmoothUpperHalfPlane u := by
    have hproj : ContDiff ℝ 2 (fun v : EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ) => v q₁) :=
      ((EuclideanSpace.proj q₁ : EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
    exact hproj.comp_contDiffOn hL.contDiffOn
  -- the eigenvalue equation
  obtain ⟨γ₀, hγ₀⟩ := QuotientGroup.mk_out_eq_mul Γ (1 : SL(2, ℤ))
  have hout : Quotient.out q₁ = 1 * γ₀ := hγ₀
  have hlap : ∀ z, positiveHyperbolicLaplacian u z = (lam : ℂ) * u z := by
    intro z
    have h := congrArg (fun F : ℍ → EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ) => F (Quotient.out q₁ • z) q₁)
      (hypLap_cosetLift (Γ := Γ) hsmooth)
    simp only at h
    rw [← hUeq, hL.eigen, cosetLift_apply, inv_smul_smul] at h
    have hu : U (Quotient.out q₁ • z) q₁ = u z := by
      change u (Quotient.out q₁ • z) = u z
      rw [hout, one_mul]
      exact hinv _ γ₀.2 z
    rw [PiLp.smul_apply, hu] at h
    have : -positiveHyperbolicLaplacian u z = -((lam : ℂ) * u z) := by
      rw [← h]
      push_cast
      ring
    exact neg_injective this
  -- `u` does not vanish identically
  have hne : ∃ z, u z ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hz₀
    refine PiLp.ext fun q => ?_
    rw [hUq, hall]
    rfl
  -- `u` is not constant
  have hnc : ¬ ∃ c : ℂ, ∀ z, u z = c := by
    rintro ⟨c, hc⟩
    set v : EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ) := WithLp.toLp 2 fun _ => c
    have hUv : ∀ z, U z = v := fun z => PiLp.ext fun q => by rw [hUq, hc]
    have hv : ∀ B, cosetRep Γ B v = v := fun B => PiLp.ext fun q => by rw [cosetRep_apply]
    have hconst : toRepL2 U hL.memLp = constRep (SL(2, ℤ) ⧸ Γ) v :=
      MemLp.toLp_congr _ (memLp_const v) (Eventually.of_forall hUv)
    have hmem : toRepL2 U hL.memLp ∈ invConst (cosetRep Γ) := by
      rw [hconst]
      exact Submodule.subset_span ⟨v, hv, rfl⟩
    have hzero : toRepL2 U hL.memLp = 0 :=
      inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hUV _ hmem)
    have hnorm := norm_toRepL2_sq hL.memLp
    rw [hzero, norm_zero] at hnorm
    simp_rw [hUv] at hnorm
    rw [setIntegral_const, smul_eq_mul, Measure.real_def] at hnorm
    have hvol : 0 < (volume fd).toReal := ENNReal.toReal_pos volume_fd_pos.ne' volume_fd_ne_top
    have hv0 : ‖v‖ ^ 2 = 0 := by
      have h2 : (0 : ℝ) = (volume fd).toReal * ‖v‖ ^ 2 := by simpa using hnorm
      nlinarith [sq_nonneg ‖v‖]
    have hv' : v = 0 := by
      rw [sq_eq_zero_iff, norm_eq_zero] at hv0
      exact hv0
    obtain ⟨z, hz⟩ := hne
    apply hz
    rw [hc]
    have := congrArg (fun w : EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ) => w q₁) hv'
    simpa [v] using this
  -- square integrability on the `Γ`-cell
  have hint : Integrable (fun z => ∑ᶠ q : SL(2, ℤ) ⧸ Γ, ‖u ((Quotient.out q)⁻¹ • z)‖ ^ 2)
      cellMeasure := by
    have h2 := (memLp_two_iff_integrable_sq_norm hL.memLp.1).1 hL.memLp
    refine h2.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [finsum_eq_sum_of_fintype, EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun q _ => by rw [hUq]
  exact ⟨u, ⟨hsmooth, hlap⟩, hinv, hnc, hint⟩

/-- **A finite-index subgroup of `SL(2, ℤ)` with a Laplace eigenvalue in `(0, ¼)`.**  There are a
finite-index `Γ ≤ SL(2, ℤ)` (a cyclic cover `Γ_N` of `Γ(2)`), a `λ ∈ (0, ¼)` and a nonconstant
`Γ`-invariant `C²` function `u` with `Δ⁺u = λ u` (positive hyperbolic Laplacian), square-integrable on
the `Γ`-cell: `∫_𝒟 Σ_{q ∈ SL(2,ℤ)/Γ} |u(g_q⁻¹ z)|² dμ(z) < ∞`. -/
theorem exists_finiteIndex_small_eigenvalue :
    ∃ Γ : Subgroup SL(2, ℤ), Γ.FiniteIndex ∧ ∃ lam : ℝ, 0 < lam ∧ lam < 1 / 4 ∧
      ∃ u : ℍ → ℂ, IsMaassEigenfunction lam u ∧ (∀ γ ∈ Γ, ∀ z, u (γ • z) = u z) ∧
        (¬ ∃ c : ℂ, ∀ z, u z = c) ∧
        Integrable (fun z => ∑ᶠ q : SL(2, ℤ) ⧸ Γ, ‖u ((Quotient.out q)⁻¹ • z)‖ ^ 2) cellMeasure := by
  obtain ⟨n, lam, h0, h1, U, hL, ⟨z₀, hz₀⟩, hUV⟩ := exists_testField_laplaceEigen
  exact ⟨windingSubgroup (n + 2), inferInstance, lam, h0, h1, exists_maass_of_laplaceEigen hL hz₀ hUV⟩

end

end GaloisForLFunctions.RHTower.NonvacuousWitness
