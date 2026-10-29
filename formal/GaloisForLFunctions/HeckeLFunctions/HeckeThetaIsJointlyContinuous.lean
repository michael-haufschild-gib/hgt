import GaloisForLFunctions.HeckeLFunctions.HeckeThetaHasMellinContinuation

/-!
# Joint continuity of the actual Hecke theta families

On every region with a positive lower Gaussian parameter and an upper bound on
place profiles, one fixed Gaussian bounds all parity kernels. Its summability
on the actual integral and trace-dual ideals proves local uniform convergence
of both weighted theta series. The resulting joint continuity supplies
measurability and compact-domain integration in the archimedean variables.
-/

noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory Set Filter Topology
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
local notation "ι" => numberFieldMixedRealCoordinateIndex K

omit [NumberField K] in
/-- The zero logarithmic profile leaves every archimedean coordinate fixed. -/
theorem numberFieldMixedPlaceScale_zero (z : mixedEmbedding.mixedSpace K) :
    numberFieldMixedPlaceScale 0 z = z := by
  apply Prod.ext
  · funext w
    change Real.exp (-(0 : ℝ)) * z.1 w = z.1 w
    rw [neg_zero, Real.exp_zero, one_mul]
  · funext w
    change (Real.exp (-(0 : ℝ)) : ℂ) * z.2 w = z.2 w
    rw [neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- A positive parameter lower bound and an upper profile bound give one Gaussian majorant. -/
theorem exists_uniform_mixedParityGaussian_majorant (ε : ι → Bool)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : InfinitePlace K → ℝ, (∀ v, y v ≤ M) →
      ∀ t : ℝ, δ ≤ t → ∀ z : mixedEmbedding.mixedSpace K,
      ‖parityGaussian ε t (numberFieldTraceCoordinates (numberFieldMixedPlaceScale y z))‖ ≤
        C * Real.exp (-(Real.pi * (δ / 2 * Real.exp (-M)^2)) *
          ‖numberFieldTraceCoordinates z‖^2) := by
  obtain ⟨C, hC, hbound⟩ := exists_parityGaussian_norm_bound ε hδ
  refine ⟨C, hC, ?_⟩
  intro y hy t ht z
  refine (norm_parityGaussian_antitone_parameter ε ht _).trans ((hbound _).trans ?_)
  rw [norm_gaussianKernel]
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (norm_sq_placeScale_ge M y hy z)
    (mul_pos Real.pi_pos (half_pos hδ)).le
  nlinarith only [h]

/-- The fixed Gaussian used in local profile majorants is summable on every integral ideal. -/
theorem summable_integralIdeal_gaussian (b : Ideal (𝓞 K)) {T : ℝ} (hT : 0 < T) :
    Summable (fun a : b => Real.exp (-(Real.pi * T) *
      ‖numberFieldTraceCoordinates (mixedEmbedding K ((a : 𝓞 K) : K))‖^2)) := by
  simpa only [parityGaussian, parityMonomial, Bool.toNat_false, pow_zero,
    Finset.prod_const_one, one_mul, numberFieldMixedPlaceScale_zero, norm_gaussianKernel] using
    summable_norm_parityGaussian_integralIdeal b (fun _ => false) 0 hT

/-- The same fixed Gaussian is summable on a nonzero fractional ideal. -/
theorem summable_fractionalIdeal_gaussian (I : FIˣ) {T : ℝ} (hT : 0 < T) :
    Summable (fun a : (I : FI) => Real.exp (-(Real.pi * T) *
      ‖numberFieldTraceCoordinates (mixedEmbedding K (a : K))‖^2)) := by
  simpa only [numberFieldMixedPlaceScale_zero] using
    summable_numberFieldScaledIdealTheta I 0 hT

variable (𝔪 : Modulus K)

/-- Physical theta has a summable majorant uniform on each positive parameter strip. -/
theorem exists_uniform_heckeThetaKernel_majorant (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K))
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ u : b → ℝ, Summable u ∧ ∀ y : InfinitePlace K → ℝ, (∀ v, y v ≤ M) →
      ∀ t : ℝ, δ ≤ t → ∀ a : b, ‖heckeThetaKernel 𝔪 ψ y t (a : 𝓞 K)‖ ≤ u a := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_mixedParityGaussian_majorant
    (heckeCoordinateParity 𝔪 ψ) hδ M
  let T : ℝ := δ / 2 * Real.exp (-M)^2
  have hT : 0 < T := mul_pos (half_pos hδ) (pow_pos (Real.exp_pos _) _)
  refine ⟨fun a => C * Real.exp (-(Real.pi * T) *
    ‖numberFieldTraceCoordinates (mixedEmbedding K ((a : 𝓞 K) : K))‖^2),
    (summable_integralIdeal_gaussian b hT).mul_left C, ?_⟩
  intro y hy t ht a
  rw [heckeThetaKernel, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_integralHeckeWeight_le_one 𝔪 ψ _)).trans
    (hbound y hy t ht _)

/-- The actual finite Fourier coefficients preserve a uniform summable dual majorant. -/
theorem exists_uniform_heckeDualThetaKernel_majorant {b : Ideal (𝓞 K)}
    (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ u : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) → ℝ,
      Summable u ∧ ∀ y : InfinitePlace K → ℝ, (∀ v, y v ≤ M) →
      ∀ t : ℝ, δ ≤ t → ∀ a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI),
        ‖finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) * heckeParityKernel 𝔪 ψ y t (a : K)‖ ≤ u a := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_mixedParityGaussian_majorant
    (heckeCoordinateParity 𝔪 ψ) hδ M
  let T : ℝ := δ / 2 * Real.exp (-M)^2
  have hT : 0 < T := mul_pos (half_pos hδ) (pow_pos (Real.exp_pos _) _)
  have hJ : ((𝔪.fin * b : Ideal (𝓞 K)) : FI) ≠ 0 := by
    rw [← coe_idealUnit (mul_ne_zero 𝔪.fin_ne_bot hb0)]
    exact (idealUnit (mul_ne_zero 𝔪.fin_ne_bot hb0)).ne_zero
  let I := FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)
  have hI : I ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ hJ
  have hs : Summable (fun a : I => Real.exp (-(Real.pi * T) *
      ‖numberFieldTraceCoordinates (mixedEmbedding K (a : K))‖^2)) := by
    have h := summable_fractionalIdeal_gaussian (Units.mk0 I hI) hT
    exact h
  refine ⟨fun a => (Ideal.absNorm 𝔪.fin : ℝ) * (C * Real.exp (-(Real.pi * T) *
    ‖numberFieldTraceCoordinates (mixedEmbedding K (a : K))‖^2)),
    (hs.mul_left C).mul_left (Ideal.absNorm 𝔪.fin : ℝ), ?_⟩
  intro y hy t ht a
  rw [norm_mul]
  exact mul_le_mul (norm_finiteHeckeFourierCoefficient_le 𝔪 hb ψ _)
    (hbound y hy t ht _) (norm_nonneg _) (Nat.cast_nonneg _)

private theorem profile_coord_le_of_norm_le {y : InfinitePlace K → ℝ} {M : ℝ}
    (hy : ‖y‖ ≤ M) (v : InfinitePlace K) : y v ≤ M :=
  (le_abs_self _).trans (((pi_norm_le_iff_of_nonneg (norm_nonneg y)).mp le_rfl v).trans hy)

private theorem profileBall_parameter_mem_nhds (p : (InfinitePlace K → ℝ) × ℝ)
    (hp : 0 < p.2) :
    Metric.closedBall 0 (‖p.1‖ + 1) ×ˢ Ici (p.2 / 2) ∈ 𝓝 p := by
  have hm : p ∈ Metric.ball 0 (‖p.1‖ + 1) ×ˢ Ioi (p.2 / 2) := by
    constructor
    · simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖p.1‖
    · change p.2 / 2 < p.2
      exact half_lt_self hp
  refine Filter.mem_of_superset ((Metric.isOpen_ball.prod isOpen_Ioi).mem_nhds hm) ?_
  intro q hq
  refine ⟨Metric.ball_subset_closedBall hq.1, ?_⟩
  change p.2 / 2 ≤ q.2
  exact (show p.2 / 2 < q.2 from hq.2).le

/-- The physical theta sum is jointly continuous for positive Gaussian parameters. -/
theorem continuousOn_heckeIdealTheta_joint (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K)) :
    ContinuousOn (fun p : (InfinitePlace K → ℝ) × ℝ => heckeIdealTheta 𝔪 ψ b p.1 p.2)
      {p | 0 < p.2} := by
  intro p hp
  let M : ℝ := ‖p.1‖ + 1
  obtain ⟨u, hu, hbound⟩ := exists_uniform_heckeThetaKernel_majorant 𝔪 ψ b (half_pos hp) M
  have hc : ContinuousOn (fun q : (InfinitePlace K → ℝ) × ℝ => heckeIdealTheta 𝔪 ψ b q.1 q.2)
      (Metric.closedBall 0 M ×ˢ Ici (p.2 / 2)) := by
    apply continuousOn_tsum
    · intro a
      exact (continuous_heckeThetaKernel_parameters 𝔪 ψ (a : 𝓞 K)).continuousOn
    · exact hu
    · intro a q hq
      have hnorm : ‖q.1‖ ≤ M := by simpa only [Metric.mem_closedBall, dist_zero_right] using hq.1
      exact hbound q.1 (profile_coord_le_of_norm_le hnorm) q.2 hq.2 a
  exact (hc.continuousAt (profileBall_parameter_mem_nhds p hp)).continuousWithinAt

/-- The finite-Fourier dual sum is jointly continuous for positive Gaussian parameters. -/
theorem continuousOn_heckeDualIdealTheta_joint {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) :
    ContinuousOn (fun p : (InfinitePlace K → ℝ) × ℝ => heckeDualIdealTheta 𝔪 hb ψ p.1 p.2)
      {p | 0 < p.2} := by
  intro p hp
  let M : ℝ := ‖p.1‖ + 1
  obtain ⟨u, hu, hbound⟩ := exists_uniform_heckeDualThetaKernel_majorant 𝔪 hb hb0 ψ
    (half_pos hp) M
  have hc : ContinuousOn (fun q : (InfinitePlace K → ℝ) × ℝ => heckeDualIdealTheta 𝔪 hb ψ q.1 q.2)
      (Metric.closedBall 0 M ×ˢ Ici (p.2 / 2)) := by
    apply continuousOn_tsum
    · intro a
      exact (continuous_const.mul
        (continuous_heckeParityKernel_parameters 𝔪 ψ (a : K))).continuousOn
    · exact hu
    · intro a q hq
      have hnorm : ‖q.1‖ ≤ M := by simpa only [Metric.mem_closedBall, dist_zero_right] using hq.1
      exact hbound q.1 (profile_coord_le_of_norm_le hnorm) q.2 hq.2 a
  exact (hc.continuousAt (profileBall_parameter_mem_nhds p hp)).continuousWithinAt

end GaloisForLFunctions.HeckeLFunctions
