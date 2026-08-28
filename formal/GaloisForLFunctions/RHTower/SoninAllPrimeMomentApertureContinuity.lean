import GaloisForLFunctions.RHTower.SoninResidualApertureHilbertSchmidtContinuity
import GaloisForLFunctions.RHTower.SoninAllPrimeMomentWeldApertureCeiling
import GaloisForLFunctions.HTGeometry.HilbertSchmidtContinuity
import GaloisForLFunctions.HTGeometry.UniformTsumLimit

/-!
# Aperture continuity and exact landing for the all-prime Sonin moment weld

Strong continuity of aperture cutoffs and Hilbert--Schmidt finite-rank density give HS continuity
of every local residual.  A compact-window Weierstrass bound then upgrades this to HS continuity
of the assembled all-prime residual kernel.  The induced positive energy and every trace moment
are continuous.  Consequently, compactness of any asymptotic F2 weld forces one exact positive
finite aperture realizing all target moments.
-/

noncomputable section

open Filter Topology Set
open scoped BigOperators InnerProductSpace

namespace RHTower

private def soninAllPrimeBlockDiagonalEquivDiff :
    (Nat.Primes × ℕ) × (SoninHilbertIndex × SoninHilbertIndex) ≃
      soninAllPrimeBlockDiagonalSupport where
  toFun pji := ⟨((pji.1, pji.2.2), (pji.1, pji.2.1)), rfl⟩
  invFun z := (z.1.1.1, (z.1.2.2, z.1.1.2))
  left_inv pji := by
    rcases pji with ⟨pk, j, i⟩
    rfl
  right_inv z := by
    apply Subtype.ext
    rcases z with ⟨⟨⟨pk, i⟩, ⟨qk, j⟩⟩, h⟩
    change pk = qk at h
    subst qk
    rfl

/-- Exact prime-block energy disintegration for a difference of assembled all-prime residual
kernels. -/
theorem hsNormSq_soninAllPrimeResidualKernel_sub_eq_tsum_block
    (b a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    HilbertSchmidt.hsNormSq
        (soninAllPrimeResidualKernel b - soninAllPrimeResidualKernel a) =
      ∑' pk : Nat.Primes × ℕ, ContinuousLinearMap.hsNormSq
        (centralSoninWeightedPrimePowerResidual b pk -
          centralSoninWeightedPrimePowerResidual a pk) := by
  let K := soninAllPrimeResidualKernel b - soninAllPrimeResidualKernel a
  have hK : HilbertSchmidt.IsHS K := HilbertSchmidt.isHS_sub
    (soninAllPrimeResidualKernel_isHS b hb) (soninAllPrimeResidualKernel_isHS a ha)
  let energy : SoninAllPrimeIndex × SoninAllPrimeIndex → ℝ := fun z => ‖K z‖ ^ 2
  have henergy : Summable energy := by
    simpa only [energy, HilbertSchmidt.IsHS] using hK
  have hoff : ∀ z, z ∉ soninAllPrimeBlockDiagonalSupport → energy z = 0 := by
    intro z hz
    have hne : z.1.1 ≠ z.2.1 := by
      simpa [soninAllPrimeBlockDiagonalSupport] using hz
    simp [energy, K, soninAllPrimeResidualKernel, hne]
  have hsub : Summable (energy ∘ Subtype.val :
      soninAllPrimeBlockDiagonalSupport → ℝ) :=
    henergy.comp_injective Subtype.val_injective
  have hrestrict : (∑' z, energy z) =
      ∑' z : soninAllPrimeBlockDiagonalSupport, energy z := by
    rw [tsum_subtype (s := soninAllPrimeBlockDiagonalSupport) energy]
    apply tsum_congr
    intro z
    by_cases hz : z ∈ soninAllPrimeBlockDiagonalSupport
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hoff z hz]
  let F : (Nat.Primes × ℕ) × (SoninHilbertIndex × SoninHilbertIndex) → ℝ :=
    fun pji => ‖inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 pji.2.2)
      ((centralSoninWeightedPrimePowerResidual b pji.1 -
          centralSoninWeightedPrimePowerResidual a pji.1)
        (ContinuousLinearMap.hsBasis ℂ SoninL2 pji.2.1))‖ ^ 2
  have hF : Summable F := by
    have hequiv : Summable (fun pji =>
        energy (soninAllPrimeBlockDiagonalEquivDiff pji)) :=
      (soninAllPrimeBlockDiagonalEquivDiff.summable_iff).2 hsub
    refine hequiv.congr fun pji => ?_
    simp [F, energy, K, soninAllPrimeBlockDiagonalEquivDiff,
      soninAllPrimeResidualKernel, sub_apply, inner_sub_right]
  rw [HilbertSchmidt.hsNormSq]
  change (∑' z, energy z) = _
  rw [hrestrict]
  calc
    (∑' z : soninAllPrimeBlockDiagonalSupport, energy z) =
        ∑' pji : (Nat.Primes × ℕ) ×
          (SoninHilbertIndex × SoninHilbertIndex), F pji := by
      calc
        _ = ∑' pji : (Nat.Primes × ℕ) ×
            (SoninHilbertIndex × SoninHilbertIndex),
            energy (soninAllPrimeBlockDiagonalEquivDiff pji) :=
          (soninAllPrimeBlockDiagonalEquivDiff.tsum_eq (fun z => energy z)).symm
        _ = ∑' pji : (Nat.Primes × ℕ) ×
            (SoninHilbertIndex × SoninHilbertIndex), F pji := by
          apply tsum_congr
          intro pji
          simp [F, energy, K, soninAllPrimeBlockDiagonalEquivDiff,
            soninAllPrimeResidualKernel, sub_apply, inner_sub_right]
    _ = ∑' pk : Nat.Primes × ℕ,
        ∑' ji : SoninHilbertIndex × SoninHilbertIndex, F (pk, ji) := hF.tsum_prod
    _ = ∑' pk : Nat.Primes × ℕ, ContinuousLinearMap.hsNormSq
        (centralSoninWeightedPrimePowerResidual b pk -
          centralSoninWeightedPrimePowerResidual a pk) := by
      apply tsum_congr
      intro pk
      let T := centralSoninWeightedPrimePowerResidual b pk -
        centralSoninWeightedPrimePowerResidual a pk
      have hT : ContinuousLinearMap.IsHilbertSchmidt T :=
        (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt b hb pk).sub
          (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha pk)
      rw [ContinuousLinearMap.hsNormSq_eq hT
        (ContinuousLinearMap.hsBasis ℂ SoninL2)]
      rw [show (∑' ji : SoninHilbertIndex × SoninHilbertIndex, F (pk, ji)) =
          ∑' j : SoninHilbertIndex, ∑' i : SoninHilbertIndex, F (pk, (j, i)) by
        have hFpk : Summable (fun ji : SoninHilbertIndex × SoninHilbertIndex =>
            F (pk, ji)) := hF.comp_injective (fun _ _ h => (Prod.mk.inj h).2)
        exact hFpk.tsum_prod]
      apply tsum_congr
      intro j
      simpa [F, T] using tsum_sq_norm_inner_hilbertBasis
        (ContinuousLinearMap.hsBasis ℂ SoninL2)
        (T (ContinuousLinearMap.hsBasis ℂ SoninL2 j))

/-- The total prime-block energy of the residual difference tends to zero at every positive
aperture.  Square-summability of the logarithmic Euler coefficients supplies the compact-window
dominating series. -/
theorem tendsto_tsum_hsNormSq_centralSoninWeightedPrimePowerResidual_sub
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun b : ℝ => ∑' pk : Nat.Primes × ℕ,
      ((ContinuousLinearMap.hsNormSq
        (centralSoninWeightedPrimePowerResidual b pk -
          centralSoninWeightedPrimePowerResidual a pk) : ℝ) : ℂ))
      (𝓝 a) (𝓝 0) := by
  let B : ℝ := a + 1
  let s : Set ℝ := Set.Ioo 0 B
  let majorant : (Nat.Primes × ℕ) → ℝ := fun pk =>
    (512 * B ^ 2) * ‖soninLogPrimePowerCoefficient pk‖ ^ 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hs : s ∈ 𝓝 a := by
    exact Ioo_mem_nhds ha (by dsimp [B]; linarith)
  have hmajorant : Summable majorant := by
    exact summable_norm_soninLogPrimePowerCoefficient_sq.mul_left (512 * B ^ 2)
  have hbound : ∀ pk : Nat.Primes × ℕ, ∀ b ∈ s,
      ‖((ContinuousLinearMap.hsNormSq
        (centralSoninWeightedPrimePowerResidual b pk -
          centralSoninWeightedPrimePowerResidual a pk) : ℝ) : ℂ)‖ ≤ majorant pk := by
    intro pk b hb
    have hbpos : 0 < b := hb.1
    have hbB : b < B := hb.2
    have hbSq : b ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ hbpos.le hB.le).2 hbB.le
    have haB : a ≤ B := by dsimp [B]; linarith
    have haSq : a ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ ha.le hB.le).2 haB
    have hWb := centralSoninWeightedPrimePowerResidual_hsNormSq_le_128_mul_sq
      b hbpos pk
    have hWa := centralSoninWeightedPrimePowerResidual_hsNormSq_le_128_mul_sq
      a ha pk
    have hdiff := ContinuousLinearMap.hsNormSq_sub_le
      (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt b hbpos pk)
      (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha pk)
    have hc : 0 ≤ ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := sq_nonneg _
    have hWb' : ContinuousLinearMap.hsNormSq
        (centralSoninWeightedPrimePowerResidual b pk) ≤
        (128 * B ^ 2) * ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := by
      calc
        _ ≤ (128 * b ^ 2) * ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := hWb
        _ ≤ (128 * B ^ 2) * ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := by
          gcongr
    have hWa' : ContinuousLinearMap.hsNormSq
        (centralSoninWeightedPrimePowerResidual a pk) ≤
        (128 * B ^ 2) * ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := by
      calc
        _ ≤ (128 * a ^ 2) * ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := hWa
        _ ≤ (128 * B ^ 2) * ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := by
          gcongr
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ContinuousLinearMap.hsNormSq_nonneg _)]
    dsimp [majorant]
    linarith
  have hlim : ∀ pk : Nat.Primes × ℕ,
      Tendsto (fun b : ℝ =>
        ((ContinuousLinearMap.hsNormSq
          (centralSoninWeightedPrimePowerResidual b pk -
            centralSoninWeightedPrimePowerResidual a pk) : ℝ) : ℂ))
        (𝓝 a) (𝓝 0) := by
    intro pk
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_hsNormSq_centralSoninWeightedPrimePowerResidual_sub ha pk)
  simpa using HTGeometry.tendsto_tsum_of_tendsto_of_norm_bounded_on
    (l := 𝓝 a) hs hmajorant hbound
    (show Summable (fun _ : Nat.Primes × ℕ => (0 : ℂ)) from summable_zero) hlim

theorem summable_hsNormSq_centralSoninWeightedPrimePowerResidual_sub
    (b a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    Summable (fun pk : Nat.Primes × ℕ => ContinuousLinearMap.hsNormSq
      (centralSoninWeightedPrimePowerResidual b pk -
        centralSoninWeightedPrimePowerResidual a pk)) := by
  let majorant : (Nat.Primes × ℕ) → ℝ := fun pk =>
    (256 * (b ^ 2 + a ^ 2)) * ‖soninLogPrimePowerCoefficient pk‖ ^ 2
  have hle : ∀ pk : Nat.Primes × ℕ,
      ContinuousLinearMap.hsNormSq
        (centralSoninWeightedPrimePowerResidual b pk -
          centralSoninWeightedPrimePowerResidual a pk) ≤ majorant pk := by
    intro pk
    have hsub := ContinuousLinearMap.hsNormSq_sub_le
      (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt b hb pk)
      (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha pk)
    have hWb := centralSoninWeightedPrimePowerResidual_hsNormSq_le_128_mul_sq b hb pk
    have hWa := centralSoninWeightedPrimePowerResidual_hsNormSq_le_128_mul_sq a ha pk
    dsimp [majorant]
    linarith
  have hmajorant : Summable majorant := by
    exact summable_norm_soninLogPrimePowerCoefficient_sq.mul_left
      (256 * (b ^ 2 + a ^ 2))
  exact Summable.of_nonneg_of_le
    (fun pk => ContinuousLinearMap.hsNormSq_nonneg _) hle hmajorant

/-- The assembled all-prime residual kernel is Hilbert--Schmidt continuous at every positive
aperture. -/
theorem tendsto_hsNormSq_soninAllPrimeResidualKernel_sub
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun b : ℝ => HilbertSchmidt.hsNormSq
      (soninAllPrimeResidualKernel b - soninAllPrimeResidualKernel a))
      (𝓝 a) (𝓝 0) := by
  have hcomplex :=
    tendsto_tsum_hsNormSq_centralSoninWeightedPrimePowerResidual_sub ha
  have hreal : Tendsto (fun b : ℝ =>
      (∑' pk : Nat.Primes × ℕ,
        ((ContinuousLinearMap.hsNormSq
          (centralSoninWeightedPrimePowerResidual b pk -
            centralSoninWeightedPrimePowerResidual a pk) : ℝ) : ℂ)).re)
      (𝓝 a) (𝓝 0) := by
    simpa [Function.comp_def] using
      Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  refine hreal.congr' ?_
  filter_upwards [Ioi_mem_nhds ha] with b hb
  rw [hsNormSq_soninAllPrimeResidualKernel_sub_eq_tsum_block b a hb ha]
  rw [← Complex.ofReal_tsum]
  simp

/-- All intrinsic trace moments of the positive all-prime residual energy are continuous along
positive aperture sequences. -/
theorem tendsto_soninAllPrimeEnergyMoment_of_tendsto
    {u : ℕ → ℝ} {a : ℝ} (huPos : ∀ n, 0 < u n) (ha : 0 < a)
    (hu : Tendsto u atTop (𝓝 a)) (r : ℕ) :
    Tendsto (fun n => soninAllPrimeEnergyMoment (u n) r) atTop
      (𝓝 (soninAllPrimeEnergyMoment a r)) := by
  let Kn : ℕ → SoninAllPrimeIndex × SoninAllPrimeIndex → ℂ :=
    fun n => soninAllPrimeResidualKernel (u n)
  let K : SoninAllPrimeIndex × SoninAllPrimeIndex → ℂ :=
    soninAllPrimeResidualKernel a
  have hKn : ∀ n, HilbertSchmidt.IsHS (Kn n) := fun n => by
    simpa [Kn] using soninAllPrimeResidualKernel_isHS (u n) (huPos n)
  have hK : HilbertSchmidt.IsHS K := by
    simpa [K] using soninAllPrimeResidualKernel_isHS a ha
  have hdiffSq : Tendsto (fun n => HilbertSchmidt.hsNormSq (Kn n - K))
      atTop (𝓝 0) := by
    simpa [Kn, K, Function.comp_def] using
      (tendsto_hsNormSq_soninAllPrimeResidualKernel_sub ha).comp hu
  have hdiffNorm : Tendsto (fun n => HilbertSchmidt.hsNorm (Kn n - K))
      atTop (𝓝 0) := by
    simpa [HilbertSchmidt.hsNorm, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hdiffSq
  have hnorm : Tendsto (fun n => HilbertSchmidt.hsNorm (Kn n)) atTop
      (𝓝 (HilbertSchmidt.hsNorm K)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hdiffNorm
    filter_upwards with n
    have hKnSplit : Kn n = (Kn n - K) + K := by
      funext z
      simp
    have hKSplit : K = (K - Kn n) + Kn n := by
      funext z
      simp
    have hupper : HilbertSchmidt.hsNorm (Kn n) ≤
        HilbertSchmidt.hsNorm (Kn n - K) + HilbertSchmidt.hsNorm K := by
      calc
        HilbertSchmidt.hsNorm (Kn n) =
            HilbertSchmidt.hsNorm ((Kn n - K) + K) := congrArg _ hKnSplit
        _ ≤ HilbertSchmidt.hsNorm (Kn n - K) + HilbertSchmidt.hsNorm K :=
          HilbertSchmidt.hsNorm_add_le
            (HilbertSchmidt.isHS_sub (hKn n) hK) hK
    have hlower : HilbertSchmidt.hsNorm K ≤
        HilbertSchmidt.hsNorm (Kn n - K) + HilbertSchmidt.hsNorm (Kn n) := by
      have h := HilbertSchmidt.hsNorm_add_le
        (HilbertSchmidt.isHS_sub hK (hKn n)) (hKn n)
      have hneg : K - Kn n = -(Kn n - K) := by
        funext z
        simp
      calc
        HilbertSchmidt.hsNorm K =
            HilbertSchmidt.hsNorm ((K - Kn n) + Kn n) := congrArg _ hKSplit
        _ ≤ HilbertSchmidt.hsNorm (K - Kn n) + HilbertSchmidt.hsNorm (Kn n) := h
        _ = HilbertSchmidt.hsNorm (Kn n - K) + HilbertSchmidt.hsNorm (Kn n) := by
          rw [hneg, HilbertSchmidt.hsNorm_neg]
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let M : ℝ := HilbertSchmidt.hsNorm K + 1
  have hM : 0 < M := by dsimp [M]; linarith [HilbertSchmidt.hsNorm_nonneg K]
  have hKnBound : ∀ᶠ n in atTop, HilbertSchmidt.hsNorm (Kn n) ≤ M := by
    exact (hnorm.eventually (Iio_mem_nhds (show HilbertSchmidt.hsNorm K < M by
      dsimp [M]; linarith))).mono fun n hn => hn.le
  let Tn : ℕ → SoninAllPrimeIndex × SoninAllPrimeIndex → ℂ := fun n =>
    HilbertSchmidt.hsComp (HilbertSchmidt.hsAdjoint (Kn n)) (Kn n)
  let T : SoninAllPrimeIndex × SoninAllPrimeIndex → ℂ :=
    HilbertSchmidt.hsComp (HilbertSchmidt.hsAdjoint K) K
  have hTn : ∀ n, HilbertSchmidt.IsHS (Tn n) := fun n =>
    HilbertSchmidt.isHS_hsComp (HilbertSchmidt.isHS_hsAdjoint (hKn n)) (hKn n)
  have hT : HilbertSchmidt.IsHS T :=
    HilbertSchmidt.isHS_hsComp (HilbertSchmidt.isHS_hsAdjoint hK) hK
  have hTdiffNorm : Tendsto (fun n => HilbertSchmidt.hsNorm (Tn n - T))
      atTop (𝓝 0) := by
    have hbound : ∀ᶠ n in atTop, HilbertSchmidt.hsNorm (Tn n - T) ≤
        (M + HilbertSchmidt.hsNorm K) * HilbertSchmidt.hsNorm (Kn n - K) := by
      filter_upwards [hKnBound] with n hn
      have hsplit : Tn n - T =
          HilbertSchmidt.hsComp
              (HilbertSchmidt.hsAdjoint (Kn n) - HilbertSchmidt.hsAdjoint K) (Kn n) +
            HilbertSchmidt.hsComp (HilbertSchmidt.hsAdjoint K) (Kn n - K) := by
        rw [HilbertSchmidt.hsComp_sub_left
          (HilbertSchmidt.isHS_hsAdjoint (hKn n))
          (HilbertSchmidt.isHS_hsAdjoint hK) (hKn n),
          HilbertSchmidt.hsComp_sub_right
            (HilbertSchmidt.isHS_hsAdjoint hK) (hKn n) hK]
        funext z
        simp only [Tn, T, Pi.add_apply, Pi.sub_apply]
        ring
      have hadj : HilbertSchmidt.hsAdjoint (Kn n) - HilbertSchmidt.hsAdjoint K =
          HilbertSchmidt.hsAdjoint (Kn n - K) := by
        funext z
        simp [HilbertSchmidt.hsAdjoint]
      rw [hsplit]
      calc
        HilbertSchmidt.hsNorm
            (HilbertSchmidt.hsComp
                (HilbertSchmidt.hsAdjoint (Kn n) - HilbertSchmidt.hsAdjoint K) (Kn n) +
              HilbertSchmidt.hsComp (HilbertSchmidt.hsAdjoint K) (Kn n - K)) ≤
            HilbertSchmidt.hsNorm (HilbertSchmidt.hsComp
              (HilbertSchmidt.hsAdjoint (Kn n) - HilbertSchmidt.hsAdjoint K) (Kn n)) +
            HilbertSchmidt.hsNorm (HilbertSchmidt.hsComp
              (HilbertSchmidt.hsAdjoint K) (Kn n - K)) :=
          HilbertSchmidt.hsNorm_add_le
            (HilbertSchmidt.isHS_hsComp
              (HilbertSchmidt.isHS_sub
                (HilbertSchmidt.isHS_hsAdjoint (hKn n))
                (HilbertSchmidt.isHS_hsAdjoint hK)) (hKn n))
            (HilbertSchmidt.isHS_hsComp (HilbertSchmidt.isHS_hsAdjoint hK)
              (HilbertSchmidt.isHS_sub (hKn n) hK))
        _ ≤ HilbertSchmidt.hsNorm
              (HilbertSchmidt.hsAdjoint (Kn n) - HilbertSchmidt.hsAdjoint K) *
                HilbertSchmidt.hsNorm (Kn n) +
            HilbertSchmidt.hsNorm (HilbertSchmidt.hsAdjoint K) *
              HilbertSchmidt.hsNorm (Kn n - K) :=
          add_le_add
            (HilbertSchmidt.hsNorm_hsComp_le
              (HilbertSchmidt.isHS_sub
                (HilbertSchmidt.isHS_hsAdjoint (hKn n))
                (HilbertSchmidt.isHS_hsAdjoint hK)) (hKn n))
            (HilbertSchmidt.hsNorm_hsComp_le (HilbertSchmidt.isHS_hsAdjoint hK)
              (HilbertSchmidt.isHS_sub (hKn n) hK))
        _ ≤ M * HilbertSchmidt.hsNorm (Kn n - K) +
            HilbertSchmidt.hsNorm K * HilbertSchmidt.hsNorm (Kn n - K) := by
          rw [hadj, HilbertSchmidt.hsNorm_hsAdjoint,
            HilbertSchmidt.hsNorm_hsAdjoint]
          have hfirst :
              HilbertSchmidt.hsNorm (Kn n - K) * HilbertSchmidt.hsNorm (Kn n) ≤
                M * HilbertSchmidt.hsNorm (Kn n - K) := by
            calc
            HilbertSchmidt.hsNorm (Kn n - K) * HilbertSchmidt.hsNorm (Kn n) ≤
                HilbertSchmidt.hsNorm (Kn n - K) * M :=
              mul_le_mul_of_nonneg_left hn (HilbertSchmidt.hsNorm_nonneg _)
            _ = M * HilbertSchmidt.hsNorm (Kn n - K) := mul_comm _ _
          linarith
        _ = (M + HilbertSchmidt.hsNorm K) *
            HilbertSchmidt.hsNorm (Kn n - K) := by ring
    refine squeeze_zero' (Eventually.of_forall fun n => HilbertSchmidt.hsNorm_nonneg _)
      hbound ?_
    simpa using hdiffNorm.const_mul (M + HilbertSchmidt.hsNorm K)
  by_cases hr : r = 0
  · subst r
    have henergy : Tendsto (fun n => HilbertSchmidt.hsNormSq (Kn n)) atTop
        (𝓝 (HilbertSchmidt.hsNormSq K)) := by
      have hsq := hnorm.pow 2
      convert hsq using 1
      · funext n
        rw [HilbertSchmidt.hsNorm, Real.sq_sqrt (HilbertSchmidt.hsNormSq_nonneg _)]
      · rw [HilbertSchmidt.hsNorm, Real.sq_sqrt (HilbertSchmidt.hsNormSq_nonneg _)]
    have hcast := (Complex.continuous_ofReal.tendsto (HilbertSchmidt.hsNormSq K)).comp henergy
    convert hcast using 1
    · funext n
      rw [soninAllPrimeEnergyMoment, HilbertSchmidt.hsPow,
        trace_soninAllPrimeResidualEnergyKernel (u n) (huPos n)]
      rfl
    · rw [soninAllPrimeEnergyMoment, HilbertSchmidt.hsPow,
        trace_soninAllPrimeResidualEnergyKernel a ha]
  · have hrform : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hr)
    let MT : ℝ := M ^ 2
    have hMT : 0 ≤ MT := sq_nonneg M
    have hTBound : HilbertSchmidt.hsNorm T ≤ MT := by
      calc
        HilbertSchmidt.hsNorm T ≤ HilbertSchmidt.hsNorm (HilbertSchmidt.hsAdjoint K) *
            HilbertSchmidt.hsNorm K :=
          HilbertSchmidt.hsNorm_hsComp_le (HilbertSchmidt.isHS_hsAdjoint hK) hK
        _ = HilbertSchmidt.hsNorm K ^ 2 := by
          rw [HilbertSchmidt.hsNorm_hsAdjoint]
          ring
        _ ≤ M ^ 2 := by
          exact (sq_le_sq₀ (HilbertSchmidt.hsNorm_nonneg K) hM.le).2
            (by dsimp [M]; linarith)
    have hTnBound : ∀ᶠ n in atTop, HilbertSchmidt.hsNorm (Tn n) ≤ MT := by
      filter_upwards [hKnBound] with n hn
      calc
        HilbertSchmidt.hsNorm (Tn n) ≤
            HilbertSchmidt.hsNorm (HilbertSchmidt.hsAdjoint (Kn n)) *
              HilbertSchmidt.hsNorm (Kn n) :=
          HilbertSchmidt.hsNorm_hsComp_le
            (HilbertSchmidt.isHS_hsAdjoint (hKn n)) (hKn n)
        _ = HilbertSchmidt.hsNorm (Kn n) ^ 2 := by
          rw [HilbertSchmidt.hsNorm_hsAdjoint]
          ring
        _ ≤ M ^ 2 := (sq_le_sq₀ (HilbertSchmidt.hsNorm_nonneg _) hM.le).2 hn
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero'
      (g := fun n => ((r + 1 : ℝ) * MT ^ r) * HilbertSchmidt.hsNorm (Tn n - T))
      (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
    · filter_upwards [hTnBound] with n hn
      have hcoef : ((r - 1 : ℕ) : ℝ) + 2 = (r : ℝ) + 1 := by
        norm_cast
        omega
      simpa [soninAllPrimeEnergyMoment, soninAllPrimeResidualEnergyKernel,
        Tn, T, Kn, K, hrform, hcoef] using
        HilbertSchmidt.hsTrace_hsPow_sub_norm_le (hTn n) hT hn hTBound (r - 1)
    · simpa using hTdiffNorm.const_mul ((r + 1 : ℝ) * MT ^ r)

/-- Every asymptotic single-section moment weld lands at one exact positive aperture. -/
theorem soninPrimeArchSingleMomentCoupling_exists_exact_positive_aperture
    {aperture : ℕ → ℝ} (h : SoninPrimeArchSingleMomentCoupling aperture) :
    ∃ aStar : ℝ, 0 < aStar ∧ ∀ r : ℕ,
      soninAllPrimeEnergyMoment aStar r =
        (((normalizedPrimeArchMoment r : ℝ) : ℂ)) := by
  obtain ⟨aStar, haStar, φ, hφ, hlim⟩ :=
    soninPrimeArchSingleMomentCoupling_exists_positive_aperture_cluster h
  refine ⟨aStar, haStar, fun r => ?_⟩
  have hsource : Tendsto
      (fun n => soninAllPrimeEnergyMoment ((aperture ∘ φ) n) r) atTop
      (𝓝 (soninAllPrimeEnergyMoment aStar r)) :=
    tendsto_soninAllPrimeEnergyMoment_of_tendsto
      (fun n => h.1 (φ n)) haStar hlim r
  have htarget : Tendsto
      (fun n => soninAllPrimeEnergyMoment ((aperture ∘ φ) n) r) atTop
      (𝓝 (((normalizedPrimeArchMoment r : ℝ) : ℂ))) := by
    simpa [Function.comp_def] using (h.2 r).comp hφ.tendsto_atTop
  exact tendsto_nhds_unique hsource htarget

/-- Compactness plus aperture continuity upgrades the asymptotic F2 weld to an exact equality at
one positive finite aperture. -/
theorem soninAllPrimeExactTraceMomentWeld_iff_exists_exact_positive_aperture :
    SoninAllPrimeExactTraceMomentWeld ↔
      ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ,
        soninAllPrimeEnergyMoment a r =
          (((normalizedPrimeArchMoment r : ℝ) : ℂ)) := by
  constructor
  · rw [soninAllPrimeExactTraceMomentWeld_iff_singleMomentCoupling]
    rintro ⟨aperture, h⟩
    exact soninPrimeArchSingleMomentCoupling_exists_exact_positive_aperture h
  · rintro ⟨a, ha, hexact⟩
    refine ⟨fun _ : ℕ => a, fun _ => ha, fun r => ?_⟩
    simp [hexact r]

/-- Exact positive-aperture all-prime moment matching is sufficient for RH. -/
theorem riemannHypothesis_of_soninAllPrimeExactPositiveApertureMomentWeld
    (h : ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ,
      soninAllPrimeEnergyMoment a r =
        (((normalizedPrimeArchMoment r : ℝ) : ℂ))) :
    RiemannHypothesis := by
  apply soninTargetFreePositiveAllPrimeOperator_and_exactTraceMomentWeldFrontier.2
  exact soninAllPrimeExactTraceMomentWeld_iff_exists_exact_positive_aperture.2 h

end RHTower
