import GaloisForLFunctions.RHTower.SteinhausFullGaussianCofactorMean
import GaloisForLFunctions.RHTower.SteinhausFullGaussianCofactorTail
import GaloisForLFunctions.RHTower.SteinhausFullGaussianPrefixStability
import GaloisForLFunctions.RHTower.SmoothAFEGaussianCofactorModes


open Filter Topology Finset
noncomputable section
namespace RHTower

/-- Complete Gaussian cofactor responses with each node's real scale removed. -/
def fullGaussianCofactorNodeVector {J : ℕ} (s : Fin J → ℂ) (R : ℝ)
    (ω : SteinhausModel.Omega) : Fin J → ℂ :=
  fun j => steinhausFullGaussianCofactor (s j) R ω * (R : ℂ) ^ (-s j)

/-- Normalize the common coherent twist and finite-prefix scalar. -/
def relativeFullGaussianCofactorMode {J : ℕ} (s : Fin J → ℂ) (t : ℝ) (A : ℂ)
    (R : ℝ) (ω : SteinhausModel.Omega) : Fin J → ℂ :=
  A⁻¹ • ((R : ℂ) ^ (-((t : ℂ) * Complex.I)) • fullGaussianCofactorNodeVector s R ω)

/-- A coherent extension approaches its Gaussian Mellin mode in the full finite node space. -/
theorem tendsto_relativeFullGaussianCofactorMode_extension
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (ω : SteinhausModel.Omega) (t : ℝ) :
    Tendsto (fun R : ℝ => relativeFullGaussianCofactorMode s t
      (finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi)))
      R (finitePrimeTwistExtension S ω t)) atTop
      (𝓝 (fun j => smoothAFEGaussianKernel (s j + (t : ℂ) * Complex.I))) := by
  let A := finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi))
  have hA : A ≠ 0 := finitePrimePhaseMean_ne_zero _ _
  apply tendsto_pi_nhds.mpr
  intro j
  have h := (tendsto_finitePrimeTwistExtension_gaussian_mean S ω t
    (s := s j) (hs j) (hs1 j)).const_mul A⁻¹
  have heq : A⁻¹ * (A * (Complex.exp ((s j + (t : ℂ) * Complex.I) ^ 2) /
      (s j + (t : ℂ) * Complex.I))) =
      smoothAFEGaussianKernel (s j + (t : ℂ) * Complex.I) := by
    simp only [smoothAFEGaussianKernel, ← mul_assoc, inv_mul_cancel₀ hA, one_mul]
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  change A⁻¹ * (_ * (R : ℂ) ^ (-(s j + (t : ℂ) * Complex.I))) =
    A⁻¹ * ((R : ℂ) ^ (-((t : ℂ) * Complex.I)) *
      (steinhausFullGaussianCofactor (s j) R (finitePrimeTwistExtension S ω t) *
        (R : ℂ) ^ (-s j)))
  change A⁻¹ * (steinhausFullGaussianCofactor (s j) R (finitePrimeTwistExtension S ω t) *
    (R : ℂ) ^ (-(s j + (t : ℂ) * Complex.I))) = _
  rw [show -(s j + (t : ℂ) * Complex.I) = -s j + -((t : ℂ) * Complex.I) by ring,
    Complex.cpow_add _ _ hR0]
  ring

/-- Finite phase agreement preserves normalized full Gaussian modes uniformly on a bounded
scale interval away from zero, including the original common twist and prefix scalar. -/
theorem exists_relativeFullGaussianCofactorMode_prefix_stability
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 ≤ (s j).re)
    (t : ℝ) {A : ℂ} (hA : A ≠ 0) (U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ (R : ℝ), 1 ≤ R → R ≤ U →
      ∀ ω ω' : SteinhausModel.Omega, (∀ p ≤ B, ω p = ω' p) →
        ‖relativeFullGaussianCofactorMode s t A R ω -
          relativeFullGaussianCofactorMode s t A R ω'‖ < ε := by
  classical
  have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hδ : 0 < ε * ‖A‖ := mul_pos hε hAnorm
  choose B hB using fun j => exists_fullGaussianCofactor_uniform_prefix_stability (s j) U hδ
  refine ⟨univ.sup B, fun R hR hRU ω ω' hphase => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have htwist : ‖(R : ℂ) ^ (-((t : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hR0]
    simp
  apply (pi_norm_lt_iff hε).mpr
  intro j
  have hd := (hB j).2 R hR0 hRU ω ω'
    (fun p hp => hphase p (hp.trans (le_sup (mem_univ j))))
  have heq : relativeFullGaussianCofactorMode s t A R ω j -
      relativeFullGaussianCofactorMode s t A R ω' j =
      A⁻¹ * ((R : ℂ) ^ (-((t : ℂ) * Complex.I)) *
        ((steinhausFullGaussianCofactor (s j) R ω - steinhausFullGaussianCofactor (s j) R ω') *
          (R : ℂ) ^ (-s j))) := by
    simp only [relativeFullGaussianCofactorMode, fullGaussianCofactorNodeVector,
      Pi.smul_apply, smul_eq_mul]
    ring
  change ‖relativeFullGaussianCofactorMode s t A R ω j -
    relativeFullGaussianCofactorMode s t A R ω' j‖ < ε
  rw [heq, norm_mul, norm_mul, norm_mul, norm_inv, htwist, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hR0, Complex.neg_re]
  calc
    _ ≤ ‖A‖⁻¹ * ‖steinhausFullGaussianCofactor (s j) R ω -
        steinhausFullGaussianCofactor (s j) R ω'‖ :=
      mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hR
          (neg_nonpos.mpr (hs j)))) (inv_nonneg.mpr hAnorm.le)
    _ < ‖A‖⁻¹ * (ε * ‖A‖) := mul_lt_mul_of_pos_left hd (inv_pos.mpr hAnorm)
    _ = ε := by field_simp [hAnorm.ne']

/-- Any prescribed coherent Gaussian mode occurs beyond an arbitrary scale, preserving a
finite phase assignment and with arbitrarily large mean-weighted block length. -/
theorem exists_fullGaussianCofactor_mode_block
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (ω : SteinhausModel.Omega) (t : ℝ) (B : ℕ) (K ε : ℝ) (hε : 0 < ε) :
    ∃ ω' : SteinhausModel.Omega, (∀ p ∈ S, ω' p = ω p) ∧
      ∃ M : ℕ, B ≤ M ∧ 1 ≤ M ∧ ∃ A : ℂ, A ≠ 0 ∧ K ≤ (M : ℝ) * ‖A‖ ^ 2 ∧
        ∀ R : ℝ, (M : ℝ) ≤ R →
          ‖relativeFullGaussianCofactorMode s t A R ω' -
            (fun j => smoothAFEGaussianKernel (s j + (t : ℂ) * Complex.I))‖ < ε := by
  let A := finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi))
  have hA : A ≠ 0 := finitePrimePhaseMean_ne_zero _ _
  have hApos : 0 < ‖A‖ ^ 2 := pow_pos (norm_pos_iff.mpr hA) 2
  have hlim := tendsto_relativeFullGaussianCofactorMode_extension s hs hs1 S ω t
  have hev := hlim.eventually (Metric.ball_mem_nhds _ hε)
  simp only [dist_eq_norm] at hev
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hev
  obtain ⟨C, hC⟩ := exists_nat_gt (max R₀ (K / ‖A‖ ^ 2))
  let M := B + C + 1
  have hCM : (C : ℝ) ≤ M := by exact_mod_cast (show C ≤ M by omega)
  have hRC : R₀ < (C : ℝ) := lt_of_le_of_lt (le_max_left _ _) hC
  refine ⟨finitePrimeTwistExtension S ω t,
    fun _ hp => finitePrimeTwistExtension_eq_on_prefix S ω t hp,
    M, by omega, by omega, A, hA, ?_, ?_⟩
  · have hc : K < (C : ℝ) * ‖A‖ ^ 2 :=
      (div_lt_iff₀ hApos).mp (lt_of_le_of_lt (le_max_right _ _) hC)
    exact hc.le.trans (mul_le_mul_of_nonneg_right hCM hApos.le)
  · intro R hR
    exact hR₀ R (hRC.le.trans (hCM.trans hR))

end RHTower
