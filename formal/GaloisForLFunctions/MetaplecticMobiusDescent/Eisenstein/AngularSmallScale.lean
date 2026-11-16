import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularKernelSeminorms
import GaloisForLFunctions.MetaplecticMobiusDescent.Mellin.UniformPolynomialKernels
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.TerminalWidths

/-!
# Small-scale angular kernel separation

The common pole-free Mellin strip gives a factor `min 1 R^(1/4)` in each reflected
angular kernel. Compact logarithmic localization separates the remaining kernel into
Fourier phases with uniform weighted integral bounds, controlled by source seminorms.
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped ContDiff ComplexConjugate Classical Topology FourierTransform SchwartzMap BigOperators
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
open CompletedHeight SchwartzPlanePoisson LocalLogFourier CanonicalRowCompletion
namespace InverseKernelSourceUniform
noncomputable section

theorem angularPaperKernel_window_source_bound (ℓ : ℕ) (a b : ℝ) (ha : 0 < a) (K : ℕ) (L : ℝ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ R : ℝ, 0 < R → ∀ j ≤ K, ∀ s : ℝ, |s| ≤ L →
      ‖eulerDeriv (angularPaperKernel ℓ V) j (R * Real.exp s)‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * smallScalar R := by
  choose orders c hc hb using fun j : Fin (K+1) =>
    angularPaperKernel_euler_source_power_decay ℓ a b ha 0 j.val
  let S := Finset.univ.biUnion orders
  let D := (∑ j : Fin (K+1), c j) + 1
  let E := (Real.exp L) ^ (1/4 : ℝ)
  have hD : 0 < D := by
    have hh := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin (K+1)))) => (hc j).le)
    dsimp only [D]
    linarith
  have hE : 0 < E := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hcD (j : Fin (K+1)) : c j ≤ D := by
    have hh := Finset.single_le_sum
      (fun q (_ : q ∈ (Finset.univ : Finset (Fin (K+1)))) => (hc q).le) (Finset.mem_univ j)
    dsimp only [D]
    linarith
  refine ⟨S, D*(1+E), by positivity, ?_⟩
  intro V hV R hR j hj s hs
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let q : Fin (K+1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
  have hsource : c q * (orders q).sup (schwartzSeminormFamily ℝ ℝ ℂ) V ≤ D*Q := by
    have hsub : orders q ⊆ S := Finset.subset_biUnion_of_mem orders (Finset.mem_univ q)
    exact mul_le_mul (hcD q) (Seminorm.le_def.mp (Finset.sup_mono hsub) V)
      (by positivity) hD.le
  have hsmall := (hb q V hV (R*Real.exp s) (mul_pos hR (Real.exp_pos _))).1
  have hlarge := (hb q V hV (R*Real.exp s) (mul_pos hR (Real.exp_pos _))).2
  have hsmall' : ‖eulerDeriv (angularPaperKernel ℓ V) j (R*Real.exp s)‖ ≤
      D*(1+E)*Q * R^(1/4 : ℝ) := by
    have he : (Real.exp s)^(1/4 : ℝ) ≤ E :=
      Real.rpow_le_rpow (by positivity) (Real.exp_le_exp.mpr ((le_abs_self s).trans hs)) (by norm_num)
    rw [Real.mul_rpow hR.le (Real.exp_pos _).le] at hsmall
    calc
      _ ≤ (c q * (orders q).sup (schwartzSeminormFamily ℝ ℝ ℂ) V) *
          (R^(1/4 : ℝ) * (Real.exp s)^(1/4 : ℝ)) := hsmall
      _ ≤ (D*Q) * (R^(1/4 : ℝ) * E) := mul_le_mul hsource
          (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hR.le _)) (by positivity) (by positivity)
      _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg hD.le hQ) (Real.rpow_nonneg hR.le (1/4 : ℝ))]
  have hlarge' : ‖eulerDeriv (angularPaperKernel ℓ V) j (R*Real.exp s)‖ ≤ D*(1+E)*Q := by
    have hh : ‖eulerDeriv (angularPaperKernel ℓ V) j (R*Real.exp s)‖ ≤ D*Q := by
      apply (le_trans ?_ hsource)
      simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] using hlarge
    exact hh.trans (by nlinarith only [mul_nonneg (mul_nonneg hD.le hE.le) hQ])
  change _ ≤ D*(1+E)*Q * min 1 (R^(1/4 : ℝ))
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ D*(1+E)*Q), mul_one]
  exact le_min hlarge' hsmall'

/-- Fixed localization preserves the small-scale gain in every Fourier moment. -/
theorem angular_localized_fourier_source_bound (ℓ : ℕ) (a b : ℝ) (ha : 0 < a)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ)
    (hχs : Function.support χ ⊆ Icc (-M) M) (J : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Icc a b →
      ∀ R : ℝ, 0 < R → ∀ t : ℝ,
        (1 + |t|) ^ J * ‖𝓕 (fun u => χ u * angularPaperKernel ℓ V (R * Real.exp u)) t‖ ≤
          C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * smallScalar R := by
  obtain ⟨S, C, hC, hkernel⟩ := angularPaperKernel_window_source_bound ℓ a b ha J M
  obtain ⟨D, hD, hFourier⟩ := localized_fourier_linear_bound χ hχ M hχs 0 J
  refine ⟨S, D * C, mul_pos hD hC, ?_⟩
  intro V hs R hR t
  let F : ℝ → ℝ → ℂ := fun _ u => angularPaperKernel ℓ V (R * Real.exp u)
  have hF (r : ℝ) (_ : 0 < r) : ContDiff ℝ ∞ (F r) :=
    angularPaperKernel_exp_smooth ℓ V a b ha hs (V.smooth ⊤) R hR
  have hb (i : ℕ) (hi : i ≤ J) (r : ℝ) (_ : 0 < r) (u : ℝ) (hu : |u| ≤ M) :
      (1 + r) ^ (0 : ℕ) * ‖iteratedDeriv i (F r) u‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * smallScalar R := by
    simp only [pow_zero, one_mul, F, iteratedDeriv_log_eq_euler]
    exact hkernel V hs R hR i hi u hu
  have hm : 0 < smallScalar R := smallScalar_pos hR
  have hh := hFourier F hF
    (C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * smallScalar R)
    (by positivity) hb 1 zero_lt_one t
  simpa only [pow_zero, one_mul, F, mul_assoc] using hh

def angularCanonicalDensity (ℓ : ℕ) (U : ℝ → ℂ) (V : 𝓢(ℝ, ℂ)) (R t : ℝ) : ℂ :=
  (smallScalar R : ℂ)⁻¹ * (𝓕 (fun s => U s * angularPaperKernel ℓ V (R * Real.exp s))) t

/-- A common compact cutoff separates all angular kernels on fixed logarithmic windows. -/
theorem angular_source_uniform_separation (ℓ : ℕ) {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 < a) (windows : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hwindows : ∀ i y, windows i y ≠ 0 → |y| ≤ M i) (J : ℕ) :
    ∃ (U : ℝ → ℂ) (S : Finset (ℕ × ℕ)) (C : ℝ),
      0 ≤ C ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Icc a b →
      ∀ R : ℝ, 0 < R →
      (∀ y : ι → ℝ, (∏ i, windows i (y i)) * angularPaperKernel ℓ V
          (R * Real.exp (∑ i, slope i * y i)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (∏ i, windows i (y i) * kernelLogPhase t (slope i * y i)) *
            angularCanonicalDensity ℓ U V R t) ∧
      Integrable (angularCanonicalDensity ℓ U V R) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖angularCanonicalDensity ℓ U V R t‖) ∧
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖angularCanonicalDensity ℓ U V R t‖) ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V ∧
      ∀ t : ℝ, (1 + ‖t‖) ^ J * ‖angularCanonicalDensity ℓ U V R t‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V := by
  let T := ∑ i, |slope i| * M i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hM i))
  obtain ⟨U, CW, hUc, hUs, hUone, hCW, hUderiv, hwindow⟩ :=
    JointLogSeparation.exists_complex_smooth_cutoff_with_derivative_bounds T (J + 2) hT
  have hUsupp : Function.support U ⊆ Icc (-(T + 1)) (T + 1) := by
    intro u hu
    have hn : ‖iteratedFDeriv ℝ 0 U u‖ ≠ 0 := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero] using
        (norm_ne_zero_iff.mpr hu)
    exact abs_le.mp ((hwindow u ⟨0, Nat.zero_le _, hn⟩).2.2)
  obtain ⟨S, C, hC, hb⟩ := angular_localized_fourier_source_bound ℓ a b ha U hUs (T + 1) hUsupp (J + 2)
  let I : ℝ := ∫ t : ℝ, ((1 + |t|) ^ (2 : ℕ))⁻¹
  have hI : 0 ≤ I := integral_nonneg (fun _ => by positivity)
  refine ⟨U, S, C * (I + 1), by positivity, hUc, hUs, ?_⟩
  intro V hs R hR
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let m := smallScalar R
  have hm : 0 < m := smallScalar_pos hR
  have hF := angularPaperKernel_compact_source_smooth ℓ V a b ha hs (V.smooth ⊤)
  let g := positiveLogProfile U (angularPaperKernel ℓ V) R hUc hUs hF hR
  let B : 𝓢(ℝ, ℂ) := ((m : ℂ)⁻¹) • (𝓕 g)
  have hcan (t : ℝ) : B t = angularCanonicalDensity ℓ U V R t := rfl
  have hnorm (t : ℝ) : ‖B t‖ = m⁻¹ * ‖(𝓕 g) t‖ := by
    simp only [B, smul_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  have hbound (t : ℝ) : (1 + |t|) ^ (J + 2) * ‖B t‖ ≤ C * Q := by
    rw [hnorm]
    calc
      _ = m⁻¹ * ((1 + |t|) ^ (J + 2) * ‖(𝓕 g) t‖) := by ring
      _ ≤ m⁻¹ * (C * Q * m) := mul_le_mul_of_nonneg_left (hb V hs R hR t) (inv_nonneg.mpr hm.le)
      _ = C * Q := by field_simp
  have hL1 := weighted_fourier_L1_bound (B : ℝ → ℂ) B.continuous 1 (C * Q)
    zero_lt_one (mul_nonneg hC.le hQ) J (by simpa only [one_mul] using hbound)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ i, windows i (y i)) ≠ 0 → U (∑ i, slope i * y i) = 1 :=
      JointLogSeparation.coupled_cutoff_active windows U slope y M hwindows (by simpa [T] using hUone)
    have hsep := coupled_positive_log_separation windows (angularPaperKernel ℓ V)
      U R slope y hUc hUs hF hR hactive
    rw [hsep, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [← hcan]
    dsimp only [B]
    simp only [smul_apply, smul_eq_mul]
    have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
    change _ = (m : ℂ) * _
    field_simp
    rfl
  · exact B.integrable.congr (Filter.Eventually.of_forall hcan)
  · simpa only [Real.norm_eq_abs, ← hcan] using hL1.1
  · have hi : (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖angularCanonicalDensity ℓ U V R t‖) ≤ (C * Q) * I := by
      simpa only [Real.norm_eq_abs, ← hcan, one_mul, I] using hL1.2
    exact hi.trans (by
      change C * Q * I ≤ C * (I + 1) * Q
      nlinarith only [mul_nonneg hC.le hQ])
  · intro t
    rw [← hcan, Real.norm_eq_abs]
    have hp : (1 + |t|) ^ J ≤ (1 + |t|) ^ (J + 2) :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
    calc
      _ ≤ (1 + |t|) ^ (J + 2) * ‖B t‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ C * Q := hbound t
      _ ≤ C * (I + 1) * Q := by nlinarith only [mul_nonneg (mul_nonneg hC.le hQ) hI]


def angularTwistedDensity (ℓ : ℕ) (U W : ℝ → ℂ) (θ R t : ℝ) : ℂ :=
  (smallScalar R : ℂ)⁻¹ *
    (𝓕 (fun s : ℝ => U s * angularPaperKernel ℓ
      (Vstar (CompletedHeight.normTwistedSource W θ)) (R * Real.exp s))) t

theorem normTwistedSource_angular_uniform_separation (ℓ : ℕ) {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 < a)
    (windows : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hwindows : ∀ i y, windows i y ≠ 0 → |y| ≤ M i)
    (W : ℝ → ℂ) (hsupp : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ → ℂ) (n : ℕ) (C : ℝ),
      0 ≤ C ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ R : ℝ, 0 < R →
      (∀ y : ι → ℝ,
        (∏ i, windows i (y i)) * angularPaperKernel ℓ
          (Vstar (CompletedHeight.normTwistedSource W θ))
          (R * Real.exp (∑ i, slope i * y i)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (∏ i, windows i (y i) * kernelLogPhase t (slope i * y i)) *
            angularTwistedDensity ℓ U W θ R t) ∧
      Integrable (angularTwistedDensity ℓ U W θ R) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖angularTwistedDensity ℓ U W θ R t‖) ∧
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖angularTwistedDensity ℓ U W θ R t‖) ≤ C * (1 + ‖θ‖)^n ∧
      (∀ t : ℝ, (1 + ‖t‖)^J * ‖angularTwistedDensity ℓ U W θ R t‖ ≤ C * (1 + ‖θ‖)^n) := by
  obtain ⟨U, orders, C, hC, hUc, hUs, hsep⟩ :=
    angular_source_uniform_separation ℓ a b ha windows slope M hM hwindows J
  let V := CompletedHeight.vstarSchwartz W a b ha hsupp hW
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b :=
    Vstar_support W a b hsupp
  obtain ⟨G, hG, hbound⟩ := CompletedHeight.normTwistedSource_schwartz V a b ha hV
  have hlink (θ : ℝ) : (G θ : ℝ → ℂ) =
      Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hG θ x]
    change kernelLogPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x) =
      (Real.sqrt x:ℂ)*(kernelLogPhase θ (Real.log x)*W x)
    ring
  have hGs (θ : ℝ) : Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b := by
    intro x hx
    change G θ x ≠ 0 at hx
    rw [hG θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  obtain ⟨n, D, hD, hpoly⟩ := hbound orders
  refine ⟨U, n, C*D, mul_nonneg hC hD.le, hUc, hUs, ?_⟩
  intro θ R hR
  have hcan : angularCanonicalDensity ℓ U (G θ) R = angularTwistedDensity ℓ U W θ R := by
    unfold angularCanonicalDensity angularTwistedDensity
    rw [hlink θ]
  obtain ⟨heq, hdi, hi, hm, hp⟩ := hsep (G θ) (hGs θ) R hR
  rw [hcan] at heq hdi hi hm hp
  rw [hlink θ] at heq
  have hb : C * orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G θ) ≤
      C*D * (1+‖θ‖)^n :=
    (mul_le_mul_of_nonneg_left (hpoly θ) hC).trans_eq (by ring)
  exact ⟨heq, hdi, hi, hm.trans hb, fun t => (hp t).trans hb⟩


end
end InverseKernelSourceUniform
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
