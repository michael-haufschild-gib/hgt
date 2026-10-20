import GaloisForLFunctions.BiScaleUncertainty.ProbeAmplitudeLaw
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import GaloisForLFunctions.RHTower.EvenLandauPairTest
import GaloisForLFunctions.RHTower.WeilPositivityConductorObstruction

/-!
# Multiplicities are read off by tuned probes

A packet weighs a critical zero by `m_ρ²|f̂(γ_ρ)|²`; the Weil functional of `h_f` weighs it by
`m_ρ|f̂(γ_ρ)|²` (`PacketWeilEnergyLaw`). A probe tuned to one ordinate separates the two.

For a bump `φ ∈ C²_c` with `∫ φ ≠ 0` and a critical zero `ρ₀ = 1/2 + iγ₀`, the **tuned probe**
`f_R(u) = φ(u/R) cos(γ₀u)` has `f̂_R(ξ) = (R/2)(φ̂(R(ξ − γ₀)) + φ̂(R(ξ + γ₀)))`: as `R → ∞` its
window shrinks onto `±γ₀`.

* `tendsto_energy_ratio_tunedProbe` (unconditional): `E(f_R)/W(f_R) → m_{ρ₀}`.
* `multiplicity_readout_of_riemannHypothesis`: under RH, for every zero `ρ₀` and every `R`, `E(f_R)`
  is the asymptotic mean square of the packet of `f_R` and `W(f_R)` is the Weil functional of its
  autocorrelation; their ratio tends to `m_{ρ₀}`. Multiplicities are prime-side observables.

**Mechanism.** `R⁻²|f̂_R(γ)|²` converges to `|φ̂(0)|²/4` at `γ = ±γ₀` and to `0` elsewhere; the
decay `|φ̂(ξ)| ≤ N/(1 + ξ²)` dominates it, uniformly in `R ≥ 1`, by a multiple of
`m_ρ/(1 + γ_ρ²)`, which is summable over the zeros (`RHTower.summable_zetaZeroConfig`). The
conjugate zero carries the same multiplicity (`RHTower.mult_conj_zetaZeroConfig`).
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-- The probe `φ(u/R) cos(γ₀u)` of width `R` tuned to the ordinate `γ₀`. -/
def tunedProbe (φ : ℝ → ℝ) (γ₀ R : ℝ) (u : ℝ) : ℝ := φ (u / R) * Real.cos (γ₀ * u)

theorem contDiff_tunedProbe {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (γ₀ R : ℝ) :
    ContDiff ℝ 2 (tunedProbe φ γ₀ R) :=
  (hφ.comp (contDiff_id.div_const R)).mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

theorem hasCompactSupport_dilate {φ : ℝ → ℝ} (hφc : HasCompactSupport φ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport fun u => φ (u / R) := by
  have e : (fun u => φ (u / R)) = fun u => φ (R⁻¹ • u) := by
    funext u; rw [smul_eq_mul, div_eq_inv_mul]
  rw [e]
  exact hφc.comp_smul (inv_ne_zero hR.ne')

theorem hasCompactSupport_tunedProbe {φ : ℝ → ℝ} (hφc : HasCompactSupport φ) (γ₀ : ℝ) {R : ℝ}
    (hR : 0 < R) : HasCompactSupport (tunedProbe φ γ₀ R) :=
  show HasCompactSupport ((fun u => φ (u / R)) * fun u => Real.cos (γ₀ * u)) from
    (hasCompactSupport_dilate hφc hR).mul_right

/-- The transform of the tuned probe: two dilated copies of `φ̂` centred at `±γ₀`. -/
theorem paperFT_tunedProbe {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) (γ₀ : ℝ)
    {R : ℝ} (hR : 0 < R) (z : ℂ) :
    Zeta23.paperFT (fun u => (tunedProbe φ γ₀ R u : ℂ)) z =
      (R / 2 : ℂ) * (Zeta23.paperFT (fun u => (φ u : ℂ)) (R * (z - γ₀)) +
        Zeta23.paperFT (fun u => (φ u : ℂ)) (R * (z + γ₀))) := by
  have hψ : Continuous fun u : ℝ => ((φ (u / R) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hφ.comp (continuous_id.div_const R))
  have hψc : HasCompactSupport fun u : ℝ => ((φ (u / R) : ℝ) : ℂ) :=
    (hasCompactSupport_dilate hφc hR).comp_left Complex.ofReal_zero
  have hI : ∀ w : ℂ, Integrable fun u : ℝ => ((φ (u / R) : ℝ) : ℂ) * cexp (I * w * u) := fun w =>
    (hψ.mul (by fun_prop)).integrable_of_hasCompactSupport hψc.mul_right
  have hcos : ∀ u : ℝ, ((tunedProbe φ γ₀ R u : ℝ) : ℂ) * cexp (I * z * u) =
      (1 / 2 : ℂ) * (((φ (u / R) : ℝ) : ℂ) * cexp (I * (z - γ₀) * u)) +
        (1 / 2 : ℂ) * (((φ (u / R) : ℝ) : ℂ) * cexp (I * (z + γ₀) * u)) := by
    intro u
    have e1 : cexp (I * (z - γ₀) * u) = cexp (I * z * u) * cexp (-((γ₀ : ℂ) * u) * I) := by
      rw [← Complex.exp_add]; ring_nf
    have e2 : cexp (I * (z + γ₀) * u) = cexp (I * z * u) * cexp ((γ₀ : ℂ) * u * I) := by
      rw [← Complex.exp_add]; ring_nf
    simp only [tunedProbe]
    push_cast
    rw [e1, e2, Complex.cos]
    ring
  have hL : Zeta23.paperFT (fun u => (tunedProbe φ γ₀ R u : ℂ)) z =
      (1 / 2 : ℂ) * Zeta23.paperFT (fun u => ((φ (u / R) : ℝ) : ℂ)) (z - γ₀) +
        (1 / 2 : ℂ) * Zeta23.paperFT (fun u => ((φ (u / R) : ℝ) : ℂ)) (z + γ₀) := by
    unfold Zeta23.paperFT
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hI _).const_mul _) ((hI _).const_mul _)]
    exact integral_congr_ae (Eventually.of_forall hcos)
  rw [hL, _root_.RHTower.paperFT_comp_div (f := fun u => (φ u : ℂ)) hR,
    _root_.RHTower.paperFT_comp_div (f := fun u => (φ u : ℂ)) hR]
  ring

/-! ## The scaled energies of tuned probes -/

/-- The conjugate of a critical zero, as a critical zero. -/
def conjCritical (ρ : criticalZeros) : criticalZeros :=
  ⟨⟨conj ((ρ : 𝒵) : ℂ), _root_.RHTower.conj_mem_zetaZeroConfig (ρ : 𝒵).2⟩,
    show (conj ((ρ : 𝒵) : ℂ)).re = 1 / 2 by rw [Complex.conj_re]; exact ρ.2⟩

theorem eq_of_im_eq_critical {ρ ρ' : criticalZeros} (h : ((ρ : 𝒵) : ℂ).im = ((ρ' : 𝒵) : ℂ).im) :
    ρ = ρ' := by
  have hr : ((ρ : 𝒵) : ℂ).re = ((ρ' : 𝒵) : ℂ).re := by
    rw [show ((ρ : 𝒵) : ℂ).re = 1 / 2 from ρ.2, show ((ρ' : 𝒵) : ℂ).re = 1 / 2 from ρ'.2]
  exact Subtype.ext (Subtype.ext (Complex.ext hr h))

theorem summable_mult_div_critical :
    Summable fun ρ : criticalZeros =>
      (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) / (1 + ((ρ : 𝒵) : ℂ).im ^ 2) := by
  refine (_root_.RHTower.summable_zetaZeroConfig.subtype criticalZeros).congr fun ρ => ?_
  simp only [Function.comp_apply]
  rw [gammaOf_of_mem_critical ρ.2, Complex.normSq_ofReal, sq]

/-- `1 + γ² ≤ 2(1 + γ₀²)(1 + (γ ∓ γ₀)²)`. -/
theorem one_add_sq_le (γ γ₀ : ℝ) : 1 + γ ^ 2 ≤ 2 * (1 + γ₀ ^ 2) * (1 + (γ - γ₀) ^ 2) := by
  nlinarith [sq_nonneg (γ - 2 * γ₀), sq_nonneg (γ₀ * (γ - γ₀)), sq_nonneg γ₀]

/-- **Scaled energy of tuned probes.** For weights `0 ≤ v_ρ ≤ m_ρ²` symmetric under conjugation at
`ρ₀`, `Σ_ρ v_ρ |φ̂(R(γ − γ₀)) + φ̂(R(γ + γ₀))|² → 2 v_{ρ₀} |φ̂(0)|²`. -/
theorem tendsto_weighted_tunedEnergy {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (ρ₀ : criticalZeros) (v : criticalZeros → ℝ) (hv0 : ∀ ρ, 0 ≤ v ρ)
    (hv : ∀ ρ, v ρ ≤ (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) ^ 2)
    (hvc : v (conjCritical ρ₀) = v ρ₀) :
    Tendsto (fun R : ℝ => ∑' ρ : criticalZeros, v ρ *
      ‖Zeta23.paperFT (fun u => (φ u : ℂ)) ((R * (((ρ : 𝒵) : ℂ).im - ((ρ₀ : 𝒵) : ℂ).im) : ℝ) : ℂ) +
        Zeta23.paperFT (fun u => (φ u : ℂ))
          ((R * (((ρ : 𝒵) : ℂ).im + ((ρ₀ : 𝒵) : ℂ).im) : ℝ) : ℂ)‖ ^ 2) atTop
      (𝓝 (2 * v ρ₀ * ‖Zeta23.paperFT (fun u => (φ u : ℂ)) 0‖ ^ 2)) := by
  classical
  set Φ : ℝ → ℂ := fun ξ => Zeta23.paperFT (fun u => (φ u : ℂ)) (ξ : ℂ)
  set γ₀ := ((ρ₀ : 𝒵) : ℂ).im
  set ρ₁ := conjCritical ρ₀
  have hγ₀ : γ₀ ≠ 0 := im_ne_zero_of_mem_critical ρ₀
  have hγ₁ : ((ρ₁ : 𝒵) : ℂ).im = -γ₀ := by simp [ρ₁, conjCritical, γ₀]
  have hne : ρ₀ ≠ ρ₁ := fun h => hγ₀ (by
    have := congrArg (fun ρ : criticalZeros => ((ρ : 𝒵) : ℂ).im) h
    simp only [hγ₁] at this
    linarith)
  -- decay of `φ̂`
  obtain ⟨N, hN0, hN⟩ := _root_.RHTower.EvenSector.exists_norm_paperFT_le_of_compact
    (Complex.ofRealCLM.contDiff.comp hφ) (hφc.comp_left Complex.ofReal_zero) 0
  have hdec : ∀ ξ : ℝ, ‖Φ ξ‖ ≤ N / (1 + ξ ^ 2) := fun ξ => by
    have := hN (ξ : ℂ) (by simp)
    rwa [Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
  have hdecR : ∀ R ξ : ℝ, 1 ≤ R → ‖Φ (R * ξ)‖ ≤ N / (1 + ξ ^ 2) := fun R ξ hR =>
    (hdec _).trans (div_le_div_of_nonneg_left hN0 (by positivity) (by
      have : ξ ^ 2 ≤ (R * ξ) ^ 2 := by
        rw [mul_pow]; exact le_mul_of_one_le_left (sq_nonneg ξ) (by nlinarith)
      linarith))
  have hlim0 : ∀ ξ : ℝ, ξ ≠ 0 → Tendsto (fun R : ℝ => Φ (R * ξ)) atTop (𝓝 0) := fun ξ hξ => by
    refine squeeze_zero_norm (fun R => hdec _) ?_
    have hξ2 : 0 < ξ ^ 2 := by positivity
    have h1 : Tendsto (fun R : ℝ => 1 + (R * ξ) ^ 2) atTop atTop := by
      refine tendsto_atTop_add_const_left _ _ ?_
      simp_rw [mul_pow]
      exact (tendsto_pow_atTop two_ne_zero).atTop_mul_const hξ2
    exact tendsto_const_nhds.div_atTop h1
  -- the pointwise limit, supported on `ρ₀` and its conjugate
  have hpart : ∀ a : ℝ, Tendsto (fun R : ℝ => Φ (R * a)) atTop (𝓝 (if a = 0 then Φ 0 else 0)) := by
    intro a
    by_cases ha : a = 0
    · simp only [ha, if_true, mul_zero]
      exact tendsto_const_nhds
    · simp only [ha, if_false]
      exact hlim0 a ha
  set g : criticalZeros → ℝ := fun ρ => v ρ *
    ‖(if ((ρ : 𝒵) : ℂ).im - γ₀ = 0 then Φ 0 else 0) +
      (if ((ρ : 𝒵) : ℂ).im + γ₀ = 0 then Φ 0 else 0)‖ ^ 2
  have hg : ∀ ρ : criticalZeros, Tendsto (fun R : ℝ => v ρ *
      ‖Φ (R * (((ρ : 𝒵) : ℂ).im - γ₀)) + Φ (R * (((ρ : 𝒵) : ℂ).im + γ₀))‖ ^ 2) atTop
        (𝓝 (g ρ)) := fun ρ =>
    (((by fun_prop : Continuous fun x : ℂ => ‖x‖ ^ 2).tendsto _).comp
      ((hpart _).add (hpart _))).const_mul (v ρ)
  have hγ₀₂ : γ₀ + γ₀ ≠ 0 := fun h => hγ₀ (by linarith)
  have htsum : ∑' ρ, g ρ = 2 * v ρ₀ * ‖Φ 0‖ ^ 2 := by
    rw [tsum_eq_sum (s := {ρ₀, ρ₁}) fun ρ hρ => ?_, Finset.sum_pair hne]
    · have a1 : ((ρ₀ : 𝒵) : ℂ).im - γ₀ = 0 := sub_self _
      have a2 : ((ρ₀ : 𝒵) : ℂ).im + γ₀ ≠ 0 := hγ₀₂
      have c1 : ((ρ₁ : 𝒵) : ℂ).im - γ₀ ≠ 0 := by rw [hγ₁]; intro h; apply hγ₀; linarith
      have c2 : ((ρ₁ : 𝒵) : ℂ).im + γ₀ = 0 := by rw [hγ₁]; ring
      simp only [g]
      rw [if_pos a1, if_neg a2, if_neg c1, if_pos c2, add_zero, zero_add, hvc]
      ring
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hρ
      have h1 : ((ρ : 𝒵) : ℂ).im - γ₀ ≠ 0 := fun h =>
        hρ.1 (eq_of_im_eq_critical (by linarith))
      have h2 : ((ρ : 𝒵) : ℂ).im + γ₀ ≠ 0 := fun h =>
        hρ.2 (eq_of_im_eq_critical (by rw [hγ₁]; linarith))
      simp only [g, h1, h2, if_false, add_zero, norm_zero]
      ring
  -- domination by a multiple of `m_ρ/(1 + γ_ρ²)`
  set B := ∑' ρ : criticalZeros,
    (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) / (1 + ((ρ : 𝒵) : ℂ).im ^ 2)
  set K := 16 * N ^ 2 * (1 + γ₀ ^ 2) ^ 2 * B
  have hbound : ∀ᶠ R in atTop, ∀ ρ : criticalZeros, ‖v ρ *
      ‖Φ (R * (((ρ : 𝒵) : ℂ).im - γ₀)) + Φ (R * (((ρ : 𝒵) : ℂ).im + γ₀))‖ ^ 2‖ ≤
        K * ((Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) / (1 + ((ρ : 𝒵) : ℂ).im ^ 2)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR ρ
    set γ := ((ρ : 𝒵) : ℂ).im
    set m := (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ)
    have hm1 : 1 ≤ m := by
      simp only [m]; exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ : 𝒵).2
    have hq : 0 < 1 + γ ^ 2 := by positivity
    have hmB : m / (1 + γ ^ 2) ≤ B :=
      summable_mult_div_critical.le_tsum ρ fun _ _ => by positivity
    have hA : ‖Φ (R * (γ - γ₀))‖ ≤ 2 * N * (1 + γ₀ ^ 2) / (1 + γ ^ 2) := by
      refine (hdecR R _ hR).trans ?_
      rw [div_le_div_iff₀ (by positivity) hq]
      have := mul_le_mul_of_nonneg_left (one_add_sq_le γ γ₀) hN0
      nlinarith [this]
    have hB' : ‖Φ (R * (γ + γ₀))‖ ≤ 2 * N * (1 + γ₀ ^ 2) / (1 + γ ^ 2) := by
      refine (hdecR R _ hR).trans ?_
      rw [div_le_div_iff₀ (by positivity) hq]
      have h := one_add_sq_le γ (-γ₀)
      rw [sub_neg_eq_add, neg_sq] at h
      have := mul_le_mul_of_nonneg_left h hN0
      nlinarith [this]
    have hx : ‖Φ (R * (γ - γ₀)) + Φ (R * (γ + γ₀))‖ ≤ 4 * N * (1 + γ₀ ^ 2) / (1 + γ ^ 2) := by
      refine (norm_add_le _ _).trans ?_
      have : 4 * N * (1 + γ₀ ^ 2) / (1 + γ ^ 2) =
          2 * N * (1 + γ₀ ^ 2) / (1 + γ ^ 2) + 2 * N * (1 + γ₀ ^ 2) / (1 + γ ^ 2) := by ring
      rw [this]
      exact add_le_add hA hB'
    have hr0 : 0 ≤ m / (1 + γ ^ 2) := by positivity
    rw [Real.norm_of_nonneg (mul_nonneg (hv0 ρ) (by positivity))]
    calc v ρ * ‖Φ (R * (γ - γ₀)) + Φ (R * (γ + γ₀))‖ ^ 2
        ≤ m ^ 2 * (4 * N * (1 + γ₀ ^ 2) / (1 + γ ^ 2)) ^ 2 :=
          mul_le_mul (hv ρ) (pow_le_pow_left₀ (norm_nonneg _) hx 2) (by positivity) (by positivity)
      _ = 16 * N ^ 2 * (1 + γ₀ ^ 2) ^ 2 * ((m / (1 + γ ^ 2)) * (m / (1 + γ ^ 2))) := by
          field_simp
          ring
      _ ≤ 16 * N ^ 2 * (1 + γ₀ ^ 2) ^ 2 * (B * (m / (1 + γ ^ 2))) := by
          gcongr
      _ = K * (m / (1 + γ ^ 2)) := by simp only [K]; ring
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (bound := fun ρ : criticalZeros =>
      K * ((Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) / (1 + ((ρ : 𝒵) : ℂ).im ^ 2)))
    (summable_mult_div_critical.mul_left K) hg hbound
  rw [htsum] at hlim
  exact hlim

theorem norm_paperFT_tunedProbe_sq {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (γ₀ : ℝ) {R : ℝ} (hR : 0 < R) (ξ : ℝ) :
    ‖Zeta23.paperFT (fun u => (tunedProbe φ γ₀ R u : ℂ)) (ξ : ℂ)‖ ^ 2 =
      R ^ 2 / 4 * ‖Zeta23.paperFT (fun u => (φ u : ℂ)) ((R * (ξ - γ₀) : ℝ) : ℂ) +
        Zeta23.paperFT (fun u => (φ u : ℂ)) ((R * (ξ + γ₀) : ℝ) : ℂ)‖ ^ 2 := by
  rw [paperFT_tunedProbe hφ hφc γ₀ hR, norm_mul]
  have h2 : ‖(R / 2 : ℂ)‖ = R / 2 := by
    rw [show (R / 2 : ℂ) = ((R / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h2]
  push_cast
  ring

/-- **Tuned probes read multiplicities.** For a critical zero `ρ₀ = 1/2 + iγ₀` and a bump `φ`
with `∫ φ ≠ 0`, the probes `f_R(u) = φ(u/R) cos(γ₀u)` satisfy `E(f_R)/W(f_R) → m_{ρ₀}`. -/
theorem tendsto_energy_ratio_tunedProbe {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∫ u, φ u ≠ 0) (ρ₀ : criticalZeros) :
    Tendsto (fun R : ℝ => criticalPacketEnergy (tunedProbe φ ((ρ₀ : 𝒵) : ℂ).im R) /
      criticalWeilEnergy (tunedProbe φ ((ρ₀ : 𝒵) : ℂ).im R)) atTop
        (𝓝 (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ)) := by
  set γ₀ := ((ρ₀ : 𝒵) : ℂ).im
  set m : criticalZeros → ℝ := fun ρ => (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ)
  have hm1 : ∀ ρ, 1 ≤ m ρ := fun ρ => by
    simp only [m]; exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ : 𝒵).2
  have hmc : m (conjCritical ρ₀) = m ρ₀ := by
    simp only [m, conjCritical]
    exact_mod_cast _root_.RHTower.mult_conj_zetaZeroConfig (ρ₀ : 𝒵).2
  have hE := tendsto_weighted_tunedEnergy hφ hφc ρ₀ (fun ρ => m ρ ^ 2)
    (fun _ => by positivity) (fun _ => le_rfl) (by simp only [hmc])
  have hW := tendsto_weighted_tunedEnergy hφ hφc ρ₀ m (fun ρ => by linarith [hm1 ρ])
    (fun ρ => by nlinarith [hm1 ρ]) hmc
  set c := ‖Zeta23.paperFT (fun u => (φ u : ℂ)) 0‖ ^ 2
  have hc : 0 < c := by
    have h0 : Zeta23.paperFT (fun u => (φ u : ℂ)) 0 = ((∫ u, φ u : ℝ) : ℂ) := by
      simp only [Zeta23.paperFT, mul_zero, zero_mul, Complex.exp_zero, mul_one]
      exact integral_complex_ofReal
    have : 0 < ‖Zeta23.paperFT (fun u => (φ u : ℂ)) 0‖ := by
      rw [h0, Complex.norm_real, Real.norm_eq_abs]
      exact abs_pos.mpr hφ0
    positivity
  have hm0 := hm1 ρ₀
  have hlim := hE.div hW (by positivity)
  have hval : 2 * (fun ρ => m ρ ^ 2) ρ₀ * c / (2 * m ρ₀ * c) = m ρ₀ := by
    simp only
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hR4 : R ^ 2 / 4 ≠ 0 := by positivity
  rw [criticalPacketEnergy, criticalWeilEnergy]
  simp_rw [norm_paperFT_tunedProbe_sq hφ.continuous hφc γ₀ hR]
  have e1 : ∀ ρ : criticalZeros, m ρ ^ 2 * (R ^ 2 / 4 * ‖Zeta23.paperFT (fun u => (φ u : ℂ))
      ((R * (((ρ : 𝒵) : ℂ).im - γ₀) : ℝ) : ℂ) + Zeta23.paperFT (fun u => (φ u : ℂ))
        ((R * (((ρ : 𝒵) : ℂ).im + γ₀) : ℝ) : ℂ)‖ ^ 2) = R ^ 2 / 4 * (m ρ ^ 2 *
      ‖Zeta23.paperFT (fun u => (φ u : ℂ)) ((R * (((ρ : 𝒵) : ℂ).im - γ₀) : ℝ) : ℂ) +
        Zeta23.paperFT (fun u => (φ u : ℂ)) ((R * (((ρ : 𝒵) : ℂ).im + γ₀) : ℝ) : ℂ)‖ ^ 2) :=
    fun ρ => by ring
  have e2 : ∀ ρ : criticalZeros, m ρ * (R ^ 2 / 4 * ‖Zeta23.paperFT (fun u => (φ u : ℂ))
      ((R * (((ρ : 𝒵) : ℂ).im - γ₀) : ℝ) : ℂ) + Zeta23.paperFT (fun u => (φ u : ℂ))
        ((R * (((ρ : 𝒵) : ℂ).im + γ₀) : ℝ) : ℂ)‖ ^ 2) = R ^ 2 / 4 * (m ρ *
      ‖Zeta23.paperFT (fun u => (φ u : ℂ)) ((R * (((ρ : 𝒵) : ℂ).im - γ₀) : ℝ) : ℂ) +
        Zeta23.paperFT (fun u => (φ u : ℂ)) ((R * (((ρ : 𝒵) : ℂ).im + γ₀) : ℝ) : ℂ)‖ ^ 2) :=
    fun ρ => by ring
  simp only [m] at e1 e2
  rw [tsum_congr e1, tsum_congr e2, tsum_mul_left, tsum_mul_left, mul_div_mul_left _ _ hR4]
  rfl

/-- **Multiplicities are prime-side observables (under RH).** For every zero `ρ₀` and every width
`R`, `E(f_R)` is the asymptotic mean square of the packet of the tuned probe `f_R` and `W(f_R)` is
the Weil functional of its autocorrelation; their ratio tends to the multiplicity `m_{ρ₀}`. -/
theorem multiplicity_readout_of_riemannHypothesis (hRH : RiemannHypothesis) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hφ0 : ∫ u, φ u ≠ 0) (ρ₀ : 𝒵) :
    (∀ R : ℝ, 0 < R → ∀ w : ℝ, 0 ≤ w → (∀ v : ℝ, w < |v| → tunedProbe φ (ρ₀ : ℂ).im R v = 0) →
      Tendsto (fun L : ℝ => (∫ τ in w..L, stationaryPacket (tunedProbe φ (ρ₀ : ℂ).im R) τ ^ 2) / L)
        atTop (𝓝 (criticalPacketEnergy (tunedProbe φ (ρ₀ : ℂ).im R)))) ∧
    (∀ R : ℝ, 0 < R → (Zeta23.EF.literatureRHS
      (Zeta23.EF.weilTest (fun u => (tunedProbe φ (ρ₀ : ℂ).im R u : ℂ))
        (fun u => (tunedProbe φ (ρ₀ : ℂ).im R u : ℂ)))).re =
          criticalWeilEnergy (tunedProbe φ (ρ₀ : ℂ).im R)) ∧
    Tendsto (fun R : ℝ => criticalPacketEnergy (tunedProbe φ (ρ₀ : ℂ).im R) /
      criticalWeilEnergy (tunedProbe φ (ρ₀ : ℂ).im R)) atTop
        (𝓝 (Zeta23.zetaZeroConfig.mult (ρ₀ : ℂ) : ℝ)) := by
  have hblind : ∀ (f : ℝ → ℝ) (ρ : 𝒵), 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := fun f ρ hρ => by
    rw [re_eq_half_of_mem hRH ρ] at hρ
    exact absurd hρ (lt_irrefl _)
  refine ⟨fun R hR w hw0 hw => tendsto_mean_sq_stationaryPacket_of_blind
      (contDiff_tunedProbe hφ _ R) (hasCompactSupport_tunedProbe hφc _ hR) hw0 hw (hblind _),
    fun R hR => ?_, tendsto_energy_ratio_tunedProbe hφ hφc hφ0 ⟨ρ₀, re_eq_half_of_mem hRH ρ₀⟩⟩
  rw [literatureRHS_weilTest_of_blind (contDiff_tunedProbe hφ _ R)
    (hasCompactSupport_tunedProbe hφc _ hR) (hblind _), ofReal_re]

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
