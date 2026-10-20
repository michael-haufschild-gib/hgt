import GaloisForLFunctions.BiScaleUncertainty.IncidenceGainOfTheSingleIntegerBathtub

/-!
# The removal law: each power node is priced by one Fourier coefficient of the folded symbol

Let `q ≥ 2`, `ℓ = log q`, `F(z) = γ(‖z‖/ℓ)` the folded symbol on `ℝ/2πℤ` and
`φ_d = ∫ F(z) cos(dz) dz/2π` its `d`-th cosine coefficient. On combinations blind at all powers
`q^j` the exact slack is `−m_q` with `m_q = ∫ F`. Delete one node `q^d`.

**Theorem** (`blindSymbolSlackOn_punctured_iff`). The exact blind symbol slack on
`{q^j : j ≥ 1, j ≠ d}` is `−(m_q − |φ_d|)`: the node `q^d` is worth exactly `|φ_d|`. The same holds
with zero pole mass.

**Lower bound: one free frequency.** Blindness off `q^d` leaves exactly one free cosine moment
`c = ∫ G(r) cos(dℓr)` of the spectral density. The phase `rℓ mod 2π` of `G` is then the measure
`(∫G + 2c cos(dz)) dz/2π` (`integral_mul_periodic_eq_of_cos_blind_off`, from Fourier uniqueness on
the circle). Its positivity forces `2|c| ≤ ∫G`, so the folded symbol integrates to at least
`(m_q − |φ_d|) ∫G`.

**Upper bound: translated pairs.** Replacing every test `f` of a near-extremal combination for the
full power grid by `f ± f(· − dℓ)` multiplies the spectral density by `2 ± 2cos(dℓr)`. All node
values at `q^j`, `j ≠ d`, stay zero, the mass doubles, and the symbol moves by `±φ_d` up to the
bathtub defect of the original combination.

**Far nodes are cheap** (`abs_foldedCosineCoefficient_le`): `φ_d = (ℓ/π) ∫_0^{π/ℓ} γ(v) cos(dℓv) dv`
and `|φ_d| ≤ (γ(π/ℓ) − γ(0))/d`, since `γ` is monotone on `[0, π/ℓ]` and the cosine integrates to
zero on each of the `d` cells.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. The cosine characters of the circle -/

/-- The `d`-th cosine character `z ↦ Re e^{idz}` of `ℝ/2πℤ`. -/
def circleCos (d : ℕ) (z : AddCircle (2 * π)) : ℝ := (fourier (d : ℤ) z).re

theorem continuous_circleCos (d : ℕ) : Continuous (circleCos d) :=
  Complex.continuous_re.comp (fourier (d : ℤ)).continuous

theorem circleCos_coe (d : ℕ) (x : ℝ) : circleCos d (x : AddCircle (2 * π)) = Real.cos (d * x) := by
  unfold circleCos
  rw [fourier_coe_apply]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : 2 * (π : ℂ) * I * ((d : ℤ) : ℂ) * (x : ℂ) / ((2 * π : ℝ) : ℂ) = ((d * x : ℝ) : ℂ) * I := by
    push_cast; field_simp
  rw [e, exp_ofReal_mul_I_re]

theorem circleCos_neg (d : ℕ) (z : AddCircle (2 * π)) : circleCos d (-z) = circleCos d z := by
  induction z using QuotientAddGroup.induction_on with
  | H x =>
    rw [← AddCircle.coe_neg, circleCos_coe, circleCos_coe, mul_neg, Real.cos_neg]

theorem circleCos_phase (d : ℕ) (ℓ r : ℝ) : circleCos d (phase ℓ r) = Real.cos (r * ((d : ℝ) * ℓ)) := by
  rw [phase, circleCos_coe]; ring_nf

theorem circleCos_zero (d : ℕ) : circleCos d 0 = 1 := by
  have := circleCos_coe d 0
  rwa [AddCircle.coe_zero, mul_zero, Real.cos_zero] at this

theorem circleCos_pi_div {d : ℕ} (hd : 1 ≤ d) :
    circleCos d ((π / d : ℝ) : AddCircle (2 * π)) = -1 := by
  rw [circleCos_coe]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [mul_div_cancel₀ _ this, Real.cos_pi]

/-- `∫ e^{inz} cos(dz) dz/2π = ([n = −d] + [n = d])/2`. -/
theorem integral_fourier_mul_circleCos (n : ℤ) (d : ℕ) :
    ∫ z, fourier n z * (circleCos d z : ℂ) ∂(AddCircle.haarAddCircle (T := 2 * π)) =
      ((if n + d = 0 then 1 else 0) + (if n - d = 0 then 1 else 0)) / 2 := by
  have hre : ∀ z : AddCircle (2 * π), (circleCos d z : ℂ) =
      (fourier (d : ℤ) z + fourier (-(d : ℤ)) z) / 2 := by
    intro z
    rw [fourier_neg, circleCos, Complex.re_eq_add_conj]
  have hprod : ∀ z : AddCircle (2 * π), fourier n z * (circleCos d z : ℂ) =
      (fourier (n + d) z + fourier (n - d) z) / 2 := by
    intro z
    rw [hre, fourier_add, sub_eq_add_neg, fourier_add]
    ring
  simp_rw [hprod]
  have i1 : Integrable (fun z => fourier (n + d) z) (AddCircle.haarAddCircle (T := 2 * π)) :=
    (BoundedContinuousFunction.mkOfCompact (fourier (n + d))).integrable _
  have i2 : Integrable (fun z => fourier (n - d) z) (AddCircle.haarAddCircle (T := 2 * π)) :=
    (BoundedContinuousFunction.mkOfCompact (fourier (n - d))).integrable _
  rw [integral_div, integral_add i1 i2, integral_fourier_haar, integral_fourier_haar]

/-! ### 2. One free frequency -/

/-- **The phase measure.** A nonnegative continuous integrable density `G` has a finite measure
`ν` on the circle whose Fourier coefficients are the cosine moments `∫ G(r) cos(nℓr)` and which
integrates every even continuous observable `P` to `∫ G P(phase)` (symmetrize `G`, push forward). -/
theorem exists_phase_measure {G : ℝ → ℝ} (hGc : Continuous G) (hG0 : ∀ r, 0 ≤ G r)
    (hGi : Integrable G) (ℓ : ℝ) :
    ∃ ν : Measure (AddCircle (2 * π)), IsFiniteMeasure ν ∧
      (∀ n : ℤ, ∫ z, fourier n z ∂ν = ((∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) : ℝ) : ℂ)) ∧
      ∀ P : AddCircle (2 * π) → ℝ, Continuous P → (∀ z, P (-z) = P z) →
        ∫ r, G r * P (phase ℓ r) = ∫ z, P z ∂ν := by
  set Gs : ℝ → ℝ := fun r => (G r + G (-r)) / 2 with hGs
  have hGsc : Continuous Gs := (hGc.add (hGc.comp continuous_neg)).div_const 2
  have hGs0 : ∀ r, 0 ≤ Gs r := fun r => by simp only [hGs]; linarith [hG0 r, hG0 (-r)]
  have hGsi : Integrable Gs := (hGi.add hGi.comp_neg).div_const 2
  set g : ℝ → NNReal := fun r => (Gs r).toNNReal with hg
  have hgm : Measurable g := hGsc.measurable.real_toNNReal
  set μ : Measure ℝ := volume.withDensity fun r => (g r : ENNReal) with hμ
  haveI : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hGsi.2
  have hint : ∀ F : ℝ → ℝ, ∫ r, F r ∂μ = ∫ r, Gs r * F r := fun F => by
    rw [hμ, integral_withDensity_eq_integral_smul hgm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [hg, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hGs0 r)]
  have hneg : ∀ F : ℝ → ℝ, ∫ r, F (-r) = ∫ r, F r := fun F => integral_neg_eq_self F volume
  have hcosS : ∀ t : ℝ, ∫ r, Gs r * Real.cos (r * t) = ∫ r, G r * Real.cos (r * t) := fun t => by
    have i1 := integrable_mul_bounded hGi (F := fun r => Real.cos (r * t)) (by fun_prop)
      (C := 1) fun r => Real.abs_cos_le_one _
    have i2 : Integrable fun r => G (-r) * Real.cos (r * t) := by
      refine i1.comp_neg.congr (Filter.Eventually.of_forall fun r => ?_)
      simp only [neg_mul, Real.cos_neg]
    have e : (fun r => Gs r * Real.cos (r * t)) =
        fun r => (G r * Real.cos (r * t) + G (-r) * Real.cos (r * t)) / 2 := by
      ext r; simp only [hGs]; ring
    rw [e, integral_div, integral_add i1 i2]
    have h2 : ∫ r, G (-r) * Real.cos (r * t) = ∫ r, G r * Real.cos (r * t) := by
      rw [← hneg (fun r => G r * Real.cos (r * t))]
      simp only [neg_mul, Real.cos_neg]
    rw [h2]; ring
  have hsinS : ∀ t : ℝ, ∫ r, Gs r * Real.sin (r * t) = 0 := fun t => by
    have h := hneg (fun r => Gs r * Real.sin (r * t))
    have e : (fun r => Gs (-r) * Real.sin (-r * t)) = fun r => -(Gs r * Real.sin (r * t)) := by
      ext r; simp only [hGs, neg_neg, neg_mul, Real.sin_neg]; ring
    simp only [e, integral_neg] at h
    linarith
  have hchar : ∀ t : ℝ, charFun μ t = ((∫ r, G r * Real.cos (r * t) : ℝ) : ℂ) := by
    intro t
    rw [charFun_apply_real, hμ, integral_withDensity_eq_integral_smul hgm]
    have e : ∀ r : ℝ, g r • Complex.exp (↑t * ↑r * I) =
        ((Gs r * Real.cos (r * t) : ℝ) : ℂ) + ((Gs r * Real.sin (r * t) : ℝ) : ℂ) * I := by
      intro r
      rw [NNReal.smul_def, Complex.real_smul, show (↑t * ↑r : ℂ) = ((r * t : ℝ) : ℂ) by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.coe_toNNReal _ (hGs0 r)]
      push_cast; ring
    have ic := integrable_mul_bounded hGsi (F := fun r => Real.cos (r * t)) (by fun_prop)
      (C := 1) fun r => Real.abs_cos_le_one (r * t)
    have is := integrable_mul_bounded hGsi (F := fun r => Real.sin (r * t)) (by fun_prop)
      (C := 1) fun r => Real.abs_sin_le_one (r * t)
    simp_rw [e]
    rw [integral_add ic.ofReal (is.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal, hcosS, hsinS]
    simp
  refine ⟨μ.map (phase ℓ), Measure.isFiniteMeasure_map _ _, fun n => ?_, fun P hP heven => ?_⟩
  · rw [integral_fourier_map_phase, hchar]
  · rw [integral_map (measurable_phase ℓ).aemeasurable hP.aestronglyMeasurable, hint]
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hP.continuousOn
    have hPb : ∀ r, |P (phase ℓ r)| ≤ C := fun r => by
      rw [← Real.norm_eq_abs]; exact hC _ (Set.mem_univ _)
    have hPc : Continuous fun r => P (phase ℓ r) := hP.comp (continuous_phase ℓ)
    have i1 := integrable_mul_bounded hGi hPc hPb
    have hph : ∀ r, phase ℓ (-r) = -phase ℓ r := fun r => by
      simp only [phase, neg_mul]; exact AddCircle.coe_neg (p := 2 * π)
    have i2 : Integrable fun r => G (-r) * P (phase ℓ r) := by
      refine i1.comp_neg.congr (Filter.Eventually.of_forall fun r => ?_)
      simp only [hph, heven]
    have e : (fun r => Gs r * P (phase ℓ r)) =
        fun r => (G r * P (phase ℓ r) + G (-r) * P (phase ℓ r)) / 2 := by
      ext r; simp only [hGs]; ring
    rw [e, integral_div, integral_add i1 i2]
    have h2 : ∫ r, G (-r) * P (phase ℓ r) = ∫ r, G r * P (phase ℓ r) := by
      rw [← hneg (fun r => G r * P (phase ℓ r))]
      simp only [hph, heven]
    rw [h2]; ring

/-- **One free frequency.** If the cosine moments of a nonnegative density `G` vanish at every
`nℓ`, `n ≥ 1`, `n ≠ d`, then for every even continuous observable `P` of the phase
`∫ G P(phase) = (∫G) ∫P + 2c ∫P cos(d·)` with `c = ∫ G(r) cos(dℓr)`. -/
theorem integral_mul_periodic_eq_of_cos_blind_off {G : ℝ → ℝ} (hGc : Continuous G)
    (hG0 : ∀ r, 0 ≤ G r) (hGi : Integrable G) {ℓ : ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hcos : ∀ n : ℕ, 1 ≤ n → n ≠ d → ∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) = 0)
    {P : AddCircle (2 * π) → ℝ} (hP : Continuous P) (heven : ∀ z, P (-z) = P z) :
    ∫ r, G r * P (phase ℓ r) = (∫ r, G r) * (∫ z, P z ∂AddCircle.haarAddCircle) +
      2 * (∫ r, G r * Real.cos (r * ((d : ℝ) * ℓ))) *
        ∫ z, P z * circleCos d z ∂AddCircle.haarAddCircle := by
  obtain ⟨ν, hνf, hνF, hνP⟩ := exists_phase_measure hGc hG0 hGi ℓ
  set c : ℝ := ∫ r, G r * Real.cos (r * ((d : ℝ) * ℓ)) with hc
  set A : ℝ := ∫ r, G r with hA
  have hA0 : 0 ≤ A := integral_nonneg hG0
  have hmoment : ∀ n : ℤ, ∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) =
      (if n = 0 then A else 0) + (if n = d ∨ n = -d then c else 0) := by
    intro n
    have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · obtain ⟨j, hj⟩ : ∃ j : ℕ, n = -(j : ℤ) := ⟨n.natAbs, by omega⟩
      have r_eq : ∀ r : ℝ, Real.cos (r * ((n : ℝ) * ℓ)) = Real.cos (r * ((j : ℝ) * ℓ)) := by
        intro r; rw [hj]; push_cast; rw [show r * (-(j : ℝ) * ℓ) = -(r * ((j : ℝ) * ℓ)) by ring,
          Real.cos_neg]
      simp_rw [r_eq]
      by_cases hjd : j = d
      · subst hjd
        rw [if_neg hn.ne, if_pos (Or.inr hj), zero_add]
      · rw [hcos j (by omega) hjd, if_neg hn.ne, if_neg (by omega), add_zero]
    · simp only [Int.cast_zero, zero_mul, mul_zero, Real.cos_zero, mul_one, if_true]
      rw [if_neg (by omega), add_zero]
    · obtain ⟨j, hj⟩ : ∃ j : ℕ, n = (j : ℤ) := ⟨n.natAbs, by omega⟩
      have r_eq : ∀ r : ℝ, Real.cos (r * ((n : ℝ) * ℓ)) = Real.cos (r * ((j : ℝ) * ℓ)) := by
        intro r; rw [hj]; push_cast; ring_nf
      simp_rw [r_eq]
      by_cases hjd : j = d
      · subst hjd
        rw [if_neg hn.ne', if_pos (Or.inl hj), zero_add]
      · rw [hcos j (by omega) hjd, if_neg hn.ne', if_neg (by omega), add_zero]
  -- the two finite measures on the circle
  set B : ℝ := 2 * |c| with hB
  have hB0 : 0 ≤ B := by positivity
  set D : AddCircle (2 * π) → ℝ := fun z => A + B + 2 * c * circleCos d z with hD
  have hDc : Continuous D := continuous_const.add (continuous_const.mul (continuous_circleCos d))
  have hD0 : ∀ z, 0 ≤ D z := by
    intro z
    have hcz : |circleCos d z| ≤ 1 := by
      unfold circleCos
      exact (Complex.abs_re_le_norm _).trans
        (((fourier (d : ℤ)).norm_coe_le_norm z).trans (fourier_norm _).le)
    have : -(2 * |c|) ≤ 2 * c * circleCos d z := by
      have := abs_le.mp (show |2 * c * circleCos d z| ≤ 2 * |c| by
        rw [abs_mul, abs_mul, abs_two]
        nlinarith [abs_nonneg c, abs_nonneg (circleCos d z)])
      linarith [this.1]
    simp only [hD, hB]; linarith
  set gD : AddCircle (2 * π) → NNReal := fun z => (D z).toNNReal with hgD
  have hgDm : Measurable gD := hDc.measurable.real_toNNReal
  have hDi : Integrable D (AddCircle.haarAddCircle (T := 2 * π)) :=
    (BoundedContinuousFunction.mkOfCompact ⟨D, hDc⟩).integrable _
  set ν₁ : Measure (AddCircle (2 * π)) :=
    ν + ENNReal.ofReal B • AddCircle.haarAddCircle with hν₁
  set ν₂ : Measure (AddCircle (2 * π)) :=
    AddCircle.haarAddCircle.withDensity fun z => (gD z : ENNReal) with hν₂
  haveI : IsFiniteMeasure (ENNReal.ofReal B • AddCircle.haarAddCircle (T := 2 * π)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure ν₁ := by rw [hν₁]; infer_instance
  haveI : IsFiniteMeasure ν₂ := isFiniteMeasure_withDensity_ofReal hDi.2
  have hintν₂ : ∀ F : AddCircle (2 * π) → ℂ, ∫ z, F z ∂ν₂ = ∫ z, (D z : ℂ) * F z ∂AddCircle.haarAddCircle :=
    fun F => by
      rw [hν₂, integral_withDensity_eq_integral_smul hgDm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hgD, NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal _ (hD0 z)]
  have hfi : ∀ (n : ℤ) (ρ : Measure (AddCircle (2 * π))) [IsFiniteMeasure ρ],
      Integrable (fun z => fourier n z) ρ := fun n ρ _ =>
    (BoundedContinuousFunction.mkOfCompact (fourier n)).integrable ρ
  have heq : ν₁ = ν₂ := by
    apply GaloisForLFunctions.HTGeometry.addCircle_measure_eq_of_fourier_integral_eq
    intro n
    rw [hν₁, integral_add_measure (hfi n _) (hfi n _), integral_smul_measure,
      hνF, hmoment, integral_fourier_haar, hintν₂]
    have e : ∀ z : AddCircle (2 * π), (D z : ℂ) * fourier n z =
        ((A + B : ℝ) : ℂ) * fourier n z + ((2 * c : ℝ) : ℂ) * (fourier n z * (circleCos d z : ℂ)) := by
      intro z; simp only [hD]; push_cast; ring
    simp_rw [e]
    have j1 : Integrable (fun z => ((A + B : ℝ) : ℂ) * fourier n z)
        (AddCircle.haarAddCircle (T := 2 * π)) := (hfi n _).const_mul _
    have j2 : Integrable (fun z => ((2 * c : ℝ) : ℂ) * (fourier n z * (circleCos d z : ℂ)))
        (AddCircle.haarAddCircle (T := 2 * π)) := by
      refine Integrable.const_mul ?_ _
      exact (BoundedContinuousFunction.mkOfCompact ⟨fun z => fourier n z * (circleCos d z : ℂ),
        (fourier n).continuous.mul (Complex.continuous_ofReal.comp (continuous_circleCos d))⟩).integrable _
    rw [integral_add j1 j2, integral_const_mul, integral_const_mul, integral_fourier_haar,
      integral_fourier_mul_circleCos, ENNReal.toReal_ofReal hB0]
    simp only [Complex.real_smul]
    have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    by_cases h0 : n = 0
    · subst h0
      simp only [if_true, zero_add, zero_sub, neg_eq_zero, hdz, if_false]
      have : ¬ ((0 : ℤ) = d ∨ (0 : ℤ) = -d) := by omega
      rw [if_neg this]
      push_cast; ring
    · rw [if_neg h0, if_neg h0]
      by_cases hpm : n = d ∨ n = -d
      · rw [if_pos hpm]
        rcases hpm with h | h
        · rw [if_neg (by omega), if_pos (by omega)]; push_cast; ring
        · rw [if_pos (by omega), if_neg (by omega)]; push_cast; ring
      · rw [if_neg hpm, if_neg (by omega), if_neg (by omega)]; push_cast; ring
  -- read off the observable `P`
  have hPi : ∀ (ρ : Measure (AddCircle (2 * π))) [IsFiniteMeasure ρ], Integrable P ρ := fun ρ _ =>
    (BoundedContinuousFunction.mkOfCompact ⟨P, hP⟩).integrable ρ
  have hPeq : ∫ z, P z ∂ν₁ = ∫ z, P z ∂ν₂ := by rw [heq]
  rw [hν₁, integral_add_measure (hPi _) (hPi _), integral_smul_measure,
    ENNReal.toReal_ofReal hB0, smul_eq_mul, ← hνP P hP heven] at hPeq
  have hν₂P : ∫ z, P z ∂ν₂ = ∫ z, D z * P z ∂AddCircle.haarAddCircle := by
    rw [hν₂, integral_withDensity_eq_integral_smul hgDm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hgD, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hD0 z)]
  rw [hν₂P] at hPeq
  have hDP : ∫ z, D z * P z ∂AddCircle.haarAddCircle = (A + B) * ∫ z, P z ∂AddCircle.haarAddCircle +
      2 * c * ∫ z, P z * circleCos d z ∂AddCircle.haarAddCircle := by
    have k1 : Integrable (fun z => (A + B) * P z) (AddCircle.haarAddCircle (T := 2 * π)) :=
      (hPi _).const_mul _
    have k2 : Integrable (fun z => 2 * c * (P z * circleCos d z))
        (AddCircle.haarAddCircle (T := 2 * π)) :=
      ((BoundedContinuousFunction.mkOfCompact ⟨fun z => P z * circleCos d z,
        hP.mul (continuous_circleCos d)⟩).integrable _).const_mul _
    have e : (fun z => D z * P z) = fun z => (A + B) * P z + 2 * c * (P z * circleCos d z) := by
      ext z; simp only [hD]; ring
    rw [e, integral_add k1 k2, integral_const_mul, integral_const_mul]
  rw [hDP] at hPeq
  linarith

/-- **The free moment is at most half the mass.** Positivity of the phase measure
`(∫G + 2c cos(dz)) dz/2π` forces `2|c| ≤ ∫G`. -/
theorem two_mul_abs_cos_moment_le_of_cos_blind_off {G : ℝ → ℝ} (hGc : Continuous G)
    (hG0 : ∀ r, 0 ≤ G r) (hGi : Integrable G) {ℓ : ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hcos : ∀ n : ℕ, 1 ≤ n → n ≠ d → ∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) = 0) :
    2 * |∫ r, G r * Real.cos (r * ((d : ℝ) * ℓ))| ≤ ∫ r, G r := by
  set c : ℝ := ∫ r, G r * Real.cos (r * ((d : ℝ) * ℓ)) with hc
  set A : ℝ := ∫ r, G r with hA
  set D₀ : AddCircle (2 * π) → ℝ := fun z => A + 2 * c * circleCos d z with hD₀
  have hD₀c : Continuous D₀ := continuous_const.add (continuous_const.mul (continuous_circleCos d))
  set P : AddCircle (2 * π) → ℝ := fun z => max 0 (-D₀ z) with hPdef
  have hPc : Continuous P := continuous_const.max hD₀c.neg
  have hPeven : ∀ z, P (-z) = P z := fun z => by simp only [hPdef, hD₀, circleCos_neg]
  have hid := integral_mul_periodic_eq_of_cos_blind_off hGc hG0 hGi hd hcos hPc hPeven
  have hL : 0 ≤ ∫ r, G r * P (phase ℓ r) :=
    integral_nonneg fun r => mul_nonneg (hG0 r) (le_max_left _ _)
  have hPi : Integrable P (AddCircle.haarAddCircle (T := 2 * π)) :=
    (BoundedContinuousFunction.mkOfCompact ⟨P, hPc⟩).integrable _
  have hPci : Integrable (fun z => P z * circleCos d z) (AddCircle.haarAddCircle (T := 2 * π)) :=
    (BoundedContinuousFunction.mkOfCompact ⟨fun z => P z * circleCos d z,
      hPc.mul (continuous_circleCos d)⟩).integrable _
  have hsqi : Integrable (fun z => P z ^ 2) (AddCircle.haarAddCircle (T := 2 * π)) :=
    (BoundedContinuousFunction.mkOfCompact ⟨fun z => P z ^ 2, (continuous_pow 2).comp hPc⟩).integrable _
  have hR : A * (∫ z, P z ∂AddCircle.haarAddCircle) +
      2 * c * (∫ z, P z * circleCos d z ∂AddCircle.haarAddCircle) =
      -∫ z, P z ^ 2 ∂AddCircle.haarAddCircle := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hPi.const_mul _)
      (hPci.const_mul _), ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hPdef, hD₀]
    rcases le_total 0 (A + 2 * c * circleCos d z) with h | h
    · rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith)]; ring
  have hsq : ∫ z, P z ^ 2 ∂AddCircle.haarAddCircle = 0 :=
    le_antisymm (by linarith) (integral_nonneg fun z => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (P z)) hsqi).mp hsq
  have hall := (Continuous.ae_eq_iff_eq (AddCircle.haarAddCircle (T := 2 * π))
    ((continuous_pow 2).comp hPc) continuous_const).mp hae
  have hD₀nn : ∀ z, 0 ≤ D₀ z := by
    intro z
    have h : P z ^ 2 = 0 := congrFun hall z
    have hP0 : P z = 0 := (pow_eq_zero_iff two_ne_zero).mp h
    have : -D₀ z ≤ P z := le_max_right _ _
    linarith
  have h1 : 0 ≤ A + 2 * c * circleCos d 0 := hD₀nn 0
  have h2 : 0 ≤ A + 2 * c * circleCos d ((π / d : ℝ) : AddCircle (2 * π)) := hD₀nn _
  rw [circleCos_zero] at h1
  rw [circleCos_pi_div hd] at h2
  cases abs_cases c <;> linarith

/-! ### 3. The punctured power grid -/

/-- The powers `q^j`, `j ≥ 1`, except `q^d`. -/
abbrev puncturedPowerNodes (q d : ℕ) : Set ℕ := {n | ∃ j : ℕ, 1 ≤ j ∧ j ≠ d ∧ n = q ^ j}

/-- The `d`-th cosine coefficient `φ_d = ∫ γ(‖z‖/ℓ) cos(dz) dz/2π` of the folded symbol. -/
def foldedCosineCoefficient (q d : ℕ) : ℝ :=
  ∫ z, foldedSymbol (Real.log q) z * circleCos d z ∂AddCircle.haarAddCircle

/-- Node values of a combination at the powers of `q` are cosine moments of its spectral
density at the multiples of `log q`. -/
theorem integral_combinationSpectralDensity_mul_cos_pow (c : WeilTestFn →₀ ℝ) {q : ℕ}
    (hq : 2 ≤ q) {j : ℕ} (hj : 1 ≤ j) :
    ∫ r, combinationSpectralDensity c r * Real.cos (r * ((j : ℝ) * Real.log q)) =
      π * Real.sqrt ((q ^ j : ℕ) : ℝ) *
        nodeVector c ⟨q ^ j, le_trans hq (Nat.le_self_pow (by omega) q)⟩ := by
  have hlog : (j : ℝ) * Real.log q = Real.log ((q ^ j : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hlog, integral_combinationSpectralDensity_mul_cos_log]

/-- **Lower bound.** A nonnegative combination blind at every `q^j`, `j ≠ d`, has archimedean
part without the pole at least `(m_q − |φ_d|)` times its mass. -/
theorem symbolPeriodMean_sub_mul_massOf_le_of_punctured {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d)
    (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f) (hb : BlindOn (puncturedPowerNodes q d) c) :
    (symbolPeriodMean q - |foldedCosineCoefficient q d|) * massOf c ≤ nodeArchOnly c := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  set G := combinationSpectralDensity c with hGdef
  have hGc := continuous_combinationSpectralDensity c
  have hG0 := combinationSpectralDensity_nonneg hc
  have hGi := integrable_combinationSpectralDensity c
  have hcos : ∀ n : ℕ, 1 ≤ n → n ≠ d →
      ∫ r, G r * Real.cos (r * ((n : ℝ) * Real.log q)) = 0 := by
    intro n hn hnd
    rw [integral_combinationSpectralDensity_mul_cos_pow c hq hn,
      hb _ ⟨n, hn, hnd, rfl⟩, mul_zero]
  have hid := integral_mul_periodic_eq_of_cos_blind_off hGc hG0 hGi hd hcos
    (continuous_foldedSymbol (Real.log q)) (foldedSymbol_neg (Real.log q))
  rw [integral_foldedSymbol hℓ] at hid
  have hpos := two_mul_abs_cos_moment_le_of_cos_blind_off hGc hG0 hGi hd hcos
  have hGf : Integrable fun r => G r * foldedSymbol (Real.log q) (phase (Real.log q) r) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_foldedSymbol (Real.log q)).continuousOn
    exact integrable_mul_bounded hGi ((continuous_foldedSymbol _).comp (continuous_phase _))
      (C := C) fun r => by rw [← Real.norm_eq_abs]; exact hC _ (Set.mem_univ _)
  have hmono := integral_mono hGf (integrable_combinationSpectralDensity_mul_gammaBracket c)
    fun r => mul_le_mul_of_nonneg_left (foldedSymbol_phase_le hℓ r) (hG0 r)
  rw [hid, integral_combinationSpectralDensity_mul_gammaBracket,
    integral_combinationSpectralDensity] at hmono
  rw [integral_combinationSpectralDensity] at hpos
  set m : ℝ := Real.log q / π * ∫ v in (0 : ℝ)..π / Real.log q, EF.gammaBracket v with hm
  set φ : ℝ := foldedCosineCoefficient q d with hφ
  set cc : ℝ := ∫ r, G r * Real.cos (r * ((d : ℝ) * Real.log q)) with hcc
  have hsm : symbolPeriodMean q = m := rfl
  have hφ' : ∫ z, foldedSymbol (Real.log q) z * circleCos d z ∂AddCircle.haarAddCircle = φ := rfl
  rw [hφ'] at hmono
  rw [hsm]
  have hpi : 0 < 2 * π := by positivity
  have hcφ : -(2 * |cc| * |φ|) ≤ 2 * cc * φ := by
    have := neg_abs_le (2 * cc * φ)
    rwa [abs_mul, abs_mul, abs_two] at this
  have hb2 : 2 * |cc| * |φ| ≤ 2 * π * massOf c * |φ| :=
    mul_le_mul_of_nonneg_right hpos (abs_nonneg φ)
  nlinarith

/-! ### 4. Translated pairs -/

/-- The translated pair `f + s f(· − τ)`. -/
def translatedPairTest (f : WeilTestFn) (τ s : ℝ) : WeilTestFn :=
  ⟨fun u => f.1 u + (s : ℂ) * f.1 (u - τ),
    f.2.1.add (contDiff_const.mul (f.2.1.comp (contDiff_id.sub contDiff_const))),
    f.2.2.add ((f.2.2.comp_homeomorph (Homeomorph.subRight τ)).mul_left)⟩

/-- `|1 + s e^{iθ}|² = 2 + 2s cos θ` for `s = ±1`, so the pair multiplies `|f̂|²` by
`2 + 2s cos(rτ)`. -/
theorem normSq_paperFT_translatedPairTest (f : WeilTestFn) (τ : ℝ) {s : ℝ} (hs : s ^ 2 = 1)
    (r : ℝ) :
    ‖paperFT (translatedPairTest f τ s).1 r‖ ^ 2 =
      (2 + 2 * s * Real.cos (r * τ)) * ‖paperFT f.1 r‖ ^ 2 := by
  have hi : ∀ g : ℝ → ℂ, Continuous g → HasCompactSupport g →
      Integrable fun u : ℝ => g u * Complex.exp (I * (r : ℂ) * u) := fun g hg hgc =>
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hshift : HasCompactSupport fun u => f.1 (u - τ) :=
    f.2.2.comp_homeomorph (Homeomorph.subRight τ)
  have hsplit : paperFT (translatedPairTest f τ s).1 r =
      paperFT f.1 r + (s : ℂ) * paperFT (fun u => f.1 (u - τ)) r := by
    change ∫ u, (f.1 u + (s : ℂ) * f.1 (u - τ)) * Complex.exp (I * (r : ℂ) * u) = _
    have e : (fun u : ℝ => (f.1 u + (s : ℂ) * f.1 (u - τ)) * Complex.exp (I * (r : ℂ) * u)) =
        fun u => f.1 u * Complex.exp (I * (r : ℂ) * u) +
          (s : ℂ) * (f.1 (u - τ) * Complex.exp (I * (r : ℂ) * u)) := by
      ext u; ring
    rw [e, integral_add (hi f.1 f.2.1.continuous f.2.2)
      ((hi (fun u => f.1 (u - τ)) (f.2.1.continuous.comp (continuous_id.sub continuous_const))
        hshift).const_mul _), integral_const_mul]
    rfl
  rw [hsplit, _root_.RHTower.paperFT_comp_sub]
  rw [show paperFT f.1 r + (s : ℂ) * (Complex.exp (I * (r : ℂ) * τ) * paperFT f.1 r) =
    (1 + (s : ℂ) * Complex.exp (I * (r : ℂ) * τ)) * paperFT f.1 r by ring, norm_mul, mul_pow]
  · congr 1
    have e : (1 : ℂ) + (s : ℂ) * Complex.exp (I * (r : ℂ) * τ) =
        ((1 + s * Real.cos (r * τ) : ℝ) : ℂ) + ((s * Real.sin (r * τ) : ℝ) : ℂ) * I := by
      rw [show I * (r : ℂ) * (τ : ℂ) = ((r * τ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast; ring
    rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
    have := Real.sin_sq_add_cos_sq (r * τ)
    nlinarith [hs]

/-- Every test of `c` replaced by its translated pair. -/
def translatedPairCombination (c : WeilTestFn →₀ ℝ) (τ s : ℝ) : WeilTestFn →₀ ℝ :=
  ∑ f ∈ c.support, Finsupp.single (translatedPairTest f τ s) (c f)

theorem translatedPairCombination_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (τ s : ℝ)
    (g : WeilTestFn) : 0 ≤ translatedPairCombination c τ s g := by
  classical
  rw [translatedPairCombination, Finsupp.finsetSum_apply]
  refine Finset.sum_nonneg fun f _ => ?_
  rw [Finsupp.single_apply]
  split_ifs
  · exact hc f
  · exact le_rfl

theorem linearCombination_translatedPairCombination (φ : WeilTestFn → ℝ) (c : WeilTestFn →₀ ℝ)
    (τ s : ℝ) :
    linearCombination ℝ φ (translatedPairCombination c τ s) =
      ∑ f ∈ c.support, c f * φ (translatedPairTest f τ s) := by
  simp only [translatedPairCombination, map_sum, linearCombination_single, smul_eq_mul]

/-- The spectral density of the translated pairs is `(2 + 2s cos(rτ)) G_c`, read through any
integrable observable. -/
theorem sum_integral_translatedPair (c : WeilTestFn →₀ ℝ) (τ : ℝ) {s : ℝ} (hs : s ^ 2 = 1)
    {F : ℝ → ℝ} (hF : ∀ f : WeilTestFn, Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * F r) :
    ∑ f ∈ c.support, c f * ∫ r : ℝ, ‖paperFT (translatedPairTest f τ s).1 r‖ ^ 2 * F r =
      ∫ r, combinationSpectralDensity c r * ((2 + 2 * s * Real.cos (r * τ)) * F r) := by
  have hi : ∀ f : WeilTestFn,
      Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * ((2 + 2 * s * Real.cos (r * τ)) * F r) := by
    intro f
    have h1 := (hF f).const_mul 2
    have h2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * F r * Real.cos (r * τ) :=
      (hF f).mul_bdd (c := 1)
        (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun r => by
          rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    refine ((h1.add (h2.const_mul (2 * s)))).congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.add_apply]; ring
  rw [combinationSpectralDensity_mul_eq, integral_finsetSum _ fun f _ => (hi f).const_mul _]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [normSq_paperFT_translatedPairTest f τ hs r]
  ring

/-! ### 5. The upper bound -/

/-- **Upper bound.** For every `N ≥ 1` there is a nonnegative combination blind at every `q^j`,
`j ≠ d`, whose archimedean part without the pole is at most `(m_q − |φ_d| + 2E/N)` times its
positive mass. -/
theorem exists_blindOn_punctured_archOnly_le {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N : ℕ, 1 ≤ N → ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      BlindOn (puncturedPowerNodes q d) c ∧ 0 < massOf c ∧
      nodeArchOnly c ≤
        (symbolPeriodMean q - |foldedCosineCoefficient q d| + 2 * E / N) * massOf c := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  obtain ⟨E, hE, hup⟩ := exists_blindOn_powers_archOnly_le hq
  refine ⟨E, hE, fun N hN => ?_⟩
  obtain ⟨c₇, hc₇, hb₇, hm₇, ha₇⟩ := hup N hN
  obtain ⟨G, hG⟩ : ∃ G, G = combinationSpectralDensity c₇ := ⟨_, rfl⟩
  have hG0 : ∀ r, 0 ≤ G r := hG ▸ combinationSpectralDensity_nonneg hc₇
  have hGi : Integrable G := hG ▸ integrable_combinationSpectralDensity c₇
  have hGm : ∫ r, G r = 2 * π * massOf c₇ := hG ▸ integral_combinationSpectralDensity c₇
  have hGa : ∫ r, G r * EF.gammaBracket r = 2 * π * nodeArchOnly c₇ :=
    hG ▸ integral_combinationSpectralDensity_mul_gammaBracket c₇
  have iγ : Integrable fun r => G r * EF.gammaBracket r :=
    hG ▸ integrable_combinationSpectralDensity_mul_gammaBracket c₇
  set φ : ℝ := foldedCosineCoefficient q d with hφ
  set s : ℝ := if 0 ≤ φ then -1 else 1 with hsdef
  have hs : s ^ 2 = 1 := by rw [hsdef]; split_ifs <;> norm_num
  have hsabs : |s| = 1 := by rw [hsdef]; split_ifs <;> norm_num
  have hsφ : s * φ = -|φ| := by
    rw [hsdef]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have hmom : ∀ j : ℕ, 1 ≤ j → ∫ r, G r * Real.cos (r * ((j : ℝ) * Real.log q)) = 0 := by
    intro j hj
    rw [hG, integral_combinationSpectralDensity_mul_cos_pow c₇ hq hj, hb₇ _ ⟨j, hj, rfl⟩,
      mul_zero]
  have hmomz : ∀ m : ℤ, m ≠ 0 → ∫ r, G r * Real.cos (r * ((m : ℝ) * Real.log q)) = 0 := by
    intro m hm
    have e : ∀ r : ℝ, Real.cos (r * ((m : ℝ) * Real.log q)) =
        Real.cos (r * ((m.natAbs : ℝ) * Real.log q)) := by
      intro r
      rw [Nat.cast_natAbs, Int.cast_abs]
      rcases abs_choice (m : ℝ) with h | h <;> rw [h]
      rw [show r * (-(m : ℝ) * Real.log q) = -(r * ((m : ℝ) * Real.log q)) by ring, Real.cos_neg]
    simp_rw [e]
    exact hmom _ (by omega)
  have ic : ∀ t : ℝ, Integrable fun r => G r * Real.cos (r * t) := fun t =>
    integrable_mul_bounded hGi (by fun_prop) (C := 1) fun r => Real.abs_cos_le_one _
  set τ : ℝ := (d : ℝ) * Real.log q with hτ
  set c' := translatedPairCombination c₇ τ s with hc'
  have hc'0 : ∀ g, 0 ≤ c' g := translatedPairCombination_nonneg hc₇ τ s
  have hpi : 0 < π := Real.pi_pos
  -- the mass doubles
  have hmass : massOf c' = 2 * massOf c₇ := by
    rw [massOf_eq_linearCombination, linearCombination_translatedPairCombination]
    have e : ∀ f : WeilTestFn, ∫ x, ‖(translatedPairTest f τ s).1 x‖ ^ 2 =
        (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT (translatedPairTest f τ s).1 r‖ ^ 2 * 1 := by
      intro f
      simp only [mul_one]
      rw [integral_normSq_paperFT_eq]
      field_simp
    simp_rw [e, ← mul_assoc, mul_comm _ (1 / (2 * π)), mul_assoc, ← Finset.mul_sum]
    rw [sum_integral_translatedPair c₇ τ hs (F := fun _ => 1)
      (fun f => by simpa using integrable_normSq_paperFT f), ← hG]
    have hsplit : ∫ r, G r * ((2 + 2 * s * Real.cos (r * τ)) * 1) =
        2 * (∫ r, G r) + 2 * s * ∫ r, G r * Real.cos (r * τ) := by
      have e : (fun r => G r * ((2 + 2 * s * Real.cos (r * τ)) * 1)) =
          fun r => 2 * G r + 2 * s * (G r * Real.cos (r * τ)) := by ext r; ring
      rw [e, integral_add (hGi.const_mul _) ((ic τ).const_mul _), integral_const_mul,
        integral_const_mul]
    rw [hsplit, hτ, hmom d hd, hGm]
    field_simp
    ring
  -- blindness off `q^d`
  have hblind : BlindOn (puncturedPowerNodes q d) c' := by
    rintro ⟨n, hn2⟩ ⟨j, hj1, hjd, rfl⟩
    rw [nodeVector_apply_eq_linearCombination, linearCombination_translatedPairCombination]
    change ∑ f ∈ c₇.support, c₇ f * logValue (translatedPairTest f τ s).1 (q ^ j) = 0
    have hqj1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ (by omega)
    have e : ∀ f : WeilTestFn, logValue (translatedPairTest f τ s).1 (q ^ j) =
        (1 / (π * Real.sqrt ((q ^ j : ℕ) : ℝ))) *
          ∫ r : ℝ, ‖paperFT (translatedPairTest f τ s).1 r‖ ^ 2 *
            Real.cos (r * Real.log ((q ^ j : ℕ) : ℝ)) := by
      intro f
      rw [integral_normSq_paperFT_mul_cos_log _ hqj1]
      have : 0 < Real.sqrt ((q ^ j : ℕ) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hqj1)
      field_simp
    simp only [e]
    simp_rw [← mul_assoc, mul_comm _ (1 / (π * Real.sqrt ((q ^ j : ℕ) : ℝ))), mul_assoc,
      ← Finset.mul_sum]
    rw [sum_integral_translatedPair c₇ τ hs
      (F := fun r => Real.cos (r * Real.log ((q ^ j : ℕ) : ℝ))) (fun f => by
        obtain ⟨a, ha⟩ := exists_Icc_support f
        exact integrable_normSq_paperFT_mul_cos f.2.1 ha _), ← hG]
    have hlog : Real.log ((q ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log q := by
      rw [Nat.cast_pow, Real.log_pow]
    rw [hlog]
    have hprod : ∀ r : ℝ, G r * ((2 + 2 * s * Real.cos (r * τ)) *
          Real.cos (r * ((j : ℝ) * Real.log q))) =
        2 * (G r * Real.cos (r * ((j : ℝ) * Real.log q))) +
          s * (G r * Real.cos (r * ((((j : ℤ) + d : ℤ) : ℝ) * Real.log q))) +
            s * (G r * Real.cos (r * ((((j : ℤ) - d : ℤ) : ℝ) * Real.log q))) := by
      intro r
      push_cast
      rw [hτ, show r * (((j : ℝ) + d) * Real.log q) =
          r * ((j : ℝ) * Real.log q) + r * ((d : ℝ) * Real.log q) by ring,
        show r * (((j : ℝ) - d) * Real.log q) =
          r * ((j : ℝ) * Real.log q) - r * ((d : ℝ) * Real.log q) by ring,
        Real.cos_add, Real.cos_sub]
      ring
    simp_rw [hprod]
    have iA : Integrable fun r => 2 * (G r * Real.cos (r * ((j : ℝ) * Real.log q))) +
        s * (G r * Real.cos (r * ((((j : ℤ) + d : ℤ) : ℝ) * Real.log q))) :=
      ((ic _).const_mul _).add ((ic _).const_mul _)
    rw [integral_add iA ((ic _).const_mul _),
      integral_add ((ic _).const_mul _) ((ic _).const_mul _), integral_const_mul,
      integral_const_mul, integral_const_mul, hmom j hj1, hmomz _ (by omega),
      hmomz _ (by omega)]
    ring
  -- the symbol
  have hcos_int : Integrable fun r => G r * (Real.cos (r * τ) * EF.gammaBracket r) := by
    refine (iγ.mul_bdd (c := 1)
      (show Continuous fun r : ℝ => Real.cos (r * τ) by fun_prop).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one (r * τ))).congr
      (Filter.Eventually.of_forall fun r => ?_)
    simp only; ring
  set X : ℝ := ∫ r, G r * (Real.cos (r * τ) * EF.gammaBracket r) with hX
  have harch : nodeArchOnly c' = 2 * nodeArchOnly c₇ + (s / π) * X := by
    rw [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, linearCombination_translatedPairCombination,
      linearCombination_translatedPairCombination, ← Finset.sum_sub_distrib]
    have e : ∀ f : WeilTestFn, c₇ f * weilArchRe (EF.weilTest (translatedPairTest f τ s).1
          (translatedPairTest f τ s).1) - c₇ f * (weilPoleTerm (EF.weilTest
          (translatedPairTest f τ s).1 (translatedPairTest f τ s).1)).re =
        (1 / (2 * π)) * (c₇ f * ∫ r : ℝ, ‖paperFT (translatedPairTest f τ s).1 r‖ ^ 2 *
          EF.gammaBracket r) := by
      intro f
      rw [← mul_sub, weilArchRe_sub_pole_eq]; ring
    simp_rw [e, ← Finset.mul_sum]
    rw [sum_integral_translatedPair c₇ τ hs integrable_normSq_paperFT_mul_gammaBracket, ← hG]
    have hsplit : ∫ r, G r * ((2 + 2 * s * Real.cos (r * τ)) * EF.gammaBracket r) =
        2 * (∫ r, G r * EF.gammaBracket r) + 2 * s * X := by
      have e : (fun r => G r * ((2 + 2 * s * Real.cos (r * τ)) * EF.gammaBracket r)) =
          fun r => 2 * (G r * EF.gammaBracket r) +
            2 * s * (G r * (Real.cos (r * τ) * EF.gammaBracket r)) := by ext r; ring
      rw [e, integral_add (iγ.const_mul _) (hcos_int.const_mul _), integral_const_mul,
        integral_const_mul]
    rw [hsplit, hGa]
    field_simp
  -- the folded parts
  have hP1c : Continuous fun z : AddCircle (2 * π) =>
      foldedSymbol (Real.log q) z * circleCos d z :=
    (continuous_foldedSymbol _).mul (continuous_circleCos d)
  have hper1 := integral_combinationSpectralDensity_mul_periodic hq hc₇ hb₇ hP1c
    (fun z => by simp only [foldedSymbol_neg, circleCos_neg])
  have hper0 := integral_combinationSpectralDensity_mul_periodic hq hc₇ hb₇
    (continuous_foldedSymbol (Real.log q)) (foldedSymbol_neg (Real.log q))
  rw [integral_foldedSymbol hℓ, ← hG] at hper0
  rw [← hG] at hper1
  have hφdef : ∫ z, foldedSymbol (Real.log q) z * circleCos d z ∂AddCircle.haarAddCircle = φ :=
    rfl
  rw [hφdef] at hper1
  obtain ⟨CF, hCF⟩ : ∃ C : ℝ, ∀ r, |foldedSymbol (Real.log q) (phase (Real.log q) r)| ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_foldedSymbol (Real.log q)).continuousOn
    exact ⟨C, fun r => by rw [← Real.norm_eq_abs]; exact hC _ (Set.mem_univ _)⟩
  have iF : Integrable fun r => G r * foldedSymbol (Real.log q) (phase (Real.log q) r) :=
    integrable_mul_bounded hGi ((continuous_foldedSymbol _).comp (continuous_phase _)) hCF
  have hcosph : ∀ r, circleCos d (phase (Real.log q) r) = Real.cos (r * τ) := fun r =>
    circleCos_phase d _ r
  have iFc : Integrable fun r =>
      G r * (foldedSymbol (Real.log q) (phase (Real.log q) r) * Real.cos (r * τ)) :=
    integrable_mul_bounded hGi (((continuous_foldedSymbol _).comp (continuous_phase _)).mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const))) (C := CF) fun r => by
      rw [abs_mul]
      have h1 := hCF r
      have h2 := Real.abs_cos_le_one (r * τ)
      nlinarith [abs_nonneg (foldedSymbol (Real.log q) (phase (Real.log q) r)),
        abs_nonneg (Real.cos (r * τ))]
  simp_rw [hcosph] at hper1
  -- `∫ G cos(rτ) γ` is `φ ∫G` up to the bathtub defect
  have hdefect : |X - 2 * π * massOf c₇ * φ| ≤
      2 * π * nodeArchOnly c₇ - 2 * π * massOf c₇ * symbolPeriodMean q := by
    rw [← hGm, ← hGa, hX]
    have hsm : symbolPeriodMean q =
        Real.log q / π * ∫ v in (0 : ℝ)..π / Real.log q, EF.gammaBracket v := rfl
    rw [← hper1, ← integral_sub hcos_int iFc, hsm, ← hper0, ← integral_sub iγ iF]
    refine (abs_integral_le_integral_abs).trans (integral_mono ((hcos_int.sub iFc).abs)
      (iγ.sub iF) fun r => ?_)
    have hle := foldedSymbol_phase_le hℓ r
    have hd0 : 0 ≤ EF.gammaBracket r - foldedSymbol (Real.log q) (phase (Real.log q) r) := by
      linarith
    have e : G r * (Real.cos (r * τ) * EF.gammaBracket r) -
        G r * (foldedSymbol (Real.log q) (phase (Real.log q) r) * Real.cos (r * τ)) =
        G r * Real.cos (r * τ) * (EF.gammaBracket r -
          foldedSymbol (Real.log q) (phase (Real.log q) r)) := by ring
    simp only
    rw [e, abs_mul, abs_mul, abs_of_nonneg (hG0 r), abs_of_nonneg hd0]
    have h3 : G r * |Real.cos (r * τ)| * (EF.gammaBracket r -
          foldedSymbol (Real.log q) (phase (Real.log q) r)) ≤
        G r * 1 * (EF.gammaBracket r - foldedSymbol (Real.log q) (phase (Real.log q) r)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hG0 r)) hd0
    linarith
  have hsX : s * X ≤ s * (2 * π * massOf c₇ * φ) +
      (2 * π * nodeArchOnly c₇ - 2 * π * massOf c₇ * symbolPeriodMean q) := by
    have h1 : s * (X - 2 * π * massOf c₇ * φ) ≤ |X - 2 * π * massOf c₇ * φ| := by
      have := le_abs_self (s * (X - 2 * π * massOf c₇ * φ))
      rwa [abs_mul, hsabs, one_mul] at this
    nlinarith
  have hfin : nodeArchOnly c' ≤ 4 * nodeArchOnly c₇ - 2 * massOf c₇ * symbolPeriodMean q +
      2 * massOf c₇ * (s * φ) := by
    rw [harch]
    have h1 : s / π * X = (s * X) / π := by ring
    have : (s * X) / π ≤ (s * (2 * π * massOf c₇ * φ) +
        (2 * π * nodeArchOnly c₇ - 2 * π * massOf c₇ * symbolPeriodMean q)) / π :=
      div_le_div_of_nonneg_right hsX hpi.le
    have e2 : (s * (2 * π * massOf c₇ * φ) +
        (2 * π * nodeArchOnly c₇ - 2 * π * massOf c₇ * symbolPeriodMean q)) / π =
        2 * massOf c₇ * (s * φ) + 2 * nodeArchOnly c₇ - 2 * massOf c₇ * symbolPeriodMean q := by
      field_simp; ring
    rw [h1]
    linarith
  refine ⟨c', hc'0, hblind, by rw [hmass]; positivity, ?_⟩
  rw [hmass]
  rw [hsφ] at hfin
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h7 : nodeArchOnly c₇ ≤ (symbolPeriodMean q + E / N) * massOf c₇ := ha₇
  have e3 : (symbolPeriodMean q - |φ| + 2 * E / N) * (2 * massOf c₇) =
      2 * massOf c₇ * symbolPeriodMean q - 2 * massOf c₇ * |φ| + 4 * (E / N) * massOf c₇ := by
    ring
  rw [e3]
  nlinarith

/-! ### 6. The removal law -/

theorem blindSymbolSlackOn_punctured {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) :
    BlindSymbolSlackOn (puncturedPowerNodes q d)
      (-(symbolPeriodMean q - |foldedCosineCoefficient q d|)) := fun c hc hb => by
  have := symbolPeriodMean_sub_mul_massOf_le_of_punctured hq hd c hc hb
  linarith

theorem le_of_blindSymbolSlackOn_punctured {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) {M : ℝ}
    (h : BlindSymbolSlackOn (puncturedPowerNodes q d) M) :
    -(symbolPeriodMean q - |foldedCosineCoefficient q d|) ≤ M := by
  by_contra hlt
  rw [not_le] at hlt
  set g : ℝ := -(symbolPeriodMean q - |foldedCosineCoefficient q d|) - M with hg
  have hgpos : 0 < g := by linarith
  obtain ⟨E, hE, hup⟩ := exists_blindOn_punctured_archOnly_le hq hd
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * E / g)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hN1 : 1 ≤ N := by exact_mod_cast hN0
  obtain ⟨c, hc, hb, hm, ha⟩ := hup N hN1
  have hEN : 2 * E / N ≤ g / 2 := by
    rw [div_le_iff₀ hN0]
    rw [div_lt_iff₀ hgpos] at hN
    linarith
  have h1 := h c hc hb
  have h2 : nodeArchOnly c + M * massOf c ≤ (-(g / 2)) * massOf c := by
    have := mul_le_mul_of_nonneg_right
      (show symbolPeriodMean q - |foldedCosineCoefficient q d| + 2 * E / N + M ≤ -(g / 2) by
        linarith) hm.le
    nlinarith
  nlinarith

/-- **The removal law.** The exact blind symbol slack on the powers of `q` without `q^d` is
`−(m_q − |φ_d|)`: the node `q^d` is worth exactly `|φ_d|`. -/
theorem blindSymbolSlackOn_punctured_iff {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) (M : ℝ) :
    BlindSymbolSlackOn (puncturedPowerNodes q d) M ↔
      -(symbolPeriodMean q - |foldedCosineCoefficient q d|) ≤ M :=
  ⟨le_of_blindSymbolSlackOn_punctured hq hd, fun h => (blindSymbolSlackOn_punctured hq hd).mono h⟩

theorem GappedNodeSet.mono {𝒩 𝒩' : Set ℕ} (h𝒩 : GappedNodeSet 𝒩) (hsub : 𝒩' ⊆ 𝒩) :
    GappedNodeSet 𝒩' := fun R => by
  obtain ⟨T, hRT, hgap⟩ := h𝒩 R
  exact ⟨T, hRT, fun n hn hn2 => hgap n (hsub hn) hn2⟩

/-- The removal law holds verbatim on zero-pole combinations. -/
theorem zeroPoleBlindSymbolSlackOn_punctured_iff {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn (puncturedPowerNodes q d) M ↔
      -(symbolPeriodMean q - |foldedCosineCoefficient q d|) ≤ M := by
  have hsub : puncturedPowerNodes q d ⊆ powerNodes q := by
    rintro n ⟨j, hj, -, hn⟩
    exact ⟨j, hj, hn⟩
  rw [zeroPoleBlindSymbolSlackOn_iff_of_gapped ((gappedNodeSet_powers hq).mono hsub),
    blindSymbolSlackOn_punctured_iff hq hd]

/-! ### 7. The coefficient as an integral of the symbol -/

theorem circleCos_eq_cos_norm (d : ℕ) (z : AddCircle (2 * π)) :
    circleCos d z = Real.cos (d * ‖z‖) := by
  induction z using QuotientAddGroup.induction_on with
  | H x =>
    change circleCos d (x : AddCircle (2 * π)) = Real.cos (d * ‖(x : AddCircle (2 * π))‖)
    rw [circleCos_coe, AddCircle.norm_eq]
    set m : ℤ := round ((2 * π)⁻¹ * x)
    rcases abs_choice (x - (m : ℝ) * (2 * π)) with h | h <;> rw [h]
    · rw [mul_sub, show (d : ℝ) * ((m : ℝ) * (2 * π)) = ((d * m : ℤ) : ℝ) * (2 * π) by
        push_cast; ring, Real.cos_sub_int_mul_two_pi]
    · rw [mul_neg, Real.cos_neg, mul_sub, show (d : ℝ) * ((m : ℝ) * (2 * π)) =
        ((d * m : ℤ) : ℝ) * (2 * π) by push_cast; ring, Real.cos_sub_int_mul_two_pi]

/-- `φ_d = (ℓ/π) ∫_0^{π/ℓ} γ(v) cos(dℓv) dv`. -/
theorem foldedCosineCoefficient_eq {q : ℕ} (hq : 2 ≤ q) (d : ℕ) :
    foldedCosineCoefficient q d = Real.log q / π *
      ∫ v in (0 : ℝ)..π / Real.log q, EF.gammaBracket v * Real.cos (d * Real.log q * v) := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have e : ∀ z : AddCircle (2 * π), foldedSymbol (Real.log q) z * circleCos d z =
      (fun v => EF.gammaBracket v * Real.cos (d * Real.log q * v)) (‖z‖ / Real.log q) := by
    intro z
    simp only [foldedSymbol, circleCos_eq_cos_norm]
    congr 2
    field_simp
  rw [foldedCosineCoefficient]
  simp_rw [e]
  exact integral_haarAddCircle_norm_comp hℓ
    (WeilHerglotz.continuous_gammaBracket.mul (Real.continuous_cos.comp (continuous_const.mul
      continuous_id)))

/-- **Far power nodes are cheap.** `|φ_d| ≤ (γ(π/ℓ) − γ(0))/d`: on each of the `d` cells of
length `π/(dℓ)` the cosine integrates to zero and `γ` moves by its increment. -/
theorem abs_foldedCosineCoefficient_le {q : ℕ} (hq : 2 ≤ q) {d : ℕ} (hd : 1 ≤ d) :
    |foldedCosineCoefficient q d| ≤
      (EF.gammaBracket (π / Real.log q) - EF.gammaBracket 0) / d := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  set ℓ := Real.log (q : ℝ) with hℓdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set w : ℝ := π / (d * ℓ) with hw
  have hw0 : 0 < w := by positivity
  set b : ℕ → ℝ := fun k => k * w with hb
  have hbd : b d = π / ℓ := by simp only [hb, hw]; field_simp
  have hγc : Continuous fun v => EF.gammaBracket v * Real.cos (d * ℓ * v) :=
    WeilHerglotz.continuous_gammaBracket.mul (Real.continuous_cos.comp (continuous_const.mul
      continuous_id))
  -- cells
  have hcell : ∀ k : ℕ, |∫ v in b k..b (k + 1), EF.gammaBracket v * Real.cos (d * ℓ * v)| ≤
      (EF.gammaBracket (b (k + 1)) - EF.gammaBracket (b k)) * w := by
    intro k
    have hbk : b k ≤ b (k + 1) := by simp only [hb]; push_cast; nlinarith
    have hlen : b (k + 1) - b k = w := by simp only [hb]; push_cast; ring
    have hcos0 : ∫ v in b k..b (k + 1), Real.cos (d * ℓ * v) = 0 := by
      have hc : (d : ℝ) * ℓ ≠ 0 := by positivity
      rw [intervalIntegral.integral_comp_mul_left (fun v => Real.cos v) hc, integral_cos,
        smul_eq_mul]
      have e1 : (d : ℝ) * ℓ * b (k + 1) = ((k + 1 : ℕ) : ℝ) * π := by
        simp only [hb, hw]; field_simp
      have e2 : (d : ℝ) * ℓ * b k = (k : ℝ) * π := by simp only [hb, hw]; field_simp
      rw [e1, e2, Real.sin_nat_mul_pi, Real.sin_nat_mul_pi, sub_zero, mul_zero]
    have hsplit : ∫ v in b k..b (k + 1), EF.gammaBracket v * Real.cos (d * ℓ * v) =
        ∫ v in b k..b (k + 1), (EF.gammaBracket v - EF.gammaBracket (b k)) *
          Real.cos (d * ℓ * v) := by
      have i1 : IntervalIntegrable (fun v => (EF.gammaBracket v - EF.gammaBracket (b k)) *
          Real.cos (d * ℓ * v)) volume (b k) (b (k + 1)) :=
        ((WeilHerglotz.continuous_gammaBracket.sub continuous_const).mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun v => EF.gammaBracket (b k) * Real.cos (d * ℓ * v))
          volume (b k) (b (k + 1)) :=
        (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul
          continuous_id))).intervalIntegrable _ _
      have e : (fun v => EF.gammaBracket v * Real.cos (d * ℓ * v)) =
          fun v => (EF.gammaBracket v - EF.gammaBracket (b k)) * Real.cos (d * ℓ * v) +
            EF.gammaBracket (b k) * Real.cos (d * ℓ * v) := by ext v; ring
      rw [e, intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul, hcos0,
        mul_zero, add_zero]
    rw [hsplit, ← Real.norm_eq_abs]
    have hbound : ∀ v ∈ Set.uIoc (b k) (b (k + 1)),
        ‖(EF.gammaBracket v - EF.gammaBracket (b k)) * Real.cos (d * ℓ * v)‖ ≤
          EF.gammaBracket (b (k + 1)) - EF.gammaBracket (b k) := by
      intro v hv
      rw [Set.uIoc_of_le hbk] at hv
      have hb0 : 0 ≤ b k := by simp only [hb]; positivity
      have hv0 : 0 ≤ v := by linarith [hv.1]
      have hv1 : 0 ≤ b (k + 1) := by linarith [hv.1, hv.2]
      have a1 : |b k| ≤ |v| := by
        rw [abs_of_nonneg hb0, abs_of_nonneg hv0]; exact hv.1.le
      have a2 : |v| ≤ |b (k + 1)| := by
        rw [abs_of_nonneg hv0, abs_of_nonneg hv1]; exact hv.2
      have h1 : EF.gammaBracket (b k) ≤ EF.gammaBracket v := gammaBracket_le_of_abs_le a1
      have h2 : EF.gammaBracket v ≤ EF.gammaBracket (b (k + 1)) := gammaBracket_le_of_abs_le a2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith)]
      have := Real.abs_cos_le_one (d * ℓ * v)
      nlinarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rwa [abs_of_nonneg (by linarith), hlen] at this
  -- sum over the cells
  have hb0 : b 0 = 0 := by simp [hb]
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (a := b) (n := d)
    (f := fun v => EF.gammaBracket v * Real.cos (d * ℓ * v)) (μ := volume)
    (fun k _ => hγc.intervalIntegrable _ _)
  rw [hb0, hbd] at hadj
  have hsum : |∑ k ∈ Finset.range d, ∫ v in b k..b (k + 1),
      EF.gammaBracket v * Real.cos (d * ℓ * v)| ≤
      (EF.gammaBracket (b d) - EF.gammaBracket (b 0)) * w := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ k ∈ Finset.range d, (EF.gammaBracket (b (k + 1)) - EF.gammaBracket (b k)) * w :=
        Finset.sum_le_sum fun k _ => hcell k
      _ = _ := by
        rw [← Finset.sum_mul, Finset.sum_range_sub (fun k => EF.gammaBracket (b k))]
  rw [hb0, hbd, hadj] at hsum
  rw [foldedCosineCoefficient_eq hq, ← hℓdef, abs_mul, abs_of_pos (by positivity : 0 < ℓ / π)]
  calc
    ℓ / π * |∫ v in (0 : ℝ)..π / ℓ, EF.gammaBracket v * Real.cos (d * ℓ * v)| ≤
        ℓ / π * ((EF.gammaBracket (π / ℓ) - EF.gammaBracket 0) * w) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [hw]; field_simp

end

end GaloisForLFunctions.BiScaleUncertainty
