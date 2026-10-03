import GaloisForLFunctions.HTGeometry.EulerStokesDepthLift
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.SourceStokesNormalizedChildUnit
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The Euler–Stokes aperture capacity

The moving cubic Grams `A_δ = W_δ^*W_δ` of the Euler-depth Stokes lift vary continuously in trace
norm on `(0, ∞)`: `‖W^*W - V^*V‖₁ ≤ (‖W‖₂ + ‖V‖₂)‖W - V‖₂`, and `‖W_δ - W_δ₀‖₂² =
Σ_i (√j_δ(i) - √j_δ₀(i))² → 0` by dominated convergence.  Their trace norms `Tr A_δ = Σ_i j_δ(i)`
are integrable against `δ dδ` with total `(1728/115)` times the primitive collision budget.  Hence
the aperture capacity

`C = (115/1728) ∫₀^∞ δ A_δ dδ`  (**(ESAC.6)**)

exists as a Bochner integral in the Schatten-one Banach space.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local notation "ℓ²E" => lp (fun _ : EulerLabel => ℂ) 2

variable {δ : ℝ}

/-! ## Differences of syntheses -/

theorem squareSummableSynthesis_sub {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {v u : ι → H} (hv : Summable fun i => ‖v i‖ ^ 2)
    (hu : Summable fun i => ‖u i‖ ^ 2) (hvu : Summable fun i => ‖(v - u) i‖ ^ 2) :
    squareSummableSynthesis v hv - squareSummableSynthesis u hu = squareSummableSynthesis (v - u) hvu := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [sub_apply, squareSummableSynthesis_apply, squareSummableSynthesis_apply,
    squareSummableSynthesis_apply, ← (summable_norm_smul_frame hv x).of_norm.tsum_sub
      (summable_norm_smul_frame hu x).of_norm]
  exact tsum_congr fun i => by rw [Pi.sub_apply, smul_sub]

/-! ## Monotone bounds and continuity of the current -/

theorem eulerStokesCurrent_le_four_mul (hδ₀ : 0 < δ) {d : ℝ} (hd1 : δ / 2 ≤ d) (hd2 : d ≤ 2 * δ)
    (i : EulerLabel) : eulerStokesCurrent d i ≤ 4 * eulerStokesCurrent (δ / 2) i := by
  have hn1 : (1 : ℝ) ≤ (xiGammaEulerValuationNat i : ℝ) := by
    have := eulerValuation_pos i
    rw [xiGammaEulerValuationNat] at this ⊢
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ i.1.property.ne_zero)
  have hpow : (xiGammaEulerValuationNat i : ℝ) ^ (-(1 + 2 * d)) ≤
      (xiGammaEulerValuationNat i : ℝ) ^ (-(1 + 2 * (δ / 2))) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hlog := (primeClock_pos i.1).le
  rw [eulerStokesCurrent, eulerStokesCurrent]
  have hd0 : 0 ≤ d := by linarith
  calc 8 * d * Real.log (i.1 : ℝ) * (xiGammaEulerValuationNat i : ℝ) ^ (-(1 + 2 * d))
      ≤ 8 * (2 * δ) * Real.log (i.1 : ℝ) * (xiGammaEulerValuationNat i : ℝ) ^ (-(1 + 2 * (δ / 2))) := by
        gcongr
    _ = 4 * (8 * (δ / 2) * Real.log (i.1 : ℝ) *
          (xiGammaEulerValuationNat i : ℝ) ^ (-(1 + 2 * (δ / 2)))) := by ring

theorem continuous_eulerStokesCurrent (i : EulerLabel) :
    Continuous fun d : ℝ => eulerStokesCurrent d i := by
  unfold eulerStokesCurrent
  have hn := (eulerValuation_pos i).ne'
  fun_prop (disch := exact hn)

/-! ## Trace-norm continuity of the moving Gram -/

/-- `‖W_δ - W_δ₀‖₂² = Σ_i (√j_δ(i) - √j_δ₀(i))²`. -/
theorem hsNormSq_eulerStokesSynthesis_sub {d d₀ : ℝ} (hd : 0 < d) (hd₀ : 0 < d₀) :
    ContinuousLinearMap.hsNormSq (eulerStokesSynthesis hd - eulerStokesSynthesis hd₀) =
      ∑' i, (Real.sqrt (eulerStokesCurrent d i) - Real.sqrt (eulerStokesCurrent d₀ i)) ^ 2 := by
  have hnorm : ∀ i, ‖(eulerStokesFrame d - eulerStokesFrame d₀) i‖ ^ 2 =
      (Real.sqrt (eulerStokesCurrent d i) - Real.sqrt (eulerStokesCurrent d₀ i)) ^ 2 := fun i => by
    rw [Pi.sub_apply, eulerStokesFrame, eulerStokesFrame, ← sub_smul, norm_smul,
      norm_gammaCoherentVector, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  have hsum : Summable fun i => ‖(eulerStokesFrame d - eulerStokesFrame d₀) i‖ ^ 2 := by
    simp_rw [hnorm]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
      ((summable_eulerStokesCurrent hd).add (summable_eulerStokesCurrent hd₀))
    have ha := Real.sqrt_nonneg (eulerStokesCurrent d i)
    have hb := Real.sqrt_nonneg (eulerStokesCurrent d₀ i)
    have h1 := Real.sq_sqrt (eulerStokesCurrent_pos hd i).le
    have h2 := Real.sq_sqrt (eulerStokesCurrent_pos hd₀ i).le
    nlinarith [mul_nonneg ha hb]
  rw [eulerStokesSynthesis, eulerStokesSynthesis, squareSummableSynthesis_sub _ _ hsum,
    hsNormSq_squareSummableSynthesis]
  exact tsum_congr hnorm

theorem tendsto_hsNorm_eulerStokesSynthesis_sub {d₀ : ℝ} (hd₀ : 0 < d₀) :
    Tendsto (fun d => ∑' i, (Real.sqrt (eulerStokesCurrent d i) -
      Real.sqrt (eulerStokesCurrent d₀ i)) ^ 2) (𝓝 d₀) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 d₀)
    (f := fun d i => (Real.sqrt (eulerStokesCurrent d i) - Real.sqrt (eulerStokesCurrent d₀ i)) ^ 2)
    (g := fun _ => (0 : ℝ))
    (bound := fun i => 4 * eulerStokesCurrent (d₀ / 2) i + eulerStokesCurrent d₀ i)
    (((summable_eulerStokesCurrent (by linarith)).mul_left 4).add (summable_eulerStokesCurrent hd₀))
    (fun i => by
      have hc : Continuous fun d => (Real.sqrt (eulerStokesCurrent d i) -
          Real.sqrt (eulerStokesCurrent d₀ i)) ^ 2 :=
        ((Real.continuous_sqrt.comp (continuous_eulerStokesCurrent i)).sub continuous_const).pow 2
      simpa using hc.tendsto d₀)
    (by
      filter_upwards [Icc_mem_nhds (by linarith : d₀ / 2 < d₀) (by linarith : d₀ < 2 * d₀)]
        with d hd i
      have hd0 : 0 < d := by linarith [hd.1]
      have ha := Real.sqrt_nonneg (eulerStokesCurrent d i)
      have hb := Real.sqrt_nonneg (eulerStokesCurrent d₀ i)
      have h1 := Real.sq_sqrt (eulerStokesCurrent_pos hd0 i).le
      have h2 := Real.sq_sqrt (eulerStokesCurrent_pos hd₀ i).le
      have h3 := eulerStokesCurrent_le_four_mul hd₀ hd.1 hd.2 i
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [mul_nonneg ha hb])
  simpa using h

/-- The moving Gram as a Schatten-one operator (zero for `δ ≤ 0`). -/
def eulerStokesGramS1 (δ : ℝ) : SchattenOneOperator ℓ²E :=
  if hδ : 0 < δ then ⟨eulerStokesGram hδ, (eulerStokesGram_traceClass hδ).2.1⟩ else 0

theorem eulerStokesGramS1_of_pos (hδ : 0 < δ) :
    (eulerStokesGramS1 δ : ℓ²E →L[ℂ] ℓ²E) = eulerStokesGram hδ := by
  rw [eulerStokesGramS1, dif_pos hδ]

theorem norm_eulerStokesGramS1 (hδ : 0 < δ) : ‖eulerStokesGramS1 δ‖ = ∑' i, eulerStokesCurrent δ i := by
  rw [SchattenOneOperator.norm_def, eulerStokesGramS1_of_pos hδ]
  exact (eulerStokesGram_traceClass hδ).2.2.2

/-- **Strong measurability.**  `δ ↦ A_δ` is trace-norm continuous on `(0, ∞)`. -/
theorem continuousOn_eulerStokesGramS1 : ContinuousOn eulerStokesGramS1 (Ioi 0) := by
  intro d₀ hd₀
  have hd₀' : (0 : ℝ) < d₀ := hd₀
  refine ContinuousAt.continuousWithinAt ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hW₀ : (eulerStokesSynthesis hd₀').IsHilbertSchmidt := squareSummableSynthesis_isHilbertSchmidt _
  have hH := tendsto_hsNorm_eulerStokesSynthesis_sub hd₀'
  have hroot : Tendsto (fun d => Real.sqrt (∑' i, (Real.sqrt (eulerStokesCurrent d i) -
      Real.sqrt (eulerStokesCurrent d₀ i)) ^ 2)) (𝓝 d₀) (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hH
    rw [Real.sqrt_zero] at h
    exact h
  have hbound : Tendsto (fun d => (2 * ContinuousLinearMap.hsNorm (eulerStokesSynthesis hd₀') +
      Real.sqrt (∑' i, (Real.sqrt (eulerStokesCurrent d i) -
        Real.sqrt (eulerStokesCurrent d₀ i)) ^ 2)) *
      Real.sqrt (∑' i, (Real.sqrt (eulerStokesCurrent d i) -
        Real.sqrt (eulerStokesCurrent d₀ i)) ^ 2)) (𝓝 d₀) (𝓝 0) := by
    simpa using (hroot.const_add _).mul hroot
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [Ioi_mem_nhds hd₀'] with d hd
  have hd' : (0 : ℝ) < d := hd
  have hW : (eulerStokesSynthesis hd').IsHilbertSchmidt := squareSummableSynthesis_isHilbertSchmidt _
  have hsq : ContinuousLinearMap.hsNorm (eulerStokesSynthesis hd' - eulerStokesSynthesis hd₀') =
      Real.sqrt (∑' i, (Real.sqrt (eulerStokesCurrent d i) - Real.sqrt (eulerStokesCurrent d₀ i)) ^ 2) := by
    rw [ContinuousLinearMap.hsNorm, hsNormSq_eulerStokesSynthesis_sub hd' hd₀']
  have htri : ContinuousLinearMap.hsNorm (eulerStokesSynthesis hd') ≤
      ContinuousLinearMap.hsNorm (eulerStokesSynthesis hd₀') +
        ContinuousLinearMap.hsNorm (eulerStokesSynthesis hd' - eulerStokesSynthesis hd₀') := by
    have := ContinuousLinearMap.hsNorm_add_le (hW.sub hW₀) hW₀
    rw [sub_add_cancel] at this
    linarith
  rw [SchattenOneOperator.norm_def, SchattenOneOperator.coe_sub, eulerStokesGramS1_of_pos hd',
    eulerStokesGramS1_of_pos hd₀']
  refine (traceNorm_adjoint_comp_self_sub_le hW hW₀).trans ?_
  rw [hsq] at htri ⊢
  have hn := ContinuousLinearMap.hsNorm_nonneg (eulerStokesSynthesis hd₀')
  have hr := Real.sqrt_nonneg (∑' i, (Real.sqrt (eulerStokesCurrent d i) -
    Real.sqrt (eulerStokesCurrent d₀ i)) ^ 2)
  nlinarith

/-! ## The aperture integral -/

/-- The integrand `(115/1728) δ A_δ`. -/
def eulerApertureIntegrand (δ : ℝ) : SchattenOneOperator ℓ²E :=
  (((115 / 1728 : ℝ) * δ : ℝ) : ℂ) • eulerStokesGramS1 δ

theorem integrableOn_mul_eulerStokesCurrent (i : EulerLabel) :
    IntegrableOn (fun δ => (115 / 1728 : ℝ) * (δ * eulerStokesCurrent δ i)) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_const_mul, integral_mul_eulerStokesCurrent]
  rw [xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
  have hp : (0 : ℝ) < (i.1 : ℝ) := by exact_mod_cast i.1.property.pos
  have hl := primeClock_pos i.1
  positivity

/-- **(ESAC.9)** `∫ ‖(115/1728) δ A_δ‖₁ dδ` is the primitive collision budget, hence finite. -/
theorem lintegral_norm_eulerApertureIntegrand :
    ∫⁻ δ in Ioi (0 : ℝ), ENNReal.ofReal ‖eulerApertureIntegrand δ‖ =
      ENNReal.ofReal routePPrimitiveCollisionCubicTraceBudget := by
  have hpt : EqOn (fun δ => ENNReal.ofReal ‖eulerApertureIntegrand δ‖)
      (fun δ => ∑' i, ENNReal.ofReal ((115 / 1728 : ℝ) * (δ * eulerStokesCurrent δ i))) (Ioi 0) := by
    intro δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    simp only
    rw [eulerApertureIntegrand, norm_smul, norm_eulerStokesGramS1 hδ', Complex.norm_real,
      Real.norm_of_nonneg (by positivity), ← tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg
        (fun i => by have := eulerStokesCurrent_pos hδ' i; positivity)
        (((summable_eulerStokesCurrent hδ').mul_left δ).mul_left _)]
    congr 1
    exact tsum_congr fun i => by ring
  have hmeas : ∀ i : EulerLabel, AEMeasurable
      (fun δ : ℝ => ENNReal.ofReal ((115 / 1728 : ℝ) * (δ * eulerStokesCurrent δ i)))
      (volume.restrict (Ioi 0)) := fun i =>
    ((continuous_const.mul (continuous_id.mul (continuous_eulerStokesCurrent i))).measurable.ennreal_ofReal).aemeasurable
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_tsum hmeas]
  have hterm : ∀ i : EulerLabel, ∫⁻ δ in Ioi (0 : ℝ),
      ENNReal.ofReal ((115 / 1728 : ℝ) * (δ * eulerStokesCurrent δ i)) =
        ENNReal.ofReal (xiGammaEulerPrimitiveCubicLogMomentWeight i) := fun i => by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_mul_eulerStokesCurrent i)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun δ hδ => by
        have := eulerStokesCurrent_pos (show (0 : ℝ) < δ from hδ) i
        have hδ' : (0 : ℝ) < δ := hδ
        simp only [Pi.zero_apply]
        positivity)), integral_const_mul, integral_mul_eulerStokesCurrent]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg
    summable_xiGammaEulerPrimitiveCubicLogMomentWeight]
  rfl

theorem integrableOn_eulerApertureIntegrand : IntegrableOn eulerApertureIntegrand (Ioi 0) := by
  refine ⟨?_, ?_⟩
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).continuousOn.smul
      continuousOn_eulerStokesGramS1
  · rw [hasFiniteIntegral_iff_norm, lintegral_norm_eulerApertureIntegrand]
    exact ENNReal.ofReal_lt_top

/-- **(ESAC.6) The aperture capacity** `C = (115/1728) ∫₀^∞ δ A_δ dδ`, a Schatten-one Bochner integral. -/
def apertureCapacity : SchattenOneOperator ℓ²E := ∫ δ in Ioi (0 : ℝ), eulerApertureIntegrand δ

/-- The matrix entry `X ↦ ⟨e_i, X e_j⟩` as a continuous functional on `𝒮₁`. -/
def schattenOneEntry (i j : EulerLabel) : SchattenOneOperator ℓ²E →L[ℂ] ℂ :=
  (innerSL ℂ (lp.single 2 i (1 : ℂ) : ℓ²E)).comp
    ((ContinuousLinearMap.apply ℂ ℓ²E (lp.single 2 j (1 : ℂ) : ℓ²E)).comp schattenOneCoeCLM)

theorem schattenOneEntry_apply (i j : EulerLabel) (X : SchattenOneOperator ℓ²E) :
    schattenOneEntry i j X =
      ⟪(lp.single 2 i (1 : ℂ) : ℓ²E), (X : ℓ²E →L[ℂ] ℓ²E) (lp.single 2 j 1)⟫_ℂ := rfl

/-! ## The sixth-order Gram -/

/-- The sixth-order frame vector `√s_i ψ^{(6)}_{λ_i}`, `s_i` the primitive Euler weight. -/
def capacityFrame (i : EulerLabel) : HalfLineL2 :=
  ((Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight i) : ℝ) : ℂ) •
    gammaCoherentVector 6 (xiGammaEulerPrimitiveLogFrequency_pos i)

theorem norm_sq_capacityFrame (i : EulerLabel) :
    ‖capacityFrame i‖ ^ 2 = xiGammaEulerPrimitiveCubicLogMomentWeight i := by
  rw [capacityFrame, norm_smul, norm_gammaCoherentVector, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg i)]

theorem summable_norm_sq_capacityFrame : Summable fun i => ‖capacityFrame i‖ ^ 2 := by
  simp_rw [norm_sq_capacityFrame]
  exact summable_xiGammaEulerPrimitiveCubicLogMomentWeight

/-- The synthesis of the sixth-order frame. -/
def capacitySynthesis : ℓ²E →L[ℂ] HalfLineL2 :=
  squareSummableSynthesis capacityFrame summable_norm_sq_capacityFrame

/-- The sixth-order Gram. -/
def capacityGram : ℓ²E →L[ℂ] ℓ²E :=
  ContinuousLinearMap.adjoint capacitySynthesis ∘L capacitySynthesis

/-- **(ESAC.10)** The explicit capacity entry
`(230/27) √(log p log q) (λλ')^{3/2} / (√(n n') (λ+λ')⁶)`. -/
def capacityEntry (i j : EulerLabel) : ℝ :=
  (230 / 27 : ℝ) * (Real.sqrt (Real.log (i.1 : ℝ)) * Real.sqrt (Real.log (j.1 : ℝ))) *
    (Real.sqrt (xiGammaEulerPrimitiveLogFrequency i) * Real.sqrt (xiGammaEulerPrimitiveLogFrequency j)) ^ 3 /
      (Real.sqrt (xiGammaEulerValuationNat i : ℝ) * Real.sqrt (xiGammaEulerValuationNat j : ℝ) *
        (xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j) ^ 6)

/-- `√s_i = √(115/864) √(log p) / (√n_i (√λ_i)³)`. -/
theorem sqrt_xiGammaEulerPrimitiveCubicLogMomentWeight (i : EulerLabel) :
    Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight i) =
      Real.sqrt (115 / 864) * Real.sqrt (Real.log (i.1 : ℝ)) /
        (Real.sqrt (xiGammaEulerValuationNat i : ℝ) * Real.sqrt (xiGammaEulerPrimitiveLogFrequency i) ^ 3) := by
  have hl := primeClock_pos i.1
  have hlam := xiGammaEulerPrimitiveLogFrequency_pos i
  have hn := eulerValuation_pos i
  have hp : (0 : ℝ) < (i.1 : ℝ) := by exact_mod_cast i.1.property.pos
  rw [Real.sqrt_eq_iff_mul_self_eq (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg i) (by positivity)]
  have e1 := Real.sq_sqrt (show (0 : ℝ) ≤ 115 / 864 by norm_num)
  have e2 := Real.sq_sqrt hl.le
  have e3 := Real.sq_sqrt hn.le
  have e4 := Real.sq_sqrt hlam.le
  have hsn : 0 < Real.sqrt (xiGammaEulerValuationNat i : ℝ) := Real.sqrt_pos.2 hn
  have hsl : 0 < Real.sqrt (xiGammaEulerPrimitiveLogFrequency i) := Real.sqrt_pos.2 hlam
  rw [xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
  have hlamr := xiGammaEulerPrimitiveLogFrequency_eq i
  have hnr : (xiGammaEulerValuationNat i : ℝ) = (i.1 : ℝ) * (i.1 : ℝ) ^ i.2 := by
    rw [xiGammaEulerValuationNat, Nat.cast_pow, pow_succ, mul_comm]
  field_simp
  rw [show Real.sqrt (xiGammaEulerPrimitiveLogFrequency i) ^ 6 =
    (Real.sqrt (xiGammaEulerPrimitiveLogFrequency i) ^ 2) ^ 3 by ring, e4,
    show Real.sqrt (xiGammaEulerValuationNat i : ℝ) ^ 2 = (xiGammaEulerValuationNat i : ℝ) from e3,
    e1, e2, hlamr, hnr]
  simp only [one_div, inv_pow]
  field_simp

theorem coherence_pow_eq {s t : ℝ} (hs : 0 < s) (k : ℕ) :
    (2 * Real.sqrt (s * t) / (s + t)) ^ k =
      2 ^ k * (Real.sqrt s * Real.sqrt t) ^ k / (s + t) ^ k := by
  rw [Real.sqrt_mul hs.le, div_pow, mul_pow]

/-- **(ESAC.11) = (ESAC.10).**  `C(i,j) = √(s_i s_j) k₆(λ_i,λ_j)` is the explicit capacity entry. -/
theorem inner_single_capacityGram (i j : EulerLabel) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²E), capacityGram (lp.single 2 j 1)⟫_ℂ =
      ((Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight i *
          xiGammaEulerPrimitiveCubicLogMomentWeight j) *
        (2 * Real.sqrt (xiGammaEulerPrimitiveLogFrequency i * xiGammaEulerPrimitiveLogFrequency j) /
          (xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j)) ^ 6 : ℝ) : ℂ) ∧
    Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight i *
          xiGammaEulerPrimitiveCubicLogMomentWeight j) *
        (2 * Real.sqrt (xiGammaEulerPrimitiveLogFrequency i * xiGammaEulerPrimitiveLogFrequency j) /
          (xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j)) ^ 6 =
      capacityEntry i j := by
  refine ⟨?_, ?_⟩
  · rw [capacityGram, capacitySynthesis, inner_single_rightGram_single, capacityFrame, capacityFrame,
      inner_smul_left, inner_smul_right, inner_gammaCoherentVector, Complex.conj_ofReal,
      Real.sqrt_mul (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg i)]
    push_cast
    ring
  · have hi := xiGammaEulerPrimitiveLogFrequency_pos i
    have hj := xiGammaEulerPrimitiveLogFrequency_pos j
    rw [Real.sqrt_mul (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg i),
      sqrt_xiGammaEulerPrimitiveCubicLogMomentWeight, sqrt_xiGammaEulerPrimitiveCubicLogMomentWeight,
      coherence_pow_eq hi, capacityEntry]
    have hsn := Real.sqrt_pos.2 (eulerValuation_pos i)
    have hsn' := Real.sqrt_pos.2 (eulerValuation_pos j)
    have hsl := Real.sqrt_pos.2 hi
    have hsl' := Real.sqrt_pos.2 hj
    have e1 := Real.sq_sqrt (show (0 : ℝ) ≤ 115 / 864 by norm_num)
    have hsum : 0 < xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j := by
      linarith
    field_simp
    rw [show Real.sqrt (115 / 864) ^ 2 = 115 / 864 from e1]
    ring

/-- `√(j_δ(i) j_δ(j)) = 8δ √(log p log q)/√(n n') e^{-δ(λ_i+λ_j)}`. -/
theorem sqrt_eulerStokesCurrent_mul (hδ : 0 < δ) (i j : EulerLabel) :
    Real.sqrt (eulerStokesCurrent δ i * eulerStokesCurrent δ j) =
      8 * δ * (Real.sqrt (Real.log (i.1 : ℝ)) * Real.sqrt (Real.log (j.1 : ℝ))) /
        (Real.sqrt (xiGammaEulerValuationNat i : ℝ) * Real.sqrt (xiGammaEulerValuationNat j : ℝ)) *
          Real.exp (-(δ * (xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j))) := by
  have hn := eulerValuation_pos i
  have hn' := eulerValuation_pos j
  have hl := primeClock_pos i.1
  have hl' := primeClock_pos j.1
  set E := Real.exp (-(δ * (xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j)))
  have hexp : Real.exp (-(2 * δ * xiGammaEulerPrimitiveLogFrequency i)) *
      Real.exp (-(2 * δ * xiGammaEulerPrimitiveLogFrequency j)) = E * E := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [Real.sqrt_eq_iff_mul_self_eq (mul_pos (eulerStokesCurrent_pos hδ i)
    (eulerStokesCurrent_pos hδ j)).le (by positivity)]
  have hsn := Real.sqrt_pos.2 hn
  have hsn' := Real.sqrt_pos.2 hn'
  have e1 := Real.sq_sqrt hn.le
  have e2 := Real.sq_sqrt hn'.le
  have e3 := Real.sq_sqrt hl.le
  have e4 := Real.sq_sqrt hl'.le
  calc eulerStokesCurrent δ i * eulerStokesCurrent δ j
      = 64 * δ ^ 2 * (Real.log (i.1 : ℝ) * Real.log (j.1 : ℝ)) /
          ((xiGammaEulerValuationNat i : ℝ) * (xiGammaEulerValuationNat j : ℝ)) *
          (Real.exp (-(2 * δ * xiGammaEulerPrimitiveLogFrequency i)) *
            Real.exp (-(2 * δ * xiGammaEulerPrimitiveLogFrequency j))) := by
        rw [eulerStokesCurrent_eq_exp, eulerStokesCurrent_eq_exp]
        field_simp
        ring
    _ = 64 * δ ^ 2 * (Real.log (i.1 : ℝ) * Real.log (j.1 : ℝ)) /
          ((xiGammaEulerValuationNat i : ℝ) * (xiGammaEulerValuationNat j : ℝ)) * (E * E) := by
        rw [hexp]
    _ = _ := by
        field_simp
        rw [e1, e2, e3, e4]
        ring

/-- **(ESAC.10) by integration.**  The entries of the aperture capacity are the explicit capacity
entries. -/
theorem schattenOneEntry_apertureCapacity (i j : EulerLabel) :
    schattenOneEntry i j apertureCapacity = (capacityEntry i j : ℂ) := by
  have hi := xiGammaEulerPrimitiveLogFrequency_pos i
  have hj := xiGammaEulerPrimitiveLogFrequency_pos j
  set S := xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j with hS
  have hS0 : 0 < S := by rw [hS]; linarith
  set K := (Real.sqrt (Real.log (i.1 : ℝ)) * Real.sqrt (Real.log (j.1 : ℝ))) /
    (Real.sqrt (xiGammaEulerValuationNat i : ℝ) * Real.sqrt (xiGammaEulerValuationNat j : ℝ)) with hK
  set k3 := cubicCoherence (xiGammaEulerPrimitiveLogFrequency i) (xiGammaEulerPrimitiveLogFrequency j)
  rw [apertureCapacity, ← (schattenOneEntry i j).integral_comp_comm integrableOn_eulerApertureIntegrand]
  have hpt : EqOn (fun δ => schattenOneEntry i j (eulerApertureIntegrand δ))
      (fun δ => (((115 / 1728 * (8 * K * k3)) * (δ ^ 2 * Real.exp (-(S * δ))) : ℝ) : ℂ)) (Ioi 0) := by
    intro δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    simp only
    rw [eulerApertureIntegrand, map_smul, schattenOneEntry_apply, eulerStokesGramS1_of_pos hδ',
      inner_single_eulerStokesGram, sqrt_eulerStokesCurrent_mul hδ', smul_eq_mul, ← Complex.ofReal_mul]
    congr 1
    rw [hK, hS, show -(δ * (xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j)) =
      -((xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j) * δ) by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal, integral_const_mul,
    (integral_exp_neg_moments hS0).2.2]
  congr 1
  have hk3 : k3 = 2 ^ 3 * (Real.sqrt (xiGammaEulerPrimitiveLogFrequency i) *
      Real.sqrt (xiGammaEulerPrimitiveLogFrequency j)) ^ 3 / S ^ 3 := coherence_pow_eq hi 3
  rw [hk3, hK, capacityEntry, ← hS]
  have hsn := Real.sqrt_pos.2 (eulerValuation_pos i)
  have hsn' := Real.sqrt_pos.2 (eulerValuation_pos j)
  field_simp
  ring

/-- **(ESAC.6)–(ESAC.11)** The aperture capacity is the sixth-order Gram. -/
theorem apertureCapacity_eq_capacityGram :
    (apertureCapacity : ℓ²E →L[ℂ] ℓ²E) = capacityGram := by
  refine ext_of_inner_single fun i j => ?_
  rw [← schattenOneEntry_apply, schattenOneEntry_apertureCapacity, (inner_single_capacityGram i j).1,
    (inner_single_capacityGram i j).2]

/-- **(ESAC.12)** `C ≥ 0`, `C ∈ 𝒮₁`, `Tr C = ‖C‖₁ = ` the primitive collision budget `< 115/108`. -/
theorem apertureCapacity_traceClass :
    (apertureCapacity : ℓ²E →L[ℂ] ℓ²E).IsPositive ∧
      (apertureCapacity : ℓ²E →L[ℂ] ℓ²E).opTrace = (routePPrimitiveCollisionCubicTraceBudget : ℂ) ∧
      ‖apertureCapacity‖ = routePPrimitiveCollisionCubicTraceBudget ∧
      routePPrimitiveCollisionCubicTraceBudget < 115 / 108 := by
  obtain ⟨hpos, hS, htr⟩ := rightGram_traceClass summable_norm_sq_capacityFrame
  simp_rw [norm_sq_capacityFrame] at htr
  have hC : (apertureCapacity : ℓ²E →L[ℂ] ℓ²E) =
      ContinuousLinearMap.adjoint capacitySynthesis ∘L capacitySynthesis :=
    apertureCapacity_eq_capacityGram
  refine ⟨hC ▸ hpos, hC ▸ htr, ?_, routePPrimitiveCollisionCubicTraceBudget_lt_quantum⟩
  rw [SchattenOneOperator.norm_def, hC]
  exact (traceNorm_eq_re_opTrace_of_isPositive hS hpos).trans (by rw [htr, Complex.ofReal_re]; rfl)

/-! ## The singular sixth boundary -/

/-- **(ESAC.13)** The source charge `c_i = √(log p) λ_i^{3/2}/√n_i`. -/
def sixthBoundaryVector (i : EulerLabel) : ℝ :=
  Real.sqrt (Real.log (i.1 : ℝ)) * Real.sqrt (xiGammaEulerPrimitiveLogFrequency i) ^ 3 /
    Real.sqrt (xiGammaEulerValuationNat i : ℝ)

/-- **(ESAC.14)** `(λ_i + λ_j)⁶ C(i,j) = (230/27) c_i c_j`. -/
theorem sixthBoundary_law (i j : EulerLabel) :
    (xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j) ^ 6 * capacityEntry i j =
      (230 / 27 : ℝ) * sixthBoundaryVector i * sixthBoundaryVector j := by
  have hi := xiGammaEulerPrimitiveLogFrequency_pos i
  have hj := xiGammaEulerPrimitiveLogFrequency_pos j
  have hsn := Real.sqrt_pos.2 (eulerValuation_pos i)
  have hsn' := Real.sqrt_pos.2 (eulerValuation_pos j)
  have hs : 0 < xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j := by linarith
  rw [capacityEntry, sixthBoundaryVector, sixthBoundaryVector]
  field_simp

/-- **(ESAC.14), operator form.**  On the prime-power basis the sixth Sylvester power of the
capacity is the rank-one form `(230/27)|c⟩⟨c|`. -/
theorem sixthBoundary_law_entry (i j : EulerLabel) :
    ((xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j : ℝ) : ℂ) ^ 6 *
        ⟪(lp.single 2 i (1 : ℂ) : ℓ²E), (apertureCapacity : ℓ²E →L[ℂ] ℓ²E) (lp.single 2 j 1)⟫_ℂ =
      (((230 / 27 : ℝ) * sixthBoundaryVector i * sixthBoundaryVector j : ℝ) : ℂ) := by
  rw [← schattenOneEntry_apply, schattenOneEntry_apertureCapacity, ← sixthBoundary_law]
  push_cast
  ring

/-- **Uniqueness.**  A bounded operator satisfying the sixth boundary law on the prime-power basis is
the aperture capacity. -/
theorem eq_apertureCapacity_of_sixthBoundary_law (X : ℓ²E →L[ℂ] ℓ²E)
    (hX : ∀ i j, ((xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j : ℝ) : ℂ) ^ 6 *
        ⟪(lp.single 2 i (1 : ℂ) : ℓ²E), X (lp.single 2 j 1)⟫_ℂ =
      (((230 / 27 : ℝ) * sixthBoundaryVector i * sixthBoundaryVector j : ℝ) : ℂ)) :
    X = (apertureCapacity : ℓ²E →L[ℂ] ℓ²E) := by
  refine ext_of_inner_single fun i j => ?_
  have h1 := hX i j
  rw [← sixthBoundary_law_entry i j] at h1
  have hne : ((xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j : ℝ) : ℂ) ^ 6 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.2 (by
      linarith [xiGammaEulerPrimitiveLogFrequency_pos i, xiGammaEulerPrimitiveLogFrequency_pos j]))
  exact mul_left_cancel₀ hne h1

theorem sq_sqrt_mul_sqrt_pow_three_div {L P : ℝ} (hL : 0 ≤ L) (hP : 0 < P) :
    (Real.sqrt L * Real.sqrt L ^ 3 / Real.sqrt P) ^ 2 = L ^ 4 / P := by
  have e1 := Real.sq_sqrt hL
  rw [div_pow, mul_pow, e1, Real.sq_sqrt hP.le,
    show (Real.sqrt L ^ 3) ^ 2 = (Real.sqrt L ^ 2) ^ 3 by ring, e1]
  ring

theorem sixthBoundaryVector_sq_depth_zero (p : Nat.Primes) :
    sixthBoundaryVector (p, 0) ^ 2 = Real.log (p : ℝ) ^ 4 / (p : ℝ) := by
  have hl := primeClock_pos p
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hlam : xiGammaEulerPrimitiveLogFrequency (p, 0) = Real.log (p : ℝ) := by
    rw [xiGammaEulerPrimitiveLogFrequency_eq]
    simp
  have hn : (xiGammaEulerValuationNat (p, 0) : ℝ) = (p : ℝ) := by
    simp [xiGammaEulerValuationNat]
  rw [sixthBoundaryVector, hlam, hn]
  exact sq_sqrt_mul_sqrt_pow_three_div hl.le hp

/-- **(ESAC.15)** `Σ_p c_{(p,0)}² = Σ_p (log p)⁴/p = ∞`: the source charge is not in `ℓ²`. -/
theorem not_summable_sixthBoundaryVector_sq_depth_zero :
    ¬ Summable fun p : Nat.Primes => sixthBoundaryVector (p, 0) ^ 2 := by
  intro h
  simp_rw [sixthBoundaryVector_sq_depth_zero] at h
  have hc : (0 : ℝ) < Real.log 2 ^ 4 := by positivity
  apply Nat.Primes.not_summable_one_div
  refine (summable_mul_left_iff hc.ne').1 (Summable.of_nonneg_of_le (fun p => by positivity)
    (fun p => ?_) h)
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have h2 : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.property.two_le)
  have h20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h20 h2 4) hp.le

theorem not_summable_sixthBoundaryVector_sq : ¬ Summable fun i => sixthBoundaryVector i ^ 2 :=
  fun h => not_summable_sixthBoundaryVector_sq_depth_zero
    (h.comp_injective fun _ _ hpq => (Prod.mk.inj hpq).1)

/-- **(ESAC.15)** The boundary form `|⟨c, x⟩|²` is unbounded on the unit sphere of the finitely
supported vectors. -/
theorem exists_unit_core_vector_boundaryForm_ge (M : ℝ) :
    ∃ x : ℓ²E, (∃ F : Finset EulerLabel, ∀ i ∉ F, (x : EulerLabel → ℂ) i = 0) ∧ ‖x‖ = 1 ∧
      M ≤ ‖∑' i, (sixthBoundaryVector i : ℂ) * (x : EulerLabel → ℂ) i‖ ^ 2 := by
  obtain ⟨F, hF⟩ : ∃ F : Finset EulerLabel, max M 1 < ∑ i ∈ F, sixthBoundaryVector i ^ 2 := by
    by_contra h
    push Not at h
    exact not_summable_sixthBoundaryVector_sq (summable_of_sum_le (fun i => sq_nonneg _) h)
  set q := ∑ i ∈ F, sixthBoundaryVector i ^ 2
  have hq : 0 < q := lt_of_lt_of_le one_pos ((le_max_right M 1).trans hF.le)
  set r := Real.sqrt q
  have hr : 0 < r := Real.sqrt_pos.2 hq
  let a : EulerLabel → ℂ := fun i => ((sixthBoundaryVector i / r : ℝ) : ℂ)
  let x : ℓ²E := ∑ i ∈ F, lp.single 2 i (a i)
  have hx : ∀ i, (x : EulerLabel → ℂ) i = if i ∈ F then a i else 0 := fun i => by
    simp only [x, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
    rw [Finset.sum_ite_eq]
  refine ⟨x, ⟨F, fun i hi => by rw [hx, if_neg hi]⟩, ?_, ?_⟩
  · have hn := lp.norm_sum_single (E := fun _ : EulerLabel => ℂ) (p := 2) (by norm_num) a F
    have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
    rw [h2] at hn
    simp only [Real.rpow_two] at hn
    have hsum : ∑ i ∈ F, ‖a i‖ ^ 2 = 1 := by
      simp only [a, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
      rw [← Finset.sum_div, Real.sq_sqrt hq.le]
      exact div_self hq.ne'
    rw [hsum] at hn
    have := norm_nonneg x
    nlinarith [sq_nonneg (‖x‖ - 1)]
  · have htsum : ∑' i, (sixthBoundaryVector i : ℂ) * (x : EulerLabel → ℂ) i = (r : ℂ) := by
      rw [tsum_eq_sum (s := F) fun i hi => by rw [hx, if_neg hi, mul_zero]]
      rw [Finset.sum_congr rfl fun i hi => by rw [hx, if_pos hi]]
      simp only [a, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
      congr 1
      rw [show ∑ i ∈ F, sixthBoundaryVector i * (sixthBoundaryVector i / r) = q / r by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring]
      rw [div_eq_iff hr.ne', ← sq, Real.sq_sqrt hq.le]
    rw [htsum, Complex.norm_real, Real.norm_of_nonneg hr.le, Real.sq_sqrt hq.le]
    exact ((le_max_left M 1).trans hF.le)

/-- **Bounded-boundary no-go.**  No `ℓ²` source vector `b` and scalar `κ` reproduce the sixth
boundary of the capacity as `κ |b⟩⟨b|`. -/
theorem not_exists_ell2_sixthBoundary_source :
    ¬ ∃ (b : ℓ²E) (κ : ℂ), ∀ i j,
      ((xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j : ℝ) : ℂ) ^ 6 *
          ⟪(lp.single 2 i (1 : ℂ) : ℓ²E), (apertureCapacity : ℓ²E →L[ℂ] ℓ²E) (lp.single 2 j 1)⟫_ℂ =
        κ * (b : EulerLabel → ℂ) i * starRingEnd ℂ ((b : EulerLabel → ℂ) j) := by
  rintro ⟨b, κ, h⟩
  apply not_summable_sixthBoundaryVector_sq
  have hdiag : ∀ i, sixthBoundaryVector i ^ 2 = (27 / 230 : ℝ) * (‖κ‖ * ‖(b : EulerLabel → ℂ) i‖ ^ 2) := by
    intro i
    have h1 := h i i
    rw [sixthBoundary_law_entry] at h1
    have h2 := congrArg norm h1
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs] at h2
    have habs : |sixthBoundaryVector i| * |sixthBoundaryVector i| = sixthBoundaryVector i ^ 2 := by
      rw [← abs_mul, abs_mul_self, sq]
    have h27 : |(230 / 27 : ℝ)| = 230 / 27 := abs_of_pos (by norm_num)
    rw [h27, mul_assoc, habs] at h2
    nlinarith
  simp_rw [hdiag]
  exact ((HilbertSchmidt.summable_coe_sq b).mul_left ‖κ‖).mul_left _

end GaloisForLFunctions.HTGeometry
