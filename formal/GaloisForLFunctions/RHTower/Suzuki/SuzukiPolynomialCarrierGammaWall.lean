import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaStripCarrierTwoSided
import GaloisForLFunctions.HTGeometry.LatticePolynomialWeight
import GaloisForLFunctions.HTGeometry.PowerTailIntegral

/-!
# The sharp Gamma dimension wall for radial polynomial orbit carriers

A degree-`κ` polynomial group estimate costs `⟨x⟩^{2κ}` in squared norm, so the polynomially
distorted homogeneous Gamma carrier on the shifted line is

`q_{κ,σ}(x) = |x|^{2κ} q_σ(x)`,   `q_σ(x) = |Γ(1-σ+ix)|/(|Γ(1+σ+ix)| |x+iσ|)`.

The exact vertical Gamma exponent gives `q_{κ,σ}(x)|x|^{1+2σ-2κ} → 1`, so the power-integral
criterion makes `q_{κ,σ}` integrable **exactly** when `κ < σ`, including the logarithmically
divergent boundary `κ = σ`.

On the lattice side a bounded orbit state lies in the weighted lattice Hilbert space exactly when
`d/2 < κ`.  Since `σ < 1`, a common exponent exists exactly when `d ≤ 1`: in rank at most one the
concrete pair `(κ,σ) = (2/3, 3/4)` works, and in rank at least two no radial polynomial exponent can
simultaneously embed every bounded orbit state and keep the worst-case Gamma transport square
integrable.
-/

open Filter Topology MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- `(7)`: the polynomially distorted squared Gamma carrier on the shifted line. -/
def suzukiGammaDistortedNormSq (κ σ x : ℝ) : ℝ :=
  |x| ^ (2 * κ) * suzukiGammaStripNormSq σ x

theorem suzukiGammaDistortedNormSq_nonneg (κ σ x : ℝ) : 0 ≤ suzukiGammaDistortedNormSq κ σ x := by
  rw [suzukiGammaDistortedNormSq, suzukiGammaStripNormSq]
  positivity

theorem suzukiGammaDistortedNormSq_neg (κ σ x : ℝ) :
    suzukiGammaDistortedNormSq κ σ (-x) = suzukiGammaDistortedNormSq κ σ x := by
  rw [suzukiGammaDistortedNormSq, suzukiGammaDistortedNormSq, abs_neg,
    suzukiGammaStripNormSq_neg]

theorem continuous_suzukiGammaDistortedNormSq {κ σ : ℝ} (hκ : 0 < κ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (suzukiGammaDistortedNormSq κ σ) := by
  refine Continuous.mul ?_ (continuous_suzukiGammaStripNormSq hσ0 hσ1)
  exact (Real.continuous_rpow_const (by linarith)).comp continuous_abs

/-- **`(8)`: the exact distorted tail exponent.** -/
theorem suzukiGammaDistortedNormSq_rpow_tendsto {κ σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    Tendsto (fun x : ℝ => suzukiGammaDistortedNormSq κ σ x * x ^ (1 + 2 * σ - 2 * κ))
      atTop (nhds 1) := by
  refine (suzukiGammaStripNormSq_rpow_tendsto hσ0 hσ1).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hsplit : x ^ (1 + 2 * σ) = x ^ (2 * κ) * x ^ (1 + 2 * σ - 2 * κ) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [suzukiGammaDistortedNormSq, abs_of_pos hx, hsplit]
  ring

/-- **`(9)`, divergence half.**  At or above the Gamma shift the distorted carrier is not
integrable. -/
theorem not_integrable_suzukiGammaDistortedNormSq {κ σ : ℝ} (hσ0 : 0 < σ)
    (hσ1 : σ < 1) (hks : σ ≤ κ) : ¬ Integrable (suzukiGammaDistortedNormSq κ σ) := by
  intro hint
  have htend := suzukiGammaStripNormSq_rpow_tendsto (σ := σ) hσ0.le hσ1
  have hlower : ∀ᶠ x : ℝ in atTop,
      (1 / 2 : ℝ) < suzukiGammaStripNormSq σ x * x ^ (1 + 2 * σ) :=
    htend.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨A, hA⟩ := mem_atTop_sets.mp hlower
  set C : ℝ := max A 1 with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have htail : IntegrableOn (suzukiGammaDistortedNormSq κ σ) (Ici C) volume := hint.integrableOn
  have hpower : IntegrableOn (fun x : ℝ => x ^ (2 * κ - 1 - 2 * σ)) (Ici C) volume := by
    apply (htail.const_mul 2).mono'
    · refine (continuousOn_id.rpow_const fun x hx => Or.inl ?_).aestronglyMeasurable
        measurableSet_Ici
      have hx1 : (1 : ℝ) ≤ x := hC1.trans hx
      simp only [id_eq]
      linarith
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hx1 : (1 : ℝ) ≤ x := hC1.trans hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
      have hprod := hA x ((le_max_left A 1).trans hx)
      have hpow1 : 0 < x ^ (1 + 2 * σ) := Real.rpow_pos_of_pos hx0 _
      have hdensity : 0 ≤ suzukiGammaStripNormSq σ x := by
        rw [suzukiGammaStripNormSq]
        positivity
      have hsplit : x ^ (2 * κ - 1 - 2 * σ) * x ^ (1 + 2 * σ) = x ^ (2 * κ) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      have hscaled : x ^ (2 * κ - 1 - 2 * σ) * (1 / 2 : ℝ)
          < x ^ (2 * κ) * suzukiGammaStripNormSq σ x := by
        calc x ^ (2 * κ - 1 - 2 * σ) * (1 / 2 : ℝ)
            < x ^ (2 * κ - 1 - 2 * σ) * (suzukiGammaStripNormSq σ x * x ^ (1 + 2 * σ)) :=
              mul_lt_mul_of_pos_left hprod (Real.rpow_pos_of_pos hx0 _)
          _ = (x ^ (2 * κ - 1 - 2 * σ) * x ^ (1 + 2 * σ)) * suzukiGammaStripNormSq σ x := by ring
          _ = x ^ (2 * κ) * suzukiGammaStripNormSq σ x := by rw [hsplit]
      have hpoint : x ^ (2 * κ - 1 - 2 * σ) ≤ 2 * suzukiGammaDistortedNormSq κ σ x := by
        rw [suzukiGammaDistortedNormSq, abs_of_pos hx0]
        nlinarith [hscaled]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      exact hpoint
  have hatTop : IntegrableAtFilter (fun x : ℝ => x ^ (2 * κ - 1 - 2 * σ)) atTop volume :=
    ⟨Ici C, Ici_mem_atTop C, hpower⟩
  have hexponent : 2 * κ - 1 - 2 * σ < -1 := integrableAtFilter_rpow_atTop_iff.mp hatTop
  linarith

/-- **`(9)`, convergence half.**  Strictly below the Gamma shift the distorted carrier is
integrable. -/
theorem integrable_suzukiGammaDistortedNormSq {κ σ : ℝ} (hκ : 0 < κ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hks : κ < σ) : Integrable (suzukiGammaDistortedNormSq κ σ) := by
  set p : ℝ := 1 + 2 * σ - 2 * κ with hpdef
  have hp : 1 < p := by rw [hpdef]; linarith
  have htend := suzukiGammaDistortedNormSq_rpow_tendsto (κ := κ) hσ0.le hσ1
  have hupper : ∀ᶠ x : ℝ in atTop, suzukiGammaDistortedNormSq κ σ x * x ^ p < 2 :=
    htend.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨A, hA⟩ := mem_atTop_sets.mp hupper
  set C : ℝ := max A 1 with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hray : ∀ x : ℝ, C ≤ x → suzukiGammaDistortedNormSq κ σ x ≤ 2 * |x| ^ (-p) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hC0 hx
    have hlt := hA x ((le_max_left A 1).trans hx)
    simp only [Set.mem_setOf_eq] at hlt
    have hpow : 0 < x ^ p := Real.rpow_pos_of_pos hx0 _
    rw [abs_of_pos hx0, Real.rpow_neg hx0.le, ← div_eq_mul_inv, le_div_iff₀ hpow]
    linarith
  have hbound : ∀ x : ℝ, C ≤ |x| → suzukiGammaDistortedNormSq κ σ x ≤ 2 * |x| ^ (-p) := by
    intro x hx
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0] at hx
      exact hray x hx
    · have hneg : C ≤ -x := by
        rw [abs_of_neg hx0] at hx
        exact hx
      have := hray (-x) hneg
      rwa [suzukiGammaDistortedNormSq_neg, abs_neg] at this
  have htail : IntegrableOn (suzukiGammaDistortedNormSq κ σ) {η : ℝ | C ≤ |η|} volume := by
    refine Integrable.mono' ((integrableOn_powerTail hC0 hp).const_mul 2) ?_ ?_
    · exact ((continuous_suzukiGammaDistortedNormSq hκ hσ0 hσ1).continuousOn).aestronglyMeasurable
        (measurableSet_centralTail C)
    · filter_upwards [ae_restrict_mem (measurableSet_centralTail C)] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (suzukiGammaDistortedNormSq_nonneg κ σ x)]
      exact hbound x hx
  have hband : IntegrableOn (suzukiGammaDistortedNormSq κ σ) {η : ℝ | |η| ≤ C} volume := by
    have hset : {η : ℝ | |η| ≤ C} = Icc (-C) C := by
      ext x
      simp [abs_le]
    rw [hset]
    exact ((continuous_suzukiGammaDistortedNormSq hκ hσ0 hσ1).continuousOn).integrableOn_Icc
  have huniv : {η : ℝ | |η| ≤ C} ∪ {η : ℝ | C ≤ |η|} = univ := by
    ext x
    simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact le_total |x| C
  have := hband.union htail
  rw [huniv, integrableOn_univ] at this
  exact this

/-- **`(9)`: the sharp threshold.** -/
theorem integrable_suzukiGammaDistortedNormSq_iff {κ σ : ℝ} (hκ : 0 < κ) (hσ0 : 0 < σ)
    (hσ1 : σ < 1) : Integrable (suzukiGammaDistortedNormSq κ σ) ↔ κ < σ := by
  constructor
  · intro hint
    by_contra hcon
    exact not_integrable_suzukiGammaDistortedNormSq hσ0 hσ1 (not_lt.mp hcon) hint
  · exact integrable_suzukiGammaDistortedNormSq hκ hσ0 hσ1

/-- **`(11)`, `(3)`: the exact common window.**  A radial polynomial exponent embedding every bounded
orbit state and keeping the distorted Gamma carrier integrable exists exactly in rank at most
one. -/
theorem exists_gamma_dimension_window_iff (d : ℕ) :
    (∃ κ σ : ℝ, (d : ℝ) / 2 < κ ∧ κ < σ ∧ σ < 1) ↔ d ≤ 1 := by
  constructor
  · rintro ⟨κ, σ, h1, h2, h3⟩
    by_contra hcon
    have hd : (2 : ℝ) ≤ (d : ℝ) := by
      have : 2 ≤ d := by omega
      exact_mod_cast this
    linarith
  · intro hd
    refine ⟨2 / 3, 3 / 4, ?_, by norm_num, by norm_num⟩
    have : (d : ℝ) ≤ 1 := by exact_mod_cast hd
    linarith

/-- **`(4)`: the rank-two wall.**  In rank at least two no radial polynomial exponent works. -/
theorem no_gamma_dimension_window_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    ¬ (∃ κ σ : ℝ, (d : ℝ) / 2 < κ ∧ κ < σ ∧ σ < 1) := by
  rw [exists_gamma_dimension_window_iff]
  omega

/-- **`(1)`: the exact lattice threshold.**  The bounded-orbit embedding holds exactly when
`d/2 < κ`. -/
theorem summable_latticeBracket_two_kappa_iff {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 0 ≤ κ) :
    Summable (fun ν : Fin d → ℤ => latticeBracket ν ^ (-(2 * κ))) ↔ (d : ℝ) / 2 < κ := by
  rw [summable_latticeBracket_rpow_iff hd (by linarith)]
  constructor <;> intro h <;> linarith

/-- **`(12)`, `(13)`: the concrete rank-one window.**  At `(κ,σ) = (2/3,3/4)` the lattice square
converges in rank one. -/
theorem summable_rankOne_window :
    Summable (fun ν : Fin 1 → ℤ => latticeBracket ν ^ (-(2 * (2 / 3 : ℝ)))) := by
  rw [summable_latticeBracket_two_kappa_iff (by norm_num) (by norm_num)]
  norm_num

end GaloisForLFunctions.RHTower
