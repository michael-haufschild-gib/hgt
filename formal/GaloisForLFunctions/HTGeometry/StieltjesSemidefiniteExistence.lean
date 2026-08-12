import GaloisForLFunctions.HTGeometry.StieltjesExistence
import GaloisForLFunctions.HTGeometry.ReciprocalTailHankelStrict

/-!
# Existence in the semidefinite Stieltjes moment problem

Vanishing Hankel determinants cannot be discarded in the Stieltjes criterion.  This module removes
strictness without any rank assumption: add a positive reciprocal-tail moment sequence, construct
the strict Stieltjes measures, prove uniform tightness, and send the perturbation to zero.  Uniform
even-moment bounds identify every limiting moment, while portmanteau preserves half-line support.
-/

open scoped BigOperators
open MeasureTheory Filter Polynomial Set

namespace HTGeometry

variable {s : ℕ → ℝ}

theorem reciprocalTailClock_positiveMomentForm : PositiveMomentForm reciprocalTailClock :=
  positiveMomentForm_of_infiniteSupport reciprocalTailClock
    reciprocalTailClock_eq_moment reciprocalTailMeasure_integrable_moments
    reciprocalTailMeasure_infiniteSupport

theorem reciprocalTailClock_shifted_nonnegative (p : Polynomial ℝ) :
    0 ≤ momentFunctional reciprocalTailClock (X * p ^ 2) := by
  apply momentFunctional_X_mul_sq_nonneg reciprocalTailClock reciprocalTailClock_eq_moment
    reciprocalTailMeasure_integrable_moments
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hx.1

noncomputable def stieltjesPerturbationScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem stieltjesPerturbationScale_pos (n : ℕ) : 0 < stieltjesPerturbationScale n := by
  simp [stieltjesPerturbationScale]
  positivity

theorem stieltjesPerturbationScale_le_one (n : ℕ) : stieltjesPerturbationScale n ≤ 1 := by
  rw [stieltjesPerturbationScale, div_le_one (by positivity)]
  norm_num

theorem stieltjesPerturbationScale_tendsto :
    Tendsto stieltjesPerturbationScale atTop (nhds 0) := by
  rw [show stieltjesPerturbationScale = fun n : ℕ => (1 / ((n : ℝ) + 1)) by
    funext n
    rw [stieltjesPerturbationScale]]
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

noncomputable def stieltjesPerturbedSequence (s : ℕ → ℝ) (n k : ℕ) : ℝ :=
  s k + stieltjesPerturbationScale n * reciprocalTailClock k

theorem stieltjesPerturbedSequence_positiveMomentForm
    (hs : ∀ p : Polynomial ℝ, 0 ≤ momentInner s p p) (n : ℕ) :
    PositiveMomentForm (stieltjesPerturbedSequence s n) := by
  exact positiveMomentForm_perturb hs reciprocalTailClock_positiveMomentForm
    (stieltjesPerturbationScale_pos n)

theorem stieltjesPerturbedSequence_shifted_nonnegative
    (hshift : ∀ p : Polynomial ℝ, 0 ≤ momentFunctional s (X * p ^ 2))
    (n : ℕ) (p : Polynomial ℝ) :
    0 ≤ momentFunctional (stieltjesPerturbedSequence s n) (X * p ^ 2) := by
  exact shiftedMomentForm_nonnegative_perturb hshift
    reciprocalTailClock_shifted_nonnegative (stieltjesPerturbationScale_pos n).le p

theorem normalized_stieltjesPerturbedSequence_tendsto
    (h0 : 0 < s 0) (k : ℕ) :
    Tendsto (fun n => ((stieltjesPerturbedSequence s n 0)⁻¹ *
      stieltjesPerturbedSequence s n k)) atTop (nhds ((s 0)⁻¹ * s k)) := by
  have hc := stieltjesPerturbationScale_tendsto
  have hden : Tendsto (fun n => stieltjesPerturbedSequence s n 0) atTop (nhds (s 0)) := by
    simpa [stieltjesPerturbedSequence, reciprocalTailClock] using
      (tendsto_const_nhds.add hc)
  have hnum : Tendsto (fun n => stieltjesPerturbedSequence s n k) atTop (nhds (s k)) := by
    simpa [stieltjesPerturbedSequence] using
      (tendsto_const_nhds.add (hc.mul_const (reciprocalTailClock k)))
  exact (hden.inv₀ h0.ne').mul hnum

theorem moment_even_nonneg_of_semidefinite
    (hs : ∀ p : Polynomial ℝ, 0 ≤ momentInner s p p) (k : ℕ) :
    0 ≤ s (2 * k) := by
  have h := hs (X ^ k)
  rw [momentInner_def, ← pow_add, ← two_mul, momentFunctional_X_pow] at h
  exact h

theorem normalized_stieltjesPerturbedSequence_even_le
    (hs : ∀ p : Polynomial ℝ, 0 ≤ momentInner s p p)
    (h0 : 0 < s 0) (n k : ℕ) :
    (stieltjesPerturbedSequence s n 0)⁻¹ *
        stieltjesPerturbedSequence s n (2 * k)
      ≤ (s 0)⁻¹ * (s (2 * k) + 1) := by
  have hcpos := stieltjesPerturbationScale_pos n
  have hcle := stieltjesPerturbationScale_le_one n
  have heven := moment_even_nonneg_of_semidefinite hs k
  have hrnonneg : 0 ≤ reciprocalTailClock (2 * k) := by
    simp [reciprocalTailClock]
    positivity
  have hrle : reciprocalTailClock (2 * k) ≤ 1 := by
    rw [reciprocalTailClock, div_le_one (by positivity)]
    norm_num
  have hden : s 0 ≤ stieltjesPerturbedSequence s n 0 := by
    simp [stieltjesPerturbedSequence, reciprocalTailClock]
    positivity
  have hdenpos : 0 < stieltjesPerturbedSequence s n 0 := lt_of_lt_of_le h0 hden
  have hnum : stieltjesPerturbedSequence s n (2 * k) ≤ s (2 * k) + 1 := by
    rw [stieltjesPerturbedSequence]
    nlinarith
  calc
    (stieltjesPerturbedSequence s n 0)⁻¹ * stieltjesPerturbedSequence s n (2 * k)
        ≤ (s 0)⁻¹ * stieltjesPerturbedSequence s n (2 * k) := by
          gcongr
          exact add_nonneg heven (mul_nonneg hcpos.le hrnonneg)
    _ ≤ (s 0)⁻¹ * (s (2 * k) + 1) := by gcongr

/-- Full semidefinite Stieltjes existence, obtained by removing a strict positive perturbation. -/
theorem exists_probabilityMeasure_hasStieltjesMoments_semidefinite
    (hs : ∀ p : Polynomial ℝ, 0 ≤ momentInner s p p)
    (hshift : ∀ p : Polynomial ℝ, 0 ≤ momentFunctional s (X * p ^ 2))
    (h0 : 0 < s 0) :
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ k : ℕ,
        Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) ∧
          ∫ x, x ^ k ∂(ν : Measure ℝ) = (s 0)⁻¹ * s k) ∧
      ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x := by
  have hexists : ∀ n : ℕ, ∃ μ : ProbabilityMeasure ℝ,
      (∀ k : ℕ,
        Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
          ∫ x, x ^ k ∂(μ : Measure ℝ) =
            (stieltjesPerturbedSequence s n 0)⁻¹ * stieltjesPerturbedSequence s n k) ∧
      ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x := by
    intro n
    exact exists_probabilityMeasure_hasStieltjesMoments
      (stieltjesPerturbedSequence_positiveMomentForm hs n)
      (stieltjesPerturbedSequence_shifted_nonnegative hshift n)
  choose μ hμ using hexists
  have hmom (n k : ℕ) :
      Integrable (fun x : ℝ => x ^ k) (μ n : Measure ℝ) ∧
        ∫ x, x ^ k ∂(μ n : Measure ℝ) =
          (stieltjesPerturbedSequence s n 0)⁻¹ * stieltjesPerturbedSequence s n k :=
    (hμ n).1 k
  have hsupport (n : ℕ) : ∀ᵐ x ∂(μ n : Measure ℝ), 0 ≤ x := (hμ n).2
  let C : ℕ → ℝ := fun k => (s 0)⁻¹ * (s (2 * k) + 1)
  have hCpos (k : ℕ) : 0 < C k := by
    dsimp only [C]
    exact mul_pos (inv_pos.mpr h0)
      (by nlinarith [moment_even_nonneg_of_semidefinite hs k])
  have hlintegral (n k : ℕ) :
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(μ n : Measure ℝ) ≤ ENNReal.ofReal (C k) := by
    have hnn : 0 ≤ᵐ[(μ n : Measure ℝ)] fun x : ℝ => x ^ (2 * k) :=
      Filter.Eventually.of_forall fun x => pow_two_mul_nonneg k x
    rw [← ofReal_integral_eq_lintegral_ofReal (hmom n (2 * k)).1 hnn,
      (hmom n (2 * k)).2]
    exact ENNReal.ofReal_le_ofReal
      (normalized_stieltjesPerturbedSequence_even_le hs h0 n k)
  have htight : IsTightMeasureSet (Set.range fun n : ℕ => (μ n : Measure ℝ)) := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · exact ⟨Icc (-1) 1, isCompact_Icc, fun ν _ => le_top⟩
    · have he0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
      have hquot : 0 < C 1 / ε.toReal := div_pos (hCpos 1) he0
      let R := Real.sqrt (C 1 / ε.toReal)
      refine ⟨Icc (-R) R, isCompact_Icc, ?_⟩
      rintro ν ⟨n, rfl⟩
      have hRpos : 0 < R := Real.sqrt_pos.mpr hquot
      refine le_trans (measure_compl_Icc_le_of_lintegral_sq_le
        (C := ENNReal.ofReal (C 1)) ?_ hRpos) ?_
      · simpa using hlintegral n 1
      · rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hRpos)]
        have hRsq : R ^ 2 = C 1 / ε.toReal := Real.sq_sqrt hquot.le
        rw [hRsq]
        have hval : C 1 / (C 1 / ε.toReal) = ε.toReal := by
          field_simp [(hCpos 1).ne', he0.ne']
        rw [hval, ENNReal.ofReal_toReal hεtop]
  have hcompact : IsCompact (closure (Set.range μ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    have hcoe : {((ρ : ProbabilityMeasure ℝ) : Measure ℝ) |
          ρ ∈ Set.range μ} = Set.range fun n : ℕ => (μ n : Measure ℝ) := by
      ext ρ
      constructor
      · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨μ n, ⟨n, rfl⟩, rfl⟩
    rw [hcoe]
    exact htight
  have hmem : ∀ n : ℕ, μ n ∈ closure (Set.range μ) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨ν, -, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
  have hopen : ∀ G, IsOpen G →
      (ν : Measure ℝ) G ≤ atTop.liminf fun i => (μ (φ i) : Measure ℝ) G :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  have hνsupport : ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x := by
    have hzero : (ν : Measure ℝ) (Iio 0) = 0 := by
      apply measure_eq_zero_of_isOpen_le_liminf hopen isOpen_Iio
      intro i
      have hi := hsupport (φ i)
      rw [ae_iff] at hi
      have hset : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by
        ext x
        simp
      rwa [hset] at hi
    rw [ae_iff]
    have hset : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by
      ext x
      simp
    rwa [hset]
  refine ⟨ν, ?_, hνsupport⟩
  intro k
  have hlint : ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(ν : Measure ℝ)
      ≤ ENNReal.ofReal (C k) :=
    lintegral_even_pow_le_of_forall_isOpen_le_liminf k hopen
      (Filter.Eventually.of_forall fun i => hlintegral (φ i) k)
  have hmeas : Measurable fun x : ℝ => x ^ (2 * k) := measurable_id.pow_const _
  have hnn : ∀ x : ℝ, 0 ≤ x ^ (2 * k) := pow_two_mul_nonneg k
  have hint2 : Integrable (fun x : ℝ => x ^ (2 * k)) (ν : Measure ℝ) :=
    integrable_of_lintegral_ofReal_lt_top hmeas hnn
      (lt_of_le_of_lt hlint (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top))
  have hMν : ∫ x, x ^ (2 * k) ∂(ν : Measure ℝ) ≤ C k := by
    have hle := integral_le_toReal_of_lintegral_le hmeas hnn ENNReal.ofReal_ne_top hlint
    rwa [ENNReal.toReal_ofReal (hCpos k).le] at hle
  have hintk : Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) :=
    integrable_pow_of_integrable_even k hint2
  refine ⟨hintk, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [h0.ne']
  have hMμ : ∀ᶠ i in atTop,
      ∫ x, x ^ (2 * k) ∂(μ (φ i) : Measure ℝ) ≤ C k :=
    Filter.Eventually.of_forall fun i =>
      (hmom (φ i) (2 * k)).2.le.trans
        (normalized_stieltjesPerturbedSequence_even_le hs h0 (φ i) k)
  have hmain := tendsto_integral_pow_of_uniform_even_moment
    (μ := (ν : Measure ℝ)) (νs := fun i => (μ (φ i) : Measure ℝ)) hk
    (fun f => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f)
    hMμ hMν
    (fun i => (hmom (φ i) k).1)
    (fun i => (hmom (φ i) (2 * k)).1)
    (fun R _ i => integrable_truncPow (μ := (μ (φ i) : Measure ℝ)) (by assumption) k)
    hintk hint2
    (fun R hR => integrable_truncPow hR k)
  have hpert : Tendsto
      (fun i => (stieltjesPerturbedSequence s (φ i) 0)⁻¹ *
        stieltjesPerturbedSequence s (φ i) k)
      atTop (nhds ((s 0)⁻¹ * s k)) :=
    (normalized_stieltjesPerturbedSequence_tendsto h0 k).comp hφ.tendsto_atTop
  have heq : (fun i => (stieltjesPerturbedSequence s (φ i) 0)⁻¹ *
        stieltjesPerturbedSequence s (φ i) k) =ᶠ[atTop]
      fun i => ∫ x, x ^ k ∂(μ (φ i) : Measure ℝ) :=
    Filter.Eventually.of_forall fun i => (hmom (φ i) k).2.symm
  have hsource : Tendsto (fun i => ∫ x, x ^ k ∂(μ (φ i) : Measure ℝ)) atTop
      (nhds ((s 0)⁻¹ * s k)) := Tendsto.congr' heq hpert
  exact tendsto_nhds_unique hmain hsource

end HTGeometry
