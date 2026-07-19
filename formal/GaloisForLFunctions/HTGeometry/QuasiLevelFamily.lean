import GaloisForLFunctions.HTGeometry.QuasiMomentLimit
import GaloisForLFunctions.HTGeometry.NevAlphaCofinal

/-!
# The quasi family along an arbitrary sequence of levels

Every per-level statement of the construction is already stated for an arbitrary level and
parameter; only the family statements fixed the level to `n+1`.  They are restated here for a level
function `ν` growing at least as fast, which is what allows the limit to be taken along the levels
where the denominator has full degree.

Those levels are cofinal, so such a `ν` exists for every parameter.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Tightness along an arbitrary level sequence.** -/
theorem isTightMeasureSet_quasiProb_of_level (h : PositiveMomentForm s) (ν : ℕ → ℕ)
    (hν : ∀ n, n + 1 ≤ ν n) (τ : ℕ → ℝ) :
    IsTightMeasureSet (Set.range fun n : ℕ => quasiProb s (ν n) (τ n)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨Set.Icc (-1) 1, isCompact_Icc, fun μ _ => le_top⟩
  · have he0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hs0 : 0 < s 0 := moment_zero_pos h
    have hs2 : 0 < s 2 := moment_two_pos h
    have hcpos : 0 < s 2 / (s 0 * ε.toReal) := div_pos hs2 (mul_pos hs0 he0)
    refine ⟨Set.Icc (-Real.sqrt (s 2 / (s 0 * ε.toReal)))
      (Real.sqrt (s 2 / (s 0 * ε.toReal))), isCompact_Icc, ?_⟩
    rintro μ ⟨n, rfl⟩
    have hRpos : 0 < Real.sqrt (s 2 / (s 0 * ε.toReal)) := Real.sqrt_pos.mpr hcpos
    have hlvl : 1 ≤ ν n := le_trans (by omega) (hν n)
    refine le_trans (quasiProb_compl_Icc_le h hlvl (τ n) hRpos) ?_
    rw [Real.sq_sqrt hcpos.le]
    have hval : (s 0)⁻¹ * (s 2 / (s 2 / (s 0 * ε.toReal))) = ε.toReal := by
      have hs0' : s 0 ≠ 0 := hs0.ne'
      have hs2' : s 2 ≠ 0 := hs2.ne'
      have he0' : ε.toReal ≠ 0 := he0.ne'
      field_simp
    rw [hval, ENNReal.ofReal_toReal hεtop]

/-- **A convergent subsequence along an arbitrary level sequence.** -/
theorem exists_subseq_tendsto_quasiProbMeasure_of_level (h : PositiveMomentForm s) (ν : ℕ → ℕ)
    (hν : ∀ n, n + 1 ≤ ν n) (τ : ℕ → ℝ) :
    ∃ (μ : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun i => quasiProbMeasure h (ν (φ i)) (τ (φ i))) atTop (nhds μ) := by
  have hK : IsCompact (closure (Set.range fun n : ℕ => quasiProbMeasure h (ν n) (τ n))) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    have hcoe : {((μ : ProbabilityMeasure ℝ) : Measure ℝ) |
          μ ∈ Set.range fun n : ℕ => quasiProbMeasure h (ν n) (τ n)}
        = Set.range fun n : ℕ => quasiProb s (ν n) (τ n) := by
      ext W
      constructor
      · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨quasiProbMeasure h (ν n) (τ n), ⟨n, rfl⟩, rfl⟩
    rw [hcoe]
    exact isTightMeasureSet_quasiProb_of_level h ν hν τ
  have hmem : ∀ n : ℕ, quasiProbMeasure h (ν n) (τ n)
      ∈ closure (Set.range fun n : ℕ => quasiProbMeasure h (ν n) (τ n)) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨μ, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  exact ⟨μ, φ, hφ, hlim⟩

/-- **The moments of a weak limit along an arbitrary level sequence.** -/
theorem hasMoments_of_tendsto_quasi_of_level (h : PositiveMomentForm s) (ν : ℕ → ℕ)
    (hν : ∀ n, n + 1 ≤ ν n) (τ : ℕ → ℝ)
    {μ : ProbabilityMeasure ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hopen : ∀ G, IsOpen G →
      (μ : Measure ℝ) G ≤ atTop.liminf fun i => quasiProb s (ν (φ i)) (τ (φ i)) G)
    (hlim : Tendsto (fun i => quasiProbMeasure h (ν (φ i)) (τ (φ i))) atTop (nhds μ)) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
      ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k := by
  have hs0 : 0 < s 0 := moment_zero_pos h
  have hs2k : 0 < s (2 * k) := moment_even_pos h k
  have hgrow : ∀ i, k ≤ i → k ≤ ν (φ i) := by
    intro i hi
    have h1 : i ≤ φ i := hφ.le_apply
    have h2 : φ i + 1 ≤ ν (φ i) := hν (φ i)
    omega
  set C : ENNReal := (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s (2 * k)) with hCdef
  have hCtop : C ≠ ⊤ := by
    rw [hCdef]
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ?_) ENNReal.ofReal_ne_top
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hs0
  have hCreal : C.toReal = (s 0)⁻¹ * s (2 * k) := by
    rw [hCdef, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hs0.le, ENNReal.toReal_ofReal hs2k.le]
  have hlint : ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(μ : Measure ℝ) ≤ C := by
    refine lintegral_even_pow_le_of_forall_isOpen_le_liminf k hopen ?_
    refine Filter.eventually_atTop.mpr ⟨k, fun i hi => ?_⟩
    exact le_of_eq (lintegral_even_pow_quasiProb h (ν (φ i)) (τ (φ i)) k (by
      have := hgrow i hi; omega))
  have hmeas : Measurable fun x : ℝ => x ^ (2 * k) := measurable_id.pow_const _
  have hnn : ∀ x : ℝ, 0 ≤ x ^ (2 * k) := pow_two_mul_nonneg k
  have hint2 : Integrable (fun x : ℝ => x ^ (2 * k)) (μ : Measure ℝ) :=
    integrable_of_lintegral_ofReal_lt_top hmeas hnn
      (lt_of_le_of_lt hlint (lt_top_iff_ne_top.mpr hCtop))
  have hMmu : ∫ x, x ^ (2 * k) ∂(μ : Measure ℝ) ≤ C.toReal :=
    integral_le_toReal_of_lintegral_le hmeas hnn hCtop hlint
  have hintk : Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) :=
    integrable_pow_of_integrable_even k hint2
  refine ⟨hintk, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : ∫ x : ℝ, x ^ 0 ∂(μ : Measure ℝ) = 1 := by simp
    rw [h0, inv_mul_cancel₀ hs0.ne']
  have hMnu : ∀ᶠ i in atTop,
      ∫ x, x ^ (2 * k) ∂(quasiProb s (ν (φ i)) (τ (φ i))) ≤ C.toReal := by
    refine Filter.eventually_atTop.mpr ⟨k, fun i hi => ?_⟩
    refine le_of_eq ?_
    rw [integral_pow_quasiProb h (ν (φ i)) (τ (φ i)) (2 * k) (by
      have := hgrow i hi; omega), hCreal]
  have hmain := tendsto_integral_pow_of_uniform_even_moment
    (μ := (μ : Measure ℝ)) (νs := fun i => quasiProb s (ν (φ i)) (τ (φ i))) hk
    (fun f => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f)
    hMnu hMmu
    (fun i => integrable_quasiProb h _ _ _)
    (fun i => integrable_quasiProb h _ _ _)
    (fun R _ i => integrable_quasiProb h _ _ _)
    hintk hint2
    (fun R hR => integrable_truncPow hR k)
  have hconst : (fun _ : ℕ => (s 0)⁻¹ * s k)
      =ᶠ[atTop] fun i => ∫ x, x ^ k ∂(quasiProb s (ν (φ i)) (τ (φ i))) := by
    refine Filter.eventually_atTop.mpr ⟨k, fun i hi => ?_⟩
    exact (integral_pow_quasiProb h (ν (φ i)) (τ (φ i)) k (by
      have := hgrow i hi; omega)).symm
  exact tendsto_nhds_unique hmain (Tendsto.congr' hconst tendsto_const_nhds)

/-! ## The levels of full degree -/

/-- A level above `n` at which the denominator has full degree. -/
noncomputable def goodLevel (h : PositiveMomentForm s) (tau : ℝ) (n : ℕ) : ℕ :=
  (exists_ge_nevAlpha_ne_zero h tau (n + 1)).choose

theorem goodLevel_ge (h : PositiveMomentForm s) (tau : ℝ) (n : ℕ) :
    n + 1 ≤ goodLevel h tau n :=
  (exists_ge_nevAlpha_ne_zero h tau (n + 1)).choose_spec.1

theorem goodLevel_nevAlpha_ne_zero (h : PositiveMomentForm s) (tau : ℝ) (n : ℕ) :
    nevAlpha s (goodLevel h tau n) tau ≠ 0 :=
  (exists_ge_nevAlpha_ne_zero h tau (n + 1)).choose_spec.2

/-- The quasi parameter selecting the level-`goodLevel n` denominator. -/
noncomputable def leafParam (h : PositiveMomentForm s) (tau : ℝ) (n : ℕ) : ℝ :=
  nevBeta s (goodLevel h tau n) tau / nevAlpha s (goodLevel h tau n) tau

end HTGeometry
