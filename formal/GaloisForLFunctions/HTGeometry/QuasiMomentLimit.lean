import GaloisForLFunctions.HTGeometry.QuasiTightness
import GaloisForLFunctions.HTGeometry.GaussMomentLimit
import GaloisForLFunctions.HTGeometry.HamburgerExistence

/-!
# A representing measure from the quasi-orthogonal family

The quasi rules reproduce the moments only to order `2n` rather than `2n+1`, which changes nothing:
every statement below needs the exactness to hold *eventually* in the level, and it does.

The parameter is allowed to vary with the level throughout, since the parameter selecting a leaf is
not constant along the approximating sequence.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

theorem lintegral_quasiMeasure (s : ℕ → ℝ) (n : ℕ) (t : ℝ) (f : ℝ → ENNReal) :
    ∫⁻ x, f x ∂(quasiMeasure s n t)
      = ∑ ξ ∈ quasiNodes s n t, ENNReal.ofReal (quasiWeight s n t ξ) * f ξ := by
  rw [quasiMeasure]
  exact lintegral_finsetWeightedDirac _ _ f

/-- The even moments of the quasi measure, as lower integrals. -/
theorem lintegral_even_pow_quasiMeasure (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (k : ℕ)
    (hk : 2 * k ≤ 2 * n) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(quasiMeasure s n t) = ENNReal.ofReal (s (2 * k)) := by
  classical
  rw [lintegral_quasiMeasure s n t]
  have hterm : ∀ ξ ∈ quasiNodes s n t,
      ENNReal.ofReal (quasiWeight s n t ξ) * ENNReal.ofReal (ξ ^ (2 * k))
        = ENNReal.ofReal (quasiWeight s n t ξ * ξ ^ (2 * k)) := by
    intro ξ hξ
    rw [← ENNReal.ofReal_mul (quasiWeight_pos h n t hξ).le]
  rw [Finset.sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg fun ξ hξ =>
      mul_nonneg (quasiWeight_pos h n t hξ).le (pow_two_mul_nonneg k ξ),
    quasiSum_pow h n t (2 * k) hk]

theorem lintegral_even_pow_quasiProb (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (k : ℕ)
    (hk : 2 * k ≤ 2 * n) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(quasiProb s n t)
      = (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s (2 * k)) := by
  rw [quasiProb, lintegral_smul_measure, lintegral_even_pow_quasiMeasure h n t k hk, smul_eq_mul]

/-- Every function is integrable against the normalised quasi measure. -/
theorem integrable_quasiProb (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (f : ℝ → ℝ) :
    Integrable f (quasiProb s n t) := by
  rw [quasiProb]
  refine (integrable_quasiMeasure n t f).smul_measure (ENNReal.inv_ne_top.mpr ?_)
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact moment_zero_pos h

/-- The Bochner moments of the normalised quasi measure. -/
theorem integral_pow_quasiProb (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (k : ℕ)
    (hk : k ≤ 2 * n) : ∫ x, x ^ k ∂(quasiProb s n t) = (s 0)⁻¹ * s k := by
  rw [quasiProb, integral_smul_measure, integral_quasiMeasure h n t fun x => x ^ k,
    quasiSum_pow h n t k hk, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (moment_zero_pos h).le, smul_eq_mul]

/-- **A convergent subsequence exists**, for any sequence of parameters. -/
theorem exists_subseq_tendsto_quasiProbMeasure (h : PositiveMomentForm s) (τ : ℕ → ℝ) :
    ∃ (μ : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun i => quasiProbMeasure h (φ i + 1) (τ (φ i))) atTop (nhds μ) := by
  have hK := isCompact_closure_quasiProbMeasure h τ
  have hmem : ∀ n : ℕ, quasiProbMeasure h (n + 1) (τ n)
      ∈ closure (Set.range fun n : ℕ => quasiProbMeasure h (n + 1) (τ n)) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨μ, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  exact ⟨μ, φ, hφ, hlim⟩

/-- The moment bound along a subsequence. -/
theorem lintegral_even_pow_limit_le_subseq_quasi (h : PositiveMomentForm s) (τ : ℕ → ℝ) (k : ℕ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {μ : Measure ℝ}
    (h_opens : ∀ G, IsOpen G →
      μ G ≤ atTop.liminf fun i => quasiProb s (φ i + 1) (τ (φ i)) G) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂μ
      ≤ (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s (2 * k)) := by
  refine lintegral_even_pow_le_of_forall_isOpen_le_liminf k h_opens ?_
  refine Filter.eventually_atTop.mpr ⟨k, fun i hi => ?_⟩
  have hle : i ≤ φ i := hφ.le_apply
  exact le_of_eq (lintegral_even_pow_quasiProb h (φ i + 1) (τ (φ i)) k (by omega))

/-- **The moments of a weak limit of the quasi family.** -/
theorem hasMoments_of_tendsto_quasi (h : PositiveMomentForm s) (τ : ℕ → ℝ)
    {μ : ProbabilityMeasure ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hopen : ∀ G, IsOpen G →
      (μ : Measure ℝ) G ≤ atTop.liminf fun i => quasiProb s (φ i + 1) (τ (φ i)) G)
    (hlim : Tendsto (fun i => quasiProbMeasure h (φ i + 1) (τ (φ i))) atTop (nhds μ)) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
      ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k := by
  have hs0 : 0 < s 0 := moment_zero_pos h
  have hs2k : 0 < s (2 * k) := moment_even_pos h k
  set C : ENNReal := (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s (2 * k)) with hCdef
  have hCtop : C ≠ ⊤ := by
    rw [hCdef]
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ?_) ENNReal.ofReal_ne_top
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hs0
  have hCreal : C.toReal = (s 0)⁻¹ * s (2 * k) := by
    rw [hCdef, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hs0.le, ENNReal.toReal_ofReal hs2k.le]
  have hlint : ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(μ : Measure ℝ) ≤ C :=
    lintegral_even_pow_limit_le_subseq_quasi h τ k hφ hopen
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
  have hMnu : ∀ᶠ i in atTop, ∫ x, x ^ (2 * k) ∂(quasiProb s (φ i + 1) (τ (φ i))) ≤ C.toReal := by
    refine Filter.eventually_atTop.mpr ⟨k, fun i hi => ?_⟩
    have hle : i ≤ φ i := hφ.le_apply
    refine le_of_eq ?_
    rw [integral_pow_quasiProb h (φ i + 1) (τ (φ i)) (2 * k) (by omega), hCreal]
  have hmain := tendsto_integral_pow_of_uniform_even_moment
    (μ := (μ : Measure ℝ)) (νs := fun i => quasiProb s (φ i + 1) (τ (φ i))) hk
    (fun f => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f)
    hMnu hMmu
    (fun i => integrable_quasiProb h _ _ _)
    (fun i => integrable_quasiProb h _ _ _)
    (fun R _ i => integrable_quasiProb h _ _ _)
    hintk hint2
    (fun R hR => integrable_truncPow hR k)
  have hconst : (fun _ : ℕ => (s 0)⁻¹ * s k)
      =ᶠ[atTop] fun i => ∫ x, x ^ k ∂(quasiProb s (φ i + 1) (τ (φ i))) := by
    refine Filter.eventually_atTop.mpr ⟨k, fun i hi => ?_⟩
    have hle : i ≤ φ i := hφ.le_apply
    exact (integral_pow_quasiProb h (φ i + 1) (τ (φ i)) k (by omega)).symm
  have htc : Tendsto (fun i => ∫ x, x ^ k ∂(quasiProb s (φ i + 1) (τ (φ i)))) atTop
      (nhds ((s 0)⁻¹ * s k)) :=
    Tendsto.congr' hconst tendsto_const_nhds
  exact tendsto_nhds_unique hmain htc

/-- **A representing measure from the quasi-orthogonal family**, for any sequence of parameters. -/
theorem exists_quasiLimit_hasMoments (h : PositiveMomentForm s) (τ : ℕ → ℝ) :
    ∃ (μ : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun i => quasiProbMeasure h (φ i + 1) (τ (φ i))) atTop (nhds μ) ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
        ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k := by
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_subseq_tendsto_quasiProbMeasure h τ
  exact ⟨μ, φ, hφ, hlim, fun k => hasMoments_of_tendsto_quasi h τ hφ
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG) hlim k⟩

end HTGeometry
