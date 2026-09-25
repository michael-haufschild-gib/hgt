import GaloisForLFunctions.RHTower.SpectralBlaschkeMatching
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.XiLaguerreZeroSumIdentity

/-!
# Localised Hermite positivity

The open core left by the Blaschke form is that the holomorphic data of `Ξ` deliver the *unweighted*
power sums of the resolvent and never the displacement weighting. This module turns that around: it
uses the unweighted power sums as they stand, in the one classical criterion that reads reality of a
spectrum out of power sums alone — Hermite's.

Fix a real base point `t` off the spectral divisor and set `u_q = (t − z_q)^{-1}`. The localised
power sums are

  `p_k(t) = Σ_q u_q^k`,

which converge for `k ≥ 2` because the divisor is locally finite, and whose lowest member is an
explicit derivative of the logarithmic derivative of `Ξ`:

  `p_2(t) = −(logDeriv Ξ)'(t)`.

For a real test vector `c` supported on a finite set, the Hankel form of these power sums factors
exactly:

  `Σ_{i,j} c_i c_j p_{i+j+2}(t) = Σ_q P(u_q)²`,   `P(x) = Σ_i c_i x^{i+1}`,

and this identity is unconditional. Under the hypothesis every `u_q` is real, so the right side is a
sum of squares of real numbers and the form is a nonnegative real. Contrapositively, **a single
negative value of the form, at a single base point and a single test vector, refutes the
hypothesis.**

What is new here is not Hermite's criterion but its *localisation*. The corpus already carries the
finite Hermite/Hankel positivity for a finite real spectrum and the finite Hermite–Sylvester
converse, and it carries the Jensen–Turán hyperbolicity route, which is global: it reads the Taylor
coefficients of `Ξ` at one point. The weight analysis of this lane says that a criterion anchored at
one base point cannot see a near-line zero, because the signal lives at the scale of the
displacement and at a place determined by the ordinate. The present form is anchored at every real
`t`, and the partner structure survives the localisation: the line conjugation acts on the resolvent
as complex conjugation, so a zero and its partner contribute `P(u)²` and its conjugate, and the orbit
contributes twice the real part. That is where a negative value can come from, and it is the only
place it can come from.
-/

open Complex

namespace RHTower

noncomputable section

/-- A real base point avoiding the spectral divisor. -/
def OffSpectralDivisor (t : ℝ) : Prop :=
  ∀ ρ : XiDivisorSupport, (t : ℂ) ≠ xiSpectralPointSupport ρ

/-- The localised resolvent of the spectral divisor at a real base point. -/
def spectralResolvent (t : ℝ) (q : XiZeroCopy) : ℂ := ((t : ℂ) - xiSpectralPoint q)⁻¹

theorem normSq_sub_xiSpectralPoint (t : ℝ) (q : XiZeroCopy) :
    Complex.normSq ((t : ℂ) - xiSpectralPoint q)
      = ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
  rw [xiSpectralPoint_eq_support]
  exact normSq_sub_xiSpectralPointSupport t q.1

/-- **The partner's resolvent is the conjugate.** -/
theorem spectralResolvent_lineConj (t : ℝ) (q : XiZeroCopy) :
    spectralResolvent t (xiZeroCopyLineConjEquiv q)
      = (starRingEnd ℂ) (spectralResolvent t q) := by
  rw [spectralResolvent, spectralResolvent, xiSpectralPoint_lineConj, map_inv₀, map_sub,
    Complex.conj_ofReal]

/-- **Uniform separation.** A real point off the spectral divisor stays a positive distance from all
of it, because the divisor is locally finite. -/
theorem exists_spectral_separation {t : ℝ} (ht : OffSpectralDivisor t) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ ρ : XiDivisorSupport,
      d₀ ≤ ((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (ρ : ℂ).im) ^ (2 : ℕ) := by
  classical
  set f : XiDivisorSupport → ℝ :=
    fun ρ => ((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (ρ : ℂ).im) ^ (2 : ℕ) with hf
  have hfpos : ∀ ρ, 0 < f ρ := by
    intro ρ
    have hns : Complex.normSq ((t : ℂ) - xiSpectralPointSupport ρ) = f ρ :=
      normSq_sub_xiSpectralPointSupport t ρ
    show 0 < f ρ
    rw [← hns, Complex.normSq_pos, sub_ne_zero]
    exact ht ρ
  set A : Set XiDivisorSupport := {ρ | f ρ ≤ 1} with hA
  have hAfin : A.Finite := by
    refine Set.Finite.subset (finite_xiDivisorSupport_band t (by norm_num : (0 : ℝ) ≤ 1)) ?_
    intro ρ hρ
    have h1 : f ρ ≤ 1 := hρ
    have h2 : (t - (ρ : ℂ).im) ^ (2 : ℕ) ≤ 1 := by
      have := sq_nonneg ((ρ : ℂ).re - 1 / 2)
      rw [hf] at h1
      nlinarith
    show |(ρ : ℂ).im - t| ≤ 1
    rw [abs_le]
    constructor <;> nlinarith
  rcases Set.eq_empty_or_nonempty A with hA0 | hAne
  · refine ⟨1, one_pos, le_refl 1, fun ρ => ?_⟩
    by_contra hc
    push Not at hc
    exact Set.eq_empty_iff_forall_notMem.mp hA0 ρ (le_of_lt hc)
  · obtain ⟨ρ₀, hρ₀A, hρ₀min⟩ := Set.exists_min_image A f hAfin hAne
    refine ⟨min (f ρ₀) 1, lt_min (hfpos ρ₀) one_pos, min_le_right _ _, fun ρ => ?_⟩
    by_cases hρ : ρ ∈ A
    · exact le_trans (min_le_left _ _) (hρ₀min ρ hρ)
    · have h1 : (1 : ℝ) ≤ f ρ := le_of_not_ge (fun hc => hρ hc)
      exact le_trans (min_le_right _ _) h1

theorem norm_sq_spectralResolvent (t : ℝ) (q : XiZeroCopy) :
    ‖spectralResolvent t q‖ ^ (2 : ℕ)
      = (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ))⁻¹ := by
  rw [← Complex.normSq_eq_norm_sq, spectralResolvent, Complex.normSq_inv,
    normSq_sub_xiSpectralPoint]

theorem summable_norm_sq_spectralResolvent {t : ℝ} (ht : OffSpectralDivisor t) :
    Summable (fun q : XiZeroCopy => ‖spectralResolvent t q‖ ^ (2 : ℕ)) := by
  obtain ⟨d₀, hd₀, hd₁, hsep⟩ := exists_spectral_separation ht
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    ((summable_xiZeroWeight t).mul_left (2 / d₀))
  have hs := hsep q.1
  have hsq : (0 : ℝ) ≤ ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) := sq_nonneg _
  have hu : (0 : ℝ) ≤ (t - (q.1 : ℂ).im) ^ (2 : ℕ) := sq_nonneg _
  have hD : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
    linarith
  have hpos : (0 : ℝ) < 1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by positivity
  have hrw : (2 / d₀) * ((1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ)))
      = 2 / (d₀ * (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ))) := by
    rw [div_mul_div_comm, mul_one]
  rw [norm_sq_spectralResolvent, hrw, inv_eq_one_div,
    le_div_iff₀ (by positivity : (0 : ℝ) < d₀ * (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ))),
    div_mul_eq_mul_div, div_le_iff₀ hD]
  nlinarith [mul_nonneg (sub_nonneg.mpr hd₁) hu]

theorem summable_spectralResolvent_pow {t : ℝ} (ht : OffSpectralDivisor t) {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun q : XiZeroCopy => spectralResolvent t q ^ k) := by
  obtain ⟨d₀, hd₀, hd₁, hsep⟩ := exists_spectral_separation ht
  set M : ℝ := 1 + 1 / d₀ with hM
  have hMnn : (0 : ℝ) ≤ M := by positivity
  have hbound : ∀ q : XiZeroCopy, ‖spectralResolvent t q‖ ≤ M := by
    intro q
    have hs := hsep q.1
    have h2 : ‖spectralResolvent t q‖ ^ (2 : ℕ) ≤ 1 / d₀ := by
      have hD : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        linarith
      rw [norm_sq_spectralResolvent, inv_eq_one_div, le_div_iff₀ hd₀,
        div_mul_eq_mul_div, div_le_iff₀ hD]
      linarith
    have hn : (0 : ℝ) ≤ ‖spectralResolvent t q‖ := norm_nonneg _
    have hd : (0 : ℝ) ≤ 1 / d₀ := by positivity
    nlinarith
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    ((summable_norm_sq_spectralResolvent ht).mul_left (M ^ (k - 2))))
  rw [norm_pow]
  have hsplit : ‖spectralResolvent t q‖ ^ k
      = ‖spectralResolvent t q‖ ^ (k - 2) * ‖spectralResolvent t q‖ ^ (2 : ℕ) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  gcongr
  exact hbound q

/-- A finite sum of summable families is summable. -/
private theorem summable_finsetSumAux {ι : Type*} (f : ι → XiZeroCopy → ℂ) (s : Finset ι)
    (h : ∀ i ∈ s, Summable (f i)) : Summable (fun q : XiZeroCopy => ∑ i ∈ s, f i q) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro a u ha ih h
  have h1 : Summable (f a) := h a (Finset.mem_insert_self a u)
  have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
  simpa [Finset.sum_insert ha] using h1.add h2

/-- The localised power sums of the spectral divisor. -/
def spectralPowerSum (t : ℝ) (k : ℕ) : ℂ := ∑' q : XiZeroCopy, spectralResolvent t q ^ k

/-- **The lowest power sum is an explicit derivative of the logarithmic derivative of `Ξ`.** -/
theorem spectralPowerSum_two (t : ℝ) (hz : XiC (t : ℂ) ≠ 0) :
    spectralPowerSum t 2 = -deriv (logDeriv XiC) (t : ℂ) := by
  have h := (hasSum_neg_inv_sq_deriv_logDeriv_XiC hz).neg
  have h2 : HasSum (fun q : XiZeroCopy => spectralResolvent t q ^ (2 : ℕ))
      (-deriv (logDeriv XiC) (t : ℂ)) := by
    simpa [spectralResolvent, inv_pow] using h
  exact h2.tsum_eq

/-- The test polynomial evaluated at one resolvent. -/
def hermiteTestValue (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) (q : XiZeroCopy) : ℂ :=
  ∑ i ∈ s, ((c i : ℝ) : ℂ) * spectralResolvent t q ^ (i + 1)

/-- **The orbit structure.** The partner's test value is the conjugate, so a functional-equation
orbit contributes twice the real part of one square. -/
theorem hermiteTestValue_lineConj (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) (q : XiZeroCopy) :
    hermiteTestValue s c t (xiZeroCopyLineConjEquiv q)
      = (starRingEnd ℂ) (hermiteTestValue s c t q) := by
  rw [hermiteTestValue, hermiteTestValue, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, Complex.conj_ofReal, spectralResolvent_lineConj]

theorem hermiteTestValue_sq (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) (q : XiZeroCopy) :
    hermiteTestValue s c t q ^ (2 : ℕ)
      = ∑ i ∈ s, ∑ j ∈ s,
          ((c i * c j : ℝ) : ℂ) * spectralResolvent t q ^ (i + j + 2) := by
  rw [hermiteTestValue, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [show i + j + 2 = (i + 1) + (j + 1) by omega, pow_add]
  ring

theorem summable_hermiteTestValue_sq {t : ℝ} (ht : OffSpectralDivisor t) (s : Finset ℕ)
    (c : ℕ → ℝ) : Summable (fun q : XiZeroCopy => hermiteTestValue s c t q ^ (2 : ℕ)) := by
  classical
  refine Summable.congr ?_ (fun q => (hermiteTestValue_sq s c t q).symm)
  exact summable_finsetSumAux _ s (fun i _ =>
    summable_finsetSumAux _ s (fun j _ =>
      (summable_spectralResolvent_pow ht (by omega)).mul_left _))

/-- **The localised Hermite identity.** Unconditional: the Hankel form of the localised power sums
is the sum over the divisor of the squares of the test polynomial at the resolvents. -/
theorem hermiteForm_eq_tsum_sq {t : ℝ} (ht : OffSpectralDivisor t) (s : Finset ℕ) (c : ℕ → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, ((c i * c j : ℝ) : ℂ) * spectralPowerSum t (i + j + 2)
      = ∑' q : XiZeroCopy, hermiteTestValue s c t q ^ (2 : ℕ) := by
  classical
  have hij : ∀ i j : ℕ, Summable (fun q : XiZeroCopy =>
      ((c i * c j : ℝ) : ℂ) * spectralResolvent t q ^ (i + j + 2)) :=
    fun i j => (summable_spectralResolvent_pow ht (by omega)).mul_left _
  have hi : ∀ i : ℕ, Summable (fun q : XiZeroCopy =>
      ∑ j ∈ s, ((c i * c j : ℝ) : ℂ) * spectralResolvent t q ^ (i + j + 2)) :=
    fun i => summable_finsetSumAux _ s (fun j _ => hij i j)
  rw [tsum_congr (hermiteTestValue_sq s c t), Summable.tsum_finsetSum (fun i _ => hi i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum (fun j _ => hij i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [spectralPowerSum, tsum_mul_left]

theorem spectralResolvent_im_eq_zero_of_riemannHypothesis (h : RiemannHypothesis) (t : ℝ)
    (q : XiZeroCopy) : (spectralResolvent t q).im = 0 := by
  have hz : (xiSpectralPoint q).im = 0 := by
    rw [xiSpectralPoint_eq_support]
    exact riemannHypothesis_iff_forall_xiSpectralPointSupport_im_eq_zero.mp h q.1
  rw [spectralResolvent, Complex.inv_im]
  simp [hz]

theorem hermiteTestValue_im_eq_zero_of_riemannHypothesis (h : RiemannHypothesis) (s : Finset ℕ)
    (c : ℕ → ℝ) (t : ℝ) (q : XiZeroCopy) : (hermiteTestValue s c t q).im = 0 := by
  rw [hermiteTestValue, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hu := spectralResolvent_im_eq_zero_of_riemannHypothesis h t q
  have hpow : (spectralResolvent t q ^ (i + 1)).im = 0 := by
    have hre : spectralResolvent t q = (((spectralResolvent t q).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simp [hu])
    rw [hre, ← Complex.ofReal_pow, Complex.ofReal_im]
  simp [Complex.mul_im, hpow]

/-- **Localised Hermite positivity.** Under the hypothesis the Hankel form of the localised power
sums is a nonnegative real, at every base point off the divisor and for every real test vector. -/
theorem hermiteForm_re_nonneg_of_riemannHypothesis (h : RiemannHypothesis) {t : ℝ}
    (ht : OffSpectralDivisor t) (s : Finset ℕ) (c : ℕ → ℝ) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, ((c i * c j : ℝ) : ℂ) * spectralPowerSum t (i + j + 2)).re := by
  rw [hermiteForm_eq_tsum_sq ht, re_tsum (summable_hermiteTestValue_sq ht s c)]
  refine tsum_nonneg fun q => ?_
  have him := hermiteTestValue_im_eq_zero_of_riemannHypothesis h s c t q
  rw [sq, Complex.mul_re, him]
  nlinarith [sq_nonneg (hermiteTestValue s c t q).re]

/-- **Falsifiability.** One negative value of the localised Hermite form, at one base point and one
test vector, refutes the hypothesis. -/
theorem not_riemannHypothesis_of_hermiteForm_re_neg {t : ℝ} (ht : OffSpectralDivisor t)
    (s : Finset ℕ) (c : ℕ → ℝ)
    (hneg : (∑ i ∈ s, ∑ j ∈ s, ((c i * c j : ℝ) : ℂ) * spectralPowerSum t (i + j + 2)).re < 0) :
    ¬ RiemannHypothesis :=
  fun h => absurd (hermiteForm_re_nonneg_of_riemannHypothesis h ht s c) (not_le.mpr hneg)

end

end RHTower
