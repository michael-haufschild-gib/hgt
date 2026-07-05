/-
The Steinhaus random multiplicative model — foundation slice (docs 86–88).

The model probability space for the MWM lane's value-law statements:
independent uniform phases ω_p per coordinate, the random completely
multiplicative unimodular character
  X n ω = exp(2πi · Σ_p v_p(n)·ω_p),
and its algebra.  This slice: the space (via `Measure.infinitePi` on
uniform-[0,1] factors), complete multiplicativity, unimodularity.  The
integration layer (orthonormality E[X_n X̄_m] = δ_{nm}, the model
second-moment identity) is the next slice.
-/
import Mathlib

namespace RHTower
namespace SteinhausModel

open MeasureTheory Complex

/-- The phase space: one real phase per natural index (only prime indices
are ever read). -/
abbrev Omega : Type := ℕ → ℝ

/-- The model measure: independent uniform phases on [0,1] in every
coordinate. -/
noncomputable def steinhausMeasure : Measure Omega :=
  Measure.infinitePi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The random completely multiplicative character:
`X n ω = exp(2πi Σ_p v_p(n) ω_p)`. -/
noncomputable def X (n : ℕ) (ω : Omega) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    ((∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * ω p : ℝ) : ℂ))

theorem X_one (ω : Omega) : X 1 ω = 1 := by
  simp [X]

/-- Unimodularity: `‖X n ω‖ = 1`. -/
theorem norm_X (n : ℕ) (ω : Omega) : ‖X n ω‖ = 1 := by
  unfold X
  rw [Complex.norm_exp]
  have hre : (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      ((∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * ω p : ℝ) : ℂ)).re
      = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre, Real.exp_zero]

/-- The phase sum is supported on the actual prime factors: extending the
summation range does not change it. -/
theorem phase_sum_extend (n : ℕ) (ω : Omega) {s : Finset ℕ}
    (hs : n.primeFactors ⊆ s) :
    ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * ω p
      = ∑ p ∈ s, (n.factorization p : ℝ) * ω p := by
  refine Finset.sum_subset hs fun p _ hp => ?_
  have h0 : n.factorization p = 0 := by
    by_contra h
    exact hp (by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr h)
  rw [h0]
  simp

/-- **Complete multiplicativity**: `X (m·n) = X m · X n` for `m, n ≠ 0` —
the factorization is additive under multiplication. -/
theorem X_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (ω : Omega) :
    X (m * n) ω = X m ω * X n ω := by
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  have hsm : m.primeFactors ⊆ (m * n).primeFactors :=
    Nat.primeFactors_mono (dvd_mul_right m n) hmn
  have hsn : n.primeFactors ⊆ (m * n).primeFactors :=
    Nat.primeFactors_mono (dvd_mul_left n m) hmn
  have hsum : ∑ p ∈ (m * n).primeFactors, ((m * n).factorization p : ℝ) * ω p
      = (∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * ω p)
        + ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * ω p := by
    rw [phase_sum_extend m ω hsm, phase_sum_extend n ω hsn,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hfac : (m * n).factorization p
        = m.factorization p + n.factorization p := by
      rw [Nat.factorization_mul hm hn]
      rfl
    rw [hfac]
    push_cast
    ring
  unfold X
  rw [← Complex.exp_add, ← mul_add, hsum]
  push_cast
  ring_nf

end SteinhausModel
end RHTower

namespace RHTower
namespace SteinhausModel

open MeasureTheory Complex

instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

/-- One Fourier factor at integer frequency `k`. -/
noncomputable def charFactor (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((k : ℝ) * t : ℝ) : ℂ))

theorem charFactor_zero (t : ℝ) : charFactor 0 t = 1 := by
  simp [charFactor]

/-- **The single-phase character integral**: nonzero integer frequencies
average to zero over one period; frequency zero averages to one. -/
theorem charInt (k : ℤ) :
    ∫ t, charFactor k t ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      = if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [charFactor_zero]
    simp
  · rw [if_neg hk]
    have hform : ∀ t : ℝ, charFactor k t
        = Complex.exp (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I * (t : ℂ)) := by
      intro t
      unfold charFactor
      congr 1
      push_cast
      ring
    have hc : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      apply mul_ne_zero _ Complex.I_ne_zero
      rw [Complex.ofReal_ne_zero]
      have : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
      positivity
    calc ∫ t, charFactor k t ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
        = ∫ t in Set.Icc (0 : ℝ) 1,
            Complex.exp ((((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
          apply integral_congr_ae
          filter_upwards with t
          rw [hform t, mul_assoc]
      _ = ∫ t in Set.Ioc (0 : ℝ) 1,
            Complex.exp ((((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) :=
          integral_Icc_eq_integral_Ioc
      _ = ∫ t in (0 : ℝ)..1,
            Complex.exp ((((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) :=
          (intervalIntegral.integral_of_le (by norm_num)).symm
      _ = 0 := by
          rw [integral_exp_mul_complex hc]
          have h1 : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * ((1 : ℝ) : ℂ)
              = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
            push_cast
            ring
          have h0 : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * ((0 : ℝ) : ℂ) = 0 := by
            push_cast
            ring
          rw [h1, h0, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_zero, sub_self,
            zero_div]

/-- The joint frequency of `X n · conj (X m)` at prime `p`. -/
def freq (n m p : ℕ) : ℤ := (n.factorization p : ℤ) - (m.factorization p : ℤ)

/-- Pointwise cylinder form: `X n · conj (X m)` is a finite product of
single-phase factors over the union support. -/
theorem X_mul_conj_eq_prod {n m : ℕ} (ω : Omega) :
    X n ω * (starRingEnd ℂ) (X m ω)
      = ∏ p ∈ n.primeFactors ∪ m.primeFactors, charFactor (freq n m p) (ω p) := by
  set s := n.primeFactors ∪ m.primeFactors with hs
  unfold X
  rw [← Complex.exp_conj]
  rw [← Complex.exp_add]
  have hconj : (starRingEnd ℂ) (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      ((∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * ω p : ℝ) : ℂ))
      = -(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * ω p : ℝ) : ℂ)) := by
    rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj]
  have hn_ext := phase_sum_extend n ω (Finset.subset_union_left (s₂ := m.primeFactors))
  have hm_ext := phase_sum_extend m ω (Finset.subset_union_right (s₁ := n.primeFactors))
  rw [hn_ext, hm_ext]
  have harg : ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((∑ p ∈ s, (n.factorization p : ℝ) * ω p : ℝ) : ℂ)
      + -(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((∑ p ∈ s, (m.factorization p : ℝ) * ω p : ℝ) : ℂ))
      = ∑ p ∈ s, ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (((freq n m p : ℝ) * ω p : ℝ) : ℂ) := by
    push_cast [freq]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [harg, Complex.exp_sum]
  exact Finset.prod_congr rfl fun p _ => rfl

/-- **Orthonormality of the Steinhaus characters**:
`E[X n · conj (X m)] = δ_{nm}` for `n, m ≠ 0`. -/
theorem integral_X_mul_conj {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    ∫ ω, X n ω * (starRingEnd ℂ) (X m ω) ∂steinhausMeasure
      = if n = m then 1 else 0 := by
  classical
  set s := n.primeFactors ∪ m.primeFactors with hs
  have hstep1 : ∫ ω, X n ω * (starRingEnd ℂ) (X m ω) ∂steinhausMeasure
      = ∫ ω, ∏ p ∈ s, charFactor (freq n m p) (ω p) ∂steinhausMeasure := by
    apply integral_congr_ae
    filter_upwards with ω
    exact X_mul_conj_eq_prod ω
  have hcont : Continuous fun y : (i : ↥s) → ℝ =>
      ∏ i : ↥s, charFactor (freq n m ↑i) (y i) := by
    apply continuous_finsetProd
    intro i _
    exact (Complex.continuous_exp.comp
      (by continuity : Continuous fun t : ℝ =>
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (((freq n m ↑i : ℝ) * t : ℝ) : ℂ))).comp (continuous_apply i)
  have hmap : Measure.map s.restrict steinhausMeasure
      = Measure.pi fun _ : ↥s => volume.restrict (Set.Icc (0 : ℝ) 1) := by
    unfold steinhausMeasure
    exact Measure.infinitePi_map_restrict _
  have hstep2 : ∫ ω, ∏ p ∈ s, charFactor (freq n m p) (ω p) ∂steinhausMeasure
      = ∫ y : (i : ↥s) → ℝ, ∏ i : ↥s, charFactor (freq n m ↑i) (y i)
          ∂(Measure.pi fun _ : ↥s => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [← hmap, integral_map (Finset.measurable_restrict s).aemeasurable
      hcont.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with ω
    rw [← Finset.prod_coe_sort s (fun p => charFactor (freq n m p) (ω p))]
    rfl
  have hstep3 : ∫ y : (i : ↥s) → ℝ, ∏ i : ↥s, charFactor (freq n m ↑i) (y i)
        ∂(Measure.pi fun _ : ↥s => volume.restrict (Set.Icc (0 : ℝ) 1))
      = ∏ i : ↥s, ∫ t, charFactor (freq n m ↑i) t
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integral_fintype_prod_eq_prod fun (i : ↥s) (t : ℝ) => charFactor (freq n m ↑i) t
  rw [hstep1, hstep2, hstep3]
  rcases eq_or_ne n m with rfl | hne
  · rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i _
    rw [show freq n n ↑i = 0 by simp [freq], charInt, if_pos rfl]
  · rw [if_neg hne]
    have hdiff : ∃ p ∈ s, freq n m p ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne
      apply Nat.eq_of_factorization_eq hn hm
      intro p
      rcases Finset.decidableMem p s with hp | hp
      · have h1 : n.factorization p = 0 := by
          by_contra h
          exact hp (Finset.mem_union_left _ (by
            rw [← Nat.support_factorization]
            exact Finsupp.mem_support_iff.mpr h))
        have h2 : m.factorization p = 0 := by
          by_contra h
          exact hp (Finset.mem_union_right _ (by
            rw [← Nat.support_factorization]
            exact Finsupp.mem_support_iff.mpr h))
        rw [h1, h2]
      · have := hall p hp
        unfold freq at this
        omega
    obtain ⟨p, hps, hpk⟩ := hdiff
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨p, hps⟩ : ↥s))
    rw [charInt, if_neg hpk]

end SteinhausModel
end RHTower
