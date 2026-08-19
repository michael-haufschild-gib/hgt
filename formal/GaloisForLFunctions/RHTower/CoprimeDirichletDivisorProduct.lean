import Mathlib
import GaloisForLFunctions.RHTower.RegularizedDivisorHarmonicLimit

/-!
# Divisor sums of a Dirichlet convolution with coprime supports

If two coefficient fields `a`, `b` are supported on mutually coprime integers then their Dirichlet
convolution has a **product** divisor sum:

```text
∑_{d ∣ k} (a ⋆ b)_d = ( ∑_{e ∣ k} a_e ) ( ∑_{f ∣ k} b_f ) .
```

The mechanism is that `e f ∣ k` is equivalent to `e ∣ k` and `f ∣ k` once `e` and `f` are coprime,
so the double sum over the divisor square is exactly the flattened sum over the antidiagonals.

This is the combinatorial step that assembles single-prime ladders into multi-prime ones: the
prime-power ladders at distinct primes have coprime supports.
-/

open Finset

namespace RHTower
namespace CoprimeDirichlet

noncomputable section

/-- Dirichlet convolution of two coefficient fields. -/
def dconv (a b : ℕ → ℝ) (d : ℕ) : ℝ := ∑ x ∈ d.divisorsAntidiagonal, a x.1 * b x.2

/-- Two coefficient fields have coprime supports. -/
def CoprimeSupport (a b : ℕ → ℝ) : Prop :=
  ∀ e f : ℕ, a e ≠ 0 → b f ≠ 0 → Nat.Coprime e f

/-- **Product law for divisor sums of a coprime-support convolution.** -/
theorem sum_divisors_dconv {a b : ℕ → ℝ} (hab : CoprimeSupport a b) {k : ℕ} (hk : k ≠ 0) :
    ∑ d ∈ k.divisors, dconv a b d = (∑ e ∈ k.divisors, a e) * (∑ f ∈ k.divisors, b f) := by
  classical
  set T := (k.divisors ×ˢ k.divisors).filter (fun y => y.1 * y.2 ∣ k) with hT
  have hzero : ∀ y ∈ k.divisors ×ˢ k.divisors, y ∉ T → a y.1 * b y.2 = 0 := by
    intro y hy hyT
    by_contra hne
    have ha : a y.1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have hb : b y.2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hcop := hab y.1 y.2 ha hb
    simp only [Finset.mem_product, Nat.mem_divisors] at hy
    exact hyT (by
      simp only [hT, Finset.mem_filter, Finset.mem_product, Nat.mem_divisors]
      exact ⟨⟨hy.1, hy.2⟩, hcop.mul_dvd_of_dvd_of_dvd hy.1.1 hy.2.1⟩)
  have hRHS : (∑ e ∈ k.divisors, a e) * (∑ f ∈ k.divisors, b f)
      = ∑ y ∈ T, a y.1 * b y.2 := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    exact (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
  rw [hRHS]
  rw [show (∑ d ∈ k.divisors, dconv a b d)
      = ∑ x ∈ (k.divisors).sigma (fun d => d.divisorsAntidiagonal), a x.2.1 * b x.2.2 from by
    simp only [dconv]
    rw [Finset.sum_sigma']]
  refine Finset.sum_nbij' (fun x => x.2) (fun y => ⟨y.1 * y.2, y⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, e, f⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisors, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨⟨hdk, -⟩, hef, -⟩ := hx
    simp only [hT, Finset.mem_filter, Finset.mem_product, Nat.mem_divisors]
    refine ⟨⟨⟨?_, hk⟩, ?_, hk⟩, ?_⟩
    · exact dvd_trans ⟨f, hef.symm⟩ hdk
    · exact dvd_trans ⟨e, by rw [← hef]; ring⟩ hdk
    · rw [hef]; exact hdk
  · rintro ⟨e, f⟩ hy
    simp only [hT, Finset.mem_filter, Finset.mem_product, Nat.mem_divisors] at hy
    have hne : e * f ≠ 0 := by
      intro h
      rcases Nat.mul_eq_zero.mp h with h0 | h0
      · exact hk (Nat.eq_zero_of_zero_dvd (by rw [← h0]; exact hy.1.1.1))
      · exact hk (Nat.eq_zero_of_zero_dvd (by rw [← h0]; exact hy.1.2.1))
    simp only [Finset.mem_sigma, Nat.mem_divisors, Nat.mem_divisorsAntidiagonal]
    exact ⟨⟨hy.2, hk⟩, trivial, hne⟩
  · rintro ⟨d, e, f⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    have : e * f = d := hx.2.1
    simp only [this]
  · rintro ⟨e, f⟩ _
    rfl
  · rintro ⟨d, e, f⟩ _
    rfl

/-! ## Injectivity of the product on coprime supports -/

open RegularizedDivisorHarmonic

theorem support_ne_zero {a : ℕ → ℝ} (ha0 : a 0 = 0) {e : ℕ} (he : a e ≠ 0) : e ≠ 0 := by
  intro h
  rw [h, ha0] at he
  exact he rfl

theorem mul_inj_on_support {a b : ℕ → ℝ} (ha0 : a 0 = 0) (_hb0 : b 0 = 0)
    (hab : CoprimeSupport a b) {e f e' f' : ℕ}
    (he : a e ≠ 0) (hf : b f ≠ 0) (he' : a e' ≠ 0) (hf' : b f' ≠ 0)
    (h : e * f = e' * f') : e = e' ∧ f = f' := by
  have he0 : e ≠ 0 := support_ne_zero ha0 he
  have hcop1 : Nat.Coprime e f' := hab e f' he hf'
  have hcop2 : Nat.Coprime e' f := hab e' f he' hf
  have hdvd1 : e ∣ e' := by
    have : e ∣ e' * f' := ⟨f, h.symm⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop1 this)
  have hdvd2 : e' ∣ e := by
    have : e' ∣ e * f := ⟨f', h⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop2 this)
  have hee : e = e' := Nat.dvd_antisymm hdvd1 hdvd2
  refine ⟨hee, ?_⟩
  subst hee
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he0) h

/-- On coprime supports the convolution is just the product. -/
theorem dconv_apply_mul {a b : ℕ → ℝ} (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (hab : CoprimeSupport a b) {e f : ℕ} (he : a e ≠ 0) (hf : b f ≠ 0) :
    dconv a b (e * f) = a e * b f := by
  have he0 : e ≠ 0 := support_ne_zero ha0 he
  have hf0 : f ≠ 0 := support_ne_zero hb0 hf
  have hef0 : e * f ≠ 0 := Nat.mul_ne_zero he0 hf0
  rw [dconv]
  refine Finset.sum_eq_single (e, f) ?_ ?_
  · rintro ⟨e', f'⟩ hmem hne
    simp only [Nat.mem_divisorsAntidiagonal] at hmem
    by_contra hprod
    have he' : a e' ≠ 0 := fun h => hprod (by rw [h, zero_mul])
    have hf' : b f' ≠ 0 := fun h => hprod (by rw [h, mul_zero])
    obtain ⟨h1, h2⟩ := mul_inj_on_support ha0 hb0 hab he' hf' he hf hmem.1
    exact hne (by rw [Prod.ext_iff]; exact ⟨h1, h2⟩)
  · intro hmem
    exact absurd (by
      simp only [Nat.mem_divisorsAntidiagonal]
      exact ⟨trivial, hef0⟩) hmem

/-! ## The density and log-mass product laws -/

theorem summable_abs_coeffDensityTerm {a : ℕ → ℝ} (h1 : Summable (logWeight a)) :
    Summable (fun d : ℕ => |a d / d|) := by
  refine Summable.of_nonneg_of_le (fun d => abs_nonneg _) (fun d => ?_) h1
  rcases Nat.eq_zero_or_pos d with h | h
  · simp [h, logWeight]
  · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hlog : 0 ≤ Real.log d := Real.log_nonneg hd1
    rw [abs_div, abs_of_nonneg (le_of_lt hdpos), logWeight]
    rw [div_le_div_iff_of_pos_right hdpos]
    nlinarith [abs_nonneg (a d)]

theorem summable_abs_coeffLogMassTerm {a : ℕ → ℝ} (h1 : Summable (logWeight a)) :
    Summable (fun d : ℕ => |a d / d * Real.log d|) := by
  refine Summable.of_nonneg_of_le (fun d => abs_nonneg _) (fun d => ?_) h1
  rcases Nat.eq_zero_or_pos d with h | h
  · simp [h, logWeight]
  · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hlog : 0 ≤ Real.log d := Real.log_nonneg hd1
    rw [abs_mul, abs_div, abs_of_nonneg (le_of_lt hdpos), abs_of_nonneg hlog, logWeight]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hdpos]
    nlinarith [abs_nonneg (a d)]

/-- **Density product law.** -/
theorem coeffDensity_dconv {a b : ℕ → ℝ} (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (hab : CoprimeSupport a b) (ha : Summable (logWeight a)) (hb : Summable (logWeight b)) :
    coeffDensity (dconv a b) = coeffDensity a * coeffDensity b := by
  have hna : Summable (fun d : ℕ => ‖a d / d‖) :=
    (summable_abs_coeffDensityTerm ha).congr fun d => (Real.norm_eq_abs (a d / d)).symm
  have hnb : Summable (fun d : ℕ => ‖b d / d‖) :=
    (summable_abs_coeffDensityTerm hb).congr fun d => (Real.norm_eq_abs (b d / d)).symm
  rw [coeffDensity, coeffDensity, coeffDensity]
  rw [tsum_mul_tsum_of_summable_norm hna hnb]
  set F : ℕ × ℕ → ℝ := fun z => a z.1 / z.1 * (b z.2 / z.2) with hF
  have hFsupp : ∀ z : ℕ × ℕ, F z ≠ 0 → a z.1 ≠ 0 ∧ b z.2 ≠ 0 := by
    rintro ⟨e, f⟩ hz
    constructor
    · intro h
      apply hz
      simp only [hF, h, zero_div, zero_mul]
    · intro h
      apply hz
      simp only [hF, h, zero_div, mul_zero]
  refine tsum_eq_tsum_of_ne_zero_bij (fun z => (z : ℕ × ℕ).1 * (z : ℕ × ℕ).2) ?_ ?_ ?_
  · rintro ⟨⟨e, f⟩, hz⟩ ⟨⟨e', f'⟩, hz'⟩ h
    obtain ⟨he, hf⟩ := hFsupp _ hz
    obtain ⟨he', hf'⟩ := hFsupp _ hz'
    obtain ⟨h1, h2⟩ := mul_inj_on_support ha0 hb0 hab he hf he' hf' h
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    exact ⟨h1, h2⟩
  · intro d hd
    simp only [Function.mem_support] at hd
    have hconv : dconv a b d ≠ 0 := by
      intro h
      apply hd
      rw [h, zero_div]
    rw [dconv] at hconv
    obtain ⟨z, hzmem, hznz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hconv
    simp only [Nat.mem_divisorsAntidiagonal] at hzmem
    have he : a z.1 ≠ 0 := fun h => hznz (by rw [h, zero_mul])
    have hf : b z.2 ≠ 0 := fun h => hznz (by rw [h, mul_zero])
    have he0 : z.1 ≠ 0 := support_ne_zero ha0 he
    have hf0 : z.2 ≠ 0 := support_ne_zero hb0 hf
    have hFz : F z ≠ 0 := by
      simp only [hF]
      have h1 : a z.1 / (z.1 : ℝ) ≠ 0 := by
        refine div_ne_zero he ?_
        exact_mod_cast he0
      have h2 : b z.2 / (z.2 : ℝ) ≠ 0 := by
        refine div_ne_zero hf ?_
        exact_mod_cast hf0
      exact mul_ne_zero h1 h2
    exact ⟨⟨z, hFz⟩, hzmem.1⟩
  · rintro ⟨⟨e, f⟩, hz⟩
    obtain ⟨he, hf⟩ := hFsupp _ hz
    have he0 : e ≠ 0 := support_ne_zero ha0 he
    have hf0 : f ≠ 0 := support_ne_zero hb0 hf
    have heR : ((e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast he0
    have hfR : ((f : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hf0
    rw [dconv_apply_mul ha0 hb0 hab he hf]
    push_cast
    field_simp

/-- **Log-mass product law.** -/
theorem coeffLogMass_dconv {a b : ℕ → ℝ} (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (hab : CoprimeSupport a b) (ha : Summable (logWeight a)) (hb : Summable (logWeight b)) :
    coeffLogMass (dconv a b)
      = coeffLogMass a * coeffDensity b + coeffDensity a * coeffLogMass b := by
  have hna : Summable (fun d : ℕ => ‖a d / d‖) :=
    (summable_abs_coeffDensityTerm ha).congr fun d => (Real.norm_eq_abs (a d / d)).symm
  have hnb : Summable (fun d : ℕ => ‖b d / d‖) :=
    (summable_abs_coeffDensityTerm hb).congr fun d => (Real.norm_eq_abs (b d / d)).symm
  have hnaL : Summable (fun d : ℕ => ‖a d / d * Real.log d‖) :=
    (summable_abs_coeffLogMassTerm ha).congr fun d =>
      (Real.norm_eq_abs (a d / d * Real.log d)).symm
  have hnbL : Summable (fun d : ℕ => ‖b d / d * Real.log d‖) :=
    (summable_abs_coeffLogMassTerm hb).congr fun d =>
      (Real.norm_eq_abs (b d / d * Real.log d)).symm
  have hsplit : coeffLogMass a * coeffDensity b + coeffDensity a * coeffLogMass b
      = ∑' z : ℕ × ℕ, (a z.1 / z.1 * Real.log z.1 * (b z.2 / z.2)
        + a z.1 / z.1 * (b z.2 / z.2 * Real.log z.2)) := by
    rw [coeffLogMass, coeffDensity, coeffDensity, coeffLogMass,
      tsum_mul_tsum_of_summable_norm hnaL hnb, tsum_mul_tsum_of_summable_norm hna hnbL]
    rw [← Summable.tsum_add ((Summable.mul_norm hnaL hnb).of_norm)
      ((Summable.mul_norm hna hnbL).of_norm)]
  rw [hsplit, coeffLogMass]
  set G : ℕ × ℕ → ℝ := fun z => a z.1 / z.1 * Real.log z.1 * (b z.2 / z.2)
    + a z.1 / z.1 * (b z.2 / z.2 * Real.log z.2) with hG
  have hGsupp : ∀ z : ℕ × ℕ, G z ≠ 0 → a z.1 ≠ 0 ∧ b z.2 ≠ 0 := by
    rintro ⟨e, f⟩ hz
    constructor
    · intro h
      apply hz
      simp only [hG, h, zero_div, zero_mul]
      ring
    · intro h
      apply hz
      simp only [hG, h, zero_div, zero_mul, mul_zero, add_zero]
  refine tsum_eq_tsum_of_ne_zero_bij (fun z => (z : ℕ × ℕ).1 * (z : ℕ × ℕ).2) ?_ ?_ ?_
  · rintro ⟨⟨e, f⟩, hz⟩ ⟨⟨e', f'⟩, hz'⟩ h
    obtain ⟨he, hf⟩ := hGsupp _ hz
    obtain ⟨he', hf'⟩ := hGsupp _ hz'
    obtain ⟨h1, h2⟩ := mul_inj_on_support ha0 hb0 hab he hf he' hf' h
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    exact ⟨h1, h2⟩
  · intro d hd
    simp only [Function.mem_support] at hd
    have hconv : dconv a b d ≠ 0 := by
      intro h
      apply hd
      rw [h, zero_div, zero_mul]
    rw [dconv] at hconv
    obtain ⟨z, hzmem, hznz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hconv
    simp only [Nat.mem_divisorsAntidiagonal] at hzmem
    have he : a z.1 ≠ 0 := fun h => hznz (by rw [h, zero_mul])
    have hf : b z.2 ≠ 0 := fun h => hznz (by rw [h, mul_zero])
    have he0 : z.1 ≠ 0 := support_ne_zero ha0 he
    have hf0 : z.2 ≠ 0 := support_ne_zero hb0 hf
    have heR : ((z.1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast he0
    have hfR : ((z.2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hf0
    have hGz : G z ≠ 0 := by
      have hval : G z = dconv a b d / d * Real.log d := by
        have hd' : d = z.1 * z.2 := hzmem.1.symm
        subst hd'
        rw [dconv_apply_mul ha0 hb0 hab he hf]
        have hlog : Real.log ((z.1 * z.2 : ℕ) : ℝ) = Real.log z.1 + Real.log z.2 := by
          push_cast
          rw [Real.log_mul heR hfR]
        simp only [hG]
        rw [hlog]
        push_cast
        field_simp
      rw [hval]
      exact hd
    exact ⟨⟨z, hGz⟩, hzmem.1⟩
  · rintro ⟨⟨e, f⟩, hz⟩
    obtain ⟨he, hf⟩ := hGsupp _ hz
    have he0 : e ≠ 0 := support_ne_zero ha0 he
    have hf0 : f ≠ 0 := support_ne_zero hb0 hf
    have heR : ((e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast he0
    have hfR : ((f : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hf0
    rw [dconv_apply_mul ha0 hb0 hab he hf]
    have hlog : Real.log ((e * f : ℕ) : ℝ) = Real.log e + Real.log f := by
      push_cast
      rw [Real.log_mul heR hfR]
    rw [hlog]
    push_cast
    field_simp

/-! ## Propagating the two regularization hypotheses -/

theorem logWeight_dconv_le {a b : ℕ → ℝ} (d : ℕ) :
    logWeight (dconv a b) d
      ≤ ∑ x ∈ d.divisorsAntidiagonal, logWeight a x.1 * logWeight b x.2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [logWeight, Nat.divisorsAntidiagonal_zero]
  · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
    have habs : |dconv a b d| ≤ ∑ x ∈ d.divisorsAntidiagonal, |a x.1| * |b x.2| := by
      rw [dconv]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact Finset.sum_le_sum fun x _ => le_of_eq (abs_mul _ _)
    have hstep : logWeight (dconv a b) d
        ≤ (∑ x ∈ d.divisorsAntidiagonal, |a x.1| * |b x.2|) * ((1 + Real.log d) / d) := by
      rw [logWeight]
      have hfac : (0 : ℝ) ≤ (1 + Real.log d) / d := by positivity
      calc |dconv a b d| * (1 + Real.log ↑d) / ↑d
          = |dconv a b d| * ((1 + Real.log ↑d) / ↑d) := by ring
        _ ≤ (∑ x ∈ d.divisorsAntidiagonal, |a x.1| * |b x.2|) * ((1 + Real.log ↑d) / ↑d) :=
            mul_le_mul_of_nonneg_right habs hfac
    refine le_trans hstep ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun x hx => ?_
    simp only [Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨hef, hd0⟩ := hx
    have he0 : x.1 ≠ 0 := by
      intro h
      apply hd0
      rw [← hef, h, zero_mul]
    have hf0 : x.2 ≠ 0 := by
      intro h
      apply hd0
      rw [← hef, h, mul_zero]
    have he1 : (1 : ℝ) ≤ (x.1 : ℝ) := by
      have : 1 ≤ x.1 := Nat.one_le_iff_ne_zero.mpr he0
      exact_mod_cast this
    have hf1 : (1 : ℝ) ≤ (x.2 : ℝ) := by
      have : 1 ≤ x.2 := Nat.one_le_iff_ne_zero.mpr hf0
      exact_mod_cast this
    have hloge : 0 ≤ Real.log x.1 := Real.log_nonneg he1
    have hlogf : 0 ≤ Real.log x.2 := Real.log_nonneg hf1
    have hdval : ((d : ℕ) : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by
      rw [← hef]; push_cast; ring
    have hlogsplit : Real.log d = Real.log x.1 + Real.log x.2 := by
      rw [hdval, Real.log_mul (by linarith) (by linarith)]
    rw [logWeight, logWeight, hlogsplit, hdval]
    have hepos : (0 : ℝ) < (x.1 : ℝ) := by linarith
    have hfpos : (0 : ℝ) < (x.2 : ℝ) := by linarith
    have hkey : (1 + (Real.log x.1 + Real.log x.2))
        ≤ (1 + Real.log x.1) * (1 + Real.log x.2) := by nlinarith
    have hnn : (0 : ℝ) ≤ |a x.1| * |b x.2| := by positivity
    rw [div_mul_div_comm, mul_div_assoc',
      div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (x.1 : ℝ) * (x.2 : ℝ))]
    calc |a x.1| * |b x.2| * (1 + (Real.log x.1 + Real.log x.2))
        ≤ |a x.1| * |b x.2| * ((1 + Real.log x.1) * (1 + Real.log x.2)) :=
          mul_le_mul_of_nonneg_left hkey hnn
      _ = |a x.1| * (1 + Real.log x.1) * (|b x.2| * (1 + Real.log x.2)) := by ring

theorem summable_logWeight_dconv {a b : ℕ → ℝ}
    (ha : Summable (logWeight a)) (hb : Summable (logWeight b)) :
    Summable (logWeight (dconv a b)) := by
  classical
  refine summable_of_sum_range_le
    (c := (∑' e : ℕ, logWeight a e) * (∑' f : ℕ, logWeight b f))
    (fun d => logWeight_nonneg _ d) (fun N => ?_)
  have hstep1 : (∑ d ∈ Finset.range N, logWeight (dconv a b) d)
      ≤ ∑ d ∈ Finset.range N,
          ∑ x ∈ d.divisorsAntidiagonal, logWeight a x.1 * logWeight b x.2 :=
    Finset.sum_le_sum fun d _ => logWeight_dconv_le d
  have hsigma : (∑ d ∈ Finset.range N,
        ∑ x ∈ d.divisorsAntidiagonal, logWeight a x.1 * logWeight b x.2)
      = ∑ x ∈ (Finset.range N).sigma (fun d => d.divisorsAntidiagonal),
          logWeight a x.2.1 * logWeight b x.2.2 := by
    rw [Finset.sum_sigma']
  have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ × ℕ => x.2)
      ((Finset.range N).sigma (fun d => d.divisorsAntidiagonal) : Set (Σ _ : ℕ, ℕ × ℕ)) := by
    rintro ⟨d, e, f⟩ hx ⟨d', e', f'⟩ hy hxy
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_range,
      Nat.mem_divisorsAntidiagonal] at hx hy
    simp only at hxy
    have h1 : e = e' ∧ f = f' := by
      rw [Prod.ext_iff] at hxy
      exact hxy
    obtain ⟨rfl, rfl⟩ := h1
    have : d = d' := by rw [← hx.2.1, ← hy.2.1]
    subst this
    rfl
  have himg : (∑ x ∈ (Finset.range N).sigma (fun d => d.divisorsAntidiagonal),
        logWeight a x.2.1 * logWeight b x.2.2)
      = ∑ y ∈ ((Finset.range N).sigma (fun d => d.divisorsAntidiagonal)).image
          (fun x : Σ _ : ℕ, ℕ × ℕ => x.2), logWeight a y.1 * logWeight b y.2 := by
    rw [Finset.sum_image (fun x hx y hy h => hinj (by simpa using hx) (by simpa using hy) h)]
  have hsubset : ((Finset.range N).sigma (fun d => d.divisorsAntidiagonal)).image
      (fun x : Σ _ : ℕ, ℕ × ℕ => x.2) ⊆ Finset.range N ×ˢ Finset.range N := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_range,
      Nat.mem_divisorsAntidiagonal] at hy
    obtain ⟨⟨d, e, f⟩, ⟨hdN, hef, hd0⟩, hyeq⟩ := hy
    simp only at hyeq
    subst hyeq
    have he0 : e ≠ 0 := by
      intro h
      apply hd0
      rw [← hef, h, zero_mul]
    have hf0 : f ≠ 0 := by
      intro h
      apply hd0
      rw [← hef, h, mul_zero]
    simp only [Finset.mem_product, Finset.mem_range]
    constructor
    · calc e ≤ e * f := Nat.le_mul_of_pos_right e (Nat.pos_of_ne_zero hf0)
        _ = d := hef
        _ < N := hdN
    · calc f ≤ e * f := Nat.le_mul_of_pos_left f (Nat.pos_of_ne_zero he0)
        _ = d := hef
        _ < N := hdN
  have hprod : (∑ y ∈ Finset.range N ×ˢ Finset.range N, logWeight a y.1 * logWeight b y.2)
      ≤ (∑' e : ℕ, logWeight a e) * (∑' f : ℕ, logWeight b f) := by
    have heq : (∑ y ∈ Finset.range N ×ˢ Finset.range N, logWeight a y.1 * logWeight b y.2)
        = (∑ e ∈ Finset.range N, logWeight a e) * (∑ f ∈ Finset.range N, logWeight b f) := by
      rw [Finset.sum_mul_sum, Finset.sum_product]
    rw [heq]
    have hA : (∑ e ∈ Finset.range N, logWeight a e) ≤ ∑' e : ℕ, logWeight a e :=
      ha.sum_le_tsum _ (fun i _ => logWeight_nonneg a i)
    have hB : (∑ f ∈ Finset.range N, logWeight b f) ≤ ∑' f : ℕ, logWeight b f :=
      hb.sum_le_tsum _ (fun i _ => logWeight_nonneg b i)
    have hA0 : (0 : ℝ) ≤ ∑ e ∈ Finset.range N, logWeight a e :=
      Finset.sum_nonneg fun i _ => logWeight_nonneg a i
    have hA0' : (0 : ℝ) ≤ ∑' e : ℕ, logWeight a e :=
      tsum_nonneg fun i => logWeight_nonneg a i
    exact mul_le_mul hA hB (Finset.sum_nonneg fun i _ => logWeight_nonneg b i) hA0'
  refine le_trans hstep1 ?_
  rw [hsigma, himg]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_) hprod
  intro y _ _
  exact mul_nonneg (logWeight_nonneg a y.1) (logWeight_nonneg b y.2)

/-! ## The coefficient-mass product bound -/

theorem sum_Icc_abs_dconv_le (a b : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, |dconv a b d|)
      ≤ (∑ e ∈ Finset.Icc 1 N, |a e|) * (∑ f ∈ Finset.Icc 1 N, |b f|) := by
  classical
  have hstep1 : (∑ d ∈ Finset.Icc 1 N, |dconv a b d|)
      ≤ ∑ d ∈ Finset.Icc 1 N, ∑ x ∈ d.divisorsAntidiagonal, |a x.1| * |b x.2| := by
    refine Finset.sum_le_sum fun d _ => ?_
    rw [dconv]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum fun x _ => le_of_eq (abs_mul _ _)
  have hsigma : (∑ d ∈ Finset.Icc 1 N, ∑ x ∈ d.divisorsAntidiagonal, |a x.1| * |b x.2|)
      = ∑ x ∈ (Finset.Icc 1 N).sigma (fun d => d.divisorsAntidiagonal),
          |a x.2.1| * |b x.2.2| := by
    rw [Finset.sum_sigma']
  have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ × ℕ => x.2)
      ((Finset.Icc 1 N).sigma (fun d => d.divisorsAntidiagonal) : Set (Σ _ : ℕ, ℕ × ℕ)) := by
    rintro ⟨d, e, f⟩ hx ⟨d', e', f'⟩ hy hxy
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_Icc,
      Nat.mem_divisorsAntidiagonal] at hx hy
    simp only at hxy
    have h1 : e = e' ∧ f = f' := by
      rw [Prod.ext_iff] at hxy
      exact hxy
    obtain ⟨rfl, rfl⟩ := h1
    have : d = d' := by rw [← hx.2.1, ← hy.2.1]
    subst this
    rfl
  have himg : (∑ x ∈ (Finset.Icc 1 N).sigma (fun d => d.divisorsAntidiagonal),
        |a x.2.1| * |b x.2.2|)
      = ∑ y ∈ ((Finset.Icc 1 N).sigma (fun d => d.divisorsAntidiagonal)).image
          (fun x : Σ _ : ℕ, ℕ × ℕ => x.2), |a y.1| * |b y.2| := by
    rw [Finset.sum_image (fun x hx y hy h => hinj (by simpa using hx) (by simpa using hy) h)]
  have hsubset : ((Finset.Icc 1 N).sigma (fun d => d.divisorsAntidiagonal)).image
      (fun x : Σ _ : ℕ, ℕ × ℕ => x.2) ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_Icc,
      Nat.mem_divisorsAntidiagonal] at hy
    obtain ⟨⟨d, e, f⟩, ⟨⟨hd1, hdN⟩, hef, hd0⟩, hyeq⟩ := hy
    simp only at hyeq
    subst hyeq
    have he0 : e ≠ 0 := by
      intro h
      apply hd0
      rw [← hef, h, zero_mul]
    have hf0 : f ≠ 0 := by
      intro h
      apply hd0
      rw [← hef, h, mul_zero]
    simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr he0, ?_⟩, Nat.one_le_iff_ne_zero.mpr hf0, ?_⟩
    · calc e ≤ e * f := Nat.le_mul_of_pos_right e (Nat.pos_of_ne_zero hf0)
        _ = d := hef
        _ ≤ N := hdN
    · calc f ≤ e * f := Nat.le_mul_of_pos_left f (Nat.pos_of_ne_zero he0)
        _ = d := hef
        _ ≤ N := hdN
  have hprod : (∑ y ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, |a y.1| * |b y.2|)
      = (∑ e ∈ Finset.Icc 1 N, |a e|) * (∑ f ∈ Finset.Icc 1 N, |b f|) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
  refine le_trans hstep1 ?_
  rw [hsigma, himg, ← hprod]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
  intro y _ _
  positivity

/-- A logarithmically polynomial bound on the absolute coefficient mass. -/
def LogPolyMass (a : ℕ → ℝ) (C : ℝ) (m : ℕ) : Prop :=
  0 ≤ C ∧ ∀ N : ℕ, (∑ d ∈ Finset.Icc 1 N, |a d|) ≤ C * (1 + Real.log N) ^ m

theorem LogPolyMass.dconv {a b : ℕ → ℝ} {C₁ C₂ : ℝ} {m₁ m₂ : ℕ}
    (ha : LogPolyMass a C₁ m₁) (hb : LogPolyMass b C₂ m₂) :
    LogPolyMass (CoprimeDirichlet.dconv a b) (C₁ * C₂) (m₁ + m₂) := by
  refine ⟨mul_nonneg ha.1 hb.1, fun N => ?_⟩
  have hlog : (0 : ℝ) ≤ 1 + Real.log N := by
    have : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hA := ha.2 N
  have hB := hb.2 N
  have hA0 : (0 : ℝ) ≤ ∑ e ∈ Finset.Icc 1 N, |a e| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0 : (0 : ℝ) ≤ ∑ f ∈ Finset.Icc 1 N, |b f| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc (∑ d ∈ Finset.Icc 1 N, |CoprimeDirichlet.dconv a b d|)
      ≤ (∑ e ∈ Finset.Icc 1 N, |a e|) * (∑ f ∈ Finset.Icc 1 N, |b f|) :=
        sum_Icc_abs_dconv_le a b N
    _ ≤ (C₁ * (1 + Real.log N) ^ m₁) * (C₂ * (1 + Real.log N) ^ m₂) := by
        refine mul_le_mul hA hB hB0 ?_
        exact le_trans hA0 hA
    _ = (C₁ * C₂) * (1 + Real.log N) ^ (m₁ + m₂) := by
        rw [pow_add]; ring

end

end CoprimeDirichlet
end RHTower
