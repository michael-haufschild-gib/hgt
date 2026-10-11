import GaloisForLFunctions.RHTower.JointAncestryBernoulliAggregate

/-!
# Log-weight Bernoulli tests centred at a strip point

Fix a centre `ξ ∈ ℂ`, a finite prime set `P` and nonnegative weights `a_p` with
`a_p p^{Re ξ + c} ≤ ½`, where `c = σ − ½`.  Testing the dressed JAS aggregate on the Bernoulli
weights `z_p = t_p e^{i(φ + Im ξ · log p)}`, where `t_p/(1 + t_p²) = a_p p^{Re ξ + c}`, every local
factor becomes `(1 + t_p²)` times

`1 + a_p (e^{iφ} p^{ξ − q} + e^{−iφ} p^{q + ξ̄ − 1})`.

The dressing parameter `σ` drops out of the factor and survives only in the admissibility
condition on the weights.  Hence positive semidefiniteness at `σ` gives
(`jasLogWeightBernoulli_nonneg`)

`Re Σ_q (1/(q(1−q))) ∏_{p∈P} (1 + a_p (e^{iφ} p^{ξ − q} + e^{−iφ} p^{q + ξ̄ − 1})) ≥ 0.`

At `ξ = q` the factor is `1 + a_p(e^{iφ} + e^{−iφ} p^{2 Re q − 1})`, so with `a_p = τ log p / p` the zero
`q` itself contributes `exp(τ e^{iφ} Σ_P log p / p)` to first order: the centre is amplified at the
rate of the Mertens sum, while every other zero `q′` sees the shifts `p^{q − q′}`.
-/

open Complex
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-- The log-weight Bernoulli local factor `1 + a (e^{iφ} p^{ξ − q} + e^{−iφ} p^{q + ξ̄ − 1})`. -/
def jasLogWeightLocal (ξ q : ℂ) (a φ : ℝ) (p : Nat.Primes) : ℂ :=
  1 + (a : ℂ) * (cexp ((φ : ℂ) * I) * cexp ((ξ - q) * (Real.log p : ℂ)) +
    cexp (((-φ : ℝ) : ℂ) * I) * cexp ((q + conj ξ - 1) * (Real.log p : ℂ)))

/-- `t ↦ t/(1 + t²)` takes every value in `[0, 1/2]` on `[0, 1]`. -/
theorem exists_div_one_add_sq_eq {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ t / (1 + t ^ 2) = s := by
  have hcont : ContinuousOn (fun t : ℝ => t / (1 + t ^ 2)) (Set.Icc 0 1) :=
    (continuous_id.div (continuous_const.add (continuous_pow 2))
      fun t => (by positivity : (0 : ℝ) < 1 + t ^ 2).ne').continuousOn
  have hmem : s ∈ Set.Icc ((fun t : ℝ => t / (1 + t ^ 2)) 0) ((fun t : ℝ => t / (1 + t ^ 2)) 1) := by
    norm_num
    exact ⟨hs0, hs⟩
  obtain ⟨t, ht, hts⟩ := intermediate_value_Icc zero_le_one hcont hmem
  exact ⟨t, ht.1, ht.2, hts⟩

/-- **The factor identity.**  At the Bernoulli weight `t e^{i(φ + Im ξ log p)}` with
`t/(1+t²) = a p^{Re ξ + c}`, the dressed Bernoulli factor is `(1 + t²)` times the log-weight
factor. -/
theorem jasBernoulliFactor_eq_mul_jasLogWeightLocal (ξ q : ℂ) (c a φ t : ℝ) (p : Nat.Primes)
    (ht : t / (1 + t ^ 2) = a * Real.exp ((ξ.re + c) * Real.log p)) :
    jasBernoulliFactor (jasHoloA (q + c) p) (jasHoloB (q - c) p)
        ((t : ℂ) * cexp (((φ + ξ.im * Real.log p : ℝ) : ℂ) * I)) =
      ((1 + t ^ 2 : ℝ) : ℂ) * jasLogWeightLocal ξ q a φ p := by
  set L : ℝ := Real.log p with hL
  have h1t : (0 : ℝ) < 1 + t ^ 2 := by positivity
  -- `(1 + t²) a = t p^{-(Re ξ + c)}`
  have hcoef : (1 + t ^ 2) * a = t * Real.exp (-((ξ.re + c) * L)) := by
    have hE : 0 < Real.exp ((ξ.re + c) * L) := Real.exp_pos _
    rw [Real.exp_neg]
    field_simp
    rw [div_eq_iff h1t.ne'] at ht
    linarith [ht]
  have hcoefC : ((1 + t ^ 2 : ℝ) : ℂ) * (a : ℂ) = (t : ℂ) * cexp (-(((ξ.re + c) * L : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_mul, hcoef, Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  have hξ : ξ = (ξ.re : ℂ) + (ξ.im : ℂ) * I := (Complex.re_add_im ξ).symm
  have hξc : conj ξ = (ξ.re : ℂ) - (ξ.im : ℂ) * I := Complex.ext (by simp) (by simp)
  -- the forward term
  have hexpA : (((φ + ξ.im * L : ℝ) : ℂ) * I + -(q + c) * (L : ℂ)) =
      -(((ξ.re + c) * L : ℝ) : ℂ) + ((φ : ℂ) * I + (ξ - q) * (L : ℂ)) := by
    push_cast
    linear_combination (-(L : ℂ)) * hξ
  have hA : (t : ℂ) * cexp (((φ + ξ.im * L : ℝ) : ℂ) * I) * jasHoloA (q + c) p =
      ((1 + t ^ 2 : ℝ) : ℂ) * ((a : ℂ) * (cexp ((φ : ℂ) * I) * cexp ((ξ - q) * (L : ℂ)))) := by
    calc (t : ℂ) * cexp (((φ + ξ.im * L : ℝ) : ℂ) * I) * jasHoloA (q + c) p
        = (t : ℂ) * cexp (((φ + ξ.im * L : ℝ) : ℂ) * I + -(q + c) * (L : ℂ)) := by
          rw [jasHoloA, ← hL, mul_assoc, ← Complex.exp_add]
      _ = (t : ℂ) * (cexp (-(((ξ.re + c) * L : ℝ) : ℂ)) *
            (cexp ((φ : ℂ) * I) * cexp ((ξ - q) * (L : ℂ)))) := by
          rw [hexpA, Complex.exp_add, Complex.exp_add]
      _ = _ := by rw [← mul_assoc ((1 + t ^ 2 : ℝ) : ℂ), hcoefC]; ring
  -- the backward term
  have hexpB : (((-(φ + ξ.im * L) : ℝ) : ℂ) * I + -(1 - (q - c)) * (L : ℂ)) =
      -(((ξ.re + c) * L : ℝ) : ℂ) + (((-φ : ℝ) : ℂ) * I + (q + conj ξ - 1) * (L : ℂ)) := by
    rw [hξc]
    push_cast
    ring
  have hB : conj ((t : ℂ) * cexp (((φ + ξ.im * L : ℝ) : ℂ) * I)) * jasHoloB (q - c) p =
      ((1 + t ^ 2 : ℝ) : ℂ) *
        ((a : ℂ) * (cexp (((-φ : ℝ) : ℂ) * I) * cexp ((q + conj ξ - 1) * (L : ℂ)))) := by
    have hconj : conj ((t : ℂ) * cexp (((φ + ξ.im * L : ℝ) : ℂ) * I)) =
        (t : ℂ) * cexp (((-(φ + ξ.im * L) : ℝ) : ℂ) * I) := by
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
        Complex.conj_I]
      push_cast
      ring_nf
    calc conj ((t : ℂ) * cexp (((φ + ξ.im * L : ℝ) : ℂ) * I)) * jasHoloB (q - c) p
        = (t : ℂ) * cexp (((-(φ + ξ.im * L) : ℝ) : ℂ) * I + -(1 - (q - c)) * (L : ℂ)) := by
          rw [hconj, jasHoloB, ← hL, mul_assoc, ← Complex.exp_add]
      _ = (t : ℂ) * (cexp (-(((ξ.re + c) * L : ℝ) : ℂ)) *
            (cexp (((-φ : ℝ) : ℂ) * I) * cexp ((q + conj ξ - 1) * (L : ℂ)))) := by
          rw [hexpB, Complex.exp_add, Complex.exp_add]
      _ = _ := by rw [← mul_assoc ((1 + t ^ 2 : ℝ) : ℂ), hcoefC]; ring
  have hzz : (t : ℂ) * cexp (((φ + ξ.im * L : ℝ) : ℂ) * I) *
      conj ((t : ℂ) * cexp (((φ + ξ.im * L : ℝ) : ℂ) * I)) = ((t ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_real,
      Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, sq_abs]
  rw [jasBernoulliFactor, hzz, hA, hB, jasLogWeightLocal, ← hL]
  push_cast
  ring

/-- **Log-weight Bernoulli positivity.**  Positive semidefiniteness of the dressed aggregate at `σ`
forces positivity of the log-weight Bernoulli sums centred at any strip point, for admissible
weights. -/
theorem jasLogWeightBernoulli_nonneg {σ : ℝ} (h : JasDressedPSD σ) (ξ : ℂ)
    (P : Finset Nat.Primes) (a : Nat.Primes → ℝ) (ha0 : ∀ p ∈ P, 0 ≤ a p)
    (ha : ∀ p ∈ P, a p * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p) ≤ 1 / 2) (φ : ℝ) :
    0 ≤ (∑' q : XiZeroCopy,
      (∏ p ∈ P, jasLogWeightLocal ξ (q.1 : ℂ) (a p) φ p) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  classical
  set c : ℝ := σ - 1 / 2 with hc
  have hex : ∀ p : Nat.Primes, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      (p ∈ P → t / (1 + t ^ 2) = a p * Real.exp ((ξ.re + c) * Real.log p)) := by
    intro p
    by_cases hp : p ∈ P
    · have hs0 : 0 ≤ a p * Real.exp ((ξ.re + c) * Real.log p) :=
        mul_nonneg (ha0 p hp) (Real.exp_pos _).le
      obtain ⟨t, ht0, ht1, hts⟩ := exists_div_one_add_sq_eq hs0 (ha p hp)
      exact ⟨t, ht0, ht1, fun _ => hts⟩
    · exact ⟨0, le_rfl, zero_le_one, fun h => absurd h hp⟩
  choose t ht0 ht1 hts using hex
  set z : Nat.Primes → ℂ := fun p =>
    (t p : ℂ) * cexp (((φ + ξ.im * Real.log p : ℝ) : ℂ) * I) with hz
  have hpos := jasBernoulliAggregate_nonneg h P z
  have hfac : ∀ q : XiZeroCopy,
      (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
        ((∏ p ∈ P, (1 + t p ^ 2) : ℝ) : ℂ) *
          ((∏ p ∈ P, jasLogWeightLocal ξ (q.1 : ℂ) (a p) φ p) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    intro q
    rw [Complex.ofReal_prod, mul_div_assoc', ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    exact jasBernoulliFactor_eq_mul_jasLogWeightLocal ξ q.1 c (a p) φ (t p) p (hts p hp)
  simp_rw [hfac] at hpos
  rw [tsum_mul_left, Complex.re_ofReal_mul] at hpos
  have hprod : 0 < ∏ p ∈ P, (1 + t p ^ 2) := Finset.prod_pos fun p _ => by positivity
  exact (mul_nonneg_iff_of_pos_left hprod).mp hpos

end

end RHTower
