/-
# The archimedean base is transcendental: `e` is transcendental over `ℤ`

The prime shifts `σ_p` that the weld couples to the archimedean generator have integer bases `p`
(with rates `log p`); the archimedean generator `∂_s` itself has exponential eigenbase
`e = exp 1` — the unique base for which `∂_s` acts with unit eigenvalue (`∂_s e^{s} = e^{s}`).  This
file records that this archimedean base is **transcendental**, qualitatively unlike the arithmetic
integer bases it is welded to.

`Mathlib` proves only the analytical half of the Lindemann–Weierstrass theorem
(`LindemannWeierstrass.exp_polynomial_approx`): for `f : ℤ[X]` with `f(0) ≠ 0` and every large prime
`p`, there is an integer `nₚ` (with `p ∤ nₚ`) and `gₚ : ℤ[X]` so that each complex root `r` of `f`
satisfies `‖nₚ·e^{r} − p·gₚ(r)‖ ≤ c^p/(p−1)!`.  This file supplies the algebraic half for the base
case `e` (Hermite's argument):

`transcendental_exp_one` — assume `e` is a root of some `q ∈ ℤ[X]`, reduced so that `q(0) ≠ 0`; then
`∑ cₖ e^{k} = 0` with `c₀ ≠ 0`.  Taking `f = ∏_{k=1}^{d}(X − k)` and multiplying the relation by
`nₚ`, each `k ≥ 1` term becomes `p·(integer)` up to an error `≤ c^p/(p−1)!`, so
`I := c₀ nₚ + p·(integer)` is an integer with `‖I‖ < 1` for large `p` — hence `I = 0`.  But then
`p ∣ c₀ nₚ`, impossible once `p` exceeds `|c₀|` (as `p ∤ nₚ` and `p` is prime).  So no such `q` exists.
-/
import Mathlib

open Polynomial Filter Complex
open scoped Nat

namespace GaloisForLFunctions
namespace RHTower

/-- **`e` is transcendental over `ℤ`.**  The archimedean eigenbase `e = exp 1` satisfies no nonzero
integer-polynomial relation.  Hermite's argument completing `exp_polynomial_approx`: a hypothetical
relation `∑ cₖ e^k = 0` (reduced to `c₀ ≠ 0`) is contradicted by the auxiliary polynomial
`∏_{k=1}^{d}(X − k)`, which forces a nonzero integer of absolute value `< 1`. -/
theorem transcendental_exp_one : Transcendental ℤ (Real.exp 1) := by
  intro ha
  set e := Real.exp 1 with he_def
  have he : e ≠ 0 := Real.exp_ne_zero 1
  obtain ⟨q, hq0, hc0, hqev⟩ : ∃ q : ℤ[X], q ≠ 0 ∧ q.coeff 0 ≠ 0 ∧ (aeval e q : ℝ) = 0 := by
    obtain ⟨p, hp0, hpev⟩ := ha
    set m := p.natTrailingDegree with hm
    have hdvd : X ^ m ∣ p := X_pow_dvd_iff.mpr (fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd)
    obtain ⟨qq, hq⟩ := hdvd
    have hcoeff : p.coeff m = qq.coeff 0 := by
      have := coeff_X_pow_mul qq m 0; rwa [Nat.zero_add, ← hq] at this
    refine ⟨qq, ?_, ?_, ?_⟩
    · rintro rfl; rw [mul_zero] at hq; exact hp0 hq
    · rw [← hcoeff]; exact coeff_natTrailingDegree_ne_zero.mpr hp0
    · have hfac : (aeval e p : ℝ) = e ^ m * aeval e qq := by
        rw [hq]; push_cast [map_mul, map_pow, aeval_X]; ring
      rw [hpev] at hfac
      exact (mul_eq_zero.mp hfac.symm).resolve_left (pow_ne_zero _ he)
  set d := q.natDegree with hd_def
  set cc : ℕ → ℤ := fun k => q.coeff k with hcc
  have hrel : ∑ k ∈ Finset.range (d + 1), (cc k : ℂ) * Complex.exp (k : ℂ) = 0 := by
    have hexpk : ∀ k : ℕ, Complex.exp (k : ℂ) = ((e ^ k : ℝ) : ℂ) := by
      intro k
      have hck : (k : ℂ) = ((k : ℝ) : ℂ) := by norm_cast
      rw [hck, ← Complex.ofReal_exp]; congr 1; rw [← Real.exp_nat_mul, mul_one]
    have hcast : ∑ k ∈ Finset.range (d + 1), (cc k : ℂ) * Complex.exp (k : ℂ)
        = (((∑ k ∈ Finset.range (d + 1), (cc k : ℝ) * e ^ k) : ℝ) : ℂ) := by
      push_cast; apply Finset.sum_congr rfl
      intro k _; rw [hexpk k]; push_cast; ring
    rw [hcast]
    have hae : (∑ k ∈ Finset.range (d + 1), (cc k : ℝ) * e ^ k) = aeval e q := by
      rw [aeval_eq_sum_range]; apply Finset.sum_congr rfl
      intro k _; rw [zsmul_eq_mul]
    rw [hae, hqev]; simp
  set f : ℤ[X] := ∏ j ∈ Finset.range d, (X - C ((j + 1 : ℕ) : ℤ)) with hf_def
  have hf0 : f.eval 0 ≠ 0 := by
    rw [hf_def, eval_prod]; apply Finset.prod_ne_zero_iff.mpr
    intro i _; simp only [eval_sub, eval_X, eval_C, zero_sub, neg_ne_zero]
    exact_mod_cast Nat.succ_ne_zero i
  obtain ⟨B, hB⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  set Cabs : ℝ := ∑ k ∈ Finset.range d, |(cc (k + 1) : ℝ)| with hCabs
  have hlim : Tendsto (fun p : ℕ => Cabs * (B ^ p / (p - 1)!)) atTop (nhds 0) := by
    have h1 := FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop (1 : ℝ) B 1
    have h2 : Tendsto (fun p : ℕ => B ^ p / (p - 1)!) atTop (nhds 0) := by simpa using h1
    simpa using h2.const_mul Cabs
  have hev : ∀ᶠ p : ℕ in atTop, Cabs * (B ^ p / (p - 1)!) < 1 :=
    hlim.eventually_lt_const (by norm_num)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨P₀, hP₀⟩ := hev
  obtain ⟨p, hp_gt, hp_prime⟩ :=
    Nat.exists_infinite_primes (max P₀ (max ((f.eval 0).natAbs + 1) ((cc 0).natAbs + 1)))
  have hp_ge_P₀ : P₀ ≤ p := le_trans (le_max_left _ _) hp_gt
  have hp_gt_f : (f.eval 0).natAbs < p := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hp_gt; omega
  have hp_gt_c0 : (cc 0).natAbs < p := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hp_gt; omega
  obtain ⟨n_p, hnp_ndvd, gp, hgp_deg, hgp_bound⟩ := hB p hp_gt_f hp_prime
  have hbound : ∀ k ∈ Finset.range d,
      ‖(n_p : ℂ) * Complex.exp ((k + 1 : ℕ) : ℂ)
        - (p : ℂ) * ((gp.eval ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ)‖ ≤ B ^ p / (p - 1)! := by
    intro k hk
    have hroot : ((k + 1 : ℕ) : ℂ) ∈ f.aroots ℂ := by
      rw [hf_def, Polynomial.mem_aroots]
      refine ⟨?_, ?_⟩
      · apply Finset.prod_ne_zero_iff.mpr; intro i _; exact X_sub_C_ne_zero _
      · rw [map_prod]; apply Finset.prod_eq_zero hk; simp
    have hb := hgp_bound hroot
    rw [zsmul_eq_mul, nsmul_eq_mul] at hb
    have haev : aeval ((k + 1 : ℕ) : ℂ) gp = ((gp.eval ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) := by
      have hcast : (((k + 1 : ℕ)) : ℂ) = (algebraMap ℤ ℂ) ((k + 1 : ℕ) : ℤ) := by push_cast; simp
      rw [hcast, aeval_algebraMap_apply_eq_algebraMap_eval]; simp
    rw [haev] at hb; exact hb
  set S : ℤ := ∑ k ∈ Finset.range d, cc (k + 1) * gp.eval ((k + 1 : ℕ) : ℤ) with hS
  set Iℤ : ℤ := cc 0 * n_p + (p : ℤ) * S with hIℤ
  set δfun : ℕ → ℂ := fun k => (cc (k + 1) : ℂ)
      * ((n_p : ℂ) * Complex.exp ((k + 1 : ℕ) : ℂ) - (p : ℂ) * ((gp.eval ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ))
      with hδ
  have hsum_exp : ∑ k ∈ Finset.range d, (cc (k + 1) : ℂ) * Complex.exp ((k + 1 : ℕ) : ℂ)
      = -(cc 0 : ℂ) := by
    have h0 := hrel
    rw [Finset.sum_range_succ' (fun k => (cc k : ℂ) * Complex.exp (k : ℂ)) d] at h0
    simp only [Nat.cast_zero, Complex.exp_zero, mul_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hkey : (Iℤ : ℂ) = - ∑ k ∈ Finset.range d, δfun k := by
    have expand : ∑ k ∈ Finset.range d, δfun k
        = (n_p : ℂ) * (∑ k ∈ Finset.range d, (cc (k + 1) : ℂ) * Complex.exp ((k + 1 : ℕ) : ℂ))
          - (p : ℂ) * (∑ k ∈ Finset.range d,
              (cc (k + 1) : ℂ) * ((gp.eval ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _; simp only [hδ]; ring
    rw [expand, hsum_exp, hIℤ]
    push_cast [hS]
    ring
  have hnorm : ‖(Iℤ : ℂ)‖ < 1 := by
    rw [hkey, norm_neg]
    calc ‖∑ k ∈ Finset.range d, δfun k‖
        ≤ ∑ k ∈ Finset.range d, ‖δfun k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range d, |(cc (k + 1) : ℝ)| * (B ^ p / (p - 1)!) := by
          apply Finset.sum_le_sum; intro k hk
          rw [hδ]
          simp only [norm_mul, Complex.norm_intCast]
          gcongr
          exact hbound k hk
      _ = Cabs * (B ^ p / (p - 1)!) := by rw [hCabs, ← Finset.sum_mul]
      _ < 1 := hP₀ p hp_ge_P₀
  have hI0 : Iℤ = 0 := by
    have habs : |(Iℤ : ℝ)| < 1 := by rw [← Complex.norm_intCast]; exact hnorm
    exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast habs)
  have hdvd : (p : ℤ) ∣ cc 0 * n_p := by
    have heq : cc 0 * n_p = -((p : ℤ) * S) := by
      have := hI0; rw [hIℤ] at this; linarith
    rw [heq]; exact (Dvd.intro S rfl).neg_right
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  rcases hp_prime_int.dvd_mul.mp hdvd with h | h
  · have hdvdnat : p ∣ (cc 0).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h; rwa [Int.natAbs_natCast] at this
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hc0) hdvdnat
    exact absurd hle (not_le.mpr hp_gt_c0)
  · exact hnp_ndvd h

end RHTower
end GaloisForLFunctions
