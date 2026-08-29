import GaloisForLFunctions.HTGeometry.SuperGaussianMonomialization

/-!
# The autonomous ADE principal face degenerates

If a transcendental entire function with super-Gaussian Taylor decay satisfies an autonomous
algebraic differential equation `P(f, f', …, f⁽ᵐ⁾) = 0`, then the sum of the coefficients on the
top-degree / minimal-weight face of `P` vanishes.  This is the Wiman–Valiron dominant-face
obstruction in the form forced by mid-plateau monomialization.

This file collects the two elementary ingredients and then the theorem:

* `norm_prod_pow_sub_one_le` — a product of factors within `ε` of `1` is within `(1+ε)^d − 1` of `1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

/-! ## A product of near-unit factors is near unit -/

/-- A power of a factor within `ε` of `1` stays within `(1+ε)^k − 1` of `1`. -/
theorem norm_pow_sub_one_le {c : ℂ} {ε : ℝ} (hε : 0 ≤ ε) (hc : ‖c - 1‖ ≤ ε) (k : ℕ) :
    ‖c ^ k - 1‖ ≤ (1 + ε) ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hcn : ‖c‖ ≤ 1 + ε := by
        have := norm_add_le (c - 1) 1
        simpa using le_trans (by simpa using this) (by linarith)
      have hstep : ‖c ^ (k + 1) - 1‖ ≤ ‖c‖ * ‖c ^ k - 1‖ + ‖c - 1‖ := by
        have hid : c ^ (k + 1) - 1 = c * (c ^ k - 1) + (c - 1) := by ring
        rw [hid]
        exact le_trans (norm_add_le _ _) (by rw [norm_mul])
      have hnn : (0 : ℝ) ≤ (1 + ε) ^ k - 1 := by
        have : (1 : ℝ) ≤ (1 + ε) ^ k := one_le_pow₀ (by linarith)
        linarith
      calc ‖c ^ (k + 1) - 1‖ ≤ ‖c‖ * ‖c ^ k - 1‖ + ‖c - 1‖ := hstep
        _ ≤ (1 + ε) * ((1 + ε) ^ k - 1) + ε := by
            have h1 : ‖c‖ * ‖c ^ k - 1‖ ≤ (1 + ε) * ((1 + ε) ^ k - 1) :=
              mul_le_mul hcn ih (norm_nonneg _) (by linarith)
            linarith [hc]
        _ = (1 + ε) ^ (k + 1) - 1 := by ring

/-- **The product perturbation bound.**  A finite product of powers of factors each within `ε` of
`1` is within `(1+ε)^d − 1` of `1`, where `d` is the total degree. -/
theorem norm_prod_pow_sub_one_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (e : ι → ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hc : ∀ i ∈ s, ‖c i - 1‖ ≤ ε) :
    ‖(∏ i ∈ s, c i ^ e i) - 1‖ ≤ (1 + ε) ^ (∑ i ∈ s, e i) - 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
      have hcb : ‖c b - 1‖ ≤ ε := hc b (Finset.mem_insert_self b s)
      have hcs : ∀ i ∈ s, ‖c i - 1‖ ≤ ε := fun i hi => hc i (Finset.mem_insert_of_mem hi)
      have hprod : ∏ i ∈ insert b s, c i ^ e i = c b ^ e b * ∏ i ∈ s, c i ^ e i :=
        Finset.prod_insert hb
      have hsum : ∑ i ∈ insert b s, e i = e b + ∑ i ∈ s, e i := Finset.sum_insert hb
      have hIH := ih hcs
      have hbpow : ‖c b ^ e b - 1‖ ≤ (1 + ε) ^ e b - 1 := norm_pow_sub_one_le hε hcb (e b)
      have hbnorm : ‖c b ^ e b‖ ≤ (1 + ε) ^ e b := by
        have := norm_add_le (c b ^ e b - 1) 1
        simp only [sub_add_cancel] at this
        have h2 : ‖c b ^ e b - 1‖ + ‖(1 : ℂ)‖ ≤ ((1 + ε) ^ e b - 1) + 1 := by
          simpa using add_le_add hbpow (le_refl (1 : ℝ))
        linarith [this, h2]
      have hnnS : (0 : ℝ) ≤ (1 + ε) ^ (∑ i ∈ s, e i) - 1 := by
        have : (1 : ℝ) ≤ (1 + ε) ^ (∑ i ∈ s, e i) := one_le_pow₀ (by linarith)
        linarith
      rw [hprod, hsum]
      have hid : c b ^ e b * (∏ i ∈ s, c i ^ e i) - 1
          = c b ^ e b * ((∏ i ∈ s, c i ^ e i) - 1) + (c b ^ e b - 1) := by ring
      rw [hid]
      calc ‖c b ^ e b * ((∏ i ∈ s, c i ^ e i) - 1) + (c b ^ e b - 1)‖
          ≤ ‖c b ^ e b‖ * ‖(∏ i ∈ s, c i ^ e i) - 1‖ + ‖c b ^ e b - 1‖ := by
            exact le_trans (norm_add_le _ _) (by rw [norm_mul])
        _ ≤ (1 + ε) ^ e b * ((1 + ε) ^ (∑ i ∈ s, e i) - 1) + ((1 + ε) ^ e b - 1) := by
            have := mul_le_mul hbnorm hIH (norm_nonneg _) (by positivity)
            linarith [hbpow]
        _ = (1 + ε) ^ (e b + ∑ i ∈ s, e i) - 1 := by rw [pow_add]; ring


/-- A crude but explicit expansion bound: `(1+δ)^D ≤ 1 + 3^D δ` for `0 ≤ δ ≤ 1`. -/
theorem one_add_pow_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (D : ℕ) :
    (1 + δ) ^ D ≤ 1 + 3 ^ D * δ := by
  induction D with
  | zero => simpa using hδ0
  | succ D ih =>
      have h3 : (1:ℝ) ≤ 3 ^ D := one_le_pow₀ (by norm_num)
      calc (1 + δ) ^ (D + 1) = (1 + δ) * (1 + δ) ^ D := by ring
        _ ≤ (1 + δ) * (1 + 3 ^ D * δ) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = 1 + 3 ^ D * δ + δ + 3 ^ D * δ * δ := by ring
        _ ≤ 1 + 3 ^ (D + 1) * δ := by nlinarith [h3, hδ0, hδ1]

/-! ## The degree and weight of a jet monomial -/

/-- The degree of a jet monomial. -/
def jetDeg {m : ℕ} (γ : Fin (m + 1) →₀ ℕ) : ℕ := ∑ i : Fin (m + 1), γ i

/-- The weight of a jet monomial: the derivative order counted with multiplicity. -/
def jetWt {m : ℕ} (γ : Fin (m + 1) →₀ ℕ) : ℕ := ∑ i : Fin (m + 1), (i : ℕ) * γ i

/-! ## Theorem 2 -/

/-- **Theorem 2: the autonomous ADE principal face degenerates.**  If a transcendental entire
function with super-Gaussian Taylor decay satisfies the autonomous algebraic differential equation
`P(f, f', …, f⁽ᵐ⁾) = 0`, then the coefficients of `P` on the top-degree, minimal-weight face sum to
zero.  Here `D` bounds the degrees, `Q` bounds the weights, and `q` is a lower bound for the weights
of the top-degree monomials. -/
theorem autonomous_face_sum_eq_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℕ → ℂ}
    (hcoeff : ∀ k : ℕ, iteratedDeriv k f 0 = (Nat.factorial k : ℂ) * a k)
    (hSG : SuperGaussianCoeffs a) (htrans : ∀ N : ℕ, ∃ n, N ≤ n ∧ a n ≠ 0)
    {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hroot : ∀ z : ℂ,
      MvPolynomial.eval (fun i : Fin (m + 1) => iteratedDeriv (i : ℕ) f z) P = 0)
    {D Q q : ℕ}
    (hD : ∀ γ ∈ P.support, jetDeg γ ≤ D)
    (hQ : ∀ γ ∈ P.support, jetWt γ ≤ Q)
    (hq : ∀ γ ∈ P.support, jetDeg γ = D → q ≤ jetWt γ)
    (hqQ : q ≤ Q) :
    ∑ γ ∈ P.support.filter (fun γ => jetDeg γ = D ∧ jetWt γ = q),
      MvPolynomial.coeff γ P = 0 := by
  classical
  set Face : Finset (Fin (m + 1) →₀ ℕ) :=
    P.support.filter (fun γ => jetDeg γ = D ∧ jetWt γ = q) with hFacedef
  set S : ℂ := ∑ γ ∈ Face, MvPolynomial.coeff γ P with hSdef
  set A : ℝ := ∑ γ ∈ P.support, ‖MvPolynomial.coeff γ P‖ with hAdef
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · -- all coefficients vanish
    have hzero : ∀ γ ∈ P.support, MvPolynomial.coeff γ P = 0 := by
      intro γ hγ
      have hle : ‖MvPolynomial.coeff γ P‖ ≤ A := by
        rw [hAdef]
        exact Finset.single_le_sum (f := fun d => ‖MvPolynomial.coeff d P‖)
          (fun i _ => norm_nonneg _) hγ
      have : ‖MvPolynomial.coeff γ P‖ ≤ 0 := by rw [← hA0] at hle; exact hle
      exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
    refine Finset.sum_eq_zero fun γ hγ => hzero γ ?_
    rw [hFacedef] at hγ
    exact (Finset.mem_filter.mp hγ).1
  -- the quantitative half
  have hgoal : ∀ ε : ℝ, 0 < ε → ‖S‖ ≤ 0 + ε := by
    intro ε hε
    set target : ℝ := ε / (2 * A) with htargetdef
    have htpos : 0 < target := by rw [htargetdef]; positivity
    -- the perturbation parameter
    set δ : ℝ := min 1 (target / 3 ^ D) with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      refine lt_min one_pos ?_
      positivity
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδtarget : (1 + δ) ^ D - 1 ≤ target := by
      have h3 : (0:ℝ) < 3 ^ D := by positivity
      have hle : δ ≤ target / 3 ^ D := min_le_right _ _
      have := one_add_pow_le hδpos.le hδ1 D
      have hmul : 3 ^ D * δ ≤ target := by
        rw [le_div_iff₀ h3] at hle
        linarith
      linarith
    -- the smallness parameter
    set ρ : ℝ := min 1 target with hρdef
    have hρpos : 0 < ρ := lt_min one_pos htpos
    have hρ1 : ρ ≤ 1 := min_le_left _ _
    have hρtarget : ρ ≤ target := min_le_right _ _
    obtain ⟨n, t, ht1, hnm, hane, hone, hsmall, hQt, hmono⟩ :=
      exists_monomialization_package hf hcoeff hSG htrans m Q hδpos hρpos
    have htpos' : (0:ℝ) < t := lt_of_lt_of_le one_pos ht1
    have hn1 : 1 ≤ n := by omega
    -- the evaluation point and the model states
    set z : ℂ := (t : ℂ) with hzdef
    have hznorm : ‖z‖ = t := by
      rw [hzdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htpos'.le]
    have hzne : z ≠ 0 := by
      intro h; rw [h] at hznorm; simp at hznorm; linarith
    set x : ℂ := a n * z ^ n with hxdef
    set η : ℂ := (n : ℂ) / z with hηdef
    have hnC : (n : ℂ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
    have hxne : x ≠ 0 := by
      rw [hxdef]; exact mul_ne_zero hane (pow_ne_zero _ hzne)
    have hηne : η ≠ 0 := by rw [hηdef]; exact div_ne_zero hnC hzne
    set u : Fin (m + 1) → ℂ := fun i => iteratedDeriv (i : ℕ) f z with hudef
    set v : Fin (m + 1) → ℂ := fun i => x * η ^ (i : ℕ) with hvdef
    have hvne : ∀ i : Fin (m + 1), v i ≠ 0 := by
      intro i; rw [hvdef]; exact mul_ne_zero hxne (pow_ne_zero _ hηne)
    have hvval : ∀ i : Fin (m + 1),
        v i = ((n : ℂ) ^ (i : ℕ)) * a n * z ^ (n - (i : ℕ)) := by
      intro i
      have hile : (i : ℕ) ≤ n := by omega
      rw [hvdef, hxdef, hηdef, div_pow, pow_sub₀ z hzne hile]
      field_simp
      ring
    have hvnorm : ∀ i : Fin (m + 1),
        ‖v i‖ = (n : ℝ) ^ (i : ℕ) * ‖a n‖ * t ^ (n - (i : ℕ)) := by
      intro i
      rw [hvval i, norm_mul, norm_mul, norm_pow, norm_pow, hznorm, Complex.norm_natCast]
    have hcdiff : ∀ i : Fin (m + 1), ‖u i / v i - 1‖ ≤ δ := by
      intro i
      have hi : (i : ℕ) ≤ m := by omega
      have hb := hmono (i : ℕ) hi z hznorm
      rw [← hvval i] at hb
      rw [← hvnorm i] at hb
      have hid : u i / v i - 1 = (u i - v i) / v i := by
        field_simp
      rw [hid, norm_div]
      rw [div_le_iff₀ (norm_pos_iff.mpr (hvne i))]
      exact hb
    -- the exact factorisation of every jet monomial
    have hvprod : ∀ γ : Fin (m + 1) →₀ ℕ,
        (∏ i : Fin (m + 1), v i ^ (γ i)) = x ^ jetDeg γ * η ^ jetWt γ := by
      intro γ
      calc (∏ i : Fin (m + 1), v i ^ (γ i))
          = ∏ i : Fin (m + 1), (x ^ (γ i) * η ^ ((i : ℕ) * γ i)) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [hvdef, mul_pow, ← pow_mul]
        _ = (∏ i : Fin (m + 1), x ^ (γ i)) * ∏ i : Fin (m + 1), η ^ ((i : ℕ) * γ i) :=
            Finset.prod_mul_distrib
        _ = x ^ (∑ i : Fin (m + 1), γ i) * η ^ (∑ i : Fin (m + 1), (i : ℕ) * γ i) := by
            rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
        _ = x ^ jetDeg γ * η ^ jetWt γ := rfl
    have huprod : ∀ γ : Fin (m + 1) →₀ ℕ,
        (∏ i : Fin (m + 1), u i ^ (γ i))
          = (x ^ jetDeg γ * η ^ jetWt γ) * ∏ i : Fin (m + 1), (u i / v i) ^ (γ i) := by
      intro γ
      rw [← hvprod γ, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_pow]
      congr 1
      field_simp
    sorry
  have hSle : ‖S‖ ≤ 0 := le_of_forall_pos_le_add hgoal
  exact norm_eq_zero.mp (le_antisymm hSle (norm_nonneg S))

end GaloisForLFunctions.HTGeometry
