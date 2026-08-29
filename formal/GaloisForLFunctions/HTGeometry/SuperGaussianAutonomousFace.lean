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
        _ ≤ 1 + 3 ^ (D + 1) * δ := by
            have hpow : (3:ℝ) ^ (D + 1) = 3 * 3 ^ D := by ring
            have h1 : δ ≤ 3 ^ D * δ := by nlinarith [h3, hδ0]
            have h2 : (3:ℝ) ^ D * δ * δ ≤ 3 ^ D * δ := by nlinarith [h3, hδ0, hδ1]
            rw [hpow]; linarith

/-! ## The degree and weight of a jet monomial -/

/-- The degree of a jet monomial. -/
def jetDeg {m : ℕ} (γ : Fin (m + 1) →₀ ℕ) : ℕ := ∑ i : Fin (m + 1), γ i

/-- The weight of a jet monomial: the derivative order counted with multiplicity. -/
def jetWt {m : ℕ} (γ : Fin (m + 1) →₀ ℕ) : ℕ := ∑ i : Fin (m + 1), (i : ℕ) * γ i

/-- **The off-face ratio estimate.**  With `X ≥ 1`, `0 ≤ H ≤ 1`, `H ≤ ρ` and `1 ≤ ρ X H^q`, a
monomial that is not on the top-degree minimal-weight face is smaller than the face monomial by the
factor `ρ`. -/
theorem monomial_face_ratio_le {X H ρ : ℝ} {D q d w : ℕ}
    (hX : 1 ≤ X) (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (hHρ : H ≤ ρ)
    (hXH : 1 ≤ ρ * X * H ^ q) (hd : d ≤ D) (hcase : d = D → q + 1 ≤ w) :
    X ^ d * H ^ w ≤ ρ * (X ^ D * H ^ q) := by
  have hX0 : (0:ℝ) ≤ X := le_trans zero_le_one hX
  rcases eq_or_lt_of_le hd with heq | hlt
  · have hwq := hcase heq
    have hsplit : H ^ w = H ^ q * H ^ (w - q) := by rw [← pow_add]; congr 1; omega
    have h1 : H ^ (w - q) ≤ H := by
      calc H ^ (w - q) ≤ H ^ 1 := pow_le_pow_of_le_one hH0 hH1 (by omega)
        _ = H := pow_one H
    calc X ^ d * H ^ w = (X ^ d * H ^ q) * H ^ (w - q) := by rw [hsplit]; ring
      _ ≤ (X ^ d * H ^ q) * ρ :=
          mul_le_mul_of_nonneg_left (le_trans h1 hHρ) (by positivity)
      _ = ρ * (X ^ d * H ^ q) := by ring
      _ = ρ * (X ^ D * H ^ q) := by rw [heq]
  · have hXd : X ^ d ≤ X ^ (D - 1) := pow_le_pow_right₀ hX (by omega)
    have hHw : H ^ w ≤ 1 := pow_le_one₀ hH0 hH1
    have hXD : X ^ (D - 1) * X = X ^ D := by rw [← pow_succ]; congr 1; omega
    calc X ^ d * H ^ w ≤ X ^ (D - 1) * 1 :=
          mul_le_mul hXd hHw (by positivity) (by positivity)
      _ = X ^ (D - 1) := mul_one _
      _ ≤ X ^ (D - 1) * (ρ * X * H ^ q) :=
          le_mul_of_one_le_right (by positivity) hXH
      _ = ρ * (X ^ D * H ^ q) := by rw [← hXD]; ring

/-! ## Theorem 2 -/

/-- **Theorem 2: the autonomous ADE principal face degenerates.**  If a transcendental entire
function with super-Gaussian Taylor decay satisfies the autonomous algebraic differential equation
`P(f, f', …, f⁽ᵐ⁾) = 0`, then the coefficients of `P` on the top-degree, minimal-weight face sum to
zero.  Here `D` bounds the degrees and `q` is a lower bound for the weights of the top-degree
monomials. -/
theorem autonomous_face_sum_eq_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℕ → ℂ}
    (hcoeff : ∀ k : ℕ, iteratedDeriv k f 0 = (Nat.factorial k : ℂ) * a k)
    (hSG : SuperGaussianCoeffs a) (htrans : ∀ N : ℕ, ∃ n, N ≤ n ∧ a n ≠ 0)
    {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hroot : ∀ z : ℂ,
      MvPolynomial.eval (fun i : Fin (m + 1) => iteratedDeriv (i : ℕ) f z) P = 0)
    {D q : ℕ}
    (hD : ∀ γ ∈ P.support, jetDeg γ ≤ D)
    (hq : ∀ γ ∈ P.support, jetDeg γ = D → q ≤ jetWt γ) :
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
      exists_monomialization_package hf hcoeff hSG htrans m q hδpos hρpos
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
      simp only [hvdef, hxdef, hηdef]
      rw [div_pow, pow_sub₀ z hzne hile]
      field_simp
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
        rw [sub_div, div_self (hvne i)]
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
      have hvi : v i ≠ 0 := hvne i
      field_simp
    -- the norms of the model data
    set X : ℝ := ‖a n‖ * t ^ n with hXdef
    set H : ℝ := (n : ℝ) / t with hHdef
    have hxnorm : ‖x‖ = X := by
      rw [hxdef, hXdef, norm_mul, norm_pow, hznorm]
    have hηnorm : ‖η‖ = H := by
      rw [hηdef, hHdef, norm_div, Complex.norm_natCast, hznorm]
    have hX1 : 1 ≤ X := hone
    have hX0 : (0:ℝ) ≤ X := le_trans zero_le_one hX1
    have hn1R : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hHlb : 1 / t ≤ H := by
      rw [hHdef, div_le_div_iff₀ htpos' htpos']
      nlinarith [hn1R, htpos']
    have hHpos : (0:ℝ) < H := lt_of_lt_of_le (by positivity) hHlb
    have hH0 : (0:ℝ) ≤ H := hHpos.le
    have hHρ : H ≤ ρ := by
      rw [hHdef, div_le_iff₀ htpos']
      linarith [hsmall]
    have hH1 : H ≤ 1 := le_trans hHρ hρ1
    have hq1 : (1 / t) ^ q ≤ H ^ q := pow_le_pow_left₀ (by positivity) hHlb q
    have hXHone : 1 ≤ ρ * X * H ^ q := by
      have hbase : 1 ≤ ρ * X * (1 / t) ^ q := by
        rw [div_pow, one_pow, mul_one_div, le_div_iff₀ (by positivity)]
        linarith [hQt]
      have hstep : ρ * X * (1 / t) ^ q ≤ ρ * X * H ^ q :=
        mul_le_mul_of_nonneg_left hq1 (by positivity)
      linarith
    set G : ℝ := X ^ D * H ^ q with hGdef
    have hGpos : 0 < G := by rw [hGdef]; positivity
    have hoffFace : ∀ γ ∈ P.support, γ ∉ Face →
        X ^ jetDeg γ * H ^ jetWt γ ≤ ρ * G := by
      intro γ hγ hγF
      refine monomial_face_ratio_le hX1 hH0 hH1 hHρ hXHone (hD γ hγ) ?_
      intro hdeq
      have hwne : jetWt γ ≠ q := by
        intro hw
        exact hγF (by rw [hFacedef]; exact Finset.mem_filter.mpr ⟨hγ, hdeq, hw⟩)
      have := hq γ hγ hdeq
      omega
    have honFace : ∀ γ ∈ Face, X ^ jetDeg γ * H ^ jetWt γ = G := by
      intro γ hγ
      rw [hFacedef] at hγ
      obtain ⟨-, hd, hw⟩ := Finset.mem_filter.mp hγ
      rw [hd, hw, hGdef]
    have hall : ∀ γ ∈ P.support, X ^ jetDeg γ * H ^ jetWt γ ≤ G := by
      intro γ hγ
      by_cases hγF : γ ∈ Face
      · exact le_of_eq (honFace γ hγF)
      · calc X ^ jetDeg γ * H ^ jetWt γ ≤ ρ * G := hoffFace γ hγ hγF
          _ ≤ 1 * G := mul_le_mul_of_nonneg_right hρ1 hGpos.le
          _ = G := one_mul G
    -- the perturbation factor
    set Cf : (Fin (m + 1) →₀ ℕ) → ℂ :=
      fun γ => ∏ i : Fin (m + 1), (u i / v i) ^ (γ i) with hCfdef
    have hCbound : ∀ γ ∈ P.support, ‖Cf γ - 1‖ ≤ (1 + δ) ^ D - 1 := by
      intro γ hγ
      have h := norm_prod_pow_sub_one_le (Finset.univ : Finset (Fin (m + 1)))
        (fun i => u i / v i) (fun i => γ i) hδpos.le (fun i _ => hcdiff i)
      have hdeg : ∑ i : Fin (m + 1), γ i = jetDeg γ := rfl
      rw [hdeg] at h
      have hmono' : (1 + δ) ^ (jetDeg γ) ≤ (1 + δ) ^ D :=
        pow_le_pow_right₀ (by linarith) (hD γ hγ)
      calc ‖Cf γ - 1‖ ≤ (1 + δ) ^ (jetDeg γ) - 1 := h
        _ ≤ (1 + δ) ^ D - 1 := by linarith
    -- the differential equation
    have hDE : ∑ γ ∈ P.support,
        MvPolynomial.coeff γ P * (∏ i : Fin (m + 1), u i ^ (γ i)) = 0 := by
      have h := hroot z
      rw [MvPolynomial.eval_eq'] at h
      exact h
    have hWsplit : ∑ γ ∈ P.support, MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ)
        = - ∑ γ ∈ P.support,
            MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ) * (Cf γ - 1) := by
      have hsum : ∑ γ ∈ P.support,
          (MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ)
            + MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ) * (Cf γ - 1)) = 0 := by
        rw [← hDE]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [huprod γ]
        simp only [hCfdef]
        ring
      rw [Finset.sum_add_distrib] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
    -- the two norm estimates
    have hcoeffle : ∀ γ ∈ P.support, ‖MvPolynomial.coeff γ P‖ ≤ A := by
      intro γ hγ
      rw [hAdef]
      exact Finset.single_le_sum (f := fun d => ‖MvPolynomial.coeff d P‖)
        (fun i _ => norm_nonneg _) hγ
    have hmonorm : ∀ γ : Fin (m + 1) →₀ ℕ,
        ‖x ^ jetDeg γ * η ^ jetWt γ‖ = X ^ jetDeg γ * H ^ jetWt γ := by
      intro γ
      rw [norm_mul, norm_pow, norm_pow, hxnorm, hηnorm]
    have hnormW : ‖∑ γ ∈ P.support, MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ)‖
        ≤ ((1 + δ) ^ D - 1) * (A * G) := by
      rw [hWsplit, norm_neg]
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ γ ∈ P.support,
          ‖MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ) * (Cf γ - 1)‖
            ≤ ((1 + δ) ^ D - 1) * (‖MvPolynomial.coeff γ P‖ * G) := by
        intro γ hγ
        rw [norm_mul, norm_mul, hmonorm γ]
        have hD1 : (0:ℝ) ≤ (1 + δ) ^ D - 1 := by
          have : (1:ℝ) ≤ (1 + δ) ^ D := one_le_pow₀ (by linarith)
          linarith
        calc ‖MvPolynomial.coeff γ P‖ * (X ^ jetDeg γ * H ^ jetWt γ) * ‖Cf γ - 1‖
            ≤ ‖MvPolynomial.coeff γ P‖ * G * ((1 + δ) ^ D - 1) := by
              refine mul_le_mul ?_ (hCbound γ hγ) (norm_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_left (hall γ hγ) (norm_nonneg _)
          _ = ((1 + δ) ^ D - 1) * (‖MvPolynomial.coeff γ P‖ * G) := by ring
      calc ∑ γ ∈ P.support, ‖MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ) * (Cf γ - 1)‖
          ≤ ∑ γ ∈ P.support, ((1 + δ) ^ D - 1) * (‖MvPolynomial.coeff γ P‖ * G) :=
            Finset.sum_le_sum hterm
        _ = ((1 + δ) ^ D - 1) * ((∑ γ ∈ P.support, ‖MvPolynomial.coeff γ P‖) * G) := by
            rw [← Finset.mul_sum, ← Finset.sum_mul]
        _ = ((1 + δ) ^ D - 1) * (A * G) := by rw [hAdef]
    have hnormOff : ‖∑ γ ∈ P.support \ Face,
        MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ)‖ ≤ ρ * (A * G) := by
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ γ ∈ P.support \ Face,
          ‖MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ)‖
            ≤ ρ * (‖MvPolynomial.coeff γ P‖ * G) := by
        intro γ hγ
        rw [Finset.mem_sdiff] at hγ
        rw [norm_mul, hmonorm γ]
        calc ‖MvPolynomial.coeff γ P‖ * (X ^ jetDeg γ * H ^ jetWt γ)
            ≤ ‖MvPolynomial.coeff γ P‖ * (ρ * G) :=
              mul_le_mul_of_nonneg_left (hoffFace γ hγ.1 hγ.2) (norm_nonneg _)
          _ = ρ * (‖MvPolynomial.coeff γ P‖ * G) := by ring
      have hsub : ∑ γ ∈ P.support \ Face, ‖MvPolynomial.coeff γ P‖ ≤ A := by
        rw [hAdef]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun i _ _ => norm_nonneg _)
      calc ∑ γ ∈ P.support \ Face, ‖MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ)‖
          ≤ ∑ γ ∈ P.support \ Face, ρ * (‖MvPolynomial.coeff γ P‖ * G) :=
            Finset.sum_le_sum hterm
        _ = ρ * ((∑ γ ∈ P.support \ Face, ‖MvPolynomial.coeff γ P‖) * G) := by
            rw [← Finset.mul_sum, ← Finset.sum_mul]
        _ ≤ ρ * (A * G) := by
            refine mul_le_mul_of_nonneg_left ?_ hρpos.le
            exact mul_le_mul_of_nonneg_right hsub hGpos.le
    -- the face sum
    have hsubF : Face ⊆ P.support := by rw [hFacedef]; exact Finset.filter_subset _ _
    have hFacesum : ∑ γ ∈ Face, MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ)
        = S * (x ^ D * η ^ q) := by
      rw [hSdef, Finset.sum_mul]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [hFacedef] at hγ
      obtain ⟨-, hd, hw⟩ := Finset.mem_filter.mp hγ
      rw [hd, hw]
    have hdecomp : S * (x ^ D * η ^ q)
        = (∑ γ ∈ P.support, MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ))
          - ∑ γ ∈ P.support \ Face,
              MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ) := by
      rw [← hFacesum, ← Finset.sum_sdiff hsubF]
      ring
    have hSGnorm : ‖S‖ * G ≤ ((1 + δ) ^ D - 1) * (A * G) + ρ * (A * G) := by
      have hnorm : ‖S * (x ^ D * η ^ q)‖ = ‖S‖ * G := by
        rw [norm_mul, norm_mul, norm_pow, norm_pow, hxnorm, hηnorm, hGdef]
      calc ‖S‖ * G = ‖S * (x ^ D * η ^ q)‖ := hnorm.symm
        _ = ‖(∑ γ ∈ P.support, MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ))
              - ∑ γ ∈ P.support \ Face,
                  MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ)‖ := by rw [hdecomp]
        _ ≤ ‖∑ γ ∈ P.support, MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ)‖
              + ‖∑ γ ∈ P.support \ Face,
                  MvPolynomial.coeff γ P * (x ^ jetDeg γ * η ^ jetWt γ)‖ := norm_sub_le _ _
        _ ≤ ((1 + δ) ^ D - 1) * (A * G) + ρ * (A * G) := add_le_add hnormW hnormOff
    -- divide by the positive model monomial
    have hfinal : ‖S‖ ≤ ε := by
      have hAG : (0:ℝ) < A * G := mul_pos hApos hGpos
      have hbound : ‖S‖ * G ≤ (target + target) * (A * G) := by
        have h1 : ((1 + δ) ^ D - 1) * (A * G) ≤ target * (A * G) :=
          mul_le_mul_of_nonneg_right hδtarget hAG.le
        have h2 : ρ * (A * G) ≤ target * (A * G) :=
          mul_le_mul_of_nonneg_right hρtarget hAG.le
        calc ‖S‖ * G ≤ ((1 + δ) ^ D - 1) * (A * G) + ρ * (A * G) := hSGnorm
          _ ≤ target * (A * G) + target * (A * G) := add_le_add h1 h2
          _ = (target + target) * (A * G) := by ring
      have hAne : A ≠ 0 := ne_of_gt hApos
      have htt : (target + target) * A = ε := by
        rw [htargetdef]; field_simp; ring
      have hSle : ‖S‖ * G ≤ ε * G := by
        calc ‖S‖ * G ≤ (target + target) * (A * G) := hbound
          _ = ((target + target) * A) * G := by ring
          _ = ε * G := by rw [htt]
      exact le_of_mul_le_mul_right hSle hGpos
    linarith [hfinal]
  have hSle : ‖S‖ ≤ 0 := le_of_forall_pos_le_add hgoal
  exact norm_eq_zero.mp (le_antisymm hSle (norm_nonneg S))


/-- **Theorem 2, canonical form.**  For a nonzero autonomous differential polynomial annihilating
such an `f`, the top degree `D` and the minimal weight `q` on the top-degree stratum are attained —
so the principal face is nonempty — and the coefficients on that face sum to zero. -/
theorem exists_autonomous_face_nonempty_sum_eq_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℕ → ℂ}
    (hcoeff : ∀ k : ℕ, iteratedDeriv k f 0 = (Nat.factorial k : ℂ) * a k)
    (hSG : SuperGaussianCoeffs a) (htrans : ∀ N : ℕ, ∃ n, N ≤ n ∧ a n ≠ 0)
    {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℂ) (hP : P ≠ 0)
    (hroot : ∀ z : ℂ,
      MvPolynomial.eval (fun i : Fin (m + 1) => iteratedDeriv (i : ℕ) f z) P = 0) :
    ∃ D q : ℕ,
      (∃ γ ∈ P.support, jetDeg γ = D ∧ jetWt γ = q) ∧
      (∀ γ ∈ P.support, jetDeg γ ≤ D) ∧
      (∀ γ ∈ P.support, jetDeg γ = D → q ≤ jetWt γ) ∧
      ∑ γ ∈ P.support.filter (fun γ => jetDeg γ = D ∧ jetWt γ = q),
        MvPolynomial.coeff γ P = 0 := by
  classical
  have hsupp : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  set D : ℕ := P.support.sup' hsupp jetDeg with hDdef
  have hDle : ∀ γ ∈ P.support, jetDeg γ ≤ D := fun γ hγ => Finset.le_sup' jetDeg hγ
  obtain ⟨γ₀, hγ₀mem, hγ₀⟩ := Finset.exists_mem_eq_sup' hsupp jetDeg
  set Top : Finset (Fin (m + 1) →₀ ℕ) := P.support.filter (fun γ => jetDeg γ = D) with hTopdef
  have hTopne : Top.Nonempty := ⟨γ₀, by rw [hTopdef]; exact Finset.mem_filter.mpr ⟨hγ₀mem, hγ₀.symm⟩⟩
  set q : ℕ := Top.inf' hTopne jetWt with hqdef
  have hqle : ∀ γ ∈ P.support, jetDeg γ = D → q ≤ jetWt γ := by
    intro γ hγ hd
    exact Finset.inf'_le jetWt (by rw [hTopdef]; exact Finset.mem_filter.mpr ⟨hγ, hd⟩)
  obtain ⟨γ₁, hγ₁mem, hγ₁⟩ := Finset.exists_mem_eq_inf' hTopne jetWt
  rw [hTopdef] at hγ₁mem
  obtain ⟨hγ₁supp, hγ₁deg⟩ := Finset.mem_filter.mp hγ₁mem
  exact ⟨D, q, ⟨γ₁, hγ₁supp, hγ₁deg, hγ₁.symm⟩, hDle, hqle,
    autonomous_face_sum_eq_zero hf hcoeff hSG htrans P hroot hDle hqle⟩

end GaloisForLFunctions.HTGeometry
