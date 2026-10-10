import GaloisForLFunctions.RHTower.JointAncestryExplicitSectorTotalVariation

/-!
# JAS explicit-formula sectors: amplification at the Kronecker point

For a strip point `s = σ + it` the Kronecker point of the prime torus is `w_p = p^{it}`.  There the
two local Cauchy factors become real: `p^{-s} w_p = p^{-σ}` and `p^{-(1-s)} w̄_p = p^{σ-1}`, so the
local explicit-formula density is the positive real number

`K_p(σ) = (1 - p⁻¹) / ((1 - p^{-σ})(1 - p^{σ-1}))`,

and the depth-`P` density at the Kronecker point is `ζ_P(σ) ζ_P(1 - σ) / ζ_P(1)`.

**Amplification.**  With `x = p^{-1/2}` one has `(1 - p^{-σ})(1 - p^{σ-1}) = (1 - x)² - D_p`,
`D_p = (p^{-σ/2} - p^{(σ-1)/2})² ≥ 0`, so `K_p(σ) ≥ (1 + D_p) K_p(1/2)` with equality exactly on
the critical line.  Off the line `D_p ≥ c/p`, and the ratio of the depth-`P` Kronecker values of an
off-line sector and of the critical sector is at least `1 + c Σ_{p ∈ P} 1/p`, unbounded.

Together with the depth theorem (phase accumulates to `π` only over many primes) this is the
amplitude half of the mechanism by which positivity tests on the prime torus see an off-line zero:
near its Kronecker point its explicit-formula sector dominates every critical sector by an
unbounded factor, while its phase becomes negative only at large prime depth.
-/

open Complex
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-- The Kronecker point of the prime circle at `p` for the height of `s`. -/
def jasKroneckerPoint (s : ℂ) (p : Nat.Primes) : ℂ := cexp (((s.im * Real.log p : ℝ) : ℂ) * I)

theorem norm_jasKroneckerPoint (s : ℂ) (p : Nat.Primes) : ‖jasKroneckerPoint s p‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem jasHoloA_mul_kronecker (s : ℂ) (p : Nat.Primes) :
    jasHoloA s p * jasKroneckerPoint s p = (jasR1 s p : ℂ) := by
  rw [jasHoloA_mul_eq, jasKroneckerPoint, ← Complex.exp_add]
  rw [show ((-(s.im * Real.log p) : ℝ) : ℂ) * I + ((s.im * Real.log p : ℝ) : ℂ) * I = 0 by
    push_cast; ring, Complex.exp_zero, mul_one]

theorem jasHoloB_mul_conj_kronecker (s : ℂ) (p : Nat.Primes) :
    jasHoloB s p * conj (jasKroneckerPoint s p) = (jasR2 s p : ℂ) := by
  rw [jasHoloB_mul_conj_eq, jasKroneckerPoint, ← Complex.exp_add]
  rw [show ((-(s.im * Real.log p) : ℝ) : ℂ) * I + ((s.im * Real.log p : ℝ) : ℂ) * I = 0 by
    push_cast; ring, Complex.exp_zero, map_one, mul_one]

/-- Local Kronecker value `(1 - p⁻¹)/((1 - r₁)(1 - r₂))`. -/
def jasKroneckerValue (r₁ r₂ : ℝ) : ℝ := (1 - r₁ * r₂) / ((1 - r₁) * (1 - r₂))

/-- At the Kronecker point the local explicit-formula density is real. -/
theorem jasHoloLocal_kronecker {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (p : Nat.Primes) :
    jasHoloLocal (jasHoloA s p) (jasHoloB s p) (jasKroneckerPoint s p) =
      (jasKroneckerValue (jasR1 s p) (jasR2 s p) : ℂ) := by
  have h1 := jasR1_lt_one hs0 p
  have h2 := jasR2_lt_one hs1 p
  have hne1 : (1 - (jasR1 s p : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]; exact_mod_cast (by linarith : 1 - jasR1 s p ≠ 0)
  have hne2 : (1 - (jasR2 s p : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]; exact_mod_cast (by linarith : 1 - jasR2 s p ≠ 0)
  rw [jasHoloLocal, jasHoloA_mul_kronecker, jasHoloB_mul_conj_kronecker, jasKroneckerValue]
  push_cast
  field_simp
  ring

/-- Product form: the depth-`P` Kronecker value is a product of positive reals. -/
theorem prod_jasHoloLocal_kronecker {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (P : Finset Nat.Primes) :
    ∏ p ∈ P, jasHoloLocal (jasHoloA s p) (jasHoloB s p) (jasKroneckerPoint s p) =
      ((∏ p ∈ P, jasKroneckerValue (jasR1 s p) (jasR2 s p) : ℝ) : ℂ) := by
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun p _ => jasHoloLocal_kronecker hs0 hs1 p

/-- The critical local Kronecker value `(1 - p⁻¹)/(1 - p^{-1/2})²`. -/
def jasCriticalKroneckerValue (p : Nat.Primes) : ℝ :=
  (1 - (p : ℝ)⁻¹) / (1 - Real.exp (-(1 / 2) * Real.log p)) ^ 2

/-- The excess `D_p = (√r₁ - √r₂)²`. -/
def jasKroneckerExcess (s : ℂ) (p : Nat.Primes) : ℝ :=
  (Real.exp (-(s.re / 2) * Real.log p) - Real.exp (-((1 - s.re) / 2) * Real.log p)) ^ 2

theorem jasR1_eq_sq (s : ℂ) (p : Nat.Primes) :
    jasR1 s p = Real.exp (-(s.re / 2) * Real.log p) ^ 2 := by
  rw [jasR1, ← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem jasR2_eq_sq (s : ℂ) (p : Nat.Primes) :
    jasR2 s p = Real.exp (-((1 - s.re) / 2) * Real.log p) ^ 2 := by
  rw [jasR2, ← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem exp_half_mul_exp_half (s : ℂ) (p : Nat.Primes) :
    Real.exp (-(s.re / 2) * Real.log p) * Real.exp (-((1 - s.re) / 2) * Real.log p) =
      Real.exp (-(1 / 2) * Real.log p) := by
  rw [← Real.exp_add]; congr 1; ring

/-- **Local amplification.**  The local Kronecker value of any strip point is at least
`(1 + D_p)` times the critical value. -/
theorem one_add_excess_mul_critical_le_kroneckerValue {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (p : Nat.Primes) :
    (1 + jasKroneckerExcess s p) * jasCriticalKroneckerValue p ≤
      jasKroneckerValue (jasR1 s p) (jasR2 s p) := by
  set a := Real.exp (-(s.re / 2) * Real.log p) with ha
  set b := Real.exp (-((1 - s.re) / 2) * Real.log p) with hb
  set x := Real.exp (-(1 / 2) * Real.log p) with hx
  have hab : a * b = x := exp_half_mul_exp_half s p
  have hr1 : jasR1 s p = a ^ 2 := jasR1_eq_sq s p
  have hr2 : jasR2 s p = b ^ 2 := jasR2_eq_sq s p
  have h1 := jasR1_lt_one hs0 p
  have h2 := jasR2_lt_one hs1 p
  have hp : (p : ℝ)⁻¹ = x ^ 2 := by
    rw [hx, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(1 / 2) * Real.log p) = -Real.log p by
      push_cast; ring, Real.exp_neg, Real.exp_log (by exact_mod_cast p.2.pos)]
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have hx1 : x < 1 := by
    rw [hx, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  have hx0 : 0 < x := Real.exp_pos _
  rw [hr1] at h1 ⊢
  rw [hr2] at h2 ⊢
  unfold jasKroneckerValue jasCriticalKroneckerValue jasKroneckerExcess
  rw [← ha, ← hb, ← hx, hp]
  -- (1 - a²)(1 - b²) = (1 - x)² - (a - b)², with x = ab
  have hden : (1 - a ^ 2) * (1 - b ^ 2) = (1 - x) ^ 2 - (a - b) ^ 2 := by
    rw [← hab]; ring
  have hnum : 1 - a ^ 2 * b ^ 2 = 1 - x ^ 2 := by rw [← hab]; ring
  rw [hnum, hden]
  have hpos1 : 0 < (1 - x) ^ 2 - (a - b) ^ 2 := by rw [← hden]; nlinarith
  have hpos2 : 0 < (1 - x) ^ 2 := by nlinarith
  have hnum0 : 0 < 1 - x ^ 2 := by nlinarith
  rw [← mul_div_assoc, div_le_div_iff₀ hpos2 hpos1]
  have hD : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  have hone : (1 - x) ^ 2 ≤ 1 := by nlinarith
  have key : (1 + (a - b) ^ 2) * ((1 - x) ^ 2 - (a - b) ^ 2) ≤ (1 - x) ^ 2 := by
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hone)]
  calc (1 + (a - b) ^ 2) * (1 - x ^ 2) * ((1 - x) ^ 2 - (a - b) ^ 2)
      = (1 - x ^ 2) * ((1 + (a - b) ^ 2) * ((1 - x) ^ 2 - (a - b) ^ 2)) := by ring
    _ ≤ (1 - x ^ 2) * (1 - x) ^ 2 := mul_le_mul_of_nonneg_left key hnum0.le

/-- Off the critical line the Kronecker excess is at least `c/p`. -/
theorem exists_pos_inv_le_jasKroneckerExcess {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hoff : s.re ≠ 1 / 2) :
    ∃ c > 0, ∀ p : Nat.Primes, c * (p : ℝ)⁻¹ ≤ jasKroneckerExcess s p := by
  -- apply the radius-gap lemma at the half-exponent point `s/2 + 1/4`
  set s' : ℂ := ((s.re / 2 + 1 / 4 : ℝ) : ℂ) with hs'
  have hre : s'.re = s.re / 2 + 1 / 4 := by rw [hs']; simp
  have hs'0 : 0 < s'.re := by rw [hre]; linarith
  have hs'1 : s'.re < 1 := by rw [hre]; linarith
  have hs'off : s'.re ≠ 1 / 2 := by rw [hre]; intro h; apply hoff; linarith
  obtain ⟨c, hc, hgap⟩ := exists_pos_inv_le_sq_jasR1_sub_jasR2 hs'0 hs'1 hs'off
  refine ⟨c * Real.exp (-(1 / 2) * Real.log 2) ^ 2, by positivity, fun p => ?_⟩
  have h := hgap p
  -- jasR1 s' p = p^{-(σ/2+1/4)} = p^{-1/4} · √r₁(s), jasR2 s' p = p^{-1/4} · √r₂(s)
  set y := Real.exp (-(1 / 4) * Real.log p) with hy
  have hR1 : jasR1 s' p = y * Real.exp (-(s.re / 2) * Real.log p) := by
    rw [jasR1, hre, hy, ← Real.exp_add]; congr 1; ring
  have hR2 : jasR2 s' p = y * Real.exp (-((1 - s.re) / 2) * Real.log p) := by
    rw [jasR2, hre, hy, ← Real.exp_add]; congr 1; ring
  rw [hR1, hR2, ← mul_sub, mul_pow] at h
  have hy2 : y ^ 2 ≤ 1 := by
    rw [hy, ← Real.exp_nat_mul, Real.exp_le_one_iff]; push_cast; nlinarith [log_prime_pos p]
  unfold jasKroneckerExcess
  have hD0 : 0 ≤ (Real.exp (-(s.re / 2) * Real.log p) -
      Real.exp (-((1 - s.re) / 2) * Real.log p)) ^ 2 := sq_nonneg _
  have hfac : Real.exp (-(1 / 2) * Real.log 2) ^ 2 ≤ 1 := by
    rw [← Real.exp_nat_mul, Real.exp_le_one_iff]; push_cast
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hinv0 : 0 ≤ ((p : ℕ) : ℝ)⁻¹ := by positivity
  calc c * Real.exp (-(1 / 2) * Real.log 2) ^ 2 * ((p : ℕ) : ℝ)⁻¹
      ≤ c * ((p : ℕ) : ℝ)⁻¹ := by
        rw [mul_assoc, mul_comm (Real.exp _ ^ 2), ← mul_assoc]
        exact mul_le_of_le_one_right (by positivity) hfac
    _ ≤ y ^ 2 * (Real.exp (-(s.re / 2) * Real.log p) -
          Real.exp (-((1 - s.re) / 2) * Real.log p)) ^ 2 := h
    _ ≤ _ := mul_le_of_le_one_left hD0 hy2

theorem jasCriticalKroneckerValue_pos (p : Nat.Primes) : 0 < jasCriticalKroneckerValue p := by
  have hx1 : Real.exp (-(1 / 2) * Real.log p) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  have hp : ((p : ℕ) : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by exact_mod_cast p.2.pos)]; exact_mod_cast p.2.one_lt
  unfold jasCriticalKroneckerValue
  apply div_pos (by linarith)
  have : 0 < 1 - Real.exp (-(1 / 2) * Real.log p) := by linarith
  positivity

/-- **Unbounded Kronecker amplification.**  Off the critical line, for every bound `B` some finite
prime set makes the depth-`P` Kronecker value exceed `B` times the critical one. -/
theorem exists_kronecker_amplification {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hoff : s.re ≠ 1 / 2) (B : ℝ) :
    ∃ P : Finset Nat.Primes, B * ∏ p ∈ P, jasCriticalKroneckerValue p <
      ∏ p ∈ P, jasKroneckerValue (jasR1 s p) (jasR2 s p) := by
  classical
  obtain ⟨c, hc, hexc⟩ := exists_pos_inv_le_jasKroneckerExcess hs0 hs1 hoff
  obtain ⟨P, hP⟩ : ∃ P : Finset Nat.Primes, (B - 1) / c < ∑ p ∈ P, ((p : ℕ) : ℝ)⁻¹ := by
    by_contra h
    push Not at h
    apply Nat.Primes.not_summable_one_div
    simp_rw [one_div]
    exact summable_of_sum_le (fun p => by positivity) h
  refine ⟨P, ?_⟩
  have hcrit : 0 < ∏ p ∈ P, jasCriticalKroneckerValue p :=
    Finset.prod_pos fun p _ => jasCriticalKroneckerValue_pos p
  have hlocal : ∀ p ∈ P, (1 + c * ((p : ℕ) : ℝ)⁻¹) * jasCriticalKroneckerValue p ≤
      jasKroneckerValue (jasR1 s p) (jasR2 s p) := by
    intro p _
    refine le_trans ?_ (one_add_excess_mul_critical_le_kroneckerValue hs0 hs1 p)
    have := hexc p
    have := jasCriticalKroneckerValue_pos p
    gcongr
  have hprod : (∏ p ∈ P, (1 + c * ((p : ℕ) : ℝ)⁻¹)) * ∏ p ∈ P, jasCriticalKroneckerValue p ≤
      ∏ p ∈ P, jasKroneckerValue (jasR1 s p) (jasR2 s p) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun p _ => mul_nonneg (by positivity)
      (jasCriticalKroneckerValue_pos p).le) hlocal
  have hsum := jas_one_add_sum_le_prod_one_add P (fun p => c * ((p : ℕ) : ℝ)⁻¹)
    fun p => by positivity
  rw [← Finset.mul_sum] at hsum
  have hB : B < 1 + c * ∑ p ∈ P, ((p : ℕ) : ℝ)⁻¹ := by
    rw [div_lt_iff₀ hc] at hP; linarith
  calc B * ∏ p ∈ P, jasCriticalKroneckerValue p
      < (1 + c * ∑ p ∈ P, ((p : ℕ) : ℝ)⁻¹) * ∏ p ∈ P, jasCriticalKroneckerValue p :=
        mul_lt_mul_of_pos_right hB hcrit
    _ ≤ (∏ p ∈ P, (1 + c * ((p : ℕ) : ℝ)⁻¹)) * ∏ p ∈ P, jasCriticalKroneckerValue p :=
        mul_le_mul_of_nonneg_right hsum hcrit.le
    _ ≤ _ := hprod

/-- On the critical line the local Kronecker value equals the critical value. -/
theorem jasKroneckerValue_eq_critical {s : ℂ} (hs : s.re = 1 / 2) (p : Nat.Primes) :
    jasKroneckerValue (jasR1 s p) (jasR2 s p) = jasCriticalKroneckerValue p := by
  have hprod := jasR1_mul_jasR2 s p
  have h12 : jasR2 s p = jasR1 s p := by rw [jasR1, jasR2, hs]; norm_num
  have h1 : jasR1 s p = Real.exp (-(1 / 2) * Real.log p) := by rw [jasR1, hs]
  unfold jasKroneckerValue jasCriticalKroneckerValue
  rw [hprod, h12, h1, sq]

end

end RHTower
