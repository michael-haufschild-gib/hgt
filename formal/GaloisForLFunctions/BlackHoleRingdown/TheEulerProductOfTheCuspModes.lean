import GaloisForLFunctions.BlackHoleRingdown.TheLFunctionsOfTheCuspModes

/-!
# The Euler products of the cusp modes

The L-function of a Hecke eigenform of the cusp channel factors over the primes
(`cusp_euler_product`): if `T_p g = c_p g` for every prime and `λ_p = c_p/√p`, then for `Re s > 3/2`

  `Σ_{n ≠ 0} ρ(n) |n|^{-s} = (ρ(1) + ρ(-1)) Π_p (1 - λ_p p^{-s} + p^{-2s})⁻¹`.

**Hecke relations.** Inserting the Whittaker modes `a_n(y) = ρ(n)√y K_ν(2π|n|y)` into the Hecke recursion
`c a_n(y) = [p ∣ n] a_{n/p}(py) + p a_{pn}(y/p)`, every term carries the same `K_ν(2π|n|y)`, so
`ρ(pn) = λ_p ρ(n) - [p ∣ n] ρ(n/p)` (`rho_hecke`). Both `n ↦ ρ(n)` and `n ↦ ρ(-n)` obey these relations.

**Arithmetic of Hecke sequences.** A sequence obeying the relations is determined by its value at `1`
(`HeckeRec.eq_zero`, by strong induction through a prime factor), so all such sequences are proportional.
Normalized by `σ(1) = 1` it splits off prime powers, `σ(p^k m) = σ(p^k) σ(m)` for `p ∤ m`, and is
multiplicative (`HeckeRec.mul`). At each prime `σ(p^{k+2}) = λ_p σ(p^{k+1}) - σ(p^k)`, so
`(1 - λ_p x + x²) Σ_k σ(p^k) x^k = 1` (`HeckeRec.local_factor`), and the Euler product follows from
multiplicativity and absolute convergence (`HeckeRec.euler`). Absolute convergence for `Re s > 3/2` comes from
`|ρ(n)| ≤ C√|n|`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair GaloisForLFunctions.RHTower.Gamma0MaassHecke
open GaloisForLFunctions.HTGeometry (modifiedBesselKOrder eventually_re_modifiedBesselKOrder_pos)
open UpperHalfPlane (ofComplex)

namespace CuspEuler

/-! ### Hecke sequences -/

/-- `σ` obeys the Hecke relations `σ(pn) = λ_p σ(n) - [p ∣ n] σ(n/p)` at every prime `p` and `n ≥ 1`. -/
def HeckeRec (lam : ℕ → ℂ) (σ : ℕ → ℂ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℕ, 0 < n → σ (p * n) = lam p * σ n - if p ∣ n then σ (n / p) else 0

variable {lam : ℕ → ℂ} {σ τ : ℕ → ℂ}

theorem HeckeRec.lin (hσ : HeckeRec lam σ) (hτ : HeckeRec lam τ) (a b : ℂ) :
    HeckeRec lam fun n => a * σ n + b * τ n := by
  intro p hp n hn
  simp only
  rw [hσ p hp n hn, hτ p hp n hn]
  split_ifs <;> ring

/-- **Uniqueness.** A Hecke sequence vanishing at `1` vanishes at every `n ≥ 1`. -/
theorem HeckeRec.eq_zero (hσ : HeckeRec lam σ) (h1 : σ 1 = 0) : ∀ n : ℕ, 0 < n → σ n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n; exact h1
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      obtain ⟨m, rfl⟩ := hpn
      have hm : 0 < m := Nat.pos_of_mul_pos_left hn
      have hmlt : m < p * m := by nlinarith [hp.two_le]
      rw [hσ p hp m hm, ih m hmlt hm, mul_zero, zero_sub]
      split_ifs with hpm
      · rw [ih (m / p) (lt_of_le_of_lt (Nat.div_le_self _ _) hmlt)
          (Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos), neg_zero]
      · rw [neg_zero]

/-- Two Hecke sequences are proportional: `σ(n) τ(1) = τ(n) σ(1)`. -/
theorem HeckeRec.proportional (hσ : HeckeRec lam σ) (hτ : HeckeRec lam τ) (n : ℕ) (hn : 0 < n) :
    σ n * τ 1 = τ n * σ 1 := by
  have h := (hσ.lin hτ (τ 1) (-σ 1)).eq_zero (by ring) n hn
  linear_combination h

/-- At a prime power the Hecke sequence obeys the three-term recursion. -/
theorem HeckeRec.pow_succ_succ (hσ : HeckeRec lam σ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    σ (p ^ (k + 2)) = lam p * σ (p ^ (k + 1)) - σ (p ^ k) := by
  have h := hσ p hp (p ^ (k + 1)) (pow_pos hp.pos _)
  have hq : p ^ (k + 1) / p = p ^ k := by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [if_pos (dvd_pow_self p (by omega)), hq, show p * p ^ (k + 1) = p ^ (k + 2) by ring] at h
  exact h

theorem HeckeRec.prime (hσ : HeckeRec lam σ) (h1 : σ 1 = 1) {p : ℕ} (hp : p.Prime) : σ p = lam p := by
  have h := hσ p hp 1 one_pos
  rw [mul_one, h1, mul_one, if_neg (Nat.Prime.not_dvd_one hp), sub_zero] at h
  exact h

/-- **The prime-power factor splits off**: `σ(p^k m) = σ(p^k) σ(m)` for `p ∤ m`. -/
theorem HeckeRec.pow_mul (hσ : HeckeRec lam σ) (h1 : σ 1 = 1) {p : ℕ} (hp : p.Prime) {m : ℕ}
    (hm : 0 < m) (hpm : ¬ p ∣ m) : ∀ k : ℕ, σ (p ^ k * m) = σ (p ^ k) * σ m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · simp [h1]
    · rw [pow_one, hσ p hp m hm, if_neg hpm, sub_zero, hσ.prime h1 hp]
    · have hk := hσ p hp (p ^ (k + 1) * m) (Nat.mul_pos (pow_pos hp.pos _) hm)
      have hq : p ^ (k + 1) * m / p = p ^ k * m := by
        rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
      rw [if_pos (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m), hq,
        show p * (p ^ (k + 1) * m) = p ^ (k + 1 + 1) * m by ring, ih (k + 1) (by omega), ih k (by omega)] at hk
      rw [hk, hσ.pow_succ_succ hp k]
      ring

/-- **Multiplicativity**: a normalized Hecke sequence is multiplicative on coprime arguments. -/
theorem HeckeRec.mul (hσ : HeckeRec lam σ) (h1 : σ 1 = 1) :
    ∀ n m : ℕ, 0 < m → 0 < n → m.Coprime n → σ (m * n) = σ m * σ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hm hn hmn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n; simp [h1]
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    obtain ⟨k, n', hpn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
    have hn' : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at hpn; exact absurd hpn hpn'
      · exact h
    have hdvd : p ∣ p ^ k * n' := dvd_mul_of_dvd_left (dvd_pow_self p hk.ne') n'
    have hpm : ¬ p ∣ m := fun h => by
      have := Nat.dvd_gcd h hdvd
      rw [hmn.gcd_eq_one] at this
      exact hp.not_dvd_one this
    have hpmn : ¬ p ∣ m * n' := fun h => (hp.dvd_mul.1 h).elim hpm hpn'
    have hlt : n' < p ^ k * n' := by
      have : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow hk.ne' p)
      nlinarith
    have hcop : m.Coprime n' := hmn.coprime_dvd_right (dvd_mul_left n' (p ^ k))
    rw [show m * (p ^ k * n') = p ^ k * (m * n') by ring, hσ.pow_mul h1 hp (Nat.mul_pos hm hn') hpmn k,
      ih n' hlt m hm hn' hcop, hσ.pow_mul h1 hp hn' hpn' k]
    ring


/-- **The local factor.** If `Σ_e σ(p^e) x^e` converges, then `(1 - λ_p x + x²) Σ_e σ(p^e) x^e = 1`. -/
theorem HeckeRec.local_factor (hσ : HeckeRec lam σ) (h1 : σ 1 = 1) {p : ℕ} (hp : p.Prime) {x : ℂ}
    (hs : Summable fun e : ℕ => σ (p ^ e) * x ^ e) :
    (1 - lam p * x + x ^ 2) * ∑' e : ℕ, σ (p ^ e) * x ^ e = 1 := by
  set a : ℕ → ℂ := fun e => σ (p ^ e) * x ^ e
  have hs1 : Summable fun e => a (e + 1) := (summable_nat_add_iff 1).2 hs
  have hs2 : Summable fun e => a (e + 2) := (summable_nat_add_iff 2).2 hs
  have hS1 : ∑' e, a e = a 0 + ∑' e, a (e + 1) := hs.tsum_eq_zero_add
  have hS2 : ∑' e, a (e + 1) = a 1 + ∑' e, a (e + 2) := hs1.tsum_eq_zero_add
  have hrec : ∀ e, a (e + 2) = lam p * x * a (e + 1) - x ^ 2 * a e := fun e => by
    simp only [a]
    rw [hσ.pow_succ_succ hp e]
    ring
  have hS3 : ∑' e, a (e + 2) = lam p * x * ∑' e, a (e + 1) - x ^ 2 * ∑' e, a e := by
    rw [tsum_congr hrec, (hs1.mul_left _).tsum_sub (hs.mul_left _), tsum_mul_left, tsum_mul_left]
  have ha0 : a 0 = 1 := by simp [a, h1]
  have ha1 : a 1 = lam p * x := by simp [a, hσ.prime h1 hp]
  change (1 - lam p * x + x ^ 2) * ∑' e, a e = 1
  rw [ha0] at hS1
  rw [ha1] at hS2
  linear_combination (1 - lam p * x) * hS1 + hS2 + hS3

/-- **The Euler product** of a normalized Hecke sequence:
`Σ_n σ(n) n^{-s} = Π_p (1 - λ_p p^{-s} + p^{-2s})⁻¹`, when the series converges absolutely. -/
theorem HeckeRec.euler (hσ : HeckeRec lam σ) (h1 : σ 1 = 1) (h0 : σ 0 = 0) {s : ℂ}
    (hsum : Summable fun n : ℕ => ‖σ n * (n : ℂ) ^ (-s)‖) :
    ∏' p : Nat.Primes, (1 - lam p * (p : ℂ) ^ (-s) + ((p : ℂ) ^ (-s)) ^ 2)⁻¹ =
      ∑' n : ℕ, σ n * (n : ℂ) ^ (-s) := by
  set f : ℕ → ℂ := fun n => σ n * (n : ℂ) ^ (-s)
  have hf1 : f 1 = 1 := by simp [f, h1]
  have hf0 : f 0 = 0 := by simp [f, h0]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [Nat.coprime_zero_left] at hmn
      subst hmn
      simp [hf1]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Nat.coprime_zero_right] at hmn
      subst hmn
      simp [hf1]
    simp only [f]
    rw [hσ.mul h1 n m hm hn hmn, Nat.cast_mul, natCast_mul_natCast_cpow]
    ring
  have h := EulerProduct.eulerProduct_tprod hf1 hmul hsum hf0
  rw [← h]
  refine tprod_congr fun p => ?_
  have hpow : ∀ e : ℕ, f ((p : ℕ) ^ e) = σ ((p : ℕ) ^ e) * ((p : ℂ) ^ (-s)) ^ e := fun e => by
    simp only [f]
    rw [Nat.cast_pow, ← natCast_cpow_natCast_mul, cpow_nat_mul]
  have hsp : Summable fun e : ℕ => σ ((p : ℕ) ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
    have := (hsum.of_norm.comp_injective (Nat.pow_right_injective p.prop.two_le))
    exact this.congr fun e => hpow e
  rw [tsum_congr hpow]
  exact (eq_inv_of_mul_eq_one_right (hσ.local_factor h1 p.prop hsp)).symm


/-! ### The Hecke relations of the Whittaker coefficients -/

open HeckeCusp CuspL

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-- The normalized Hecke eigenvalue `λ_p = c_p / √p`. -/
def heckeLam (c : ℕ → ℂ) (p : ℕ) : ℂ := c p / (Real.sqrt p : ℂ)

/-- There is a point where the Whittaker function of index `n` does not vanish. -/
theorem exists_K_ne_zero (lamE : ℝ) {n : ℤ} (hn : n ≠ 0) :
    ∃ y : ℝ, 0 < y ∧ modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE) ≠ 0 := by
  obtain ⟨X, hX1, hXpos⟩ := eventually_re_modifiedBesselKOrder_pos (nu lamE)
  have hn0 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
  refine ⟨X / (2 * Real.pi * |(n : ℝ)|), by positivity, ?_⟩
  rw [show 2 * Real.pi * |(n : ℝ)| * (X / (2 * Real.pi * |(n : ℝ)|)) = X by field_simp]
  intro h
  have := hXpos X le_rfl
  rw [h, zero_re] at this
  exact lt_irrefl _ this

/-- **The Hecke relations of the coefficients**: `c_p ρ(n) = √p ([p ∣ n] ρ(n/p) + ρ(pn))` for `n ≠ 0`. -/
theorem rho_hecke (hg : g ∈ cuspSpace lamE)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE))
    (p : ℕ) [hp : Fact p.Prime] {c : ℂ} (hc : heckeH p g = c • g) {n : ℤ} (hn : n ≠ 0) :
    c * ρ n = (Real.sqrt p : ℂ) * ((if (p : ℤ) ∣ n then ρ (n / p) else 0) + ρ (p * n)) := by
  obtain ⟨y, hy, hK⟩ := exists_K_ne_zero lamE hn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hrec := hecke_recursion hg p hc n hy
  have hsp : Real.sqrt p ≠ 0 := (Real.sqrt_pos.2 hp0).ne'
  have hsy : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  set K := modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)
  have hpn : modifiedBesselKOrder (2 * Real.pi * |((p * n : ℤ) : ℝ)| * (y / p)) (nu lamE) = K := by
    congr 1
    push_cast
    rw [abs_mul, Nat.abs_cast]
    field_simp
  have h2 : fourierCoeff g (p * n) (y / p) = ρ (p * n) * ((Real.sqrt y / Real.sqrt p : ℝ) : ℂ) * K := by
    rw [hρ _ _ (by positivity), hpn, Real.sqrt_div' _ hp0.le]
  rw [hρ n y hy, h2] at hrec
  have hpsq : ((p : ℕ) : ℂ) = (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt hp0.le]; norm_cast
  have hspC : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast hsp
  have e : ((p : ℕ) : ℂ) * ((Real.sqrt y : ℂ) / (Real.sqrt p : ℂ)) = (Real.sqrt p : ℂ) * (Real.sqrt y : ℂ) := by
    rw [hpsq]; field_simp
  have hK' : (Real.sqrt y : ℂ) * K ≠ 0 := mul_ne_zero (by exact_mod_cast hsy) hK
  push_cast at hrec
  split_ifs at hrec ⊢ with hdvd
  · obtain ⟨m, hm⟩ := hdvd
    have hp0' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hq : n / p = m := by rw [hm, Int.mul_ediv_cancel_left _ hp0']
    rw [hq] at hrec ⊢
    have hmK : modifiedBesselKOrder (2 * Real.pi * |(m : ℝ)| * (p * y)) (nu lamE) = K := by
      congr 1
      rw [hm]
      push_cast
      rw [abs_mul, Nat.abs_cast]
      ring
    rw [hρ m (p * y) (by positivity), hmK, Real.sqrt_mul hp0.le] at hrec
    push_cast at hrec
    apply mul_right_cancel₀ hK'
    linear_combination hrec + (ρ (p * n) * K) * e
  · apply mul_right_cancel₀ hK'
    linear_combination hrec + (ρ (p * n) * K) * e

/-- The coefficients at positive and at negative indices are Hecke sequences. -/
theorem heckeRec_rho (hg : g ∈ cuspSpace lamE)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE))
    (c : ℕ → ℂ) (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    HeckeRec (heckeLam c) fun n : ℕ => ρ (ε * n) := by
  intro p hp n hn
  haveI := Fact.mk hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsp : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hp0).ne'
  have hεn : ε * (n : ℤ) ≠ 0 := by
    rcases hε with rfl | rfl <;> simp <;> omega
  have h := rho_hecke hg hρ p (hc p) hεn
  have hdvd : ((p : ℤ) ∣ ε * n) ↔ p ∣ n := by
    rcases hε with rfl | rfl
    · simp [Int.natCast_dvd_natCast]
    · simp [Int.natCast_dvd_natCast]
  have hdiv : p ∣ n → ε * ((n : ℤ) / (p : ℤ)) = ε * (n : ℤ) / p := by
    intro hpn
    rcases hε with rfl | rfl
    · simp
    · rw [neg_one_mul, neg_one_mul, Int.neg_ediv_of_dvd (Int.natCast_dvd_natCast.2 hpn)]
  simp only
  rw [Nat.cast_mul, show ε * ((p : ℤ) * n) = (p : ℤ) * (ε * n) by ring]
  unfold heckeLam
  by_cases hpn : p ∣ n
  · rw [if_pos hpn, Int.natCast_div, hdiv hpn]
    rw [if_pos (hdvd.2 hpn)] at h
    rw [eq_sub_iff_add_eq, div_mul_eq_mul_div, eq_div_iff hsp]
    linear_combination -h
  · rw [if_neg hpn, sub_zero]
    rw [if_neg (fun h' => hpn (hdvd.1 h'))] at h
    rw [div_mul_eq_mul_div, eq_div_iff hsp]
    linear_combination -h

/-- **The Euler product of a Hecke–Maass L-function.** If `g ∈ S(λ)` satisfies `T_p g = c_p g` for every
prime `p` and `Σ_n |ρ(n)| |n|^{-Re s} < ∞`, then
`Σ_{n≠0} ρ(n)|n|^{-s} = (ρ(1) + ρ(-1)) Π_p (1 - λ_p p^{-s} + p^{-2s})⁻¹` with `λ_p = c_p/√p`. -/
theorem cusp_euler_product_of_summable (hg : g ∈ cuspSpace lamE) (c : ℕ → ℂ)
    (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ}
    (hab : Summable fun n : ℤ => ‖ρ n‖ * |(n : ℝ)| ^ (-s.re)) :
    lSeries ρ s = (ρ 1 + ρ (-1)) *
      ∏' p : Nat.Primes, (1 - heckeLam c p * (p : ℂ) ^ (-s) + ((p : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  have hP := heckeRec_rho hg hρ c hc 1 (Or.inl rfl)
  have hM := heckeRec_rho hg hρ c hc (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at hP hM
  -- the series over `ℤ` converges absolutely
  have hnormZ : ∀ n : ℤ, ‖ρ n * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)‖ ≤ ‖ρ n‖ * |(n : ℝ)| ^ (-s.re) := by
    intro n
    by_cases hn : n = 0
    · simp [hn, hρ0]
    have hn0 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hn0, neg_re]
  have hsumZ : Summable fun n : ℤ => ρ n * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s) :=
    Summable.of_norm_bounded hab hnormZ
  have hNat := hsumZ.hasSum.nat_add_neg
  have hf0 : ρ 0 * ((|((0 : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-s) = 0 := by rw [hρ0, zero_mul]
  rw [hf0, add_zero] at hNat
  have hfold : ∀ n : ℕ, ρ n * ((|((n : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-s) +
      ρ (-(n : ℤ)) * ((|((-(n : ℤ) : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-s) = (ρ n + ρ (-(n : ℤ))) * (n : ℂ) ^ (-s) := by
    intro n
    have h1 : ((|((n : ℤ) : ℝ)| : ℝ) : ℂ) = (n : ℂ) := by simp
    have h2 : ((|((-(n : ℤ) : ℤ) : ℝ)| : ℝ) : ℂ) = (n : ℂ) := by simp
    rw [h1, h2]; ring
  simp_rw [hfold] at hNat
  by_cases h01 : ρ 1 = 0 ∧ ρ (-1) = 0
  · have hz : ∀ n : ℕ, ρ n + ρ (-(n : ℤ)) = 0 := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [hρ0]
      have e1 := hP.eq_zero (by simpa using h01.1) n hn
      have e2 := hM.eq_zero (by simpa using h01.2) n hn
      rw [e1, e2, add_zero]
    simp_rw [hz, zero_mul] at hNat
    rw [show lSeries ρ s = 0 from hNat.unique hasSum_zero, h01.1, h01.2, add_zero, zero_mul]
  -- normalize a nonzero sequence
  push Not at h01
  set σ₀ : ℕ → ℂ := if ρ 1 ≠ 0 then (fun n => ρ n) else (fun n => ρ (-(n : ℤ)))
  have hσ₀ : HeckeRec (heckeLam c) σ₀ := by
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]; exact hP
    · simp only [σ₀, if_neg h]; exact hM
  have ha : σ₀ 1 ≠ 0 := by
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]; simpa using h
    · simp only [σ₀, if_neg h]; push Not at h; simpa using h01 h
  set τ : ℕ → ℂ := fun n => (σ₀ 1)⁻¹ * σ₀ n + 0 * σ₀ n
  have hτ : HeckeRec (heckeLam c) τ := hσ₀.lin hσ₀ _ _
  have hτ1 : τ 1 = 1 := by simp only [τ]; field_simp; ring
  have hσ0 : σ₀ 0 = 0 := by
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]; simpa using hρ0
    · simp only [σ₀, if_neg h]; simpa using hρ0
  have hτ0 : τ 0 = 0 := by simp [τ, hσ0]
  have hsplit : ∀ n : ℕ, ρ n + ρ (-(n : ℤ)) = (ρ 1 + ρ (-1)) * τ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hρ0, hτ0]
    have e1 := hP.proportional hτ n hn
    have e2 := hM.proportional hτ n hn
    rw [hτ1] at e1 e2
    simp only [Nat.cast_one, mul_one] at e1 e2
    rw [e1, e2]; ring
  simp_rw [hsplit] at hNat
  -- absolute convergence of the normalized series
  have habN : Summable fun n : ℕ => ‖σ₀ n‖ * (n : ℝ) ^ (-s.re) := by
    have hpos := hab.comp_injective (Nat.cast_injective (R := ℤ))
    have hneg := hab.comp_injective (show Function.Injective (fun n : ℕ => -(n : ℤ)) from
      fun a b h => by simpa using h)
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]
      exact hpos.congr fun n => by simp
    · simp only [σ₀, if_neg h]
      exact hneg.congr fun n => by simp
  have hsumN : Summable fun n : ℕ => ‖τ n * (n : ℂ) ^ (-s)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (habN.mul_left ‖σ₀ 1‖⁻¹)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [hτ0, zero_mul, norm_zero]
      exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (by positivity))
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_mul, show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast, norm_cpow_eq_rpow_re_of_pos hn0, neg_re]
    simp only [τ, zero_mul, add_zero, norm_mul, norm_inv]
    exact le_of_eq (by ring)
  have hE := hτ.euler hτ1 hτ0 hsumN
  rw [hE, ← tsum_mul_left]
  have e := hNat.tsum_eq.symm
  simp only [mul_assoc] at e
  exact e

/-- **The Euler product of a Hecke–Maass L-function** for `Re s > 3/2`. -/
theorem cusp_euler_product (hg : g ∈ cuspSpace lamE) (c : ℕ → ℂ)
    (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 3 / 2 < s.re) :
    lSeries ρ s = (ρ 1 + ρ (-1)) *
      ∏' p : Nat.Primes, (1 - heckeLam c p * (p : ℂ) ^ (-s) + ((p : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_coeff_bound hg hρ0 hρ
  have hσ1 : 1 < s.re - 1 / 2 := by linarith
  refine cusp_euler_product_of_summable hg c hc hρ0 hρ (Summable.of_nonneg_of_le
    (fun n => by positivity) (fun n => ?_) ((Real.summable_abs_int_rpow hσ1).mul_left C))
  by_cases hn : n = 0
  · rw [hn, hρ0, norm_zero, zero_mul]; positivity
  have hn0 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
  calc ‖ρ n‖ * |(n : ℝ)| ^ (-s.re) ≤ (C * Real.sqrt |(n : ℝ)|) * |(n : ℝ)| ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (hC n) (by positivity)
    _ = C * |(n : ℝ)| ^ (-(s.re - 1 / 2)) := by
        rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hn0]; congr 2; ring

/-- **Multiplicativity of the coefficients**: `ρ(1) ρ(mn) = ρ(m) ρ(n)` for coprime `m, n ≥ 1`, and
`ρ(p^{k+2}) = λ_p ρ(p^{k+1}) - ρ(p^k)` at every prime. -/
theorem rho_mul (hg : g ∈ cuspSpace lamE) (c : ℕ → ℂ)
    (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    (∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → ρ 1 * ρ ((m * n : ℕ) : ℤ) = ρ m * ρ n) ∧
      ∀ p : ℕ, p.Prime → ∀ k : ℕ,
        ρ ((p ^ (k + 2) : ℕ) : ℤ) = heckeLam c p * ρ ((p ^ (k + 1) : ℕ) : ℤ) - ρ ((p ^ k : ℕ) : ℤ) := by
  have hP := heckeRec_rho hg hρ c hc 1 (Or.inl rfl)
  simp only [one_mul] at hP
  refine ⟨fun m n hm hn hmn => ?_, fun p hp k => hP.pow_succ_succ hp k⟩
  by_cases h1 : ρ 1 = 0
  · have hz := hP.eq_zero (by simpa using h1)
    rw [h1, zero_mul, hz m hm, zero_mul]
  set τ : ℕ → ℂ := fun k => (ρ 1)⁻¹ * ρ k + 0 * ρ k
  have hτ : HeckeRec (heckeLam c) τ := hP.lin hP _ _
  have hτ1 : τ 1 = 1 := by simp only [τ, Nat.cast_one]; field_simp; ring
  have h := hτ.mul hτ1 n m hm hn hmn
  simp only [τ, zero_mul, add_zero] at h
  field_simp at h
  linear_combination h

end CuspEuler

end GaloisForLFunctions.BlackHoleRingdown
