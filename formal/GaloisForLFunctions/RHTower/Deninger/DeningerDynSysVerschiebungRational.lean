import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Verschiebung and rationality of Witt vectors

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Theorem 1.8 (`t29`):

`V_N (W (A)) ∩ W_rat (A) = V_N (W_rat (A))`.

Here `W (A) = 1 + t A[[t]]` is the big Witt ring, `W_rat (A)` its subring of normalized rational
functions `P / Q`, and `V_N` is the Verschiebung, which on power series is the substitution
`t ↦ t ^ N`.

The source proves this for Fatou domains, by passing to the fraction field and using the finiteness
of the continued-fraction expansion of a rational Laurent series.  The proof given here is a direct
*sectioning identity*: if `Q (t) · F (t ^ N) = P (t)` with `Q (0) = 1`, then reading off the
coefficients in degrees divisible by `N` yields `Q₀ (u) · F (u) = P₀ (u)`, where `Q₀` and `P₀`
collect the coefficients of `Q` and `P` in degrees divisible by `N` and again `Q₀ (0) = Q (0) = 1`.
This works over an arbitrary commutative ring, so the Fatou hypothesis of the source is not needed.
-/

namespace RHTower

open Finset

variable {A : Type*} [CommRing A]

/-- Reindexing an antidiagonal sum along the `N`-fold dilation, valid whenever the summand
vanishes on pairs whose second entry is not divisible by `N`. -/
theorem deningerAntidiagonalDilation {M : Type*} [AddCommMonoid M] {N : ℕ} (hN : N ≠ 0) (n : ℕ)
    (h : ℕ × ℕ → M) (h0 : ∀ p ∈ Finset.antidiagonal (N * n), ¬ N ∣ p.2 → h p = 0) :
    ∑ p ∈ Finset.antidiagonal (N * n), h p
      = ∑ p ∈ Finset.antidiagonal n, h (N * p.1, N * p.2) := by
  classical
  set e : ℕ × ℕ → ℕ × ℕ := fun p => (N * p.1, N * p.2) with he
  have hsub : (Finset.antidiagonal n).image e ⊆ Finset.antidiagonal (N * n) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_antidiagonal] at hp ⊢
    simp only [he, ← Nat.mul_add, hp]
  have hzero : ∀ q ∈ Finset.antidiagonal (N * n),
      q ∉ (Finset.antidiagonal n).image e → h q = 0 := by
    intro q hq hqS
    refine h0 q hq ?_
    intro hdvd
    obtain ⟨j, hj⟩ := hdvd
    rw [Finset.mem_antidiagonal] at hq
    have hq2 : q.2 ≤ N * n := hq ▸ Nat.le_add_left q.2 q.1
    have hjn : j ≤ n := by
      by_contra hc
      rw [not_le] at hc
      have h2 : N * j ≤ N * n := by rw [← hj]; exact hq2
      have h3 : N * n + N ≤ N * n + 0 := by
        rw [Nat.add_zero]
        calc N * n + N = N * (n + 1) := by ring
          _ ≤ N * j := Nat.mul_le_mul le_rfl hc
          _ ≤ N * n := h2
      exact hN (Nat.le_zero.mp (Nat.le_of_add_le_add_left h3))
    have h1 : q.1 = N * (n - j) := by
      have : q.1 + N * j = N * n := by rw [← hj]; exact hq
      have hnj : N * (n - j) + N * j = N * n := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hjn]
      omega
    refine hqS (Finset.mem_image.mpr ⟨(n - j, j), ?_, ?_⟩)
    · rw [Finset.mem_antidiagonal]; omega
    · simp only [he, ← h1, ← hj]
  have hinj : ∀ p ∈ Finset.antidiagonal n, ∀ q ∈ Finset.antidiagonal n, e p = e q → p = q := by
    intro p _ q _ hpq
    have h1 : N * p.1 = N * q.1 := congrArg Prod.fst hpq
    have h2 : N * p.2 = N * q.2 := congrArg Prod.snd hpq
    have hN0 : 0 < N := Nat.pos_of_ne_zero hN
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hN0 h1) (Nat.eq_of_mul_eq_mul_left hN0 h2)
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image hinj]

/-- The `N`-th Verschiebung on power series: the substitution `t ↦ t ^ N`. -/
noncomputable def deningerVerschiebungSeries (N : ℕ) (F : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun m => if N ∣ m then PowerSeries.coeff (m / N) F else 0

@[simp] theorem deningerVerschiebungSeries_coeff_mul (N : ℕ) (hN : N ≠ 0) (F : PowerSeries A)
    (n : ℕ) : PowerSeries.coeff (N * n) (deningerVerschiebungSeries N F)
      = PowerSeries.coeff n F := by
  simp [deningerVerschiebungSeries, Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hN)]

theorem deningerVerschiebungSeries_coeff_of_not_dvd (N : ℕ) (F : PowerSeries A) {m : ℕ}
    (hm : ¬ N ∣ m) : PowerSeries.coeff m (deningerVerschiebungSeries N F) = 0 := by
  simp [deningerVerschiebungSeries, hm]

theorem deningerVerschiebungSeries_one (N : ℕ) (hN : N ≠ 0) :
    deningerVerschiebungSeries N (1 : PowerSeries A) = 1 := by
  ext m
  by_cases hm : N ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [deningerVerschiebungSeries_coeff_mul N hN]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hne : N * k ≠ 0 := Nat.mul_ne_zero hN hk.ne'
      simp [PowerSeries.coeff_one, hk.ne', hne]
  · rw [deningerVerschiebungSeries_coeff_of_not_dvd N _ hm, PowerSeries.coeff_one]
    have : m ≠ 0 := by rintro rfl; exact hm ⟨0, by simp⟩
    simp [this]

theorem deningerVerschiebungSeries_mul (N : ℕ) (hN : N ≠ 0) (F G : PowerSeries A) :
    deningerVerschiebungSeries N (F * G)
      = deningerVerschiebungSeries N F * deningerVerschiebungSeries N G := by
  ext m
  by_cases hm : N ∣ m
  · obtain ⟨n, rfl⟩ := hm
    rw [deningerVerschiebungSeries_coeff_mul N hN, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    rw [deningerAntidiagonalDilation hN n
      (fun p => PowerSeries.coeff p.1 (deningerVerschiebungSeries N F) *
        PowerSeries.coeff p.2 (deningerVerschiebungSeries N G))
      (by
        intro p _ hp
        rw [deningerVerschiebungSeries_coeff_of_not_dvd N _ hp, mul_zero])]
    exact Finset.sum_congr rfl fun p _ => by
      rw [deningerVerschiebungSeries_coeff_mul N hN, deningerVerschiebungSeries_coeff_mul N hN]
  · rw [deningerVerschiebungSeries_coeff_of_not_dvd N _ hm, PowerSeries.coeff_mul]
    refine (Finset.sum_eq_zero fun p hp => ?_).symm
    rw [Finset.mem_antidiagonal] at hp
    by_cases h1 : N ∣ p.1
    · have h2 : ¬ N ∣ p.2 := by
        intro h2
        exact hm (hp ▸ Dvd.dvd.add h1 h2)
      rw [deningerVerschiebungSeries_coeff_of_not_dvd N _ h2, mul_zero]
    · rw [deningerVerschiebungSeries_coeff_of_not_dvd N _ h1, zero_mul]

/-- The `N`-section of a polynomial: the coefficients in degrees divisible by `N`. -/
noncomputable def deningerPolynomialSection (N : ℕ) (P : Polynomial A) : Polynomial A :=
  ∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.monomial i (P.coeff (N * i))

@[simp] theorem deningerPolynomialSection_coeff {N : ℕ} (hN : N ≠ 0) (P : Polynomial A) (n : ℕ) :
    (deningerPolynomialSection N P).coeff n = P.coeff (N * n) := by
  classical
  rw [deningerPolynomialSection, Polynomial.finsetSum_coeff]
  by_cases hn : n ≤ P.natDegree
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hbn
      simp [Polynomial.coeff_monomial, hbn]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) hcon
  · rw [not_le] at hn
    have hzero : P.coeff (N * n) = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      calc P.natDegree < n := hn
        _ = 1 * n := (one_mul n).symm
        _ ≤ N * n := Nat.mul_le_mul_right n (Nat.one_le_iff_ne_zero.mpr hN)
    rw [hzero]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hbn : b ≠ n := by
      intro h
      rw [h] at hb
      exact absurd (Finset.mem_range.mp hb) (by omega)
    simp [Polynomial.coeff_monomial, hbn]

theorem deningerPolynomialSection_coeff_zero {N : ℕ} (hN : N ≠ 0) (P : Polynomial A) :
    (deningerPolynomialSection N P).coeff 0 = P.coeff 0 := by
  simp [deningerPolynomialSection_coeff hN]

/-- **Sectioning identity.**  Multiplying by a polynomial and reading off the coefficients in
degrees divisible by `N` is the same as multiplying by its `N`-section. -/
theorem deningerSection_mul_verschiebung {N : ℕ} (hN : N ≠ 0) (Q : Polynomial A)
    (F : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff (N * n) ((Q : PowerSeries A) * deningerVerschiebungSeries N F)
      = PowerSeries.coeff n ((deningerPolynomialSection N Q : PowerSeries A) * F) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [deningerAntidiagonalDilation hN n
    (fun p => PowerSeries.coeff p.1 (Q : PowerSeries A) *
      PowerSeries.coeff p.2 (deningerVerschiebungSeries N F))
    (by
      intro p _ hp
      rw [deningerVerschiebungSeries_coeff_of_not_dvd N _ hp, mul_zero])]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [deningerVerschiebungSeries_coeff_mul N hN]
  simp [Polynomial.coeff_coe, deningerPolynomialSection_coeff hN]

/-- A power series is *rational* when it is a quotient `P / Q` of polynomials both of which have
constant coefficient one, i.e. when it lies in `W_rat` of the coefficient ring. -/
def DeningerIsRationalSeries (F : PowerSeries A) : Prop :=
  ∃ P Q : Polynomial A, P.coeff 0 = 1 ∧ Q.coeff 0 = 1 ∧ (Q : PowerSeries A) * F = (P : PowerSeries A)

/-- **Deninger, Theorem 1.8 (`t29`), hard inclusion**, in the strengthened form valid over every
commutative ring: if the `N`-th Verschiebung of a power series is rational, the series itself is
rational.  The source assumes a Fatou domain; the sectioning identity removes that hypothesis. -/
theorem deningerIsRationalSeries_of_verschiebung {N : ℕ} (hN : N ≠ 0) (F : PowerSeries A)
    (h : DeningerIsRationalSeries (deningerVerschiebungSeries N F)) :
    DeningerIsRationalSeries F := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := h
  refine ⟨deningerPolynomialSection N P, deningerPolynomialSection N Q, ?_, ?_, ?_⟩
  · rw [deningerPolynomialSection_coeff_zero hN, hP]
  · rw [deningerPolynomialSection_coeff_zero hN, hQ]
  · ext n
    rw [← deningerSection_mul_verschiebung hN, hPQ]
    simp [Polynomial.coeff_coe, deningerPolynomialSection_coeff hN]

/-- The `N`-th dilation of a polynomial: `P (t) ↦ P (t ^ N)`. -/
noncomputable def deningerDilatePolynomial (N : ℕ) (P : Polynomial A) : Polynomial A :=
  ∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.monomial (N * i) (P.coeff i)

theorem deningerDilatePolynomial_coeff {N : ℕ} (hN : N ≠ 0) (P : Polynomial A) (m : ℕ) :
    (deningerDilatePolynomial N P).coeff m = if N ∣ m then P.coeff (m / N) else 0 := by
  classical
  rw [deningerDilatePolynomial, Polynomial.finsetSum_coeff]
  by_cases hm : N ∣ m
  · obtain ⟨k, rfl⟩ := hm
    have hdiv : N * k / N = k := Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hN)
    rw [if_pos ⟨k, rfl⟩, hdiv]
    by_cases hk : k ≤ P.natDegree
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hbk
        have : N * b ≠ N * k := fun h => hbk (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h)
        simp [Polynomial.coeff_monomial, this]
      · intro hcon
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hcon
    · rw [not_le] at hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk]
      refine Finset.sum_eq_zero fun b hb => ?_
      have hbk : b ≠ k := by
        intro h; rw [h] at hb; exact absurd (Finset.mem_range.mp hb) (by omega)
      have : N * b ≠ N * k := fun h => hbk (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h)
      simp [Polynomial.coeff_monomial, this]
  · rw [if_neg hm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : N * b ≠ m := fun h => hm ⟨b, h.symm⟩
    simp [Polynomial.coeff_monomial, this]

@[simp] theorem deningerDilatePolynomial_coeff_zero {N : ℕ} (hN : N ≠ 0) (P : Polynomial A) :
    (deningerDilatePolynomial N P).coeff 0 = P.coeff 0 := by
  simp [deningerDilatePolynomial_coeff hN]

theorem deningerDilatePolynomial_coe {N : ℕ} (hN : N ≠ 0) (P : Polynomial A) :
    ((deningerDilatePolynomial N P : Polynomial A) : PowerSeries A)
      = deningerVerschiebungSeries N (P : PowerSeries A) := by
  ext m
  rw [Polynomial.coeff_coe, deningerDilatePolynomial_coeff hN]
  by_cases hm : N ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [if_pos ⟨k, rfl⟩, deningerVerschiebungSeries_coeff_mul N hN, Polynomial.coeff_coe,
      Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hN)]
  · rw [if_neg hm, deningerVerschiebungSeries_coeff_of_not_dvd N _ hm]

/-- **Deninger, Theorem 1.8 (`t29`), easy inclusion:** the Verschiebung of a rational series is
rational. -/
theorem deningerIsRationalSeries_verschiebung {N : ℕ} (hN : N ≠ 0) (F : PowerSeries A)
    (h : DeningerIsRationalSeries F) :
    DeningerIsRationalSeries (deningerVerschiebungSeries N F) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := h
  refine ⟨deningerDilatePolynomial N P, deningerDilatePolynomial N Q, ?_, ?_, ?_⟩
  · rw [deningerDilatePolynomial_coeff_zero hN, hP]
  · rw [deningerDilatePolynomial_coeff_zero hN, hQ]
  · rw [deningerDilatePolynomial_coe hN, deningerDilatePolynomial_coe hN,
      ← deningerVerschiebungSeries_mul N hN, hPQ]

/-- **Deninger, Theorem 1.8 (`t29`).**  For every commutative ring `A` and every `N ≥ 1`,
`V_N (W (A)) ∩ W_rat (A) = V_N (W_rat (A))`: a Verschiebung is rational exactly when the series it
comes from is. -/
theorem deningerIsRationalSeries_verschiebung_iff {N : ℕ} (hN : N ≠ 0) (F : PowerSeries A) :
    DeningerIsRationalSeries (deningerVerschiebungSeries N F) ↔ DeningerIsRationalSeries F :=
  ⟨deningerIsRationalSeries_of_verschiebung hN F, deningerIsRationalSeries_verschiebung hN F⟩

/-- Set form of Deninger's Theorem 1.8. -/
theorem deningerVerschiebung_inter_rational (N : ℕ) (hN : N ≠ 0) :
    (Set.range (deningerVerschiebungSeries (A := A) N)) ∩ {F | DeningerIsRationalSeries F}
      = deningerVerschiebungSeries (A := A) N '' {F | DeningerIsRationalSeries F} := by
  ext F
  constructor
  · rintro ⟨⟨G, rfl⟩, hrat⟩
    exact ⟨G, (deningerIsRationalSeries_verschiebung_iff hN G).mp hrat, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    exact ⟨⟨G, rfl⟩, deningerIsRationalSeries_verschiebung hN G hG⟩

end RHTower
