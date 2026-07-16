import GaloisForLFunctions.HTGeometry.OrbitFreeness
import GaloisForLFunctions.RHTower.ExpNatIrrational
import GaloisForLFunctions.RHTower.StieltjesWeld

/-!
# Stieltjes–log weld, Tier 1: the weight-one datum admits no rational isolation

For a friable auxiliary `F(s) = Σ_{n∈A} λ_n n^{-s}` the weight-one Taylor datum
at `s = 1` is `c₁ = -Σ_{n∈A} λ_n (log n)/n`, a rational combination
`Σ_p β_p·log p` of prime logarithms with explicit lane coordinates
`β_p = -Σ_n λ_n v_p(n)/n`.  Everything here is unconditional.

* `logPrime_int_affine_relation_eq_zero`, `logPrime_rat_affine_relation_eq_zero`
  — the affine line `ℚ + Σ_p ℚ·log p` meets `ℚ` only trivially: a relation
  `Σ_p β_p·log p = q` with rational data forces `q = 0` and every `β_p = 0`.
  Mechanism: exponentiating an integer relation gives `e^a ∈ ℚ`, contradicting
  the irrationality of `e^a` (`exp_int_irrational`); the coefficients then die
  by the `ℚ`-linear independence of the prime logarithms.
* `friableC1_eq_sum_beta_log` — `c₁` lies in the rational span of the prime
  logarithms, with the lane coordinates `β_p`.
* `friableC1_rat_iff_zero`, `friableC1_eq_zero_iff`,
  `friableC1_irrational_of_ne_zero` — the weight-one datum is rational only
  when it vanishes; a nonzero `c₁` is irrational.
* `tier1_no_isolation` — if the Cauchy-pairing coefficient `[H]_N` (`N ≥ 2`)
  is, uniformly in the Stieltjes coordinates, a rational affine form in
  `γ_0, …, γ_{N-1}`, then `c₁ = 0` and every lane coordinate vanishes.  A
  nontrivial weight-one auxiliary therefore welds the Stieltjes block to the
  prime-log block: no rational functional isolates one from the other.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **Integer-affine independence of prime logarithms.**  An integer relation
`Σ_{p∈s} n_p·log p = a` forces `a = 0` and all `n_p = 0`.  The constant dies by
irrationality of `e^a`; the coefficients die by `ℚ`-linear independence. -/
theorem logPrime_int_affine_relation_eq_zero (s : Finset Nat.Primes)
    (n : Nat.Primes → ℤ) (a : ℤ)
    (h : ∑ p ∈ s, (n p : ℝ) * Real.log ((p : ℕ) : ℝ) = (a : ℝ)) :
    a = 0 ∧ ∀ p ∈ s, n p = 0 := by
  have hppos : ∀ p : Nat.Primes, (0 : ℝ) < ((p : ℕ) : ℝ) := fun p => by
    exact_mod_cast p.2.pos
  have ha : a = 0 := by
    by_contra ha0
    refine RHTower.exp_int_irrational ha0 ⟨∏ p ∈ s, ((p : ℕ) : ℚ) ^ (n p), ?_⟩
    have hprod : ((∏ p ∈ s, ((p : ℕ) : ℚ) ^ (n p) : ℚ) : ℝ)
        = ∏ p ∈ s, ((p : ℕ) : ℝ) ^ (n p) := by
      push_cast
      rfl
    rw [hprod, ← h, Real.exp_sum]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [← Real.log_zpow, Real.exp_log (zpow_pos (hppos p) _)]
  refine ⟨ha, ?_⟩
  subst ha
  rw [Int.cast_zero] at h
  have h0 : ∑ p ∈ s, (n p : ℚ) • Real.log ((p : ℕ) : ℝ) = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Rat.smul_def]
    norm_num
  intro p hp
  exact_mod_cast logPrime_no_rat_relation s (fun q => (n q : ℚ)) h0 p hp

/-- **Rational-affine independence of prime logarithms.**  A rational relation
`Σ_{p∈s} β_p·log p = q` forces `q = 0` and all `β_p = 0`. -/
theorem logPrime_rat_affine_relation_eq_zero (s : Finset Nat.Primes)
    (β : Nat.Primes → ℚ) (q : ℚ)
    (h : ∑ p ∈ s, (β p : ℝ) * Real.log ((p : ℕ) : ℝ) = (q : ℝ)) :
    q = 0 ∧ ∀ p ∈ s, β p = 0 := by
  classical
  set N : ℕ := q.den * ∏ p ∈ s, (β p).den with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    exact mul_pos q.pos (Finset.prod_pos fun p _ => (β p).pos)
  have hmul : ∀ x : ℚ, x.den ∣ N → ∃ z : ℤ, x * (N : ℚ) = (z : ℚ) := by
    rintro x ⟨k, hk⟩
    refine ⟨x.num * k, ?_⟩
    have hden0 : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.pos.ne'
    have hx : (x.num : ℚ) = x * (x.den : ℚ) := (div_eq_iff hden0).mp (Rat.num_div_den x)
    rw [hk]
    push_cast
    rw [hx]
    ring
  have hdvd : ∀ p ∈ s, (β p).den ∣ N := by
    intro p hp
    rw [hNdef]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hp) q.den
  have hqdvd : q.den ∣ N := by
    rw [hNdef]
    exact dvd_mul_right _ _
  have hcast : ∀ p ∈ s, (((β p * (N : ℚ)).num : ℤ) : ℚ) = β p * (N : ℚ) := by
    intro p hp
    obtain ⟨z, hz⟩ := hmul (β p) (hdvd p hp)
    rw [hz, Rat.num_intCast]
  have hacast : (((q * (N : ℚ)).num : ℤ) : ℚ) = q * (N : ℚ) := by
    obtain ⟨z, hz⟩ := hmul q hqdvd
    rw [hz, Rat.num_intCast]
  have hrel0 : ∑ p ∈ s, ((β p * (N : ℚ) : ℚ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      = ((q * (N : ℚ) : ℚ) : ℝ) := by
    push_cast
    calc ∑ p ∈ s, (β p : ℝ) * (N : ℝ) * Real.log ((p : ℕ) : ℝ)
        = (∑ p ∈ s, (β p : ℝ) * Real.log ((p : ℕ) : ℝ)) * (N : ℝ) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ = (q : ℝ) * (N : ℝ) := by rw [h]
  have hrel : ∑ p ∈ s, (((β p * (N : ℚ)).num : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      = ((((q * (N : ℚ)).num : ℤ)) : ℝ) := by
    have e1 : ∀ p ∈ s, ((((β p * (N : ℚ)).num : ℤ)) : ℝ) = ((β p * (N : ℚ) : ℚ) : ℝ) := by
      intro p hp
      exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) (hcast p hp)
    have e2 : ((((q * (N : ℚ)).num : ℤ)) : ℝ) = ((q * (N : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) hacast
    rw [e2, ← hrel0]
    exact Finset.sum_congr rfl fun p hp => by rw [e1 p hp]
  obtain ⟨haz, hbz⟩ := logPrime_int_affine_relation_eq_zero s _ _ hrel
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hNpos.ne'
  constructor
  · have hq0 : q * (N : ℚ) = 0 := by rw [← hacast, haz]; norm_num
    exact (mul_eq_zero.mp hq0).resolve_right hN0
  · intro p hp
    have hb0 : β p * (N : ℚ) = 0 := by rw [← hcast p hp, hbz p hp]; norm_num
    exact (mul_eq_zero.mp hb0).resolve_right hN0

/-- Prime-log expansion of `log n` over any finite set of primes covering the
support of the factorization of `n`. -/
theorem log_natCast_eq_sum_factorization (n : ℕ) (hn : n ≠ 0)
    (S : Finset Nat.Primes)
    (hS : ∀ p : Nat.Primes, n.factorization (p : ℕ) ≠ 0 → p ∈ S) :
    Real.log (n : ℝ)
      = ∑ p ∈ S, (n.factorization (p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
  have hsupp : n.factorization.support ⊆ S.image Subtype.val := by
    intro p' hp'
    have hprime : p'.Prime :=
      Nat.prime_of_mem_primeFactors (by rwa [← Nat.support_factorization])
    have hne : n.factorization p' ≠ 0 := Finsupp.mem_support_iff.mp hp'
    exact Finset.mem_image.mpr ⟨⟨p', hprime⟩, hS _ hne, rfl⟩
  have hprodeq : (n : ℕ) = ∏ p' ∈ S.image Subtype.val,
      p' ^ n.factorization p' := by
    rw [← Finsupp.prod_of_support_subset _ hsupp _ (fun p _ => pow_zero p)]
    exact (Nat.prod_factorization_pow_eq_self hn).symm
  have hcast : ((n : ℕ) : ℝ) = ∏ p' ∈ S.image Subtype.val,
      ((p' : ℝ)) ^ n.factorization p' := by
    conv_lhs => rw [hprodeq]
    push_cast
    rfl
  rw [hcast, Real.log_prod]
  · rw [Finset.sum_image (fun a _ b _ hab => Subtype.ext hab)]
    exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]
  · intro p' hp'
    obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hp'
    exact pow_ne_zero _ (by exact_mod_cast P.2.pos.ne')

/-- The weight-one Taylor datum of the friable auxiliary `Σ_{n∈A} λ_n n^{-s}`
at `s = 1`: `c₁ = -Σ_{n∈A} λ_n (log n)/n`. -/
def friableC1 (A : Finset ℕ) (lam : ℕ → ℚ) : ℝ :=
  -∑ n ∈ A, (lam n : ℝ) * Real.log (n : ℝ) / (n : ℝ)

/-- The prime-lane coordinate of the weight-one datum: `β_p = -Σ_{n∈A} λ_n v_p(n)/n`. -/
def friableBeta (A : Finset ℕ) (lam : ℕ → ℚ) (p : Nat.Primes) : ℚ :=
  -∑ n ∈ A, lam n * (n.factorization (p : ℕ) : ℚ) / (n : ℚ)

/-- The primes seen by the auxiliary's support. -/
def friablePrimes (A : Finset ℕ) : Finset Nat.Primes :=
  (A.biUnion Nat.primeFactors).attach.image
    (fun x => ⟨x.1, by
      obtain ⟨a, _, hx⟩ := Finset.mem_biUnion.mp x.2
      exact Nat.prime_of_mem_primeFactors hx⟩)

theorem mem_friablePrimes {A : Finset ℕ} {p : Nat.Primes} {n : ℕ} (hn : n ∈ A)
    (hv : n.factorization (p : ℕ) ≠ 0) : p ∈ friablePrimes A := by
  have hmem : (p : ℕ) ∈ A.biUnion Nat.primeFactors := by
    refine Finset.mem_biUnion.mpr ⟨n, hn, ?_⟩
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr hv
  exact Finset.mem_image.mpr ⟨⟨(p : ℕ), hmem⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

theorem friableBeta_eq_zero_of_not_mem {A : Finset ℕ} {lam : ℕ → ℚ} {p : Nat.Primes}
    (hp : p ∉ friablePrimes A) : friableBeta A lam p = 0 := by
  unfold friableBeta
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun n hn => ?_
  have hv : n.factorization (p : ℕ) = 0 := by
    by_contra hv0
    exact hp (mem_friablePrimes hn hv0)
  rw [hv]
  norm_num

/-- **`c₁` lies in the rational span of the prime logarithms**, with the
explicit lane coordinates `β_p`, over any covering prime set. -/
theorem friableC1_eq_sum_beta_log (A : Finset ℕ) (lam : ℕ → ℚ) (h0 : ∀ n ∈ A, n ≠ 0)
    (S : Finset Nat.Primes)
    (hS : ∀ n ∈ A, ∀ p : Nat.Primes, n.factorization (p : ℕ) ≠ 0 → p ∈ S) :
    friableC1 A lam = ∑ p ∈ S, (friableBeta A lam p : ℝ) * Real.log ((p : ℕ) : ℝ) := by
  have key : ∀ n ∈ A, Real.log (n : ℝ)
      = ∑ p ∈ S, (n.factorization (p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) :=
    fun n hn => log_natCast_eq_sum_factorization n (h0 n hn) S (hS n hn)
  unfold friableC1
  calc -∑ n ∈ A, (lam n : ℝ) * Real.log (n : ℝ) / (n : ℝ)
      = -∑ n ∈ A, ∑ p ∈ S,
          (lam n : ℝ) * ((n.factorization (p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)) / (n : ℝ) := by
        congr 1
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [key n hn, Finset.mul_sum, Finset.sum_div]
    _ = -∑ p ∈ S, ∑ n ∈ A,
          (lam n : ℝ) * ((n.factorization (p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)) / (n : ℝ) := by
        rw [Finset.sum_comm]
    _ = ∑ p ∈ S, -(∑ n ∈ A,
          (lam n : ℝ) * ((n.factorization (p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)) / (n : ℝ)) := by
        rw [← Finset.sum_neg_distrib]
    _ = ∑ p ∈ S, (friableBeta A lam p : ℝ) * Real.log ((p : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        unfold friableBeta
        push_cast
        rw [neg_mul, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun n _ => by ring

/-- **Tier-1 rationality dichotomy**: the weight-one datum is rational iff every
prime-lane coordinate vanishes. -/
theorem friableC1_rat_iff_zero (A : Finset ℕ) (lam : ℕ → ℚ) (h0 : ∀ n ∈ A, n ≠ 0) :
    (∃ r : ℚ, friableC1 A lam = (r : ℝ)) ↔ ∀ p : Nat.Primes, friableBeta A lam p = 0 := by
  have hexp := friableC1_eq_sum_beta_log A lam h0 (friablePrimes A)
    (fun n hn p hv => mem_friablePrimes hn hv)
  constructor
  · rintro ⟨r, hr⟩
    rw [hexp] at hr
    obtain ⟨-, hβ⟩ := logPrime_rat_affine_relation_eq_zero _ _ _ hr
    intro p
    by_cases hp : p ∈ friablePrimes A
    · exact hβ p hp
    · exact friableBeta_eq_zero_of_not_mem hp
  · intro hβ
    refine ⟨0, ?_⟩
    rw [hexp, Rat.cast_zero]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [hβ p]
    norm_num

/-- The weight-one datum vanishes iff every prime-lane coordinate vanishes. -/
theorem friableC1_eq_zero_iff (A : Finset ℕ) (lam : ℕ → ℚ) (h0 : ∀ n ∈ A, n ≠ 0) :
    friableC1 A lam = 0 ↔ ∀ p : Nat.Primes, friableBeta A lam p = 0 := by
  have hexp := friableC1_eq_sum_beta_log A lam h0 (friablePrimes A)
    (fun n hn p hv => mem_friablePrimes hn hv)
  constructor
  · intro hz
    exact (friableC1_rat_iff_zero A lam h0).mp ⟨0, by rw [hz]; norm_num⟩
  · intro hβ
    rw [hexp]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [hβ p]
    norm_num

/-- A nonzero weight-one datum is irrational: the Tier-1 transcendence floor. -/
theorem friableC1_irrational_of_ne_zero (A : Finset ℕ) (lam : ℕ → ℚ)
    (h0 : ∀ n ∈ A, n ≠ 0) (hne : friableC1 A lam ≠ 0) :
    Irrational (friableC1 A lam) := by
  rintro ⟨r, hr⟩
  have hβ := (friableC1_rat_iff_zero A lam h0).mp ⟨r, hr.symm⟩
  exact hne ((friableC1_eq_zero_iff A lam h0).mpr hβ)

/-- **Tier-1 no-isolation (the Stieltjes–log weld).**  Fix `N ≥ 2` and let the
auxiliary Taylor data have weight-one entry `c 1 = c₁`.  If the Cauchy-pairing
coefficient `[H]_N` is, uniformly in the Stieltjes coordinates `γ`, a rational
affine form in `γ_0, …, γ_{N-1}`, then the weight-one datum vanishes.  A
nontrivial weight-one friable auxiliary admits no rational isolation of the
Stieltjes block from the prime-log block. -/
theorem tier1_no_isolation (A : Finset ℕ) (lam : ℕ → ℚ) (h0 : ∀ n ∈ A, n ≠ 0)
    (c : ℕ → ℂ) (hc1 : c 1 = ((friableC1 A lam : ℝ) : ℂ))
    (N : ℕ) (hN : 2 ≤ N) (q0 : ℚ) (qc : ℕ → ℚ)
    (hrep : ∀ γ : ℕ → ℂ,
      (PowerSeries.coeff N)
        ((PowerSeries.mk (auxiliaryTaylorCoeff c)) * (PowerSeries.mk (stieltjesGCoeff γ)))
      = (q0 : ℂ) + ∑ k ∈ Finset.range N, (qc k : ℂ) * γ k) :
    friableC1 A lam = 0 := by
  classical
  set δ : ℕ → ℂ := fun k => if k = N - 2 then 1 else 0 with hδ
  have h1 := hrep (fun _ => 0)
  have h2 := hrep δ
  rw [stieltjes_pairing_cauchy_j] at h1 h2
  simp only [stieltjesA, mul_zero, zero_div,
    Finset.sum_const_zero, add_zero] at h1
  -- h1 : auxiliaryTaylorCoeff c N = q0
  have hsum : ∑ j ∈ Finset.range N, auxiliaryTaylorCoeff c j * stieltjesA δ (N - j - 1)
      = auxiliaryTaylorCoeff c 1 * ((-1 : ℂ) ^ (N - 2) / ((N - 2).factorial : ℂ)) := by
    rw [Finset.sum_eq_single 1]
    · congr 1
      simp only [stieltjesA, hδ]
      rw [if_pos (by omega : N - 1 - 1 = N - 2)]
      rw [show N - 1 - 1 = N - 2 by omega]
      ring
    · intro j hj hj1
      have hjN : j < N := Finset.mem_range.mp hj
      have hne : N - j - 1 ≠ N - 2 := by omega
      simp only [stieltjesA, hδ]
      rw [if_neg hne]
      ring
    · intro h1'
      exact absurd (Finset.mem_range.mpr (by omega : 1 < N)) h1'
  have hrhs : ∑ k ∈ Finset.range N, (qc k : ℂ) * δ k = (qc (N - 2) : ℂ) := by
    rw [Finset.sum_eq_single (N - 2)]
    · simp only [hδ]
      rw [if_true, mul_one]
    · intro k _ hkne
      simp only [hδ]
      rw [if_neg hkne, mul_zero]
    · intro habs
      exact absurd (Finset.mem_range.mpr (by omega : N - 2 < N)) habs
  rw [hsum, hrhs, h1] at h2
  have hkey : auxiliaryTaylorCoeff c 1 * ((-1 : ℂ) ^ (N - 2) / ((N - 2).factorial : ℂ))
      = (qc (N - 2) : ℂ) := by
    exact add_left_cancel h2
  have haux1 : auxiliaryTaylorCoeff c 1 = c 1 := by
    simp [auxiliaryTaylorCoeff]
  rw [haux1] at hkey
  have hfact : ((N - 2).factorial : ℂ) ≠ 0 := by
    exact_mod_cast (N - 2).factorial_ne_zero
  have hkey' : c 1 * (-1 : ℂ) ^ (N - 2) = (qc (N - 2) : ℂ) * ((N - 2).factorial : ℂ) := by
    rw [← mul_div_assoc, div_eq_iff hfact] at hkey
    exact hkey
  have hss : ((-1 : ℂ)) ^ (N - 2) * ((-1 : ℂ)) ^ (N - 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hc : c 1 = ((qc (N - 2) * ((-1 : ℚ)) ^ (N - 2) * ((N - 2).factorial : ℚ) : ℚ) : ℂ) := by
    have hexpand : c 1 = c 1 * ((-1 : ℂ)) ^ (N - 2) * ((-1 : ℂ)) ^ (N - 2) := by
      rw [mul_assoc, hss, mul_one]
    rw [hexpand, hkey']
    push_cast
    ring
  have hR : friableC1 A lam
      = ((qc (N - 2) * ((-1 : ℚ)) ^ (N - 2) * ((N - 2).factorial : ℚ) : ℚ) : ℝ) := by
    have hcc := hc1.symm.trans hc
    exact_mod_cast hcc
  exact (friableC1_eq_zero_iff A lam h0).mpr ((friableC1_rat_iff_zero A lam h0).mp ⟨_, hR⟩)

end

end GaloisForLFunctions
