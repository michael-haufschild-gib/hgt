import Mathlib.NumberTheory.SelbergSieve

/-!
# Möbius inversion for the Selberg sieve

Mathlib diagonalises the `Λ²` main term as

`mainSum (lambdaSquared w) = ∑_{l ∣ P} g_l⁻¹ · (∑_{d ∣ P, l ∣ d} ν_d w_d)²`,

so the natural variables are `y_l = ∑_{d ∣ P, l ∣ d} ν_d w_d`.  This file records the Möbius
inversion that translates the normalisation `w 1 = 1` — the hypothesis of
`upperMoebius_lambdaSquared` — into the linear constraint

`∑_{l ∣ P} μ(l) · y_l = 1`.

With the main term written as `∑ g_l⁻¹ y_l²` under that constraint, Cauchy–Schwarz gives the
Selberg bound `∑ g_l⁻¹ y_l² ≥ 1 / ∑ g_l`, with equality at `y_l = μ(l) g_l / ∑ g_l`; the
inequality direction proved here is the one needed to certify that no admissible weight can beat
`1/S`, and the equality case is what an explicit optimal weight must reproduce.
-/

namespace RHTower.Sieve

open Finset Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius

/-- The alternating divisor sum of the Möbius function. -/
theorem sum_divisors_moebius_real (d : ℕ) :
    ∑ l ∈ d.divisors, (μ l : ℝ) = if d = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f d) (coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [coe_mul_zeta_apply, one_apply] at h
  exact h

/-- The diagonalising variables of the Selberg sieve. -/
def selbergY (s : BoundingSieve) (w : ℕ → ℝ) (l : ℕ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * w d else 0

/-- The main term in the diagonalising variables. -/
theorem mainSum_lambdaSquared_eq_sum_selbergY (s : BoundingSieve) (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w)
      = ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ * (selbergY s w l) ^ (2 : ℕ) :=
  mainSum_lambdaSquared_eq_sum_mul_sum_sq w

/-- **Möbius inversion of the normalisation.**  The hypothesis `w 1 = 1` of
`upperMoebius_lambdaSquared` is exactly the linear constraint `∑ μ(l) y_l = 1`. -/
theorem sum_moebius_mul_selbergY (s : BoundingSieve) (w : ℕ → ℝ) :
    ∑ l ∈ s.prodPrimes.divisors, (μ l : ℝ) * selbergY s w l = w 1 := by
  classical
  have hP : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  have hexpand : ∀ l ∈ s.prodPrimes.divisors,
      (μ l : ℝ) * selbergY s w l
        = ∑ d ∈ s.prodPrimes.divisors, (if l ∣ d then (μ l : ℝ) * (s.nu d * w d) else 0) := by
    intro l _
    rw [selbergY, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro d _
    by_cases h : l ∣ d <;> simp [h]
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  have hinner : ∀ d ∈ s.prodPrimes.divisors,
      (∑ l ∈ s.prodPrimes.divisors, (if l ∣ d then (μ l : ℝ) * (s.nu d * w d) else 0))
        = (s.nu d * w d) * (if d = 1 then 1 else 0) := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : d ≠ 0 := Nat.pos_of_mem_divisors hd |>.ne'
    have hfilter : {l ∈ s.prodPrimes.divisors | l ∣ d} = d.divisors := by
      ext l
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨-, hld⟩
        exact ⟨hld, hd0⟩
      · rintro ⟨hld, -⟩
        exact ⟨⟨hld.trans hdvd, hP⟩, hld⟩
    rw [← Finset.sum_filter, hfilter, ← Finset.sum_mul, sum_divisors_moebius_real d]
    ring
  rw [Finset.sum_congr rfl hinner]
  have hsingle : ∑ d ∈ s.prodPrimes.divisors, (s.nu d * w d) * (if d = 1 then 1 else 0)
      = s.nu 1 * w 1 := by
    have hmem : (1 : ℕ) ∈ s.prodPrimes.divisors := Nat.mem_divisors.2 ⟨one_dvd _, hP⟩
    rw [Finset.sum_eq_single_of_mem 1 hmem (fun d _ hne => by simp [hne])]
    simp
  rw [hsingle, s.nu_mult.map_one, one_mul]

/-- **Selberg's Cauchy–Schwarz bound.**  No admissible weight makes the main term smaller than the
reciprocal of the total Selberg mass. -/
theorem inv_sum_selbergTerms_le_mainSum (s : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    (∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l)⁻¹ ≤ s.mainSum (lambdaSquared w) := by
  classical
  have hg : ∀ l ∈ s.prodPrimes.divisors, 0 < s.selbergTerms l := fun l hl =>
    selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
  have hcs := Finset.sq_sum_div_le_sum_sq_div s.prodPrimes.divisors
      (fun l => (μ l : ℝ) * selbergY s w l) hg
  rw [sum_moebius_mul_selbergY, hw] at hcs
  have hmu : ∑ l ∈ s.prodPrimes.divisors,
      ((μ l : ℝ) * selbergY s w l) ^ (2 : ℕ) / s.selbergTerms l
      = ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ * (selbergY s w l) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro l hl
    have hsq : Squarefree l :=
      s.prodPrimes_squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hl)
    have hmusq : (μ l : ℝ) ^ (2 : ℕ) = 1 := by
      have h : (μ l : ℤ) = (-1) ^ (ArithmeticFunction.cardFactors l) :=
        moebius_apply_of_squarefree hsq
      have hcast : (μ l : ℝ) = (-1 : ℝ) ^ (ArithmeticFunction.cardFactors l) := by
        exact_mod_cast h
      rw [hcast, ← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [mul_pow, hmusq, one_mul, div_eq_inv_mul]
  rw [mainSum_lambdaSquared_eq_sum_selbergY, ← hmu]
  simpa using hcs

/-- **Divisor-interval Möbius sum.**  The alternating sum over the divisors of `k` that are
multiples of `l` detects `k = l`. -/
theorem sum_divisors_interval_moebius {l k : ℕ} (hk : k ≠ 0) :
    (∑ d ∈ k.divisors, if l ∣ d then (μ (k / d) : ℝ) else 0)
      = if k = l then 1 else 0 := by
  classical
  by_cases hlk : l ∣ k
  · have hl0 : l ≠ 0 := by
      intro h
      exact hk (Nat.eq_zero_of_zero_dvd (h ▸ hlk))
    have hql : k / l ≠ 0 := by
      intro h
      rw [← Nat.mul_div_cancel' hlk, h, mul_zero] at hk
      exact hk rfl
    have hinv : (∑ d ∈ k.divisors, if l ∣ d then (μ (k / d) : ℝ) else 0)
        = ∑ d ∈ k.divisors, (if l ∣ k / d then (μ d : ℝ) else 0) := by
      rw [← Nat.sum_div_divisors k (fun d => if l ∣ k / d then (μ d : ℝ) else 0)]
      refine Finset.sum_congr rfl ?_
      intro d hd
      obtain ⟨hdk, -⟩ := Nat.mem_divisors.1 hd
      rw [Nat.div_div_self hdk hk]
    rw [hinv, ← Finset.sum_filter]
    have hset : {d ∈ k.divisors | l ∣ k / d} = (k / l).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdk, -⟩, hlkd⟩
        rw [Nat.dvd_div_iff_mul_dvd hdk] at hlkd
        exact ⟨(Nat.dvd_div_iff_mul_dvd hlk).2 (by rwa [mul_comm]), hql⟩
      · rintro ⟨hdq, -⟩
        rw [Nat.dvd_div_iff_mul_dvd hlk] at hdq
        have hdk : d ∣ k := dvd_trans (dvd_mul_left d l) hdq
        exact ⟨⟨hdk, hk⟩, (Nat.dvd_div_iff_mul_dvd hdk).2 (by rwa [mul_comm])⟩
    rw [hset, sum_divisors_moebius_real]
    congr 1
    rw [eq_iff_iff]
    constructor
    · intro h
      have hmul := Nat.mul_div_cancel' hlk
      rw [h, mul_one] at hmul
      exact hmul.symm
    · intro h
      subst h
      exact Nat.div_self (Nat.pos_of_ne_zero hl0)
  · have hne : k ≠ l := by
      intro h
      exact hlk (h ▸ dvd_refl k)
    rw [if_neg hne]
    refine Finset.sum_eq_zero ?_
    intro d hd
    obtain ⟨hdk, -⟩ := Nat.mem_divisors.1 hd
    by_cases hld : l ∣ d
    · exact absurd (hld.trans hdk) hlk
    · rw [if_neg hld]

/-- The Selberg weight reconstructed from a prescribed diagonal profile. -/
noncomputable def selbergW (s : BoundingSieve) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  (∑ l ∈ s.prodPrimes.divisors, if d ∣ l then (μ (l / d) : ℝ) * y l else 0) / s.nu d

/-- **Inversion.**  The reconstructed weight has the prescribed diagonal profile. -/
theorem selbergY_selbergW (s : BoundingSieve) (y : ℕ → ℝ) {l₀ : ℕ}
    (hl₀ : l₀ ∣ s.prodPrimes) :
    selbergY s (selbergW s y) l₀ = y l₀ := by
  classical
  have hP0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  have hstep : ∀ d ∈ s.prodPrimes.divisors,
      (if l₀ ∣ d then s.nu d * selbergW s y d else 0)
        = ∑ l ∈ s.prodPrimes.divisors,
            (if l₀ ∣ d then (if d ∣ l then (μ (l / d) : ℝ) * y l else 0) else 0) := by
    intro d hd
    have hnu : s.nu d ≠ 0 := nu_ne_zero (Nat.dvd_of_mem_divisors hd)
    by_cases h : l₀ ∣ d
    · rw [if_pos h, selbergW, mul_div_cancel₀ _ hnu]
      exact (Finset.sum_congr rfl fun l _ => by rw [if_pos h]).symm
    · rw [if_neg h]
      exact (Finset.sum_eq_zero fun l _ => by rw [if_neg h]).symm
  rw [selbergY, Finset.sum_congr rfl hstep, Finset.sum_comm]
  have hinner : ∀ l ∈ s.prodPrimes.divisors,
      (∑ d ∈ s.prodPrimes.divisors,
        (if l₀ ∣ d then (if d ∣ l then (μ (l / d) : ℝ) * y l else 0) else 0))
        = (if l = l₀ then (1 : ℝ) else 0) * y l := by
    intro l hl
    obtain ⟨hlP, -⟩ := Nat.mem_divisors.1 hl
    have hl0 : l ≠ 0 := Nat.pos_of_mem_divisors hl |>.ne'
    have hswap : ∀ d : ℕ,
        (if l₀ ∣ d then (if d ∣ l then (μ (l / d) : ℝ) * y l else 0) else 0)
          = (if d ∣ l then (if l₀ ∣ d then (μ (l / d) : ℝ) else 0) * y l else 0) := by
      intro d
      by_cases h1 : l₀ ∣ d <;> by_cases h2 : d ∣ l <;> simp [h1, h2]
    rw [Finset.sum_congr rfl (fun d _ => hswap d), ← Finset.sum_filter,
      Nat.divisors_filter_dvd_of_dvd hP0 hlP, ← Finset.sum_mul,
      sum_divisors_interval_moebius hl0]
  rw [Finset.sum_congr rfl hinner]
  have hmem : l₀ ∈ s.prodPrimes.divisors := Nat.mem_divisors.2 ⟨hl₀, hP0⟩
  rw [Finset.sum_eq_single_of_mem l₀ hmem (fun l _ hne => by simp [hne])]
  simp

/-- Möbius values on divisors of a squarefree modulus are signs. -/
theorem moebius_sq_eq_one_of_dvd {s : BoundingSieve} {l : ℕ} (hl : l ∣ s.prodPrimes) :
    (μ l : ℝ) ^ (2 : ℕ) = 1 := by
  have hsq : Squarefree l := s.prodPrimes_squarefree.squarefree_of_dvd hl
  have h : (μ l : ℤ) = (-1) ^ (ArithmeticFunction.cardFactors l) :=
    moebius_apply_of_squarefree hsq
  have hcast : (μ l : ℝ) = (-1 : ℝ) ^ (ArithmeticFunction.cardFactors l) := by exact_mod_cast h
  rw [hcast, ← pow_mul, mul_comm, pow_mul]
  norm_num

/-- The total Selberg mass. -/
noncomputable def selbergMass (s : BoundingSieve) : ℝ :=
  ∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l

theorem selbergMass_pos (s : BoundingSieve) : 0 < selbergMass s := by
  refine Finset.sum_pos (fun l hl => selbergTerms_pos (Nat.dvd_of_mem_divisors hl)) ⟨1, ?_⟩
  exact Nat.mem_divisors.2 ⟨one_dvd _, s.prodPrimes_squarefree.ne_zero⟩

/-- The diagonal profile achieving the Selberg optimum. -/
noncomputable def selbergOptimalY (s : BoundingSieve) (l : ℕ) : ℝ :=
  (μ l : ℝ) * s.selbergTerms l / selbergMass s

/-- The Selberg optimal weight. -/
noncomputable def selbergOptimalWeight (s : BoundingSieve) : ℕ → ℝ :=
  selbergW s (selbergOptimalY s)

/-- The optimal weight is admissible for `upperMoebius_lambdaSquared`. -/
theorem selbergOptimalWeight_one (s : BoundingSieve) : selbergOptimalWeight s 1 = 1 := by
  classical
  have hS := selbergMass_pos s
  unfold selbergOptimalWeight selbergW
  rw [s.nu_mult.map_one, div_one]
  have hterm : ∀ l ∈ s.prodPrimes.divisors,
      (if (1 : ℕ) ∣ l then (μ (l / 1) : ℝ) * selbergOptimalY s l else 0)
        = s.selbergTerms l / selbergMass s := by
    intro l hl
    rw [if_pos (one_dvd l), Nat.div_one, selbergOptimalY]
    have hmusq := moebius_sq_eq_one_of_dvd (s := s) (Nat.dvd_of_mem_divisors hl)
    have hrw : (μ l : ℝ) * ((μ l : ℝ) * s.selbergTerms l / selbergMass s)
        = (μ l : ℝ) ^ (2 : ℕ) * s.selbergTerms l / selbergMass s := by ring
    rw [hrw, hmusq, one_mul]
  rw [Finset.sum_congr rfl hterm]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← selbergMass]
  exact mul_inv_cancel₀ hS.ne'

/-- **The Selberg optimum.**  The main term of the optimal weight is the reciprocal of the total
Selberg mass, matching the Cauchy–Schwarz lower bound exactly. -/
theorem mainSum_selbergOptimalWeight (s : BoundingSieve) :
    s.mainSum (lambdaSquared (selbergOptimalWeight s)) = (selbergMass s)⁻¹ := by
  classical
  have hS := selbergMass_pos s
  rw [mainSum_lambdaSquared_eq_sum_selbergY]
  have hterm : ∀ l ∈ s.prodPrimes.divisors,
      (s.selbergTerms l)⁻¹ * (selbergY s (selbergOptimalWeight s) l) ^ (2 : ℕ)
        = s.selbergTerms l / (selbergMass s) ^ (2 : ℕ) := by
    intro l hl
    have hdvd := Nat.dvd_of_mem_divisors hl
    have hy : selbergY s (selbergOptimalWeight s) l = selbergOptimalY s l :=
      selbergY_selbergW s (selbergOptimalY s) hdvd
    have hg : 0 < s.selbergTerms l := selbergTerms_pos hdvd
    have hmusq := moebius_sq_eq_one_of_dvd (s := s) hdvd
    rw [hy, selbergOptimalY, div_pow, mul_pow, hmusq, one_mul]
    field_simp
  rw [Finset.sum_congr rfl hterm]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← selbergMass, sq, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ hS.ne', one_mul]

/-- **Selberg's sieve.**  The sifted sum is bounded by the total mass divided by the Selberg mass,
plus the remainder sum of the optimal `Λ²` coefficients.

This is the conclusion mathlib's `SelbergSieve` file sets up but does not state: mathlib supplies
the `Λ²` upper-Möbius machinery and the diagonalisation, and the optimisation performed here
(inversion from the diagonal profile `μ(l) g_l / S`) closes it. -/
theorem siftedSum_le_selberg (s : BoundingSieve) :
    s.siftedSum ≤ s.totalMass / selbergMass s
      + s.errSum (lambdaSquared (selbergOptimalWeight s)) := by
  have h := siftedSum_le_mainSum_errSum_of_upperMoebius (s := s)
    (lambdaSquared (selbergOptimalWeight s))
    (upperMoebius_lambdaSquared _ (selbergOptimalWeight_one s))
  rw [mainSum_selbergOptimalWeight] at h
  rwa [div_eq_mul_inv]

/-- The Selberg main term is optimal: the weight constructed here attains the Cauchy–Schwarz
lower bound. -/
theorem mainSum_selbergOptimalWeight_le (s : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    s.mainSum (lambdaSquared (selbergOptimalWeight s)) ≤ s.mainSum (lambdaSquared w) := by
  rw [mainSum_selbergOptimalWeight]
  exact inv_sum_selbergTerms_le_mainSum s w hw

end RHTower.Sieve
