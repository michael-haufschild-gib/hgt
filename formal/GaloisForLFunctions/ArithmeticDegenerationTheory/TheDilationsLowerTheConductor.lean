import GaloisForLFunctions.BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient
import GaloisForLFunctions.BezoutValuationIncidence.QuotientDualOctaveReciprocityAndValuationSwitching
import GaloisForLFunctions.TransThresholdPairCorrelation.ParitySensitiveRamanujanStabilizerTransfer
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesAreAsymptoticallyOrthonormal

/-!
# The dilations lower the conductor

The graded pieces of the degenerating complete Weil family are the Ramanujan packets of the
conductors `m`. This file computes how the multiplicative monoid acts on them: the dilation
`n ↦ pn` by a prime preserves the span of Ramanujan sums and **lowers the `p`-valuation of the
conductor**. It is the monodromy of the degeneration, one branch per prime.

* **Dilation law** (`ramanujanLagCoefficient_prime_mul_eq`): for a prime `p` and `m ≥ 1`,
  `c_m(pn) = w_p(m) c_{ℓ_p m}(n)`, where `ℓ_p m = m/p` if `p ∣ m` and `m` otherwise, and
  `w_p(m) = 1` (`p ∤ m`), `p − 1` (`p ∥ m`), `p` (`p² ∣ m`).
  When `p² ∣ m` only the divisors `d` with `p ∣ d` survive Möbius; when `p ∥ m` the divisors prime
  to `p` contribute `−c_{m/p}(n)` and those divisible by `p` contribute `p c_{m/p}(n)`.
* **The normalized packets** (`ramanujanPoleProfile_prime_mul`): in the pole gauge
  `r_m(n) = c_m(n)/√(φ(m) n)` the law reads `r_m(pn) = θ_p(m) r_{ℓ_p m}(n)` with
  `θ_p(m) = 1/√p, √((p−1)/p), 1`. Deep in the `p`-tower (`p² ∣ m`) the dilation is an exact
  isometric lowering.
* **The cone of lowerings** (`conductorLower_comm`, `conductorLower_lt`,
  `forall_conductorLower_eq_self_iff`): lowerings by distinct primes commute; each strictly lowers
  a conductor it divides; the pole conductor `1` is the only conductor fixed by every lowering.
  The conductor towers `{m'p^k}` are the weight strings of the monodromy, and every string ends at
  the pole conductor.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open BezoutValuationIncidence

/-- The lowering of a conductor by a prime: `ℓ_p m = m/p` if `p ∣ m`, else `m`. -/
def conductorLower (p m : ℕ) : ℕ := if p ∣ m then m / p else m

/-- The dilation weight: `1` if `p ∤ m`, `p − 1` if `p ∥ m`, `p` if `p² ∣ m`. -/
def dilationWeight (p m : ℕ) : ℝ := if p ∣ m then (if p ∣ m / p then (p : ℝ) else (p : ℝ) - 1) else 1

/-- The normalized dilation factor: `1/√p` if `p ∤ m`, `√((p−1)/p)` if `p ∥ m`, `1` if `p² ∣ m`. -/
def dilationFactor (p m : ℕ) : ℝ :=
  if p ∣ m then (if p ∣ m / p then 1 else Real.sqrt (((p : ℝ) - 1) / p)) else 1 / Real.sqrt p

/-! ## The dilation law for Ramanujan sums -/

/-- A dilation by a prime not dividing the conductor fixes the Ramanujan sum. -/
theorem ramanujanLagCoefficient_prime_mul_of_not_dvd {p m : ℕ} (hp : p.Prime) (hpm : ¬p ∣ m)
    (n : ℕ) : ramanujanLagCoefficient m (p * n) = ramanujanLagCoefficient m n := by
  unfold ramanujanLagCoefficient
  refine sum_congr rfl fun d hd => ?_
  have hdm := Nat.dvd_of_mem_divisors hd
  have hcop : Nat.Coprime d p :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpm (h.trans hdm)))
  have hiff : d ∣ p * n ↔ d ∣ n := hcop.dvd_mul_left
  simp only [hiff]

/-- The divisors divisible by `p` of `m = p m'` are `p` times the divisors of `m'`. -/
theorem sum_divisors_filter_prime_dvd {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    (F : ℕ → ℝ) :
    ∑ d ∈ m.divisors.filter (p ∣ ·), F d = ∑ d ∈ (m / p).divisors, F (p * d) := by
  have hm' : m / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos).ne'
  refine sum_nbij' (fun d => d / p) (fun d => p * d) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    simp only [mem_coe, Nat.mem_divisors]
    exact ⟨Nat.div_dvd_div hd.2 hd.1.1, hm'⟩
  · intro d hd
    simp only [mem_coe, Nat.mem_divisors] at hd
    simp only [mem_coe, mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hm.ne'⟩, dvd_mul_right p d⟩
    rw [← Nat.mul_div_cancel' hpm]
    exact Nat.mul_dvd_mul_left p hd.1
  · intro d hd
    simp only [mem_coe, mem_filter] at hd
    exact Nat.mul_div_cancel' hd.2
  · intro d _
    exact Nat.mul_div_cancel_left d hp.pos
  · intro d hd
    simp only [mem_filter] at hd
    rw [Nat.mul_div_cancel' hd.2]

/-- The part of the Ramanujan sum over divisors divisible by `p`. -/
theorem sum_filter_prime_dvd_eq {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m) (n : ℕ) :
    ∑ d ∈ m.divisors.filter (p ∣ ·),
        moebiusReal (m / d) * (if d ∣ p * n then (d : ℝ) else 0) =
      p * ramanujanLagCoefficient (m / p) n := by
  rw [sum_divisors_filter_prime_dvd hp hm hpm, ramanujanLagCoefficient, mul_sum]
  refine sum_congr rfl fun d hd => ?_
  have hmd : m / (p * d) = m / p / d := (Nat.div_div_eq_div_mul m p d).symm
  have hiff : p * d ∣ p * n ↔ d ∣ n := Nat.mul_dvd_mul_iff_left hp.pos
  rw [hmd]
  simp only [hiff]
  split_ifs <;> push_cast <;> ring

/-- **The dilation law.** For a prime `p` dividing `m ≥ 1`,
`c_m(pn) = p c_{m/p}(n)` if `p² ∣ m` and `(p − 1) c_{m/p}(n)` if `p ∥ m`. -/
theorem ramanujanLagCoefficient_prime_mul_of_dvd {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hpm : p ∣ m) (n : ℕ) :
    ramanujanLagCoefficient m (p * n) =
      (if p ∣ m / p then (p : ℝ) else (p : ℝ) - 1) * ramanujanLagCoefficient (m / p) n := by
  have hsplit := sum_filter_add_sum_filter_not m.divisors (p ∣ ·)
    (fun d => moebiusReal (m / d) * (if d ∣ p * n then (d : ℝ) else 0))
  rw [ramanujanLagCoefficient, ← hsplit, sum_filter_prime_dvd_eq hp hm hpm]
  set m' := m / p with hm'
  have hmm : m = p * m' := (Nat.mul_div_cancel' hpm).symm
  split_ifs with hpm'
  · -- `p² ∣ m`: the divisors prime to `p` carry non-squarefree cofactors
    have hzero : ∑ d ∈ m.divisors.filter (fun d => ¬p ∣ d),
        moebiusReal (m / d) * (if d ∣ p * n then (d : ℝ) else 0) = 0 := by
      refine sum_eq_zero fun d hd => ?_
      simp only [mem_filter, Nat.mem_divisors] at hd
      have hcop : Nat.Coprime (p * p) d :=
        Nat.Coprime.mul ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd.2)
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd.2)
      have hpp : p * p ∣ m / d * d := by
        rw [Nat.div_mul_cancel hd.1.1, hmm]
        exact Nat.mul_dvd_mul_left p hpm'
      have hsq : ¬Squarefree (m / d) := fun hsf =>
        hp.not_isUnit (hsf p (hcop.dvd_of_dvd_mul_right hpp))
      simp [moebiusReal, moebius_eq_zero_of_not_squarefree hsq]
    rw [hzero, add_zero]
  · -- `p ∥ m`: the divisors prime to `p` are the divisors of `m'`
    have hset : m.divisors.filter (fun d => ¬p ∣ d) = m'.divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdm, -⟩, hpd⟩
        refine ⟨?_, (Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos).ne'⟩
        have hcop : Nat.Coprime d p :=
          Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
        rw [hmm] at hdm
        exact hcop.dvd_of_dvd_mul_left hdm
      · rintro ⟨hdm', hm'0⟩
        exact ⟨⟨hdm'.trans (hmm ▸ dvd_mul_left m' p), hm.ne'⟩, fun h => hpm' (h.trans hdm')⟩
    have hpart : ∑ d ∈ m.divisors.filter (fun d => ¬p ∣ d),
        moebiusReal (m / d) * (if d ∣ p * n then (d : ℝ) else 0) =
          -ramanujanLagCoefficient m' n := by
      rw [hset, ramanujanLagCoefficient, ← sum_neg_distrib]
      refine sum_congr rfl fun d hd => ?_
      have hdm' := Nat.dvd_of_mem_divisors hd
      have hpd : ¬p ∣ d := fun h => hpm' (h.trans hdm')
      have hcop : Nat.Coprime d p :=
        Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
      have hq : m / d = p * (m' / d) := by
        rw [hmm, Nat.mul_div_assoc p hdm']
      have hpq : Nat.Coprime p (m' / d) :=
        (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpm' (h.trans (Nat.div_dvd_of_dvd hdm'))
      have hmu : moebiusReal (m / d) = -moebiusReal (m' / d) := by
        rw [hq, moebiusReal, moebiusReal, isMultiplicative_moebius.map_mul_of_coprime hpq,
          moebius_apply_prime hp]
        push_cast
        ring
      have hiff : d ∣ p * n ↔ d ∣ n := hcop.dvd_mul_left
      rw [hmu]
      simp only [hiff]
      split_ifs <;> ring
    rw [hpart]
    ring

/-- **The dilation law, unified.** `c_m(pn) = w_p(m) c_{ℓ_p m}(n)` for every prime `p` and `m ≥ 1`. -/
theorem ramanujanLagCoefficient_prime_mul_eq {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (n : ℕ) :
    ramanujanLagCoefficient m (p * n) =
      dilationWeight p m * ramanujanLagCoefficient (conductorLower p m) n := by
  unfold dilationWeight conductorLower
  by_cases hpm : p ∣ m
  · simp only [if_pos hpm]
    exact ramanujanLagCoefficient_prime_mul_of_dvd hp hm hpm n
  · simp only [if_neg hpm, one_mul]
    exact ramanujanLagCoefficient_prime_mul_of_not_dvd hp hpm n

/-! ## The normalized packets -/

open RenormalizedArithmeticPotentialTheory in
/-- **The dilation law in the pole gauge.** `r_m(pn) = θ_p(m) r_{ℓ_p m}(n)`. -/
theorem ramanujanPoleProfile_prime_mul {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (n : ℕ) :
    ramanujanPoleProfile m (p * n) =
      dilationFactor p m * ramanujanPoleProfile (conductorLower p m) n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl0 : 0 < conductorLower p m := by
    unfold conductorLower
    split_ifs with h
    · exact Nat.div_pos (Nat.le_of_dvd hm h) hp.pos
    · exact hm
  simp only [ramanujanPoleProfile, normalizedRamanujanMode,
    TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hm,
    TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hl0,
    ramanujanLagCoefficient_prime_mul_eq hp hm]
  push_cast
  rw [Real.sqrt_mul hp0.le]
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hspp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  unfold dilationWeight dilationFactor conductorLower
  split_ifs with hpm hpm'
  · -- `p² ∣ m`
    have ht : (m.totient : ℝ) = p * (m / p).totient := by
      conv_lhs => rw [← Nat.mul_div_cancel' hpm]
      exact_mod_cast Nat.totient_mul_of_prime_of_dvd hp hpm'
    have htm : 0 < ((m / p).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos)
    rw [ht, Real.sqrt_mul hp0.le]
    have hst : 0 < Real.sqrt ((m / p).totient : ℝ) := Real.sqrt_pos.mpr htm
    field_simp
    rw [Real.sq_sqrt hp0.le]
    ring
  · -- `p ∥ m`
    have ht : (m.totient : ℝ) = ((p : ℝ) - 1) * (m / p).totient := by
      conv_lhs => rw [← Nat.mul_div_cancel' hpm]
      rw [Nat.totient_mul_of_prime_of_not_dvd hp hpm']
      push_cast [Nat.cast_sub hp.one_lt.le]
      ring
    have htm : 0 < ((m / p).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos)
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    rw [ht, Real.sqrt_mul hp1.le, Real.sqrt_div hp1.le]
    have hst : 0 < Real.sqrt ((m / p).totient : ℝ) := Real.sqrt_pos.mpr htm
    have hs1 : 0 < Real.sqrt ((p : ℝ) - 1) := Real.sqrt_pos.mpr hp1
    have hss : Real.sqrt ((p : ℝ) - 1) * Real.sqrt ((p : ℝ) - 1) = (p : ℝ) - 1 :=
      Real.mul_self_sqrt hp1.le
    field_simp
    rw [Real.sq_sqrt hp1.le]
    ring
  · -- `p ∤ m`
    have ht : 0 < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
    have hst : 0 < Real.sqrt (m.totient : ℝ) := Real.sqrt_pos.mpr ht
    field_simp

/-- In the deep part of a tower (`p² ∣ m`) the dilation is an isometric lowering. -/
theorem dilationFactor_eq_one_of_sq_dvd {p m : ℕ} (hpm : p ∣ m) (hpm' : p ∣ m / p) :
    dilationFactor p m = 1 := by
  simp [dilationFactor, hpm, hpm']

/-! ## The cone of lowerings -/

theorem conductorLower_of_dvd {p m : ℕ} (h : p ∣ m) : conductorLower p m = m / p := if_pos h

theorem conductorLower_of_not_dvd {p m : ℕ} (h : ¬p ∣ m) : conductorLower p m = m := if_neg h

/-- A lowering strictly lowers every conductor it divides. -/
theorem conductorLower_lt {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (h : p ∣ m) :
    conductorLower p m < m := by
  rw [conductorLower_of_dvd h]
  exact Nat.div_lt_self hm hp.one_lt

theorem conductorLower_eq_self_iff {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    conductorLower p m = m ↔ ¬p ∣ m := by
  constructor
  · intro h hpm
    exact (conductorLower_lt hp hm hpm).ne h
  · exact conductorLower_of_not_dvd

/-- **The pole conductor is the only fixed point of the cone.** -/
theorem forall_conductorLower_eq_self_iff {m : ℕ} (hm : 0 < m) :
    (∀ p : ℕ, p.Prime → conductorLower p m = m) ↔ m = 1 := by
  constructor
  · intro h
    by_contra hm1
    have hp := Nat.minFac_prime hm1
    exact (conductorLower_eq_self_iff hp hm).mp (h _ hp) (Nat.minFac_dvd m)
  · rintro rfl p hp
    exact conductorLower_of_not_dvd (Nat.Prime.not_dvd_one hp)

/-- Lowering by `q` does not change divisibility by a different prime `p`. -/
theorem prime_dvd_conductorLower_iff {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    p ∣ conductorLower q m ↔ p ∣ m := by
  unfold conductorLower
  split_ifs with hqm
  · constructor
    · intro h; exact h.trans (Nat.div_dvd_of_dvd hqm)
    · intro h
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
      rw [← Nat.div_mul_cancel hqm] at h
      exact hcop.dvd_of_dvd_mul_right h
  · rfl

/-- **Lowerings by distinct primes commute.** -/
theorem conductorLower_comm {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    conductorLower p (conductorLower q m) = conductorLower q (conductorLower p m) := by
  by_cases hpm : p ∣ m <;> by_cases hqm : q ∣ m
  · rw [conductorLower_of_dvd ((prime_dvd_conductorLower_iff hp hq hpq).mpr hpm),
      conductorLower_of_dvd ((prime_dvd_conductorLower_iff hq hp hpq.symm).mpr hqm),
      conductorLower_of_dvd hqm, conductorLower_of_dvd hpm, Nat.div_div_eq_div_mul,
      Nat.div_div_eq_div_mul, mul_comm]
  · rw [conductorLower_of_not_dvd hqm, conductorLower_of_not_dvd
      (fun h => hqm ((prime_dvd_conductorLower_iff hq hp hpq.symm).mp h))]
  · rw [conductorLower_of_not_dvd hpm, conductorLower_of_not_dvd
      (fun h => hpm ((prime_dvd_conductorLower_iff hp hq hpq).mp h))]
  · simp only [conductorLower_of_not_dvd hqm, conductorLower_of_not_dvd hpm]

/-- The two orders of dilation by `p` and `q` give the same Ramanujan sum: the weights of the
cone are a cocycle, `w_p(m) w_q(ℓ_p m) = w_q(m) w_p(ℓ_q m)` on every nonzero Ramanujan sum. -/
theorem dilationWeight_cocycle {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hm : 0 < m) (n : ℕ) :
    dilationWeight p m * (dilationWeight q (conductorLower p m) *
        ramanujanLagCoefficient (conductorLower q (conductorLower p m)) n) =
      dilationWeight q m * (dilationWeight p (conductorLower q m) *
        ramanujanLagCoefficient (conductorLower p (conductorLower q m)) n) := by
  have hl : ∀ r : ℕ, r.Prime → 0 < conductorLower r m := fun r hr => by
    unfold conductorLower
    split_ifs with h
    · exact Nat.div_pos (Nat.le_of_dvd hm h) hr.pos
    · exact hm
  rw [← ramanujanLagCoefficient_prime_mul_eq hq (hl p hp), ← ramanujanLagCoefficient_prime_mul_eq hp
    (hl q hq), ← ramanujanLagCoefficient_prime_mul_eq hp hm, ← ramanujanLagCoefficient_prime_mul_eq hq hm,
    mul_left_comm]

end GaloisForLFunctions.ArithmeticDegenerationTheory
