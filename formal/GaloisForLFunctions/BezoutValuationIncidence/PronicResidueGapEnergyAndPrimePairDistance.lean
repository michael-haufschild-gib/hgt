import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanMoment

/-!
# Gap energy of pronic residue modes

An exact quotient-cell calculation gives the energy of nearby residue modes
before their jump intervals overlap. The prefix correction telescopes, leaving
`h * harmonic (p / h)` up to a gap-sized error. A convergent tail estimate
provides explicit upper and lower bounds, without an equidistribution premise.

For prime moduli, the literal energy-centered Ramanujan distance is the residue
distance minus the squared logarithmic mean difference. This yields a symmetric
gap budget for transporting one prime mode to another. It is not a bound for
arbitrary unmodified prime packets.
-/

open scoped BigOperators
open Finset RHTower

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- Squared residue difference with the non-periodic pronic weight. -/
def residueGapPronicTerm (p q n : ℕ) : ℝ :=
  (((n % p : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

private theorem gap_pronic_interval {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Ico a b, 1 / ((n : ℝ) * ((n : ℝ) + 1))) = 1 / (a : ℝ) - 1 / b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab, ih]
    have hb : (b : ℝ) ≠ 0 := by have : 0 < b := ha.trans_le hab; positivity
    have haR : (a : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- The exact pronic mass of a positive integer interval. -/
theorem sum_Ico_reciprocal_pronic {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Ico a b, 1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      1 / (a : ℝ) - 1 / b :=
  gap_pronic_interval ha hab

private theorem gap_cast_mod {p n k : ℕ}
    (hl : k * p ≤ n) (hu : n < (k + 1) * p) :
    (n % p : ℕ) = n - k * p := by
  have hd : n / p = k := Nat.div_eq_of_lt_le hl hu
  have he := Nat.mod_add_div n p
  rw [hd] at he
  rw [Nat.mul_comm p k] at he
  omega

private theorem gap_residue_first_cell {p h k n : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hkh : k * h ≤ p)
    (hn : n ∈ Ico (k * p) (k * (p + h))) :
    ((n % p : ℕ) : ℝ) - ((n % (p + h) : ℕ) : ℝ) =
      (k : ℝ) * h - (p + h : ℕ) := by
  have hnl := (mem_Ico.mp hn).1
  have hnu := (mem_Ico.mp hn).2
  have hnp : n < (k + 1) * p := by nlinarith
  have hk0 : 1 ≤ k := hk
  have hpred : (k - 1) * (p + h) ≤ n := by
    have he : k - 1 + 1 = k := by omega
    nlinarith
  have hpredU : n < (k - 1 + 1) * (p + h) := by simpa [Nat.sub_add_cancel hk0] using hnu
  rw [gap_cast_mod hnl hnp, gap_cast_mod hpred hpredU,
    Nat.cast_sub hnl, Nat.cast_sub hpred]
  push_cast
  have hkR : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk0, Nat.cast_one]
  rw [hkR]
  ring

private theorem gap_residue_second_cell {p h k n : ℕ}
    (hh : 0 < h)
    (hn : n ∈ Ico (k * (p + h)) ((k + 1) * p)) :
    ((n % p : ℕ) : ℝ) - ((n % (p + h) : ℕ) : ℝ) = (k : ℝ) * h := by
  have hnl := (mem_Ico.mp hn).1
  have hnu := (mem_Ico.mp hn).2
  have hnp : k * p ≤ n := by nlinarith
  have hnq : n < (k + 1) * (p + h) := by nlinarith
  rw [gap_cast_mod hnp hnu, gap_cast_mod hnl hnq,
    Nat.cast_sub hnp, Nat.cast_sub hnl]
  push_cast
  ring

private theorem residue_gap_pronic_block {p h k : ℕ}
    (hp : 0 < p) (hh : 0 < h) (hk : 0 < k) (hkh : k * h ≤ p) :
    (∑ n ∈ Ico (k * p) ((k + 1) * p), residueGapPronicTerm p (p + h) n) =
      ((p : ℝ) + h) * h / ((p : ℝ) * k) -
        (h : ℝ) ^ 2 / p * ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
  have hleft : k * p ≤ k * (p + h) := by nlinarith
  have hright : k * (p + h) ≤ (k + 1) * p := by nlinarith
  rw [← sum_Ico_consecutive (residueGapPronicTerm p (p + h)) hleft hright]
  have hkp : 0 < k * p := by positivity
  have hkq : 0 < k * (p + h) := by positivity
  have hfirst : (∑ n ∈ Ico (k * p) (k * (p + h)), residueGapPronicTerm p (p + h) n) =
      ((k : ℝ) * h - ((p : ℝ) + h)) ^ 2 *
        (1 / ((k : ℝ) * p) - 1 / ((k : ℝ) * ((p : ℝ) + h))) := by
    calc
      _ = ∑ n ∈ Ico (k * p) (k * (p + h)),
          ((k : ℝ) * h - ((p : ℝ) + h)) ^ 2 *
            (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_congr rfl
        intro n hn
        rw [residueGapPronicTerm, gap_residue_first_cell hh hk hkh hn]
        push_cast
        ring
      _ = _ := by
        rw [← mul_sum, gap_pronic_interval hkp hleft]
        push_cast
        rfl
  have hsecond : (∑ n ∈ Ico (k * (p + h)) ((k + 1) * p),
      residueGapPronicTerm p (p + h) n) =
      ((k : ℝ) * h) ^ 2 *
        (1 / ((k : ℝ) * ((p : ℝ) + h)) - 1 / (((k : ℝ) + 1) * p)) := by
    calc
      _ = ∑ n ∈ Ico (k * (p + h)) ((k + 1) * p),
          ((k : ℝ) * h) ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_congr rfl
        intro n hn
        rw [residueGapPronicTerm, gap_residue_second_cell hh hn]
        ring
      _ = _ := by
        rw [← mul_sum, gap_pronic_interval hkq hright]
        push_cast
        rfl
  rw [hfirst, hsecond]
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hqR : (p : ℝ) + h ≠ 0 := by positivity
  field_simp
  ring

/-- Total pronic energy of the difference of two residue modes. -/
def residueGapPronicEnergy (p q : ℕ) : ℝ :=
  ∑' n : ℕ, residueGapPronicTerm p q n

private theorem residue_gap_prefix_eq {p h : ℕ} (hp : 0 < p) (hh : 0 < h)
    (K : ℕ) (hK : K * h ≤ p) :
    (∑ n ∈ range ((K + 1) * p), residueGapPronicTerm p (p + h) n) =
      (h : ℝ) * (harmonic K : ℝ) -
        (h : ℝ) ^ 2 / p * (K : ℝ) ^ 2 / ((K : ℝ) + 1) := by
  induction K with
  | zero =>
    simp only [zero_add, one_mul, harmonic_zero, Rat.cast_zero, Nat.cast_zero,
      mul_zero, zero_pow (by omega : 2 ≠ 0), zero_div, sub_zero]
    apply sum_eq_zero
    intro n hn
    have hnp := mem_range.mp hn
    have hnq : n < p + h := by omega
    simp [residueGapPronicTerm, Nat.mod_eq_of_lt hnp, Nat.mod_eq_of_lt hnq]
  | succ K ih =>
    have hK' : K * h ≤ p := by nlinarith
    have hle : (K + 1) * p ≤ (K + 1 + 1) * p := by nlinarith
    rw [← sum_range_add_sum_Ico (residueGapPronicTerm p (p + h)) hle,
      residue_gap_pronic_block hp hh (by omega : 0 < K + 1) hK, ih hK', harmonic_succ]
    push_cast
    have hpR : (p : ℝ) ≠ 0 := by positivity
    field_simp
    ring

private theorem residue_gap_prefix_le {p h : ℕ} (hp : 0 < p) (hh : 0 < h)
    (K : ℕ) (hK : K * h ≤ p) :
    (∑ n ∈ range ((K + 1) * p), residueGapPronicTerm p (p + h) n) ≤
      (h : ℝ) * (harmonic K : ℝ) := by
  rw [residue_gap_prefix_eq hp hh K hK]
  exact sub_le_self _ (by positivity)

private theorem residue_gap_sq_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≤ q) (n : ℕ) :
    (((n % p : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) ^ 2 ≤ (q : ℝ) ^ 2 := by
  have hpmod : ((n % p : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.mod_lt n hp).le.trans hpq
  have hqmod : ((n % q : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt n hq).le
  have hp0 : (0 : ℝ) ≤ ((n % p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ ((n % q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlo : 0 ≤ (q : ℝ) - (((n % p : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) := by linarith
  have hhi : 0 ≤ (q : ℝ) + (((n % p : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) := by linarith
  nlinarith [mul_nonneg hlo hhi]

private theorem summable_residueGapPronicTerm {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≤ q) : Summable (residueGapPronicTerm p q) := by
  apply Summable.of_norm_bounded (hasSum_pm_reciprocal_weight.summable.mul_left ((q : ℝ) ^ 2))
  intro n
  calc
    ‖residueGapPronicTerm p q n‖ = residueGapPronicTerm p q n := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold residueGapPronicTerm; positivity)]
    _ ≤ (q : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right (residue_gap_sq_le hp hq hpq n) (by positivity)
    _ = _ := by ring

private theorem residue_gap_tail_le {p q N : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≤ q) (hN : 0 < N) :
    (∑' n : ℕ, residueGapPronicTerm p q (N + n)) ≤ (q : ℝ) ^ 2 / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmass := GaloisForLFunctions.hasSum_one_div_shift_mul_succ hNR
  have hsum : Summable (fun n : ℕ => residueGapPronicTerm p q (N + n)) :=
    (summable_residueGapPronicTerm hp hq hpq).comp_injective
      (fun i j h => Nat.add_left_cancel h)
  calc
    _ ≤ ∑' n : ℕ, (q : ℝ) ^ 2 *
        (1 / (((N : ℝ) + n) * ((N : ℝ) + n + 1))) := by
      apply Summable.tsum_le_tsum _ hsum (hmass.summable.mul_left ((q : ℝ) ^ 2))
      intro n
      have h := div_le_div_of_nonneg_right (residue_gap_sq_le hp hq hpq (N + n))
        (by positivity : 0 ≤ (((N + n : ℕ) : ℝ) * (((N + n : ℕ) : ℝ) + 1)))
      simpa only [residueGapPronicTerm, Nat.cast_add, mul_one_div] using h
    _ = _ := by rw [tsum_mul_left, hmass.tsum_eq]; ring

private theorem residue_gap_energy_bound {p h : ℕ} (hp : 0 < p) (hh : 0 < h)
    (K : ℕ) (hK : K * h ≤ p) :
    residueGapPronicEnergy p (p + h) ≤
      (h : ℝ) * (harmonic K : ℝ) +
        ((p : ℝ) + h) ^ 2 / ((p : ℝ) * ((K : ℝ) + 1)) := by
  have hq : 0 < p + h := by omega
  have hpq : p ≤ p + h := by omega
  have hs := summable_residueGapPronicTerm hp hq hpq
  have he := hs.sum_add_tsum_nat_add ((K + 1) * p)
  have hhead := residue_gap_prefix_le hp hh K hK
  have htail := residue_gap_tail_le hp hq hpq
    (by positivity : 0 < (K + 1) * p)
  have he' : residueGapPronicEnergy p (p + h) =
      (∑ n ∈ range ((K + 1) * p), residueGapPronicTerm p (p + h) n) +
      ∑' n : ℕ, residueGapPronicTerm p (p + h) ((K + 1) * p + n) := by
    simpa only [residueGapPronicEnergy, Nat.add_comm] using he.symm
  rw [he']
  have htail' : (∑' n : ℕ, residueGapPronicTerm p (p + h) ((K + 1) * p + n)) ≤
      ((p : ℝ) + h) ^ 2 / ((p : ℝ) * ((K : ℝ) + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, mul_comm] using htail
  exact add_le_add hhead htail'

/-- Exact energy of one pair of neighboring quotient cells. -/
theorem residueGapPronicBlock_exact (h k : ℕ+) (r : ℕ) :
    let p := (k : ℕ) * (h : ℕ) + r
    (∑ n ∈ Ico ((k : ℕ) * p) (((k : ℕ) + 1) * p),
      residueGapPronicTerm p (p + h) n) =
      ((p : ℝ) + h) * h / ((p : ℝ) * k) -
        (h : ℝ) ^ 2 / p * ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
  dsimp only
  exact residue_gap_pronic_block (by positivity) h.pos k.pos (by omega)

/-- A gap-sensitive estimate from an exact finite prefix and a bounded tail. -/
theorem residueGapPronicEnergy_le_harmonic_budget (p h : ℕ+) :
    let K := (p : ℕ) / (h : ℕ)
    residueGapPronicEnergy p ((p : ℕ) + h) ≤
      (h : ℝ) * (harmonic K : ℝ) +
        ((p : ℝ) + h) ^ 2 / ((p : ℝ) * ((K : ℝ) + 1)) := by
  dsimp only
  exact residue_gap_energy_bound p.pos h.pos _
    (by simpa only [Nat.mul_comm] using Nat.mul_div_le (p : ℕ) (h : ℕ))

/-- The entire pre-overlap prefix has an exact harmonic energy. -/
theorem residueGapPronicPrefix_exact (p h : ℕ+) :
    let K := (p : ℕ) / (h : ℕ)
    (∑ n ∈ range ((K + 1) * (p : ℕ)), residueGapPronicTerm p ((p : ℕ) + h) n) =
      (h : ℝ) * (harmonic K : ℝ) -
        (h : ℝ) ^ 2 / p * (K : ℝ) ^ 2 / ((K : ℝ) + 1) := by
  dsimp only
  exact residue_gap_prefix_eq p.pos h.pos _
    (by simpa only [Nat.mul_comm] using Nat.mul_div_le (p : ℕ) (h : ℕ))

/-- The harmonic gap cost is forced by the prefix, up to one gap. -/
theorem residueGapPronicEnergy_ge_harmonic_budget (p h : ℕ+) :
    let K := (p : ℕ) / (h : ℕ)
    (h : ℝ) * (harmonic K : ℝ) - h ≤ residueGapPronicEnergy p ((p : ℕ) + h) := by
  let K := (p : ℕ) / (h : ℕ)
  have hK : K * (h : ℕ) ≤ (p : ℕ) := by
    simpa only [K, Nat.mul_comm] using Nat.mul_div_le (p : ℕ) (h : ℕ)
  have hKR : (h : ℝ) * (K : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (show (h : ℕ) * K ≤ (p : ℕ) by simpa only [Nat.mul_comm] using hK)
  have hpR : (0 : ℝ) < p := by exact_mod_cast p.pos
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hcor : (h : ℝ) ^ 2 / p * (K : ℝ) ^ 2 / ((K : ℝ) + 1) ≤ h := by
    apply (div_le_iff₀ hK1).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hpR).mpr
    have hmul := mul_le_mul_of_nonneg_left hKR
      (show 0 ≤ (h : ℝ) * (K : ℝ) by positivity)
    nlinarith [show (0 : ℝ) ≤ (h : ℝ) * p by positivity]
  have hs := summable_residueGapPronicTerm p.pos
    (by positivity : 0 < (p : ℕ) + h) (by omega : (p : ℕ) ≤ (p : ℕ) + h)
  have he := hs.sum_add_tsum_nat_add ((K + 1) * (p : ℕ))
  have ht : 0 ≤ ∑' n : ℕ, residueGapPronicTerm p ((p : ℕ) + h)
      (n + (K + 1) * (p : ℕ)) := by
    apply tsum_nonneg
    intro n
    unfold residueGapPronicTerm
    positivity
  rw [residue_gap_prefix_eq p.pos h.pos K hK] at he
  change _ = residueGapPronicEnergy p ((p : ℕ) + h) at he
  change (h : ℝ) * (harmonic K : ℝ) - h ≤ _
  linarith

/-- For gaps at most the smaller modulus, the cost is at most a gap times a harmonic sum. -/
theorem residueGapPronicEnergy_le_nearby (p : ℕ+) (d : Fin (p : ℕ)) :
    let h := d.val + 1
    let K := (p : ℕ) / h
    residueGapPronicEnergy p ((p : ℕ) + h) ≤
      (h : ℝ) * (harmonic K : ℝ) + 4 * h := by
  dsimp only
  have hh : 0 < d.val + 1 := by omega
  have hhp : d.val + 1 ≤ (p : ℕ) := d.isLt
  have hpR : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.pos
  have hhpR : ((d.val + 1 : ℕ) : ℝ) ≤ (p : ℕ) := by exact_mod_cast hhp
  have h := residue_gap_energy_bound p.pos hh ((p : ℕ) / (d.val + 1))
    (by simpa only [Nat.mul_comm] using Nat.mul_div_le (p : ℕ) (d.val + 1))
  have hK : (p : ℝ) ≤ ((d.val + 1 : ℕ) : ℝ) *
      (((p : ℕ) / (d.val + 1) : ℕ) + 1 : ℝ) := by
    exact_mod_cast (Nat.lt_mul_div_succ (p : ℕ) hh).le
  have hden : 0 < (p : ℝ) * (((p : ℕ) / (d.val + 1) : ℕ) + 1 : ℝ) := by positivity
  have htail : ((p : ℝ) + (d.val + 1 : ℕ)) ^ 2 /
      ((p : ℝ) * (((p : ℕ) / (d.val + 1) : ℕ) + 1 : ℝ)) ≤ 4 * (d.val + 1 : ℕ) := by
    apply (div_le_iff₀ hden).mpr
    have hmul := mul_le_mul_of_nonneg_left hK hpR.le
    have hprod := mul_nonneg (sub_nonneg.mpr hhpR)
      (show 0 ≤ 3 * (p : ℝ) + (d.val + 1 : ℕ) by positivity)
    nlinarith
  exact h.trans (add_le_add le_rfl htail)

/-- The residue distance is the centered prime-mode distance plus the squared mean difference. -/
theorem primePair_centered_distance_eq_residueGap (p q : Nat.Primes) :
    pmRamanujanEnergyCenteredGram p p + pmRamanujanEnergyCenteredGram q q -
      2 * pmRamanujanEnergyCenteredGram p q =
      residueGapPronicEnergy p q - (Real.log (p : ℕ) - Real.log (q : ℕ)) ^ 2 := by
  have hs := ((summable_pmRamanujanPrimitiveGramTerm p.property.one_lt p.property.one_lt
    ).hasSum.add (summable_pmRamanujanPrimitiveGramTerm q.property.one_lt q.property.one_lt
    ).hasSum).sub ((summable_pmRamanujanPrimitiveGramTerm p.property.one_lt q.property.one_lt
    ).hasSum.mul_left 2)
  have he : HasSum (residueGapPronicTerm p q)
      (pmRamanujanPrimitiveGram p p + pmRamanujanPrimitiveGram q q -
        2 * pmRamanujanPrimitiveGram p q) := by
    apply hs.congr_fun
    intro n
    simp only [residueGapPronicTerm, pmRamanujanPrimitiveGramTerm,
      pmRamanujanPrimitive_prime p.property, pmRamanujanPrimitive_prime q.property,
      Complex.neg_re, Complex.natCast_re]
    ring
  have ht := he.tsum_eq
  change residueGapPronicEnergy p q = _ at ht
  rw [pmRamanujanPrimitiveGram_eq_energyCentered p.property.one_lt p.property.one_lt,
    pmRamanujanPrimitiveGram_eq_energyCentered q.property.one_lt q.property.one_lt,
    pmRamanujanPrimitiveGram_eq_energyCentered p.property.one_lt q.property.one_lt,
    ArithmeticFunction.vonMangoldt_apply_prime p.property,
    ArithmeticFunction.vonMangoldt_apply_prime q.property] at ht
  nlinarith

/-- Symmetric gap budget; the diagonal costs zero. -/
def residueGapPronicBudget (p q : ℕ) : ℝ :=
  if p = q then 0 else
    let m := min p q
    let M := max p q
    let h := M - m
    let K := m / h
    (h : ℝ) * (harmonic K : ℝ) +
      (M : ℝ) ^ 2 / ((m : ℝ) * ((K : ℝ) + 1))

/-- Reversing the endpoints does not change their pronic distance. -/
theorem residueGapPronicEnergy_comm (p q : ℕ) :
    residueGapPronicEnergy p q = residueGapPronicEnergy q p := by
  apply tsum_congr
  intro n
  unfold residueGapPronicTerm
  ring

/-- The explicit budget depends only on the unordered pair. -/
theorem residueGapPronicBudget_comm (p q : ℕ) :
    residueGapPronicBudget p q = residueGapPronicBudget q p := by
  simp only [residueGapPronicBudget, min_comm p q, max_comm p q, eq_comm]

private theorem residue_gap_le_budget_of_lt {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    residueGapPronicEnergy p q ≤ residueGapPronicBudget p q := by
  have hh : 0 < q - p := by omega
  have he : p + (q - p) = q := Nat.add_sub_of_le hpq.le
  have heR : (p : ℝ) + (q - p : ℕ) = (q : ℝ) := by exact_mod_cast he
  have hb := residue_gap_energy_bound hp hh (p / (q - p))
    (by simpa only [Nat.mul_comm] using Nat.mul_div_le p (q - p))
  rw [he, heR] at hb
  simpa only [residueGapPronicBudget, ne_of_lt hpq, ite_false,
    Nat.min_eq_left hpq.le, Nat.max_eq_right hpq.le] using hb

/-- Every pair of positive integer moduli satisfies the explicit gap estimate. -/
theorem residueGapPronicEnergy_le_budget (p q : ℕ+) :
    residueGapPronicEnergy p q ≤ residueGapPronicBudget p q := by
  rcases lt_trichotomy (p : ℕ) (q : ℕ) with h | h | h
  · exact residue_gap_le_budget_of_lt p.pos h
  · simp [residueGapPronicEnergy, residueGapPronicTerm, residueGapPronicBudget, h]
  · rw [residueGapPronicEnergy_comm, residueGapPronicBudget_comm]
    exact residue_gap_le_budget_of_lt q.pos h

/-- Nearby prime modes cancel at a cost controlled by their gap, with no averaging premise. -/
theorem primePair_centered_distance_le_gapBudget (p q : Nat.Primes) :
    pmRamanujanEnergyCenteredGram p p + pmRamanujanEnergyCenteredGram q q -
      2 * pmRamanujanEnergyCenteredGram p q ≤ residueGapPronicBudget p q := by
  calc
    _ = residueGapPronicEnergy p q - (Real.log (p : ℕ) - Real.log (q : ℕ)) ^ 2 :=
      primePair_centered_distance_eq_residueGap p q
    _ ≤ residueGapPronicEnergy p q := sub_le_self _ (sq_nonneg _)
    _ ≤ _ := residueGapPronicEnergy_le_budget ⟨p, p.property.pos⟩ ⟨q, q.property.pos⟩

end
end GaloisForLFunctions.BezoutValuationIncidence
