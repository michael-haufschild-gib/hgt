import GaloisForLFunctions.RHTower.EulerDeletionDirichletGram

/-!
# Literal interference in composite Euler deletion

Composite deletion is the sum of one source and a source inserted at its multiples.
The overlap is strictly negative throughout the doubled-abscissa convergence chamber.
Thus the literal arithmetic interleaving is not an orthogonal replication. All statements
precede zero selection; no chronological transport-coherence premise is assumed.
-/

namespace RHTower

open scoped BigOperators

/-- The arithmetic leg inserted at the multiples of `p`, with its literal coefficient `p`. -/
noncomputable def deletionInsertedSource (p q : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  if p ∣ n then (p : ℂ) * ((blockDeletionCoefficient q (n / p) : ℝ) : ℂ) *
    (n : ℂ) ^ (-s) else 0

/-- Composite deletion is an interleaving identity, with no coprimality restriction. -/
theorem deletionMellinSource_mul_eq_add_inserted {p : ℕ} (hp : 0 < p)
    (q : ℕ) (s : ℂ) (n : ℕ) :
    deletionMellinSource (p * q) s n =
      deletionMellinSource p s n + deletionInsertedSource p q s n := by
  by_cases hd : p ∣ n
  · obtain ⟨k, rfl⟩ := hd
    have hdiv : p * q ∣ p * k ↔ q ∣ k := Nat.mul_dvd_mul_iff_left hp
    by_cases hq : q ∣ k <;>
      simp [deletionMellinSource, deletionInsertedSource, blockDeletionCoefficient,
        Nat.mul_div_cancel_left _ hp, hdiv, hq] <;> ring
  · have hpq : ¬p * q ∣ n := fun h => hd ((dvd_mul_right p q).trans h)
    simp [deletionMellinSource, deletionInsertedSource, blockDeletionCoefficient, hd, hpq]

/-- The inserted leg is exactly Euler amplitude times the original source on its dilated clock. -/
theorem deletionInsertedSource_at_multiple {p : ℕ} (hp : 0 < p)
    (q : ℕ) (s : ℂ) (k : ℕ) :
    deletionInsertedSource p q s (p * k) =
      ((p : ℂ) * (p : ℂ) ^ (-s)) * deletionMellinSource q s k := by
  simp only [deletionInsertedSource, dvd_mul_right, if_true,
    Nat.mul_div_cancel_left _ hp, deletionMellinSource, Nat.cast_mul]
  have hpow := Complex.mul_cpow_ofReal_nonneg
    (Nat.cast_nonneg p) (Nat.cast_nonneg k) (-s)
  simp only [Complex.ofReal_natCast] at hpow
  rw [hpow]
  ring

theorem deletionInsertedSource_eq_sub {p : ℕ} (hp : 0 < p)
    (q : ℕ) (s : ℂ) (n : ℕ) :
    deletionInsertedSource p q s n =
      deletionMellinSource (p * q) s n - deletionMellinSource p s n := by
  rw [deletionMellinSource_mul_eq_add_inserted hp]
  ring

/-- Literal real Gram energy of a deletion source. -/
noncomputable def deletionSourceEnergy (α : ℝ) (p : ℕ) : ℝ :=
  ∑' n, (blockDeletionCoefficient p n : ℝ) ^ 2 * deletionDirichletWeight α n

theorem deletionSourceEnergy_eq {α : ℝ} (hα : 1 < α) {p : ℕ} (hp : 0 < p) :
    deletionSourceEnergy α p = deletionDirichletMass α *
      (1 - 2 * p * (p : ℝ) ^ (-α) + (p : ℝ) ^ 2 * (p : ℝ) ^ (-α)) := by
  rw [deletionSourceEnergy, tsum_deletionDirichlet_gram_self hα hp]
  ring

theorem normSq_deletionMellinSource {s : ℂ} (hs : 1 / 2 < s.re) (p n : ℕ) :
    Complex.normSq (deletionMellinSource p s n) =
      (blockDeletionCoefficient p n : ℝ) ^ 2 * deletionDirichletWeight (2 * s.re) n := by
  have h := deletionMellinSource_pair_re hs p p n
  change (deletionMellinSource p s n * (starRingEnd ℂ) (deletionMellinSource p s n)).re = _ at h
  rw [Complex.mul_conj, Complex.ofReal_re] at h
  simpa only [pow_two] using h

theorem tsum_normSq_deletionMellinSource {s : ℂ} (hs : 1 / 2 < s.re) (p : ℕ) :
    ∑' n, Complex.normSq (deletionMellinSource p s n) = deletionSourceEnergy (2 * s.re) p := by
  simp_rw [normSq_deletionMellinSource hs]
  rfl

theorem summable_normSq_deletionInsertedSource {s : ℂ} (hs : 1 / 2 < s.re)
    {p : ℕ} (hp : 0 < p) (q : ℕ) :
    Summable (fun n => Complex.normSq (deletionInsertedSource p q s n)) := by
  have hα : 1 < 2 * s.re := by linarith
  have h0 := summable_deletionDirichlet_gram hα (p * q) (p * q)
  have h1 := summable_deletionDirichlet_gram hα p p
  have h2 := (summable_deletionDirichlet_gram hα (p * q) p).mul_left (2 : ℝ)
  simp_rw [deletionInsertedSource_eq_sub hp, Complex.normSq_sub,
    normSq_deletionMellinSource hs, starRingEnd_apply, deletionMellinSource_pair_re hs, pow_two]
  exact (h0.add h1).sub h2

/-- The inserted leg has the exact squared Euler amplitude, not an independent-copy scale. -/
theorem tsum_normSq_deletionInsertedSource {s : ℂ} (hs : 1 / 2 < s.re)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∑' n, Complex.normSq (deletionInsertedSource p q s n) =
      (p : ℝ) ^ 2 * (p : ℝ) ^ (-(2 * s.re)) * deletionSourceEnergy (2 * s.re) q := by
  have hα : 1 < 2 * s.re := by linarith
  have h0 := summable_deletionDirichlet_gram hα (p * q) (p * q)
  have h1 := summable_deletionDirichlet_gram hα p p
  have h2 := (summable_deletionDirichlet_gram hα (p * q) p).mul_left (2 : ℝ)
  simp_rw [deletionInsertedSource_eq_sub hp, Complex.normSq_sub,
    normSq_deletionMellinSource hs, starRingEnd_apply, deletionMellinSource_pair_re hs, pow_two]
  rw [(h0.add h1).tsum_sub h2, h0.tsum_add h1, tsum_mul_left]
  rw [tsum_deletionDirichlet_gram hα (Nat.mul_pos hp hq) (Nat.mul_pos hp hq),
    tsum_deletionDirichlet_gram hα hp hp,
    tsum_deletionDirichlet_gram hα (Nat.mul_pos hp hq) hp,
    Nat.lcm_self, Nat.lcm_self, Nat.lcm_comm (p * q) p,
    Nat.lcm_eq_right (dvd_mul_right p q), deletionSourceEnergy_eq hα hq, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg q)]
  ring

/-- The inserted leg's overlap has absolute admission on the same source chamber. -/
theorem summable_deletionSource_inserted_pair_re {s : ℂ} (hs : 1 / 2 < s.re)
    {p : ℕ} (hp : 0 < p) (q : ℕ) :
    Summable (fun n => (deletionMellinSource p s n *
      star (deletionInsertedSource p q s n)).re) := by
  have h0 := summable_deletionDirichlet_gram (by linarith : 1 < 2 * s.re) p (p * q)
  have h1 := summable_deletionDirichlet_gram (by linarith : 1 < 2 * s.re) p p
  simp_rw [deletionInsertedSource_eq_sub hp, star_sub, mul_sub, Complex.sub_re,
    deletionMellinSource_pair_re hs]
  exact h0.sub h1

/-- Exact signed arithmetic overlap; no endpoint, zero, or positivity input is present. -/
theorem tsum_deletionSource_inserted_pair_re {s : ℂ} (hs : 1 / 2 < s.re)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∑' n, (deletionMellinSource p s n * star (deletionInsertedSource p q s n)).re =
      deletionDirichletMass (2 * s.re) * p * (1 - (p : ℝ)) * (p : ℝ) ^ (-(2 * s.re)) *
        (1 - q * (q : ℝ) ^ (-(2 * s.re))) := by
  have hα : 1 < 2 * s.re := by linarith
  have h0 := summable_deletionDirichlet_gram hα p (p * q)
  have h1 := summable_deletionDirichlet_gram hα p p
  simp_rw [deletionInsertedSource_eq_sub hp, star_sub, mul_sub, Complex.sub_re,
    deletionMellinSource_pair_re hs]
  rw [h0.tsum_sub h1, tsum_deletionDirichlet_gram hα hp (Nat.mul_pos hp hq),
    tsum_deletionDirichlet_gram hα hp hp, Nat.lcm_self,
    Nat.lcm_eq_right (dvd_mul_right p q), Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg q)]
  ring

/-- Every nontrivial deletion first moment in the positive Dirichlet law is positive. -/
theorem deletionDirichletMean_pos {α : ℝ} (hα : 1 < α)
    {p : ℕ} (hp : 1 < p) : 0 < 1 - p * (p : ℝ) ^ (-α) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have heq : (p : ℝ) * (p : ℝ) ^ (-α) = (p : ℝ) ^ (1 - α) := by
    rw [sub_eq_add_neg, Real.rpow_add (by linarith : (0 : ℝ) < p), Real.rpow_one]
  rw [heq]
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith))

/-- Actual composite source legs have strictly destructive interference everywhere right of half. -/
theorem tsum_deletionSource_inserted_pair_re_neg {s : ℂ} (hs : 1 / 2 < s.re)
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    (∑' n, (deletionMellinSource p s n * star (deletionInsertedSource p q s n)).re) < 0 := by
  rw [tsum_deletionSource_inserted_pair_re hs (by omega : 0 < p) (by omega : 0 < q)]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hα : 1 < 2 * s.re := by linarith
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg
        (mul_pos (deletionDirichletMass_pos hα) (by linarith)) (by linarith))
      (Real.rpow_pos_of_pos (by linarith) _))
    (deletionDirichletMean_pos hα hq)

/-- Exact composite energy conservation includes the negative overlap term. -/
theorem deletionSourceEnergy_mul {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    deletionSourceEnergy α (p * q) =
      deletionSourceEnergy α p + (p : ℝ) ^ 2 * (p : ℝ) ^ (-α) * deletionSourceEnergy α q -
        2 * deletionDirichletMass α * p * (p - 1 : ℝ) * (p : ℝ) ^ (-α) *
          (1 - q * (q : ℝ) ^ (-α)) := by
  rw [deletionSourceEnergy_eq hα (Nat.mul_pos hp hq), deletionSourceEnergy_eq hα hp,
    deletionSourceEnergy_eq hα hq, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg q)]
  ring

/-- Independent-copy energy addition is strictly false for the literal arithmetic interleaving. -/
theorem deletionSourceEnergy_mul_lt_independent {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    deletionSourceEnergy α (p * q) <
      deletionSourceEnergy α p + (p : ℝ) ^ 2 * (p : ℝ) ^ (-α) * deletionSourceEnergy α q := by
  rw [deletionSourceEnergy_mul hα (by omega : 0 < p) (by omega : 0 < q)]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : 0 < 2 * deletionDirichletMass α * p * (p - 1 : ℝ) *
      (p : ℝ) ^ (-α) * (1 - q * (q : ℝ) ^ (-α)) := by
    exact mul_pos
      (mul_pos
        (mul_pos (mul_pos (mul_pos (by norm_num) (deletionDirichletMass_pos hα))
          (by linarith)) (by linarith))
        (Real.rpow_pos_of_pos (by linarith) _))
      (deletionDirichletMean_pos hα hq)
  linarith

/-- Actual source interleaving has strictly less energy than its two separate legs. -/
theorem deletionMellinSource_composite_energy_strict {s : ℂ} (hs : 1 / 2 < s.re)
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    (∑' n, Complex.normSq (deletionMellinSource (p * q) s n)) <
      (∑' n, Complex.normSq (deletionMellinSource p s n)) +
        ∑' n, Complex.normSq (deletionInsertedSource p q s n) := by
  rw [tsum_normSq_deletionMellinSource hs, tsum_normSq_deletionMellinSource hs,
    tsum_normSq_deletionInsertedSource hs (by omega : 0 < p) (by omega : 0 < q)]
  exact deletionSourceEnergy_mul_lt_independent (by linarith) hp hq

end RHTower
