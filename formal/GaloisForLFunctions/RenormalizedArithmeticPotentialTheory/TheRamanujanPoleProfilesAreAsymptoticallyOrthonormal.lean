import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanPlacePaysTheArithmeticPoint
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCovarianceCancellation

/-!
# Harmonic orthogonality of Ramanujan pole profiles

The complete-period Ramanujan Gram survives logarithmic averaging. Consequently
the profiles `c_m(n)/sqrt(φ(m)n)` have asymptotically orthonormal finite restrictions
after division of their Gram matrix by `log N`.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open RenormalizedBiarithmeticGeometry

private theorem tendsto_periodic_nat_mean {p : ℕ → ℝ} {q : ℕ}
    (hq : 0 < q) (hper : Function.Periodic p q) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, p n) / (N : ℝ))
      atTop (𝓝 (periodMean p q)) := by
  let b : ℕ → ℝ := fun n => p (n + 1) - periodMean p q
  have hbper : Function.Periodic b q := by
    intro n
    dsimp only [b]
    rw [show n + q + 1 = (n + 1) + q by omega, hper]
  have hshift : (∑ i ∈ range q, p (i + 1)) = ∑ i ∈ range q, p i := by
    simpa only [Nat.add_comm] using sum_range_shift_of_periodic hper 1
  have hbzero : (∑ i ∈ range q, b i) = 0 := by
    simp only [b, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hshift,
      periodMean]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    ring
  have hb (N : ℕ) := abs_sum_range_le_of_periodic hq hbper hbzero N
  have hlim : Tendsto (fun N : ℕ => (∑ i ∈ range N, b i) / (N : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => ?_)
      (show Tendsto (fun N : ℕ => (∑ i ∈ range q, |b i|) / (N : ℝ))
        atTop (𝓝 0) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (show 0 ≤ (N : ℝ) from Nat.cast_nonneg N)]
    exact div_le_div_of_nonneg_right (hb N) (Nat.cast_nonneg N)
  have heq : ∀ᶠ N : ℕ in atTop,
      (∑ i ∈ range N, b i) / (N : ℝ) + periodMean p q =
        (∑ n ∈ Icc 1 N, p n) / (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [_root_.RHTower.RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range]
    simp only [b, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp
    ring
  simpa only [zero_add] using (hlim.add_const (periodMean p q)).congr' heq

/-- A periodic real sequence has the same logarithmic and complete-period means. -/
theorem tendsto_periodic_harmonic_mean {p : ℕ → ℝ} {q : ℕ}
    (hq : 0 < q) (hper : Function.Periodic p q) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, p n / (n : ℝ)) / Real.log N)
      atTop (𝓝 (periodMean p q)) :=
  _root_.RHTower.pm_tendsto_harmonic_average_of_mean (tendsto_periodic_nat_mean hq hper)

/-- The real Ramanujan mode normalized by its complete-period squared mass. -/
def normalizedRamanujanMode (m n : ℕ) : ℝ :=
  ramanujanMode m n / Real.sqrt (m.totient : ℝ)

/-- The normalized Ramanujan mode in the pole gauge. -/
def ramanujanPoleProfile (m n : ℕ) : ℝ :=
  normalizedRamanujanMode m n / Real.sqrt n

theorem normalizedRamanujanMode_periodic {m : ℕ} (hm : 0 < m) :
    Function.Periodic (normalizedRamanujanMode m) m := by
  intro n
  rw [normalizedRamanujanMode, normalizedRamanujanMode, ramanujanMode_periodic hm]

theorem abs_normalizedRamanujanMode_le {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |normalizedRamanujanMode m n| ≤ ∑ j ∈ range m, |normalizedRamanujanMode m j| :=
  abs_le_of_periodic hm (normalizedRamanujanMode_periodic hm) n

theorem periodMean_normalizedRamanujanMode_mul {m l q : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hmq : m ∣ q) (hlq : l ∣ q) (hq : 0 < q) :
    periodMean (fun n => normalizedRamanujanMode m n * normalizedRamanujanMode l n) q =
      if m = l then 1 else 0 := by
  have hfactor : periodMean
      (fun n => normalizedRamanujanMode m n * normalizedRamanujanMode l n) q =
      periodMean (fun n => ramanujanMode m n * ramanujanMode l n) q /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) := by
    simp only [periodMean, normalizedRamanujanMode, div_mul_div_comm, ← sum_div]
    ring
  rw [hfactor, periodMean_ramanujanMode_mul hm hl hmq hlq hq]
  by_cases hml : m = l
  · subst l
    have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
    rw [if_pos rfl, if_pos rfl, ← sq, Real.sq_sqrt hφ.le, div_self hφ.ne']
  · rw [if_neg hml, if_neg hml, zero_div]

/-- Distinct conductors are orthogonal at logarithmic scale on the actual integer interval. -/
theorem tendsto_ramanujanPoleProfile_gram {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) / Real.log N)
      atTop (𝓝 (if m = l then 1 else 0)) := by
  have hpm : Function.Periodic (normalizedRamanujanMode m) (m * l) := by
    simpa only [Nat.cast_id, Nat.mul_comm] using (normalizedRamanujanMode_periodic hm).nat_mul l
  have hpl : Function.Periodic (normalizedRamanujanMode l) (m * l) := by
    simpa only [Nat.cast_id] using (normalizedRamanujanMode_periodic hl).nat_mul m
  have hper : Function.Periodic
      (fun n => normalizedRamanujanMode m n * normalizedRamanujanMode l n) (m * l) := by
    intro n
    exact congrArg₂ (· * ·) (hpm n) (hpl n)
  have h := tendsto_periodic_harmonic_mean (Nat.mul_pos hm hl) hper
  rw [periodMean_normalizedRamanujanMode_mul hm hl (dvd_mul_right m l)
    (dvd_mul_left l m) (Nat.mul_pos hm hl)] at h
  refine h.congr fun N => ?_
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [ramanujanPoleProfile, ramanujanPoleProfile, div_mul_div_comm, ← sq,
    Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Every positive-conductor pole profile has squared mass asymptotic to `log N`. -/
theorem tendsto_ramanujanPoleProfile_sq {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2) / Real.log N)
      atTop (𝓝 1) := by
  simpa only [eq_self_iff_true, ite_true, pow_two] using tendsto_ramanujanPoleProfile_gram hm hm

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

