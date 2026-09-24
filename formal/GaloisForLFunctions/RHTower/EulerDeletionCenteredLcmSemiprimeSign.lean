import GaloisForLFunctions.RHTower.EulerDeletionCenteredLcmIncidence

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction

namespace RHTower

private theorem prime_mul_divisors {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p * q).divisors = ({1, p, q, p * q} : Finset ℕ) := by
  ext d
  simp [Nat.divisors_mul, hp.divisors, hq.divisors, Finset.mem_mul, mul_comm]
  tauto

private theorem one_cell_discrepancy (d k : ℕ) (hk : 0 < k) :
    DeletionResidueMartingale.divisorWindowDiscrepancy d (k - 1) 1 =
      (d : ℝ)⁻¹ - divisorIndicator d k := by
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  unfold DeletionResidueMartingale.divisorWindowDiscrepancy divisorIndicator
  rw [show (k - 1) + 1 = k from hk']
  have hinterval : Ioc (k - 1) k = ({k} : Finset ℕ) := by
    simpa only [hk'] using Nat.Ioc_succ_singleton (k - 1)
  rw [hinterval]
  by_cases hd : d ∣ k <;> simp [div_eq_mul_inv, hd, Finset.filter_singleton]

/-- The actual complete semiprime lcm fibre is a signed quadratic in the three
divisor-dependent physical discrepancies, not a single incidence indicator. -/
theorem physicalCenteredLcmFibre_semiprime_eq {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (t H : ℕ) :
    physicalCenteredLcmFibre (p * q) t H t H =
      let D : ℕ → ℝ := fun d =>
        DeletionResidueMartingale.divisorWindowDiscrepancy d t H
      D (p * q) ^ (2 : ℕ) + 2 * D p * D q -
        2 * D (p * q) * (D p + D q) := by
  have hpq : p.Coprime q := (Nat.coprime_primes hp hq).mpr hne
  have hmu : ((moebius (p * q) : ℤ) : ℝ) = 1 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpq,
      ArithmeticFunction.moebius_apply_prime hp,
      ArithmeticFunction.moebius_apply_prime hq]
    norm_num
  have hone : DeletionResidueMartingale.divisorWindowDiscrepancy 1 t H = 0 :=
    DeletionResidueMartingale.divisorWindowDiscrepancy_eq_zero_of_dvd
      1 t H (by omega) (one_dvd H)
  have hplt : p < p * q := (Nat.lt_mul_iff_one_lt_right hp.pos).2 hq.one_lt
  have hqlt : q < p * q := by
    rw [mul_comm]
    exact (Nat.lt_mul_iff_one_lt_right hq.pos).2 hp.one_lt
  have hpmul : Nat.lcm p (p * q) = p * q := Nat.lcm_eq_right (dvd_mul_right p q)
  have hqmul : Nat.lcm q (p * q) = p * q := by
    rw [mul_comm]
    exact Nat.lcm_eq_right (dvd_mul_right q p)
  have hqpmul : Nat.lcm q p = p * q := by
    rw [Nat.lcm_comm]
    exact hpq.lcm_eq_mul
  have hmulp : Nat.lcm (p * q) p = p * q := by
    rw [Nat.lcm_comm]
    exact hpmul
  have hmulq : Nat.lcm (p * q) q = p * q := by
    rw [Nat.lcm_comm]
    exact hqmul
  unfold physicalCenteredLcmFibre
  rw [prime_mul_divisors hp hq, Finset.sum_filter, Finset.sum_product]
  simp [hone, hmu, hne, hplt.ne, hqlt.ne,
    hpq.lcm_eq_mul, hqpmul, hpmul, hqmul, hmulp, hmulq,
    ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hq]
  ring

/-- Exact negative semiprime diagonal at the one-cell window ending at `p`. -/
theorem physicalCenteredLcmFibre_semiprime_oneCell_eq {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    physicalCenteredLcmFibre (p * q) (p - 1) 1 (p - 1) 1 =
      (1 - 2 * (p : ℝ) - 2 * ((p : ℝ) - 1) ^ (2 : ℕ) * (q : ℝ)) /
        ((p : ℝ) ^ (2 : ℕ) * (q : ℝ) ^ (2 : ℕ)) := by
  have hqnot : ¬q ∣ p := by
    intro h
    exact hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have hpqnot : ¬p * q ∣ p := by
    intro h
    have hlt : p < p * q := (Nat.lt_mul_iff_one_lt_right hp.pos).2 hq.one_lt
    exact (Nat.not_le_of_gt hlt) (Nat.le_of_dvd hp.pos h)
  have hDp : DeletionResidueMartingale.divisorWindowDiscrepancy p (p - 1) 1 =
      (p : ℝ)⁻¹ - 1 := by
    rw [one_cell_discrepancy p p hp.pos]
    simp [divisorIndicator]
  have hDq : DeletionResidueMartingale.divisorWindowDiscrepancy q (p - 1) 1 =
      (q : ℝ)⁻¹ := by
    rw [one_cell_discrepancy q p hp.pos]
    simp [divisorIndicator, hqnot]
  have hDpq : DeletionResidueMartingale.divisorWindowDiscrepancy (p * q) (p - 1) 1 =
      ((p * q : ℕ) : ℝ)⁻¹ := by
    rw [one_cell_discrepancy (p * q) p hp.pos]
    simp [divisorIndicator, hpqnot]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpR0 : (p : ℝ) ≠ 0 := ne_of_gt hpR
  have hqR0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  rw [physicalCenteredLcmFibre_semiprime_eq hp hq hne]
  dsimp
  rw [hDp, hDq, hDpq, Nat.cast_mul, mul_inv_rev]
  have hid : ((q : ℝ)⁻¹ * (p : ℝ)⁻¹) ^ (2 : ℕ) +
      2 * ((p : ℝ)⁻¹ - 1) * (q : ℝ)⁻¹ -
      2 * ((q : ℝ)⁻¹ * (p : ℝ)⁻¹) *
        (((p : ℝ)⁻¹ - 1) + (q : ℝ)⁻¹) =
      (1 - 2 * (p : ℝ) - 2 * ((p : ℝ) - 1) ^ (2 : ℕ) * (q : ℝ)) /
        ((p : ℝ) ^ (2 : ℕ) * (q : ℝ) ^ (2 : ℕ)) := by
    field_simp
    ring
  exact hid

/-- Unlike prime complete fibres, some physical semiprime diagonal fibres are
strictly negative. This is local cancellation, not an EDQ signed upper bound. -/
theorem physicalCenteredLcmFibre_semiprime_oneCell_neg {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    physicalCenteredLcmFibre (p * q) (p - 1) 1 (p - 1) 1 < 0 := by
  rw [physicalCenteredLcmFibre_semiprime_oneCell_eq hp hq hne]
  have hpR2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  apply div_neg_of_neg_of_pos
  · have hnonneg : 0 ≤ ((p : ℝ) - 1) ^ (2 : ℕ) * (q : ℝ) :=
      mul_nonneg (sq_nonneg _) hqR.le
    linarith
  · positivity

end RHTower
