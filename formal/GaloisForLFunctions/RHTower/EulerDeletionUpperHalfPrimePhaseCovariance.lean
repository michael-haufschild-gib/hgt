import GaloisForLFunctions.RHTower.EulerDeletionUpperHalfPhysicalPrimeSupport
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeWordPeriodicity
/-!
# Upper-half EDQ physical prime-phase covariance

After the physical old-cofactor boundary is recombined, each surviving prime window
prefix has period `p` in the starting phase, rather than the `p * clock L` period
of its separated reduced-residue coefficient. Distinct prime phases are orthogonal
over one `p*q` period; every incomplete or geometrically weighted prefix has
an explicit `p*q` bound. These bounds concern the prime residual component, not
the full normalized martingale drift.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace RHTower.DeletionPrimeWindowPhase

def phase (p H t : ℕ) : ℝ :=
  (((t + H) % p : ℕ) : ℝ) / (p : ℝ) - ((t % p : ℕ) : ℝ) / (p : ℝ)

theorem phase_periodic (p H : ℕ) : Function.Periodic (phase p H) p := by
  intro t
  simp [phase, Nat.add_assoc, Nat.add_mod]

private theorem sum_range_periodic_shift {f : ℕ → ℝ} {p : ℕ}
    (hf : Function.Periodic f p) (H : ℕ) :
    (∑ t ∈ range p, f (t + H)) = ∑ t ∈ range p, f t := by
  induction H with
  | zero => simp
  | succ H ih =>
    have h := Finset.sum_range_succ' (fun j => f (j + H)) p
    rw [Finset.sum_range_succ] at h
    have hperiod : f (p + H) = f H := by
      simpa [Nat.add_comm] using hf H
    rw [hperiod] at h
    have hstep : (∑ t ∈ range p, f (t + (H + 1))) =
        ∑ t ∈ range p, f (t + H) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
    exact hstep.trans ih

theorem phase_mean_zero (p H : ℕ) :
    ∑ t ∈ range p, phase p H t = 0 := by
  have hf : Function.Periodic (fun t : ℕ => ((t % p : ℕ) : ℝ)) p := by
    intro t
    simp
  have hsum : (∑ t ∈ range p, (((t + H) % p : ℕ) : ℝ)) =
      ∑ t ∈ range p, ((t % p : ℕ) : ℝ) :=
    sum_range_periodic_shift hf H
  simp only [phase, Finset.sum_sub_distrib, ← Finset.sum_div, hsum, sub_self]

theorem phase_pair_period_sum_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p.Coprime q) (H K : ℕ) :
    ∑ t ∈ range (p * q), phase p H t * phase q K t = 0 := by
  rw [DeletionCoprimeWords.coprime_period_sum_mul hp hq hpq
    (phase_periodic p H) (phase_periodic q K),
    phase_mean_zero, zero_mul]

theorem phase_pair_periodic (p q H K : ℕ) :
    Function.Periodic (fun t => phase p H t * phase q K t) (p * q) := by
  have hpP : Function.Periodic (phase p H) (p * q) := by
    simpa [Nat.mul_comm] using (phase_periodic p H).nat_mul q
  have hqP : Function.Periodic (phase q K) (p * q) := by
    simpa [Nat.mul_comm] using (phase_periodic q K).nat_mul p
  intro t
  simp only [hpP t, hqP t]

theorem phase_abs_le_one {p : ℕ} (hp : 0 < p) (H t : ℕ) :
    |phase p H t| ≤ 1 := by
  have h := DeletionResidueMartingale.interval_multiple_discrepancy_abs_lt_one
    p t H hp
  rw [DeletionResidueMartingale.interval_multiple_discrepancy_eq_remainder
    p t H hp] at h
  exact le_of_lt (by simpa [phase] using h)

theorem phase_pair_prefix_abs_le_period {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p.Coprime q) (H K M : ℕ) :
    |∑ t ∈ range M, phase p H t * phase q K t| ≤ (p * q : ℕ) := by
  have hdecomp := DeletionResidueMartingale.sum_range_periodic_beta_div_mod
    (fun t => phase p H t * phase q K t) (p * q) M 1
      (phase_pair_periodic p q H K)
  simp [phase_pair_period_sum_zero hp hq hpq H K] at hdecomp
  rw [hdecomp]
  calc
    |∑ t ∈ range (M % (p * q)), phase p H t * phase q K t| ≤
        ∑ t ∈ range (M % (p * q)), |phase p H t * phase q K t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ range (M % (p * q)), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      have hp1 := phase_abs_le_one hp H t
      have hq1 := phase_abs_le_one hq K t
      simpa using
        (mul_le_mul hp1 hq1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
    _ = (M % (p * q) : ℕ) := by simp
    _ ≤ (p * q : ℕ) := by exact_mod_cast (Nat.mod_lt M (Nat.mul_pos hp hq)).le

private theorem sum_range_mul_eq_prefix_last_add_sum_prefix_mul_sub
    (d w : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ range (N + 1), d j * w j =
      (∑ i ∈ range (N + 1), d i) * w N +
        ∑ j ∈ range N,
          (∑ i ∈ range (j + 1), d i) * (w j - w (j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Finset.sum_range_succ]
    ring

theorem phase_pair_weighted_prefix_abs_le_period {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    (H K M : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |∑ t ∈ range M, phase p H t * phase q K t * x ^ t| ≤ (p * q : ℕ) := by
  let f : ℕ → ℝ := fun t => phase p H t * phase q K t
  cases M with
  | zero => simp; positivity
  | succ N =>
    change |∑ t ∈ range (N + 1), f t * x ^ t| ≤ (p * q : ℕ)
    rw [sum_range_mul_eq_prefix_last_add_sum_prefix_mul_sub f (fun t => x ^ t) N]
    have hprefix (k : ℕ) : |∑ t ∈ range k, f t| ≤ (p * q : ℕ) :=
      phase_pair_prefix_abs_le_period hp hq hpq H K k
    have hpow : 0 ≤ x ^ N := pow_nonneg hx0 _
    have hlast : |(∑ i ∈ range (N + 1), f i) * x ^ N| ≤
        (p * q : ℕ) * x ^ N := by
      rw [abs_mul, abs_of_nonneg hpow]
      exact mul_le_mul_of_nonneg_right (hprefix (N + 1)) hpow
    have hterm (j : ℕ) :
        |(∑ i ∈ range (j + 1), f i) * (x ^ j - x ^ (j + 1))| ≤
          (p * q : ℕ) * (x ^ j - x ^ (j + 1)) := by
      have hdiff : 0 ≤ x ^ j - x ^ (j + 1) := by
        calc
          0 ≤ x ^ j * (1 - x) :=
            mul_nonneg (pow_nonneg hx0 _) (sub_nonneg.mpr hx1)
          _ = x ^ j - x ^ (j + 1) := by rw [pow_succ]; ring
      rw [abs_mul, abs_of_nonneg hdiff]
      exact mul_le_mul_of_nonneg_right (hprefix (j + 1)) hdiff
    have htail :
        |∑ j ∈ range N,
          (∑ i ∈ range (j + 1), f i) * (x ^ j - x ^ (j + 1))| ≤
        ∑ j ∈ range N, (p * q : ℕ) * (x ^ j - x ^ (j + 1)) :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j _ => hterm j)
    have hgeom : (1 - x) * ∑ j ∈ range N, x ^ j = 1 - x ^ N := by
      linear_combination -mul_geom_sum x N
    have hsum : ∑ j ∈ range N, (x ^ j - x ^ (j + 1)) =
        (1 - x) * ∑ j ∈ range N, x ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring
    calc
      |(∑ i ∈ range (N + 1), f i) * x ^ N +
        ∑ j ∈ range N,
          (∑ i ∈ range (j + 1), f i) * (x ^ j - x ^ (j + 1))| ≤
        |(∑ i ∈ range (N + 1), f i) * x ^ N| +
          |∑ j ∈ range N,
            (∑ i ∈ range (j + 1), f i) * (x ^ j - x ^ (j + 1))| :=
        abs_add_le _ _
      _ ≤ (p * q : ℕ) * x ^ N +
          ∑ j ∈ range N, (p * q : ℕ) * (x ^ j - x ^ (j + 1)) :=
        add_le_add hlast htail
      _ = (p * q : ℕ) * (x ^ N + (1 - x) * ∑ j ∈ range N, x ^ j) := by
        rw [← Finset.mul_sum, hsum]
        ring
      _ = (p * q : ℕ) := by rw [hgeom]; ring

end RHTower.DeletionPrimeWindowPhase
