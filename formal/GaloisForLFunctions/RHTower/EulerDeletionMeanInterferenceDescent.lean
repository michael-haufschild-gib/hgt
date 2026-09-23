import GaloisForLFunctions.RHTower.EulerDeletionCompositeInterference
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleCylinderSquareNoGo

/-!
# Arithmetic mean descent of Euler-deletion interference

The literal inserted coefficient is the difference of product-modulus and original
coefficients. Its overlap with the original coefficient is a fixed multiple of that
difference, hence has arithmetic mean zero. Diagonal and inserted square means are
p-1 and p(q-1), giving exact conservation pq-1=(p-1)+p(q-1).

Recovering the prescribed Mellin weight before averaging gives the same positive
coefficient masses for every complex exponent. The Euler amplitude, weight recovery,
and sampling density combine to p independently of the exponent. Thus this particular
interference-free quotient does not retain the literal weighted Dirichlet bracket or
select the critical line. No zeta zero, continuation, or renormalized positivity premise
enters the construction.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace RHTower.DeletionMeanDescent

def meanPrefix (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, f (n+1)) / N

def coefficient (p n : ℕ) : ℝ := blockDeletionCoefficient p n

/-- Literal inserted coefficient, before any Mellin weight or zero selection. -/
def insertedCoefficient (p q n : ℕ) : ℝ := coefficient (p*q) n - coefficient p n

theorem meanPrefix_add (f g : ℕ → ℝ) (N : ℕ) :
    meanPrefix (fun n => f n + g n) N = meanPrefix f N + meanPrefix g N := by
  simp [meanPrefix, Finset.sum_add_distrib, add_div]

theorem meanPrefix_sub (f g : ℕ → ℝ) (N : ℕ) :
    meanPrefix (fun n => f n - g n) N = meanPrefix f N - meanPrefix g N := by
  simp [meanPrefix, Finset.sum_sub_distrib, sub_div]

theorem meanPrefix_mul (c : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    meanPrefix (fun n => c * f n) N = c * meanPrefix f N := by
  simp [meanPrefix, ← Finset.mul_sum, mul_div_assoc]

theorem meanPrefix_const (c : ℝ) (N : ℕ) :
    meanPrefix (fun _ => c) N = c * ((N : ℝ) / N) := by
  simp [meanPrefix]
  ring

theorem meanPrefix_coefficient_eq_mod (p N : ℕ) :
    meanPrefix (coefficient p) N = ((N % p : ℕ) : ℝ) / N := by
  unfold meanPrefix coefficient
  rw [← Int.cast_sum]
  change ((deletionCoeffPartialSum p N : ℤ) : ℝ) / N = _
  rw [deletionCoeffPartialSum_eq_mod, Int.cast_natCast]

theorem tendsto_mean_coefficient {p : ℕ} (hp : 0 < p) :
    Tendsto (meanPrefix (coefficient p)) atTop (nhds 0) := by
  exact (tendsto_mod_div_atTop_nhds_zero_nat hp).congr
    (fun N => (meanPrefix_coefficient_eq_mod p N).symm)

theorem coefficient_sq (p n : ℕ) :
    coefficient p n ^ 2 = ((p : ℝ)-1) + (2-(p : ℝ)) * coefficient p n := by
  dsimp [coefficient]
  exact_mod_cast blockDeletionCoefficient_sq_eq p n

/-- Nontrivial diagonal square mass survives the zero-mean quotient. -/
theorem tendsto_mean_coefficient_sq {p : ℕ} (hp : 0 < p) :
    Tendsto (meanPrefix (fun n => coefficient p n ^ 2)) atTop (nhds ((p : ℝ)-1)) := by
  have h := ((tendsto_natCast_div_add_atTop (0 : ℝ)).const_mul ((p : ℝ)-1)).add
    ((tendsto_mean_coefficient hp).const_mul (2-(p : ℝ)))
  have hid (N : ℕ) : meanPrefix (fun n => coefficient p n ^ 2) N =
      ((p : ℝ)-1)*((N : ℝ)/(N+0)) + (2-(p : ℝ))*meanPrefix (coefficient p) N := by
    simp_rw [coefficient_sq, meanPrefix_add, meanPrefix_mul, meanPrefix_const]
    simp only [add_zero]
  simpa using h.congr (fun N => (hid N).symm)

/-- The overlap is itself a zero-mean deletion difference, not an independent copy. -/
theorem coefficient_mul_inserted (p q n : ℕ) :
    coefficient p n * insertedCoefficient p q n =
      (1-(p : ℝ)) * insertedCoefficient p q n := by
  by_cases hp : p ∣ n
  · simp [coefficient, blockDeletionCoefficient, hp]
  · have hpq : ¬p*q ∣ n := fun h => hp ((dvd_mul_right p q).trans h)
    simp [insertedCoefficient, coefficient, blockDeletionCoefficient, hp, hpq]

theorem tendsto_mean_interference {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (meanPrefix (fun n => coefficient p n * insertedCoefficient p q n))
      atTop (nhds 0) := by
  have h := ((tendsto_mean_coefficient (Nat.mul_pos hp hq)).sub
    (tendsto_mean_coefficient hp)).const_mul (1-(p : ℝ))
  have hid (N : ℕ) : meanPrefix (fun n => coefficient p n * insertedCoefficient p q n) N =
      (1-(p : ℝ))*(meanPrefix (coefficient (p*q)) N - meanPrefix (coefficient p) N) := by
    unfold meanPrefix
    simp_rw [coefficient_mul_inserted, insertedCoefficient]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  simpa using h.congr (fun N => (hid N).symm)

theorem insertedCoefficient_sq (p q n : ℕ) :
    insertedCoefficient p q n ^ 2 = coefficient (p*q) n ^ 2 - coefficient p n ^ 2 -
      2 * (coefficient p n * insertedCoefficient p q n) := by
  dsimp [insertedCoefficient]
  ring

/-- Sampling on multiples leaves exactly p times the inner coefficient variance. -/
theorem tendsto_mean_inserted_sq {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (meanPrefix (fun n => insertedCoefficient p q n ^ 2))
      atTop (nhds ((p : ℝ)*((q : ℝ)-1))) := by
  have h := ((tendsto_mean_coefficient_sq (Nat.mul_pos hp hq)).sub
    (tendsto_mean_coefficient_sq hp)).sub ((tendsto_mean_interference hp hq).const_mul 2)
  have hid (N : ℕ) : meanPrefix (fun n => insertedCoefficient p q n ^ 2) N =
      (meanPrefix (fun n => coefficient (p*q) n ^ 2) N -
        meanPrefix (fun n => coefficient p n ^ 2) N) -
      2 * meanPrefix (fun n => coefficient p n * insertedCoefficient p q n) N := by
    simp_rw [insertedCoefficient_sq, meanPrefix_sub, meanPrefix_mul]
  convert h.congr (fun N => (hid N).symm) using 1
  push_cast
  ring

/-- Exact source conservation in the coefficient-mean quotient, in either factorization order. -/
theorem coefficient_mean_factorization (p q : ℕ) :
    (p*q : ℝ)-1 = ((p : ℝ)-1) + p*((q : ℝ)-1) ∧
    (p*q : ℝ)-1 = ((q : ℝ)-1) + q*((p : ℝ)-1) := by
  constructor <;> ring

/-- Strip only the prescribed Mellin factor from a literal weighted jump. -/
theorem unweight_mellin_normSq (a : ℝ) (s : ℂ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (2*s.re) * Complex.normSq ((a : ℂ)*(n : ℂ)^(-s)) = a^(2 : ℕ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm : ‖(n : ℂ)^(-s)‖ = (n : ℝ)^(-s.re) := by
    simpa only [Complex.ofReal_natCast, Complex.neg_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos hnR (-s)
  rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq, hnorm,
    ← Real.rpow_mul_natCast hnR.le (-s.re) 2]
  calc
    (n : ℝ)^(2*s.re) * (a*a * (n : ℝ)^(-s.re*2)) =
        a^(2 : ℕ) * ((n : ℝ)^(2*s.re) * (n : ℝ)^(-s.re*2)) := by ring
    _ = a^(2 : ℕ) := by rw [← Real.rpow_add hnR]; ring_nf; simp

def recoveredMass (s : ℂ) (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  meanPrefix (fun n => (n : ℝ)^(2*s.re) * Complex.normSq (f n)) N

/-- The same weight recovery keeps the exact coefficient product, including its sign. -/
theorem unweight_mellin_pair (a b : ℝ) (s : ℂ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ)^(2*s.re) *
      (((a : ℂ)*(n : ℂ)^(-s)) * star ((b : ℂ)*(n : ℂ)^(-s))).re = a*b := by
  let z : ℂ := (n : ℂ)^(-s)
  have hpair : (((a : ℂ)*z) * star ((b : ℂ)*z)).re = a*b*Complex.normSq z := by
    change (((a : ℂ)*z) * (starRingEnd ℂ) ((b : ℂ)*z)).re = _
    rw [map_mul, Complex.conj_ofReal]
    have heq : ((a : ℂ)*z) * ((b : ℂ)*(starRingEnd ℂ) z) =
        ((a*b : ℝ) : ℂ)*(z*(starRingEnd ℂ) z) := by push_cast; ring
    rw [heq, Complex.mul_conj]
    simp
  have hunit := unweight_mellin_normSq 1 s hn
  simp only [Complex.ofReal_one, one_mul, one_pow] at hunit
  change (n : ℝ)^(2*s.re) * (((a : ℂ)*z)*star ((b : ℂ)*z)).re = a*b
  rw [hpair]
  calc
    _ = a*b*((n : ℝ)^(2*s.re)*Complex.normSq z) := by ring
    _ = a*b := by rw [hunit, mul_one]

theorem recoveredMass_source (p : ℕ) (s : ℂ) (N : ℕ) :
    recoveredMass s (deletionMellinSource p s) N =
      meanPrefix (fun n => coefficient p n ^ 2) N := by
  unfold recoveredMass meanPrefix
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact unweight_mellin_normSq (coefficient p (n+1)) s (Nat.succ_pos n)

theorem insertedSource_coefficient {p : ℕ} (hp : 0 < p)
    (q : ℕ) (s : ℂ) (n : ℕ) :
    deletionInsertedSource p q s n =
      (insertedCoefficient p q n : ℂ) * (n : ℂ)^(-s) := by
  rw [deletionInsertedSource_eq_sub hp]
  dsimp [deletionMellinSource, insertedCoefficient, coefficient]
  push_cast
  ring

theorem recoveredMass_inserted {p : ℕ} (hp : 0 < p) (q : ℕ) (s : ℂ) (N : ℕ) :
    recoveredMass s (deletionInsertedSource p q s) N =
      meanPrefix (fun n => insertedCoefficient p q n ^ 2) N := by
  unfold recoveredMass meanPrefix
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  rw [insertedSource_coefficient hp]
  exact unweight_mellin_normSq (insertedCoefficient p q (n+1)) s (Nat.succ_pos n)

/-- Literal source interference vanishes after coefficient recovery and arithmetic averaging. -/
theorem recovered_interference_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (s : ℂ) :
    Tendsto (meanPrefix (fun n => (n : ℝ)^(2*s.re) *
      (deletionMellinSource p s n * star (deletionInsertedSource p q s n)).re))
      atTop (nhds 0) := by
  apply (tendsto_mean_interference hp hq).congr
  intro N
  unfold meanPrefix
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  rw [insertedSource_coefficient hp]
  exact (unweight_mellin_pair (coefficient p (n+1))
    (insertedCoefficient p q (n+1)) s (Nat.succ_pos n)).symm

/-- Weight recovery and the density of multiples exactly cancel the exponent dependence. -/
theorem recovered_dilation_factor (p : ℝ) (hp : 0 < p) (σ : ℝ) :
    p^(2-2*σ) * p^(2*σ) / p = p := by
  rw [← Real.rpow_add hp]
  norm_num
  field_simp

/-- The interference-free nonzero coefficient bracket exists at every complex exponent. -/
theorem recovered_source_mass_conservation {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (s : ℂ) :
    Tendsto (recoveredMass s (deletionMellinSource p s)) atTop (nhds ((p : ℝ)-1)) ∧
    Tendsto (recoveredMass s (deletionInsertedSource p q s))
      atTop (nhds ((p : ℝ)*((q : ℝ)-1))) ∧
    Tendsto (recoveredMass s (deletionMellinSource (p*q) s))
      atTop (nhds ((p*q : ℝ)-1)) := by
  refine ⟨(tendsto_mean_coefficient_sq hp).congr
    (fun N => (recoveredMass_source p s N).symm),
    (tendsto_mean_inserted_sq hp hq).congr
    (fun N => (recoveredMass_inserted hp q s N).symm), ?_⟩
  have h := (tendsto_mean_coefficient_sq (Nat.mul_pos hp hq)).congr
    (fun N => (recoveredMass_source (p*q) s N).symm)
  simpa only [Nat.cast_mul] using h

end RHTower.DeletionMeanDescent

