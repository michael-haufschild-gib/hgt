import GaloisForLFunctions.HyperbolicArakelovTheory.ThePrimeFibresRecoverArithmeticContact
import GaloisForLFunctions.HyperbolicArakelovTheory.TheGreenDampingOnSmoothProbes

/-!
# Translated finite prime Green ladders

Average a finite prime ladder over real translations of a compact packet.
The continuum diagonal is exactly its L² mass. The complement at the upper
KMS bound is positive and has explicit triangular prime-power correlations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
open ArithmeticIntersectionTheory
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm

open FullAdelic AdelicGreen CoupledProductObstruction in
/-- The matrix being averaged is the actual normalized point-source kernel on a prime fibre. -/
theorem prime_ladder_entry (p : PrimeFibres.Prime) (i j : ℕ) :
    Real.log p.1 * (((p.1 : ℝ) - 1) / Real.sqrt p.1) *
      PrimeFibres.fibreGreen p
        (finitePoint (upperDegree ⟨p.1 ^ i, pow_pos p.2.pos i⟩))
        (finitePoint (upperDegree ⟨p.1 ^ j, pow_pos p.2.pos j⟩)) =
      Real.log p.1 * kmsEntry (1 / Real.sqrt p.1) i j := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  have ho (k : ℕ) : ordCompl[p.1] (p.1 ^ k) = 1 := by
    simpa only [mul_one, Nat.factorization_one, Finsupp.zero_apply, pow_zero, Nat.div_one]
      using Nat.ordCompl_self_pow_mul 1 k p.2
  have hf := (PrimeFibres.sameFibre_degree p
    ⟨p.1 ^ i, pow_pos p.2.pos i⟩ ⟨p.1 ^ j, pow_pos p.2.pos j⟩).mpr ((ho i).trans (ho j).symm)
  rw [PrimeFibres.fibreGreen, if_pos hf, mul_assoc, PrimeFibres.normalized_localGreen]
  change Real.log p.1 * localFactor p (principalVertex (upperDegree _) p)
    (principalVertex (upperDegree _) p) = _
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hq : (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt p.1 := by
    rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow, one_div]
  have ht (k : ℕ) : treeGreen p.1 (1 / 2) k =
      treeGreen p.1 (1 / 2) 0 * (1 / Real.sqrt p.1) ^ k := by
    simp only [treeGreen, pow_zero, mul_one, hq]
  have hc : treeGreen p.1 (1 / 2) 0 ≠ 0 := by
    rw [← localGreen_self p (1 / 2) (baseVertex p)]
    exact (localGreen_pos p (by norm_num) _ _).ne'
  rw [localFactor_upperDegree_eq_treeGreen, ht, mul_div_cancel_left₀ _ hc]
  change Real.log p.1 * (1 / Real.sqrt p.1) ^
    (((p.1 ^ i).factorization p.1 : ℤ) - (p.1 ^ j).factorization p.1).natAbs = _
  simp only [p.2.factorization_pow, Finsupp.single_eq_same, kmsEntry]
  congr 2
  omega

private theorem toeplitz_sum (h : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, h (max i j - min i j)) =
      (N : ℝ) * h 0 + 2 * ∑ k ∈ Finset.range N, ((N : ℝ) - (k + 1)) * h (k + 1) := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, mul_zero, add_zero]
  | succ N ih =>
    have hrow : (∑ i ∈ Finset.range N, h (max i N - min i N)) =
        ∑ k ∈ Finset.range N, h (k + 1) := by
      calc
        _ = ∑ i ∈ Finset.range N, h (N - i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiN := (Finset.mem_range.mp hi).le
          rw [max_eq_right hiN, min_eq_left hiN]
        _ = ∑ i ∈ Finset.range N, h (N - (N - 1 - i)) :=
          (Finset.sum_range_reflect (fun i => h (N - i)) N).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          have hiN := Finset.mem_range.mp hi
          omega
    have hcol : (∑ j ∈ Finset.range N, h (max N j - min N j)) =
        ∑ k ∈ Finset.range N, h (k + 1) := by
      simpa only [max_comm N, min_comm N] using hrow
    rw [Finset.sum_range_succ]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib, ih, hrow, hcol]
    simp only [max_self, min_self, Nat.sub_self, Nat.cast_add, Nat.cast_one,
      sub_self, zero_mul, add_zero]
    have he : (∑ k ∈ Finset.range N, ((N : ℝ) + 1 - (k + 1)) * h (k + 1)) =
        (∑ k ∈ Finset.range N, ((N : ℝ) - (k + 1)) * h (k + 1)) +
          ∑ k ∈ Finset.range N, h (k + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he]
    ring

private theorem integrable_shift_pair {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (a b : ℝ) :
    Integrable (fun u => f (u + a) * f (u + b)) :=
  ((hf.comp (continuous_add_const a)).mul (hf.comp (continuous_add_const b))).integrable_of_hasCompactSupport
    ((hfc.comp_homeomorph (Homeomorph.addRight a)).mul_right)

private theorem integral_shift_pair (f : ℝ → ℝ) (a b : ℝ) :
    (∫ u, f (u + a) * f (u + b)) = autocorr f (b - a) := by
  rw [autocorr, ← integral_add_right_eq_self (fun u => f u * f (u + (b - a))) a]
  congr 1
  funext u
  rw [show u + a + (b - a) = u + b by ring]

private theorem autocorr_step (f : ℝ → ℝ) (L : ℝ) (i j : ℕ) :
    autocorr f ((j : ℝ) * L - i * L) =
      autocorr f ((max i j - min i j : ℕ) * L) := by
  rcases le_total i j with hij | hji
  · rw [max_eq_right hij, min_eq_left hij, Nat.cast_sub hij]
    congr 1
    ring
  · rw [max_eq_left hji, min_eq_right hji, Nat.cast_sub hji,
      show (j : ℝ) * L - i * L = -(((i : ℝ) - j) * L) by ring, autocorr_neg]

private theorem integrable_ladder {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (q L : ℝ) (N : ℕ) :
    Integrable (fun u => kmsForm q N (fun i => f (u + i * L))) := by
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (integrable_shift_pair hf hfc _ _).mul_const _

/-- Translation averaging turns the ladder matrix into triangular correlations. -/
theorem integral_ladder {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (q L : ℝ) (N : ℕ) :
    (∫ u, kmsForm q N (fun i => f (u + i * L))) =
      (N : ℝ) * (∫ u, f u ^ 2) +
        2 * ∑ k ∈ Finset.range N,
          ((N : ℝ) - (k + 1)) * (q ^ (k + 1) * autocorr f ((k + 1 : ℕ) * L)) := by
  have hsum : (∫ u, kmsForm q N (fun i => f (u + i * L))) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        q ^ (max i j - min i j) * autocorr f ((max i j - min i j : ℕ) * L) := by
    rw [show (fun u => kmsForm q N (fun i => f (u + i * L))) =
      (fun u => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        f (u + i * L) * f (u + j * L) * kmsEntry q i j) from rfl]
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _
      (fun j hj => (integrable_shift_pair hf hfc _ _).mul_const _))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (fun j hj => (integrable_shift_pair hf hfc _ _).mul_const _)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_mul_const, integral_shift_pair, autocorr_step, kmsEntry, mul_comm]
  rw [hsum, toeplitz_sum (fun k => q ^ k * autocorr f ((k : ℝ) * L))]
  simp only [pow_zero, Nat.cast_zero, zero_mul, one_mul, autocorr, add_zero, ← pow_two]

/-- Translation-averaged prime ladder energy. -/
def greenEnergy (p N : ℕ) (f : ℝ → ℝ) : ℝ :=
  Real.log p / N * ∫ u,
    kmsForm (1 / Real.sqrt p) N (fun i => f (u + i * Real.log p))

/-- The upper spectral complement of the translated Green ladder. -/
def positiveChannel (p N : ℕ) (f : ℝ → ℝ) : ℝ :=
  Real.log p * ((1 + 1 / Real.sqrt p) / (1 - 1 / Real.sqrt p)) *
    (∫ u, f u ^ 2) - greenEnergy p N f

/-- The continuum mass coefficient left after removing the ladder's unit diagonal. -/
def capacity (p : ℕ) : ℝ := 2 * Real.log p / (Real.sqrt p - 1)

theorem capacity_eq {p : ℕ} (hp : p.Prime) :
    capacity p = Real.log p * ((1 + 1 / Real.sqrt p) / (1 - 1 / Real.sqrt p) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hs : 1 < Real.sqrt p := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hp1
  have hs0 : Real.sqrt p ≠ 0 := by linarith
  have hsm : Real.sqrt p - 1 ≠ 0 := by linarith
  rw [capacity]
  field_simp
  ring

/-- The geometric average retains exactly the triangular prime-power correlations. -/
theorem greenEnergy_eq {p N : ℕ} (hN : 0 < N) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    greenEnergy p N f = Real.log p * (∫ u, f u ^ 2) +
      2 * Real.log p * ∑ k ∈ Finset.range N,
        (1 - ((k + 1 : ℕ) : ℝ) / N) *
          ((1 / Real.sqrt p) ^ (k + 1) * autocorr f ((k + 1 : ℕ) * Real.log p)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [greenEnergy, integral_ladder hf hfc]
  have hs : (∑ k ∈ Finset.range N, ((N : ℝ) - (k + 1)) *
      ((1 / Real.sqrt p) ^ (k + 1) * autocorr f ((k + 1 : ℕ) * Real.log p))) =
      (N : ℝ) * ∑ k ∈ Finset.range N, (1 - ((k + 1 : ℕ) : ℝ) / N) *
        ((1 / Real.sqrt p) ^ (k + 1) * autocorr f ((k + 1 : ℕ) * Real.log p)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    field_simp
  rw [hs]
  field_simp

/-- The positive continuum channel has one universal mass and no discriminant term. -/
theorem positiveChannel_eq {p N : ℕ} (hp : p.Prime) (hN : 0 < N)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    positiveChannel p N f = capacity p * (∫ u, f u ^ 2) -
      2 * Real.log p * ∑ k ∈ Finset.range N,
        (1 - ((k + 1 : ℕ) : ℝ) / N) *
          ((1 / Real.sqrt p) ^ (k + 1) * autocorr f ((k + 1 : ℕ) * Real.log p)) := by
  rw [positiveChannel, greenEnergy_eq hN hf hfc, capacity_eq hp]
  ring

/-- Each translated ladder complement is positive for every continuous compact packet. -/
theorem positiveChannel_nonneg {p N : ℕ} (hp : p.Prime) (hN : 0 < N)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    0 ≤ positiveChannel p N f := by
  have hq0 := inv_sqrt_prime_nonneg p
  have hq1 := inv_sqrt_prime_lt_one hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hmass : (∫ u, ∑ i ∈ Finset.range N, f (u + i * Real.log p) ^ 2) =
      (N : ℝ) * ∫ u, f u ^ 2 := by
    rw [integral_finsetSum _ (fun i hi => by
      simpa only [pow_two] using integrable_shift_pair hf hfc
        (i * Real.log p) (i * Real.log p))]
    simp only [integral_add_right_eq_self (fun u => f u ^ 2),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hupper : (1 - 1 / Real.sqrt p) *
      (∫ u, kmsForm (1 / Real.sqrt p) N (fun i => f (u + i * Real.log p))) ≤
        (1 + 1 / Real.sqrt p) * ((N : ℝ) * ∫ u, f u ^ 2) := by
    rw [← integral_const_mul, ← hmass, ← integral_const_mul]
    apply integral_mono
    · exact (integrable_ladder hf hfc _ _ _).const_mul _
    · apply Integrable.const_mul
      apply integrable_finsetSum
      intro i hi
      simpa only [pow_two] using integrable_shift_pair hf hfc
        (i * Real.log p) (i * Real.log p)
    · intro u
      exact kmsForm_upper hq0 hq1.le N _
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hbound : (∫ u, kmsForm (1 / Real.sqrt p) N
      (fun i => f (u + i * Real.log p))) ≤
        ((1 + 1 / Real.sqrt p) * ((N : ℝ) * ∫ u, f u ^ 2)) /
          (1 - 1 / Real.sqrt p) := by
    apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
    simpa only [mul_comm (1 - 1 / Real.sqrt p)] using hupper
  rw [positiveChannel]
  apply sub_nonneg.mpr
  calc
    greenEnergy p N f ≤ (Real.log p / N) *
        (((1 + 1 / Real.sqrt p) * ((N : ℝ) * ∫ u, f u ^ 2)) /
          (1 - 1 / Real.sqrt p)) :=
      mul_le_mul_of_nonneg_left hbound (div_nonneg hlog hN0.le)
    _ = _ := by field_simp

#print axioms prime_ladder_entry
#print axioms integral_ladder
#print axioms positiveChannel_eq
#print axioms positiveChannel_nonneg

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
