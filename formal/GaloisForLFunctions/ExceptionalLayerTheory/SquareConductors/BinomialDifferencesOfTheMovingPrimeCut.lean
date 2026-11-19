import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFixedPrimeCutAfterSummingConductors
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Signed binomial differences at the moving conductor cut

The Gatea–Huang cancellation of lower polynomial degrees removes the
quadratic conductor counterterm after three cut differences. Below the
first spline knot the remaining weights are positive multiples of
`p log p`. Away from the prime two, consecutive surviving primes occupy
one parity, so every surviving term in any binomial difference has the
same sign. This applies eventually at the actual cut of exponent `17/9`.
-/

open Finset Filter Topology
open GaloisForLFunctions.CountingHolography.Sections

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

noncomputable section

private def lastPrimeIndex (N : ℕ) : ℕ := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊

/-- Actual integrated weight of one integer, including the terminal prime cutoff. -/
def cutPrimeAtom (N p : ℕ) : ℂ :=
  if p ∈ ordinaryPrimeLags (lastPrimeIndex N) then
    (N:ℂ)^2 * ((Real.log p : ℂ) * squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2))
  else 0

private theorem split_tail_step (S : Finset ℕ) (f : ℕ → ℂ) (K : ℕ) :
    ∑ p ∈ S.filter (K < ·), f p =
      (∑ p ∈ S.filter (K+1 < ·), f p) + (if K+1 ∈ S then f (K+1) else 0) := by
  rw [Finset.sum_filter, Finset.sum_filter]
  have h (p : ℕ) : (if K < p then f p else 0) =
      (if K+1 < p then f p else 0) + (if p = K+1 then f p else 0) := by
    split_ifs <;> first | omega | simp_all
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  simp

/-- A single cut step reads a centered prime atom exactly. -/
theorem centeredFixedPrimeTail_difference (N K : ℕ) :
    fwdDiff 1 (centeredFixedPrimeTail N) K =
      (innerPrimeSlope : ℂ) * ((K : ℂ)+1) - cutPrimeAtom N (K+1) := by
  unfold fwdDiff centeredFixedPrimeTail cutPrimeAtom
  dsimp only
  rw [split_tail_step _ _ K]
  unfold lastPrimeIndex
  split_ifs <;> push_cast <;> ring

private def affineCut (k : ℕ) : ℂ := (innerPrimeSlope : ℂ)*((k : ℂ)+1)

private theorem affine_differences_vanish (r : ℕ) :
    (fwdDiff 1)^[r+2] affineCut = 0 := by
  have hz : (fwdDiff 1)^[2] affineCut = 0 := by
    funext x
    change affineCut (x+1+1) - affineCut (x+1) - (affineCut (x+1) - affineCut x) = 0
    simp only [affineCut, Nat.cast_add, Nat.cast_one]
    ring
  induction r with
  | zero => exact hz
  | succ r ih =>
    rw [show r+1+2 = (r+2)+1 by omega, Function.iterate_succ_apply', ih]
    funext x
    exact sub_self _

/-- At all terminal conductors the entire higher difference is a local signed sum of prime atoms. -/
theorem centeredFixedPrimeTail_high_difference (N K r : ℕ) :
    (fwdDiff 1)^[r+3] (centeredFixedPrimeTail N) K =
      -∑ j ∈ range (r+3), ((-1 : ℤ)^(r+2-j) * (r+2).choose j) • cutPrimeAtom N (K+j+1) := by
  have hf : fwdDiff 1 (centeredFixedPrimeTail N) =
      affineCut + (-1 : ℂ) • (fun k : ℕ => cutPrimeAtom N (k+1)) := by
    funext k
    simp only [centeredFixedPrimeTail_difference, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      neg_one_mul, affineCut, sub_eq_add_neg]
  rw [Function.iterate_succ_apply, hf, fwdDiff_iter_add, affine_differences_vanish,
    fwdDiff_iter_const_smul, zero_add, Pi.smul_apply, smul_eq_mul, neg_one_mul, fwdDiff_iter_eq_sum_shift]
  simp

/-- Unsigned local average of the prime first moments, with binomial weights. -/
def binomialPrimeMass (K m : ℕ) : ℝ :=
  ∑ j ∈ range (m+1), if (K+j+1).Prime then
    (m.choose j : ℝ) * (K+j+1 : ℕ) * Real.log (K+j+1 : ℕ) else 0

private theorem inner_atom {N p : ℕ} (hN : 0 < N) (hp : 0 < p)
    (hcut : (p : ℝ) ≤ Real.exp (-8)*(N : ℝ)^2) :
    cutPrimeAtom N p = if p.Prime then (innerPrimeSlope : ℂ)*p*Real.log p else 0 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hH : p ≤ lastPrimeIndex N := by
    apply Nat.le_floor
    have hlo : squareConductorBVWindow.lower ≤ 1 := he
    exact hcut.trans ((mul_le_of_le_one_left (sq_nonneg _) he).trans
      (pow_le_pow_left₀ hn.le (le_div_self hn.le squareConductorBVWindow.lower_pos hlo) 2))
  have hmem : p ∈ ordinaryPrimeLags (lastPrimeIndex N) ↔ p.Prime := by
    simp only [ordinaryPrimeLags, mem_filter, mem_Icc]
    exact ⟨And.right, fun h => ⟨⟨h.two_le, hH⟩, h⟩⟩
  simp only [cutPrimeAtom, hmem]
  split_ifs
  · rw [squarePrefixPrimeWeight_before_first_knot (div_pos (Nat.cast_pos.mpr hp) (sq_pos_of_pos hn))
      ((div_le_iff₀ (sq_pos_of_pos hn)).mpr hcut)]
    push_cast
    have hn' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp [hn']
  · rfl

private theorem coherent_inner_difference {N K : ℕ} (r : ℕ) (hN : 0 < N) (hK : 2 ≤ K)
    (hcut : ((K+r+3 : ℕ) : ℝ) ≤ Real.exp (-8)*(N : ℝ)^2) :
    (fwdDiff 1)^[r+3] (centeredFixedPrimeTail N) K =
      (-1 : ℂ)^(K+r+3) * (innerPrimeSlope : ℂ) * (binomialPrimeMass K (r+2) : ℂ) := by
  rw [centeredFixedPrimeTail_high_difference, binomialPrimeMass, Complex.ofReal_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ r+2 := by have := mem_range.mp hj; omega
  have hpr : ((K+j+1 : ℕ) : ℝ) ≤ Real.exp (-8)*(N : ℝ)^2 :=
    (Nat.cast_le.mpr (by omega : K+j+1 ≤ K+r+3)).trans hcut
  rw [inner_atom hN (by omega) hpr]
  by_cases hp : (K+j+1).Prime
  · have hodd := hp.odd_of_ne_two (by omega)
    have hev : Even (K+j) := by obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩
    have hsign : (-1 : ℂ)^(K+r+3) = -((-1 : ℂ)^(r+2-j)) := by
      rw [show K+r+3 = (r+2-j)+(K+j)+1 by omega, pow_succ, pow_add, hev.neg_one_pow]
      ring
    rw [if_pos hp, if_pos hp, hsign, zsmul_eq_mul]
    push_cast
    ring
  · simp [hp]

private theorem terminal_inner_window (r : ℕ) : ∀ᶠ N : ℕ in atTop,
    let K := ⌊(N : ℝ)^(17/9 : ℝ)⌋₊
    0 < N ∧ 2 ≤ K ∧ ((K+r+3 : ℕ) : ℝ) ≤ Real.exp (-8)*(N : ℝ)^2 := by
  have ha := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 17/9)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/9)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1, ha.eventually_ge_atTop ((r : ℝ)+3),
    hb.eventually_ge_atTop (2*Real.exp 8)] with N hN hA hB
  change (r : ℝ)+3 ≤ (N : ℝ)^(17/9 : ℝ) at hA
  change 2*Real.exp 8 ≤ (N : ℝ)^(1/9 : ℝ) at hB
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hf := Nat.floor_le (Real.rpow_nonneg hn.le (17/9 : ℝ))
  refine ⟨hN, Nat.le_floor (by push_cast; linarith), ?_⟩
  push_cast
  rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos _)]
  have h := mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hn.le (17/9 : ℝ))
  rw [← Real.rpow_add hn, show (17/9 : ℝ)+1/9 = 2 by norm_num, Real.rpow_two] at h
  exact (mul_le_mul_of_nonneg_right (by linarith only [hA, hf] :
    (⌊(N : ℝ)^(17/9 : ℝ)⌋₊ : ℝ) + r + 3 ≤ 2*((N : ℝ)^(17/9 : ℝ))) (Real.exp_pos 8).le).trans
    (by convert h using 1 <;> ring)

/-- At the actual moving cut every order at least three has a completely coherent prime sign. -/
theorem moving_cut_difference_eq_signed_prime_mass (r : ℕ) : ∀ᶠ N : ℕ in atTop,
    let K := ⌊(N : ℝ)^(17/9 : ℝ)⌋₊
    (fwdDiff 1)^[r+3] (centeredFixedPrimeTail N) K =
      (-1 : ℂ)^(K+r+3) * (innerPrimeSlope : ℂ) * (binomialPrimeMass K (r+2) : ℂ) := by
  filter_upwards [terminal_inner_window r] with N h
  exact coherent_inner_difference r h.1 h.2.1 h.2.2

private theorem term_nonneg (K m j : ℕ) :
    0 ≤ (if (K+j+1).Prime then
      (m.choose j : ℝ) * (K+j+1 : ℕ) * Real.log (K+j+1 : ℕ) else 0) := by
  split_ifs with hp
  · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hp.one_le))
  · exact le_rfl

/-- A binomial prime mass is positive exactly when its entire integer window contains a prime. -/
theorem binomialPrimeMass_pos_iff (K m : ℕ) :
    0 < binomialPrimeMass K m ↔ ∃ j ≤ m, (K+j+1).Prime := by
  constructor
  · intro h
    by_contra! hn
    have hz : binomialPrimeMass K m = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [if_neg (hn j (mem_range_succ_iff.mp hj))]
    exact h.ne' hz
  · rintro ⟨j, hj, hp⟩
    apply Finset.sum_pos' (fun i _ => term_nonneg K m i)
    refine ⟨j, mem_range_succ_iff.mpr hj, ?_⟩
    rw [if_pos hp]
    exact mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hj)) (Nat.cast_pos.mpr hp.pos))
      (Real.log_pos (by exact_mod_cast hp.one_lt))

/-- At the moving cut the norm recovers the unsigned local binomial mass with its true scale. -/
theorem moving_cut_difference_norm (r : ℕ) : ∀ᶠ N : ℕ in atTop,
    let K := ⌊(N : ℝ)^(17/9 : ℝ)⌋₊
    ‖(fwdDiff 1)^[r+3] (centeredFixedPrimeTail N) K‖ = innerPrimeSlope * binomialPrimeMass K (r+2) := by
  filter_upwards [moving_cut_difference_eq_signed_prime_mass r] with N he
  dsimp only at he ⊢
  rw [he, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos innerPrimeSlope_pos, Complex.norm_real, Real.norm_eq_abs]
  have hmass (K m : ℕ) : 0 ≤ binomialPrimeMass K m :=
    Finset.sum_nonneg (fun j _ => term_nonneg K m j)
  rw [abs_of_nonneg (hmass _ _)]

/-- Prime gaps are exactly the vanishing higher cut differences, eventually for each order. -/
theorem moving_cut_difference_ne_zero_iff (r : ℕ) : ∀ᶠ N : ℕ in atTop,
    let K := ⌊(N : ℝ)^(17/9 : ℝ)⌋₊
    (fwdDiff 1)^[r+3] (centeredFixedPrimeTail N) K ≠ 0 ↔ ∃ j ≤ r+2, (K+j+1).Prime := by
  filter_upwards [moving_cut_difference_norm r] with N he
  dsimp only at he ⊢
  rw [← norm_pos_iff, he, mul_pos_iff_of_pos_left innerPrimeSlope_pos, binomialPrimeMass_pos_iff]

#print axioms moving_cut_difference_ne_zero_iff
#print axioms centeredFixedPrimeTail_high_difference
#print axioms moving_cut_difference_eq_signed_prime_mass

end

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
