import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.JordanEnergyOfAnIntegerFloorRow
import Mathlib.Data.Nat.Totient

/-!
# Divisor classes of the jumps below the Jordan ceiling

A first difference of two adjacent heights loses part of their quadratic
defect, as in the level-one Haar readings of Arushi–Goswami–Das–Santra.
The jumps are constant on each gcd class. Its Euler totient weight gives
an explicit deficit threshold forcing divisibility of each individual
coefficient, including coefficients reconstructed by Möbius inversion.
-/
noncomputable section
open Finset GaloisForLFunctions.ArithmeticKreinLangerTheory
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

variable {c : ℕ →₀ ℤ} {m B K : ℕ}

/-- Quadratic defect of a jump of absolute size at most the peak. -/
def jumpDefect (c : ℕ →₀ ℤ) (d : ℕ) :=
  |(increment c d : ℝ)| * ((peak c:ℝ) - |(increment c d:ℝ)|)

private theorem all_dvd_period (hp : IsProducer c m B) (hk : AlphabetLE c K) :
    ∀ k∈c.support, k ∣ K.factorial := by
  intro k h
  apply Nat.dvd_factorial _ (hk k h)
  exact Nat.pos_of_ne_zero fun hz => (Finsupp.mem_support_iff.mp h) (hz ▸ hp.zero)

private theorem jump_gcd (hp : IsProducer c m B) (hk : AlphabetLE c K) (r : ℕ) :
    increment c (K.factorial.gcd r) = increment c r := by
  unfold increment
  refine sum_congr rfl fun k h => ?_
  simp only [show (k ∣ K.factorial.gcd r) ↔ k ∣ r from
    ⟨fun h => h.trans (Nat.gcd_dvd_right _ _),Nat.dvd_gcd (all_dvd_period hp hk k h)⟩]

private theorem defect_swap (P a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a ≤ P) (hb' : b ≤ P) :
    |b-a| * (P-|b-a|) ≤ a*(P-a)+b*(P-b) := by
  rcases le_total a b with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith only [mul_nonneg ha (sub_nonneg.mpr hb')]
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith only [mul_nonneg hb (sub_nonneg.mpr ha')]

private theorem sum_cyclic (T : ℕ) (f : ℕ → ℝ) (he : f T = f 0) :
    ∑ r ∈ range T, f (r+1) = ∑ r ∈ range T, f r := by
  have h := Finset.sum_range_succ' f T
  rw [Finset.sum_range_succ,he] at h
  exact (add_right_cancel h).symm

private theorem abs_jump_pos_index (hp : IsProducer c m B) (d : ℕ) (hd : 0<d) :
    |increment c d| ≤ peak c := by
  obtain ⟨r,rfl⟩ : ∃ r, d=r+1 := ⟨d-1,by omega⟩
  have h := stepWeight_succ c r
  exact abs_le.mpr ⟨by linarith only [h,hp.nonneg (r+1),hp.stepWeight_le_peak r],
    by linarith only [h,hp.nonneg r,hp.stepWeight_le_peak (r+1)]⟩

private theorem nonneg_defect (hp : IsProducer c m B) {d : ℕ} (hd : 0<d) :
    0 ≤ jumpDefect c d := by
  have h : |(increment c d : ℝ)| ≤ (peak c:ℝ) := by exact_mod_cast abs_jump_pos_index hp d hd
  exact mul_nonneg (abs_nonneg _) (sub_nonneg.mpr h)

private theorem group_by_gcd (T : ℕ) (hT : 0<T) (f : ℕ → ℝ) :
    ∑ r∈range T, f (T.gcd r) = ∑ d∈T.divisors, ((T/d).totient:ℝ)*f d := by
  have hmap (r : ℕ) (_ : r∈range T) : T.gcd r ∈ T.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hT.ne'⟩
  rw [←sum_fiberwise_of_maps_to hmap (fun r => f (T.gcd r))]
  refine sum_congr rfl fun d hd => ?_
  have h := Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)
  calc _ = ∑ _r ∈ (range T).filter (fun r => T.gcd r=d), f d :=
            sum_congr rfl fun r hr => congrArg f (mem_filter.mp hr).2
       _ = _ := by rw [sum_const,nsmul_eq_mul,←h]

/-- All Euler totient classes spend one joint budget. A class of small
divisor d can have macroscopic weight even when the period is enormous. -/
theorem divisor_jump_defect_budget (hp : IsProducer c m B) (hk : AlphabetLE c K) :
    6*∑ d∈K.factorial.divisors, ((K.factorial/d).totient:ℝ)*jumpDefect c d ≤
      (K.factorial:ℝ)*(3*(peak c:ℝ)^2-jordanEnergy K c) := by
  let T := K.factorial
  let H := fun r => (stepWeight c r:ℝ)
  let P : ℝ := peak c
  let D := fun r => H r*(P-H r)
  have hn (r : ℕ) : 0 ≤ H r := by dsimp [H]; exact_mod_cast hp.nonneg r
  have hu (r : ℕ) : H r ≤ P := by dsimp [H,P]; exact_mod_cast hp.stepWeight_le_peak r
  have hj (r : ℕ) : jumpDefect c (r+1) ≤ D r+D (r+1) := by
    have hi : (increment c (r+1):ℝ) = H (r+1)-H r := by
      dsimp only [H]; exact_mod_cast (show increment c (r+1)=_ by linarith only [stepWeight_succ c r])
    rw [jumpDefect,hi]; exact defect_swap _ _ _ (hn _) (hn _) (hu _) (hu _)
  have hsum := sum_le_sum (s:=range T) (fun r _ => hj r)
  have hHT : H T=H 0 := by
    have h := stepWeight_periodic hp.zero hp.balanced (all_dvd_period hp hk) 1 0
    simpa only [H,T,one_mul,add_zero] using congrArg ((↑) : ℤ → ℝ) h
  have hDT : D T=D 0 := by simp only [D,hHT]
  have hJT : jumpDefect c T=jumpDefect c 0 := by
    have h := jump_gcd hp hk 0
    simpa only [jumpDefect,T,Nat.gcd_zero_right] using
      congrArg (fun j : ℤ => |(j:ℝ)| * ((peak c:ℝ)-|(j:ℝ)|)) h
  rw [sum_cyclic T _ hJT,sum_add_distrib,sum_cyclic T _ hDT] at hsum
  rw [←group_by_gcd _ (Nat.factorial_pos _) (jumpDefect c)]
  have hgroup (r : ℕ) : jumpDefect c (K.factorial.gcd r)=jumpDefect c r := by
    rw [jumpDefect,jumpDefect,jump_gcd hp hk]
  simp_rw [hgroup]
  rw [jordan_defect hp hk, ←mul_assoc,show (K.factorial:ℝ)*(12/K.factorial)=12 by
    rw [mul_comm,div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero K))]]
  change 6*(∑ r∈range T, jumpDefect c r) ≤ 12*∑ r∈range T, D r
  linarith only [hsum]

private theorem indivisible_price (hp : IsProducer c m B) {d : ℕ} (hd : 0<d)
    (h : ¬peak c ∣ increment c d) : (peak c:ℝ)-1 ≤ jumpDefect c d := by
  have h0 : 0 < |increment c d| := abs_pos.mpr fun hz => h (hz ▸ dvd_zero _)
  have htop : |increment c d| < peak c := by
    apply lt_of_le_of_ne (abs_jump_pos_index hp _ hd)
    intro he
    apply h
    rw [←he]
    rcases le_total 0 (increment c d) with hh|hh
    · rw [abs_of_nonneg hh]
    · rw [abs_of_nonpos hh]
      exact neg_dvd.mpr dvd_rfl
  have hl : (1:ℝ) ≤ |(increment c d:ℝ)| := by exact_mod_cast (show 1 ≤ |increment c d| by omega)
  have hu : |(increment c d:ℝ)| ≤ (peak c:ℝ)-1 := by
    exact_mod_cast (show |increment c d| ≤ peak c-1 by omega)
  unfold jumpDefect
  nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)]

/-- The normalized number of indivisible jump classes, with their true
multiplicities, is controlled by the Jordan defect. -/
theorem corrupted_jump_mass (hp : IsProducer c m B) (hk : AlphabetLE c K) :
    6 * (∑ d∈K.factorial.divisors.filter (fun d => ¬peak c ∣ increment c d),
      ((K.factorial/d).totient:ℝ)) * ((peak c:ℝ)-1) ≤
      (K.factorial:ℝ)*(3*(peak c:ℝ)^2-jordanEnergy K c) := by
  classical
  let S := K.factorial.divisors.filter (fun d => ¬peak c ∣ increment c d)
  have hle : ∑ d∈S, ((K.factorial/d).totient:ℝ)*((peak c:ℝ)-1) ≤
      ∑ d∈K.factorial.divisors, ((K.factorial/d).totient:ℝ)*jumpDefect c d := by
    apply (sum_le_sum (s:=S) fun d hd => mul_le_mul_of_nonneg_left
      (indivisible_price hp (Nat.pos_of_mem_divisors (mem_filter.mp hd).1) (mem_filter.mp hd).2)
      (Nat.cast_nonneg _)).trans
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun d hd _ =>
      mul_nonneg (Nat.cast_nonneg _) (nonneg_defect hp (Nat.pos_of_mem_divisors hd))
  rw [←sum_mul] at hle
  have hs := (mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 6)).trans
    (divisor_jump_defect_budget hp hk)
  simpa only [S,mul_assoc] using hs

/-- A coefficient is forced to be a multiple of the peak if the observed
defect is smaller than one indivisible jump at the least expensive divisor
of its index. This applies to composite indices with repeated factors. -/
theorem coefficient_divisibility_from_defect (hp : IsProducer c m B) (hk : AlphabetLE c K)
    {n : ℕ} (hn : 0<n) (hperiod : n ∣ K.factorial)
    (hsmall : (K.factorial:ℝ)*(3*(peak c:ℝ)^2-jordanEnergy K c) <
      6*((K.factorial/n).totient:ℝ)*((peak c:ℝ)-1)) : peak c ∣ c n := by
  have hP : 0 ≤ (peak c:ℝ)-1 := by exact_mod_cast (show (0:ℤ) ≤ peak c-1 by
    have hw := hp.le_peak
    have hm := hp.one_le_m
    omega)
  have hgood (d : ℕ) (hd : d ∣ n) : peak c ∣ increment c d := by
    by_contra hbad
    let w := fun d : ℕ => ((K.factorial/d).totient:ℝ)
    let S := K.factorial.divisors.filter (fun d => ¬peak c ∣ increment c d)
    have hmem : d∈S := mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd.trans hperiod,Nat.factorial_ne_zero _⟩,hbad⟩
    have hdiv := Nat.div_dvd_div_left hperiod hd
    have hpos := Nat.totient_pos.mpr (Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) (hd.trans hperiod))
      (Nat.pos_of_dvd_of_pos hd hn))
    have hweight : w n ≤ w d := by
      exact Nat.cast_le.mpr (Nat.le_of_dvd hpos (Nat.totient_dvd_of_dvd hdiv))
    have hsum : w d ≤ ∑ k∈S,w k := single_le_sum (f := w) (fun k _ => Nat.cast_nonneg _) hmem
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hweight.trans hsum)
      (by norm_num : (0:ℝ) ≤ 6)) hP
    exact (not_lt_of_ge (h.trans (corrupted_jump_mass hp hk))) hsmall
  rw [coeff_eq_moebius_increment c hn]
  apply Finset.dvd_sum
  intro x hx
  have he := Nat.mem_divisorsAntidiagonal.mp hx
  exact dvd_mul_of_dvd_right (hgood x.2 ⟨x.1,he.1.symm.trans (Nat.mul_comm _ _)⟩) _

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
