import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeWindows
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.ScalarPrimePacketNorm
import GaloisForLFunctions.SignedArithmeticHodgeTheory.GrowingRamanujanFamiliesHaveAUniformGramBudget

/-!
# Logarithmic moments of receiving-mode windows

The bounded harmonic Gram discrepancy acquires only one logarithm under
Abel summation. The logarithmic second moment of a fixed mode therefore
has the same leading term as the scalar harmonic window.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory SignedArithmeticHodgeTheory

private theorem sum_range_succ_window (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, f (n + 1)) = ∑ n ∈ Icc 1 N, f n := by
  induction N with
  | zero => simp only [range_zero, sum_empty, Icc_eq_empty_of_lt (by omega : 0 < 1)]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- Every centered product of positive conductor modes has bounded harmonic prefixes. -/
theorem abs_modeProduct_harmonic_prefix_le {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (N : ℕ) :
    |∑ n ∈ Icc 1 N,
      (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
        (if m = l then 1 else 0)) / (n : ℝ)| ≤ 2 * (m : ℝ) * l := by
  have h := ramanujanPoleProfile_gram_error_le ⟨m, hm⟩ ⟨l, hl⟩ N
  have hδ : (if (⟨m, hm⟩ : ℕ+) = ⟨l, hl⟩ then (1 : ℝ) else 0) =
      (if m = l then 1 else 0) := by
    by_cases he : m = l
    · subst l
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg he, if_neg (fun h => he (congrArg Subtype.val h))]
  have hprod (n : ℕ) : ramanujanPoleProfile m n * ramanujanPoleProfile l n =
      normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ) := by
    rw [ramanujanPoleProfile, ramanujanPoleProfile, div_mul_div_comm, ← sq,
      Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hδ] at h
  change |(∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) -
    (if m = l then 1 else 0) * (∑ n ∈ Icc 1 N, 1 / (n : ℝ))| ≤
      2 * (m : ℝ) * l at h
  simp only [hprod] at h
  have he : (∑ n ∈ Icc 1 N,
      (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
        (if m = l then 1 else 0)) / (n : ℝ)) =
      (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
        (if m = l then 1 else 0) * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
    simp only [sub_div, sum_sub_distrib, mul_sum, mul_one_div]
  rw [he]
  exact h

/-- A nonnegative increasing weight costs twice the bounded harmonic-prefix discrepancy. -/
theorem abs_modeProduct_harmonic_mono_prefix_le {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (w : ℕ → ℝ)
    (hw0 : ∀ n, 0 ≤ w n) (hwmono : ∀ n, 1 ≤ n → w n ≤ w (n + 1)) (N : ℕ) :
    |∑ n ∈ Icc 1 N,
      (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
        (if m = l then 1 else 0)) * w n / (n : ℝ)| ≤
      4 * (m : ℝ) * l * w N := by
  let a (n : ℕ) := (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
    (if m = l then 1 else 0)) / (n : ℝ)
  have hpartial (k : ℕ) : |∑ j ∈ range k, a (j + 1)| ≤ 2 * (m : ℝ) * l := by
    rw [sum_range_succ_window]
    exact abs_modeProduct_harmonic_prefix_le hm hl k
  have h := _root_.RHTower.abs_sum_mul_le_of_bounded_partial_mono
    (g := fun j => a (j + 1)) (w := fun j => w (j + 1)) N
    hpartial (fun j => hw0 (j + 1)) (fun j => hwmono (j + 1) (by omega))
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty, abs_zero]
    exact mul_nonneg (by positivity) (hw0 0)
  rw [Nat.sub_add_cancel hN, sum_range_succ_window (fun n => w n * a n)] at h
  have he : (∑ n ∈ Icc 1 N, w n * a n) =
      ∑ n ∈ Icc 1 N,
        (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
          (if m = l then 1 else 0)) * w n / (n : ℝ) :=
    sum_congr rfl fun _ _ => by dsimp only [a]; ring
  rw [he] at h
  exact h.trans_eq (by ring)

/-- Increasing weighted windows have only the two endpoint costs. -/
theorem abs_modeProduct_harmonic_mono_window_le {m l A B : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hAB : A ≤ B) (w : ℕ → ℝ)
    (hw0 : ∀ n, 0 ≤ w n) (hwmono : ∀ n, 1 ≤ n → w n ≤ w (n + 1)) :
    |∑ n ∈ Ioc A B,
      (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
        (if m = l then 1 else 0)) * w n / (n : ℝ)| ≤
      4 * (m : ℝ) * l * (w A + w B) := by
  let f (n : ℕ) := (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
    (if m = l then 1 else 0)) * w n / (n : ℝ)
  have hs : (Ioc A B : Finset ℕ) = Icc 1 B \ Icc 1 A := by
    ext n
    simp only [mem_Ioc, mem_sdiff, mem_Icc]
    omega
  have hsub : Icc 1 A ⊆ Icc 1 B := Icc_subset_Icc le_rfl hAB
  have he := sum_sdiff (f := f) hsub
  rw [← hs] at he
  have hdiff : (∑ n ∈ Ioc A B, f n) =
      (∑ n ∈ Icc 1 B, f n) - ∑ n ∈ Icc 1 A, f n := by linarith only [he]
  change |∑ n ∈ Ioc A B, f n| ≤ _
  rw [hdiff]
  exact ((abs_sub _ _).trans (add_le_add
    (abs_modeProduct_harmonic_mono_prefix_le hm hl w hw0 hwmono B)
    (abs_modeProduct_harmonic_mono_prefix_le hm hl w hw0 hwmono A))).trans_eq (by ring)

/-- A signed contrast retains the endpoint cost of any nonnegative increasing weight. -/
theorem abs_primeChargeWindowContrast_modeProduct_mono_pairing_le {m l A B C N : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hAB : A ≤ B) (hBC : B ≤ C) (hCN : C ≤ N)
    (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n)
    (hwmono : ∀ n, 1 ≤ n → w n ≤ w (n + 1)) :
    |∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n *
      ((normalizedRamanujanMode m n * normalizedRamanujanMode l n -
        (if m = l then 1 else 0)) * w n / (n : ℝ))| ≤
      4 * (m : ℝ) * l * ((w B + w C) +
        |primeChargeWindowMass B C / primeChargeWindowMass A B| * (w A + w B)) := by
  rw [primeChargeWindowContrast_sum (hBC.trans hCN) hCN]
  calc
    _ ≤ |∑ n ∈ Ioc B C,
        (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
          (if m = l then 1 else 0)) * w n / (n : ℝ)| +
        |primeChargeWindowMass B C / primeChargeWindowMass A B| *
          |∑ n ∈ Ioc A B,
            (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
              (if m = l then 1 else 0)) * w n / (n : ℝ)| := by
      simpa only [abs_mul] using abs_sub
        (∑ n ∈ Ioc B C,
          (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
            (if m = l then 1 else 0)) * w n / (n : ℝ))
        ((primeChargeWindowMass B C / primeChargeWindowMass A B) *
          ∑ n ∈ Ioc A B,
            (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
              (if m = l then 1 else 0)) * w n / (n : ℝ))
    _ ≤ 4 * (m : ℝ) * l * (w B + w C) +
        |primeChargeWindowMass B C / primeChargeWindowMass A B| *
          (4 * (m : ℝ) * l * (w A + w B)) :=
      add_le_add (abs_modeProduct_harmonic_mono_window_le hm hl hBC w hw0 hwmono)
        (mul_le_mul_of_nonneg_left
          (abs_modeProduct_harmonic_mono_window_le hm hl hAB w hw0 hwmono) (abs_nonneg _))
    _ = _ := by ring

/-- The logarithmic conductor-product moment differs from its scalar diagonal by one logarithm. -/
theorem abs_modeProduct_harmonic_log_prefix_le {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (N : ℕ) :
    |∑ n ∈ Icc 1 N,
      (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
        (if m = l then 1 else 0)) * Real.log n / (n : ℝ)| ≤
      4 * (m : ℝ) * l * Real.log N :=
  abs_modeProduct_harmonic_mono_prefix_le hm hl (fun n => Real.log n)
    Real.log_natCast_nonneg (fun n hn => Real.log_le_log (by exact_mod_cast hn)
      (by exact_mod_cast (Nat.le_succ n))) N

/-- A clipped logarithmic ramp has only one prime-cutoff logarithm of mode discrepancy. -/
theorem abs_primeChargeWindowContrast_modeProduct_ramp_pairing_le {m l A B C N : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hAB : A ≤ B) (hBC : B ≤ C) (hCN : C ≤ N) (Q : ℕ) :
    |∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n *
      ((normalizedRamanujanMode m n * normalizedRamanujanMode l n -
        (if m = l then 1 else 0)) *
          max (Real.log Q + Real.log n - Real.log N) 0 / (n : ℝ))| ≤
      8 * (m : ℝ) * l *
        (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) * Real.log Q := by
  let w (n : ℕ) := max (Real.log Q + Real.log n - Real.log N) 0
  have hw0 (n : ℕ) : 0 ≤ w n := le_max_right _ _
  have hwmono (n : ℕ) (hn : 1 ≤ n) : w n ≤ w (n + 1) := by
    have hlog := Real.log_le_log (show (0 : ℝ) < n by exact_mod_cast hn)
      (show (n : ℝ) ≤ (n + 1 : ℕ) by exact_mod_cast Nat.le_succ n)
    exact max_le_max (by linarith only [hlog]) le_rfl
  have hwN (n : ℕ) (hn : n ≤ N) : w n ≤ Real.log Q := by
    have hlog : Real.log (n : ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simpa only [Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg N
      · exact Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hn)
    exact max_le (by linarith only [hlog]) (Real.log_natCast_nonneg Q)
  have h := abs_primeChargeWindowContrast_modeProduct_mono_pairing_le
    hm hl hAB hBC hCN w hw0 hwmono
  refine h.trans ?_
  have hA := hwN A (hAB.trans (hBC.trans hCN))
  have hB := hwN B (hBC.trans hCN)
  have hC := hwN C hCN
  have hsum := add_le_add (add_le_add hB hC)
    (mul_le_mul_of_nonneg_left (add_le_add hA hB)
      (abs_nonneg (primeChargeWindowMass B C / primeChargeWindowMass A B)))
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4 * (m : ℝ) * l)).trans_eq
    (by ring)

#print axioms abs_modeProduct_harmonic_mono_prefix_le
#print axioms abs_primeChargeWindowContrast_modeProduct_mono_pairing_le
#print axioms abs_primeChargeWindowContrast_modeProduct_ramp_pairing_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
