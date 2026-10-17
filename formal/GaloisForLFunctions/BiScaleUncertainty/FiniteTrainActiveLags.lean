import GaloisForLFunctions.BiScaleUncertainty.FiniteCopyTailRigidity

/-!
# Active correlation packets of finite common-seed trains

Signed aperiodic coefficients group all pairs with the same displacement. Separation
isolates each complete packet, including exact cancellation at an interior lag.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def copyTrainLagCoefficient {m : ℕ} (c : Fin (m + 1) → ℝ) (k : ℤ) : ℝ :=
  ∑ i, ∑ j, if (j.val : ℤ) - (i.val : ℤ) = k then c i * c j else 0

def copyTrainExpSymbol {m : ℕ} (c : Fin (m + 1) → ℝ) (S β : ℝ) : ℝ :=
  ∑ i, c i * Real.exp (β * ((i.val : ℝ) * S))

theorem copyTrainMass_pos_of_exists {m : ℕ} {c : Fin (m + 1) → ℝ}
    (hc : ∃ i, c i ≠ 0) : 0 < copyTrainMass c := by
  obtain ⟨i, hi⟩ := hc
  have hp : 0 < c i ^ 2 := by positivity
  exact hp.trans_le (Finset.single_le_sum (s := Finset.univ) (f := fun j => c j ^ 2)
    (fun j _ => sq_nonneg (c j)) (by simp))

theorem copyTrainLagCoefficient_zero {m : ℕ} (c : Fin (m + 1) → ℝ) :
    copyTrainLagCoefficient c 0 = copyTrainMass c := by
  classical
  unfold copyTrainLagCoefficient copyTrainMass
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = c i * c i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have hv : j.val ≠ i.val := fun h => hji (Fin.ext h)
        simp only [if_neg (show (j.val : ℤ) - (i.val : ℤ) ≠ 0 by omega)]
      · simp
    _ = _ := by ring

theorem copyTrainLagCoefficient_neg {m : ℕ} (c : Fin (m + 1) → ℝ) (k : ℤ) :
    copyTrainLagCoefficient c (-k) = copyTrainLagCoefficient c k := by
  classical
  unfold copyTrainLagCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (i.val : ℤ) - (j.val : ℤ) = -k ↔ (j.val : ℤ) - (i.val : ℤ) = k := by omega
  simp only [he]
  split_ifs <;> ring

theorem autocorr_copyTrain_grouped {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {m : ℕ} (c : Fin (m + 1) → ℝ) (S x : ℝ) :
    autocorr (copyTrain f c S) x =
      ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        copyTrainLagCoefficient c k * autocorr f (x - (k : ℝ) * S) := by
  classical
  rw [autocorr_copyTrain hf hfc]
  symm
  simp only [copyTrainLagCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hmem : (j.val : ℤ) - (i.val : ℤ) ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    have hi := i.is_lt
    have hj := j.is_lt
    simp only [Finset.mem_Icc]
    omega
  rw [Finset.sum_eq_single ((j.val : ℤ) - (i.val : ℤ))]
  · simp only [Int.cast_sub, Int.cast_natCast]
    congr 2
    ring
  · intro k _ hk
    rw [if_neg (Ne.symm hk), zero_mul]
  · exact fun h => (h hmem).elim

/-- Every integer lag has a whole packet coefficient; individual pairs need not survive. -/
theorem autocorr_copyTrain_near_lag {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {m : ℕ} (c : Fin (m + 1) → ℝ) {D S x : ℝ}
    (hD : 0 ≤ D) (hsupp : ∀ y, D < |y| → autocorr f y = 0) (hS : D + 1 < S)
    {k : ℤ} (hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)) (hx : |x - (k : ℝ) * S| ≤ 1) :
    autocorr (copyTrain f c S) x = copyTrainLagCoefficient c k * autocorr f (x - (k : ℝ) * S) := by
  classical
  have hS0 : 0 < S := by linarith
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  rw [autocorr_copyTrain_grouped hf hfc]
  apply Finset.sum_eq_single k
  · intro l _ hl
    have hz : autocorr f (x - (l : ℝ) * S) = 0 := by
      rcases lt_or_gt_of_ne hl with hlt | hgt
      · have hb : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show l + 1 ≤ k by omega)
        have hm := mul_le_mul_of_nonneg_right hb hS0.le
        apply hsupp
        exact lt_of_lt_of_le (by nlinarith : D < x - (l : ℝ) * S) (le_abs_self _)
      · have hb : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast (show k + 1 ≤ l by omega)
        have hm := mul_le_mul_of_nonneg_right hb hS0.le
        apply hsupp
        exact lt_of_lt_of_le (by nlinarith : D < -(x - (l : ℝ) * S)) (neg_le_abs _)
    rw [hz, mul_zero]
  · exact fun h => (h hk).elim

theorem integral_copyTrain_mul_exp {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {m : ℕ} (c : Fin (m + 1) → ℝ) (S β : ℝ) :
    (∫ u, copyTrain f c S u * Real.exp (β * u)) =
      copyTrainExpSymbol c S β * ∫ u, f u * Real.exp (β * u) := by
  have hi (i : Fin (m + 1)) : Integrable (fun u =>
      c i * (f (u - (i.val : ℝ) * S) * Real.exp (β * u))) := by
    apply Integrable.const_mul
    exact ((hf.comp (continuous_id.sub continuous_const)).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hfc.comp_homeomorph (Homeomorph.subRight ((i.val : ℝ) * S))).mul_right
  simp only [copyTrain, finiteTranslateSource, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const_mul, integral_shift_mul_exp, copyTrainExpSymbol, Finset.sum_mul, mul_assoc]

/-- A zero of the finite translation symbol enforces the actual hyperbolic polar moment. -/
theorem integral_copyTrain_autocorr_cosh_of_symbol_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {m : ℕ}
    (c : Fin (m + 1) → ℝ) (S : ℝ) (hB : copyTrainExpSymbol c S (1 / 2) = 0) :
    (∫ x in Ioi 0, autocorr (copyTrain f c S) x * Real.cosh (x / 2)) = 0 := by
  have hm := integral_copyTrain_mul_exp hf.continuous hfc c S (1 / 2)
  rw [hB, zero_mul] at hm
  have hmhalf : (∫ u, copyTrain f c S u * Real.exp (u / 2)) = 0 := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hm
  have hwhole := integral_autocorr_mul_cosh (contDiff_copyTrain hf c S)
    (hasCompactSupport_copyTrain hfc c S)
  change (∫ x, autocorr (copyTrain f c S) x * Real.cosh (x / 2)) =
    (∫ u, copyTrain f c S u * Real.exp (u / 2)) *
      ∫ u, copyTrain f c S u * Real.exp (-u / 2) at hwhole
  rw [hmhalf, zero_mul] at hwhole
  have heven := integral_comp_abs (f := fun x => autocorr (copyTrain f c S) x * Real.cosh (x / 2))
  have hid : (fun x : ℝ => autocorr (copyTrain f c S) |x| * Real.cosh (|x| / 2)) =
      fun x => autocorr (copyTrain f c S) x * Real.cosh (x / 2) := by
    funext x
    rcases abs_choice x with hx | hx
    · rw [hx]
    · rw [hx, autocorr_neg, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
  rw [hid, hwhole] at heven
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
