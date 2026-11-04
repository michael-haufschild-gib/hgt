import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramUniformRemainder
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMoments
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandTopTailBounds

/-!
# Harmonic contrasts on terminal windows

Two adjacent windows admit an exact harmonic-pole-neutral contrast. Its
mass and square are explicit. Nonpolar conductor coordinates cost only the
reciprocal left endpoint, because the torsion finite part cancels between
the two ends of each window.
-/

noncomputable section

open Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SuccessorShellArithmetic ArithmeticEffectivityTheory BezoutValuationIncidence
  CompletedArithmeticForms

private theorem prefix_add_window {A B : ℕ} (hAB : A ≤ B) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 A, f n) + (∑ n ∈ Ioc A B, f n) = ∑ n ∈ Icc 1 B, f n := by
  have hs : (Ioc A B : Finset ℕ) = Icc 1 B \ Icc 1 A := by
    ext n
    simp only [mem_Ioc, mem_sdiff, mem_Icc]
    omega
  rw [hs, add_comm]
  exact sum_sdiff (Icc_subset_Icc le_rfl hAB)

/-- The torsion finite part cancels on every terminal window of a nonpolar conductor. -/
theorem abs_normalizedRamanujan_harmonic_window_le {m A B : ℕ}
    (hm : 1 < m) (hAB : A ≤ B) :
    |∑ n ∈ Ioc A B, normalizedRamanujanMode m n / (n : ℝ)| ≤
      8 * (m : ℝ) / ((A : ℝ) + 1) := by
  have hm1 : m ≠ 1 := ne_of_gt hm
  have hA := abs_normalizedRamanujan_harmonicGram_torsion_remainder
    (m := m) (l := 1) (by omega) zero_lt_one A
  have hB := abs_normalizedRamanujan_harmonicGram_torsion_remainder
    (m := m) (l := 1) (by omega) zero_lt_one B
  simp only [normalizedRamanujanMode_one, mul_one, if_neg hm1, zero_mul, sub_zero,
    Nat.totient_one, Nat.cast_one, Real.sqrt_one] at hA hB
  have hs := prefix_add_window hAB (fun n => normalizedRamanujanMode m n / (n : ℝ))
  have hden : 4 * (m : ℝ) / ((B : ℝ) + 1) ≤ 4 * (m : ℝ) / ((A : ℝ) + 1) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast Nat.add_le_add_right hAB 1)
  have hdiff := abs_sub
    ((∑ n ∈ Icc 1 B, normalizedRamanujanMode m n / (n : ℝ)) +
      orbitIntersection m 1 / Real.sqrt (m.totient : ℝ))
    ((∑ n ∈ Icc 1 A, normalizedRamanujanMode m n / (n : ℝ)) +
      orbitIntersection m 1 / Real.sqrt (m.totient : ℝ))
  have hid : ((∑ n ∈ Icc 1 B, normalizedRamanujanMode m n / (n : ℝ)) +
      orbitIntersection m 1 / Real.sqrt (m.totient : ℝ)) -
    ((∑ n ∈ Icc 1 A, normalizedRamanujanMode m n / (n : ℝ)) +
      orbitIntersection m 1 / Real.sqrt (m.totient : ℝ)) =
      ∑ n ∈ Ioc A B, normalizedRamanujanMode m n / (n : ℝ) := by linarith only [hs]
  rw [hid] at hdiff
  calc
    _ ≤ 4 * (m : ℝ) / ((B : ℝ) + 1) + 4 * (m : ℝ) / ((A : ℝ) + 1) :=
      hdiff.trans (add_le_add hB hA)
    _ ≤ 4 * (m : ℝ) / ((A : ℝ) + 1) + 4 * (m : ℝ) / ((A : ℝ) + 1) :=
      add_le_add hden le_rfl
    _ = _ := by ring

/-- Literal harmonic mass of an interval, excluding its left endpoint. -/
def primeChargeWindowMass (A B : ℕ) : ℝ := ∑ n ∈ Ioc A B, 1 / (n : ℝ)

theorem primeChargeWindowMass_pos {A B : ℕ} (hAB : A < B) :
    0 < primeChargeWindowMass A B := by
  apply sum_pos'
  · intro n _
    positivity
  · refine ⟨A + 1, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
    positivity

/-- Adjacent windows balanced by their exact finite harmonic masses. -/
def primeChargeWindowContrast (A B C : ℕ) (n : ℕ) : ℝ :=
  (if n ∈ Ioc B C then 1 else 0) -
    (primeChargeWindowMass B C / primeChargeWindowMass A B) *
      (if n ∈ Ioc A B then 1 else 0)

private theorem sum_window_indicator {A B N : ℕ} (hBN : B ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, if n ∈ Ioc A B then f n else 0) = ∑ n ∈ Ioc A B, f n := by
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem_Ioc]
  omega

/-- Every pairing with the contrast is the difference of its two window sums. -/
theorem primeChargeWindowContrast_sum {A B C N : ℕ} (hBN : B ≤ N) (hCN : C ≤ N)
    (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n * f n) =
      (∑ n ∈ Ioc B C, f n) -
        (primeChargeWindowMass B C / primeChargeWindowMass A B) * ∑ n ∈ Ioc A B, f n := by
  simp only [primeChargeWindowContrast, sub_mul, mul_assoc, ite_mul, one_mul, zero_mul,
    sum_sub_distrib, ← mul_sum]
  rw [sum_window_indicator hCN, sum_window_indicator hBN]

/-- The terminal contrast has exactly zero pole coordinate at its finite horizon. -/
theorem primeChargeWindowContrast_harmonic_neutral {A B C N : ℕ}
    (hAB : A < B) (hBN : B ≤ N) (hCN : C ≤ N) :
    (∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n / (n : ℝ)) = 0 := by
  simp only [div_eq_mul_inv]
  rw [primeChargeWindowContrast_sum hBN hCN]
  have hmass (D E : ℕ) : (∑ n ∈ Ioc D E, (n : ℝ)⁻¹) = primeChargeWindowMass D E := by
    simp only [primeChargeWindowMass, one_div]
  rw [hmass, hmass]
  change primeChargeWindowMass B C -
    (primeChargeWindowMass B C / primeChargeWindowMass A B) * primeChargeWindowMass A B = 0
  rw [div_mul_cancel₀ _ (primeChargeWindowMass_pos hAB).ne', sub_self]

/-- Its square contains exactly the two disjoint harmonic window masses. -/
theorem primeChargeWindowContrast_harmonic_square {A B C N : ℕ}
    (hBN : B ≤ N) (hCN : C ≤ N) :
    (∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n ^ 2 / (n : ℝ)) =
      primeChargeWindowMass B C +
        (primeChargeWindowMass B C / primeChargeWindowMass A B) ^ 2 * primeChargeWindowMass A B := by
  have hpoint (n : ℕ) : primeChargeWindowContrast A B C n ^ 2 / (n : ℝ) =
      (if n ∈ Ioc B C then 1 / (n : ℝ) else 0) +
        (primeChargeWindowMass B C / primeChargeWindowMass A B) ^ 2 *
          (if n ∈ Ioc A B then 1 / (n : ℝ) else 0) := by
    unfold primeChargeWindowContrast
    by_cases hu : n ∈ Ioc B C
    · have hl : n ∉ Ioc A B := by
        intro h
        have := (mem_Ioc.mp hu).1
        have := (mem_Ioc.mp h).2
        omega
      simp only [if_pos hu, if_neg hl]
      ring
    · by_cases hl : n ∈ Ioc A B
      · simp only [if_neg hu, if_pos hl]
        ring
      · simp only [if_neg hu, if_neg hl]
        ring
  simp only [hpoint, sum_add_distrib, ← mul_sum]
  rw [sum_window_indicator hCN, sum_window_indicator hBN]
  rfl

/-- The contrast's nonpolar conductor coordinate is a boundary error. -/
theorem abs_primeChargeWindowContrast_mode_pairing_le {m A B C N : ℕ}
    (hm : 1 < m) (hAB : A ≤ B) (hBC : B ≤ C) (hCN : C ≤ N) :
    |∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n *
      (normalizedRamanujanMode m n / (n : ℝ))| ≤
      8 * (m : ℝ) * (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) /
        ((A : ℝ) + 1) := by
  rw [primeChargeWindowContrast_sum (hBC.trans hCN) hCN]
  have hupper := abs_normalizedRamanujan_harmonic_window_le hm hBC
  have hlower := abs_normalizedRamanujan_harmonic_window_le hm hAB
  have hden : 8 * (m : ℝ) / ((B : ℝ) + 1) ≤ 8 * (m : ℝ) / ((A : ℝ) + 1) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast Nat.add_le_add_right hAB 1)
  calc
    _ ≤ |∑ n ∈ Ioc B C, normalizedRamanujanMode m n / (n : ℝ)| +
        |(primeChargeWindowMass B C / primeChargeWindowMass A B) *
          ∑ n ∈ Ioc A B, normalizedRamanujanMode m n / (n : ℝ)| := abs_sub _ _
    _ ≤ 8 * (m : ℝ) / ((A : ℝ) + 1) +
        |primeChargeWindowMass B C / primeChargeWindowMass A B| *
          (8 * (m : ℝ) / ((A : ℝ) + 1)) := by
      rw [abs_mul]
      exact add_le_add (hupper.trans hden) (mul_le_mul_of_nonneg_left hlower (abs_nonneg _))
    _ = _ := by ring

/-- The lower conductor frame bounds the projection by its actual conductor coordinates. -/
theorem primeCharge_conductor_projection_sq_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖(conductorSubspace Q N).starProjection x‖ ^ 2 ≤
      2 * ∑ m ∈ Icc 1 Q, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
  let p := (conductorSubspace Q N).starProjection x
  have hp : p ∈ conductorSubspace Q N := (conductorSubspace Q N).starProjection_apply_mem x
  obtain ⟨a, -, ha⟩ := (mem_conductorSubspace_iff (x := p)).mp hp
  have hcoef := (half_and_three_halves_riesz_of_log_le hQ hQN hlog a).1
  rw [← ha] at hcoef
  have hxp : ⟪x, p⟫ = ‖p‖ ^ 2 := by
    have h := (conductorSubspace Q N).starProjection_inner_eq_zero x p hp
    change ⟪x - p, p⟫ = 0 at h
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
    linarith only [h]
  have hsum : (∑ m ∈ Icc 1 Q, a m * ⟪x, normalizedRamanujanHorizonVector m N⟫) =
      ‖p‖ ^ 2 := by
    rw [← hxp, ha, inner_sum]
    simp only [real_inner_smul_right]
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 Q) a
    (fun m => ⟪x, normalizedRamanujanHorizonVector m N⟫)
  rw [hsum] at hcs
  have hcoef' : (∑ m ∈ Icc 1 Q, a m ^ 2) ≤ 2 * ‖p‖ ^ 2 := by linarith only [hcoef]
  have hbound := hcs.trans (mul_le_mul_of_nonneg_right hcoef'
    (sum_nonneg fun m _ => sq_nonneg ⟪x, normalizedRamanujanHorizonVector m N⟫))
  change ‖p‖ ^ 2 ≤ _
  by_cases hp0 : ‖p‖ ^ 2 = 0
  · rw [hp0]
    exact mul_nonneg zero_le_two (sum_nonneg fun m _ => sq_nonneg _)
  · have hp2 : 0 < ‖p‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hp0)
    have hh : ‖p‖ ^ 2 * ‖p‖ ^ 2 ≤ ‖p‖ ^ 2 *
        (2 * ∑ m ∈ Icc 1 Q, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2) := by
      calc
        _ = (‖p‖ ^ 2) ^ 2 := (sq _).symm
        _ ≤ _ := hbound
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ hp2).mp hh

/-- The terminal contrast in the same physical normalization as conductor vectors. -/
def primeChargeWindowVector (A B C N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ • packetVector (primeChargeWindowContrast A B C) N

private theorem packet_inner_ramanujan (F : ℕ → ℝ) (m N : ℕ) :
    ⟪packetVector F N, ramanujanHorizonVector m N⟫ =
      ∑ n ∈ Icc 1 N, F n * (normalizedRamanujanMode m n / (n : ℝ)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N,
    (normalizedRamanujanMode m n / Real.sqrt (n : ℕ)) * (F n / Real.sqrt (n : ℕ))) = _
  rw [sum_coe_sort (Icc 1 N) (fun n =>
    (normalizedRamanujanMode m n / Real.sqrt n) * (F n / Real.sqrt n))]
  apply sum_congr rfl
  intro n _
  rw [div_mul_div_comm, ← sq, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

/-- Conductor coordinates are literal harmonic pairings divided by the horizon logarithm. -/
theorem primeChargeWindowVector_inner (A B C m N : ℕ) :
    ⟪primeChargeWindowVector A B C N, normalizedRamanujanHorizonVector m N⟫ =
      (∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n *
        (normalizedRamanujanMode m n / (n : ℝ))) / Real.log N := by
  rw [primeChargeWindowVector, normalizedRamanujanHorizonVector,
    real_inner_smul_left, real_inner_smul_right, packet_inner_ramanujan]
  have hs : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← mul_assoc, hs]
  ring

/-- The contrast has an explicit physical norm. -/
theorem primeChargeWindowVector_norm_sq {A B C N : ℕ}
    (hBN : B ≤ N) (hCN : C ≤ N) :
    ‖primeChargeWindowVector A B C N‖ ^ 2 =
      (primeChargeWindowMass B C +
        (primeChargeWindowMass B C / primeChargeWindowMass A B) ^ 2 * primeChargeWindowMass A B) /
          Real.log N := by
  rw [primeChargeWindowVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N), packetVector_norm_sq,
    primeChargeWindowContrast_harmonic_square hBN hCN]
  ring

/-- A terminal contrast has a quantitatively negligible projection onto sufficiently low conductors. -/
theorem primeChargeWindowVector_projection_sq_le {Q A B C N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    (hAB : A < B) (hBC : B ≤ C) (hCN : C ≤ N) :
    ‖(conductorSubspace Q N).starProjection (primeChargeWindowVector A B C N)‖ ^ 2 ≤
      128 * (Q : ℝ) ^ 3 *
        (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) ^ 2 /
          (((A : ℝ) + 1) ^ 2 * Real.log N ^ 2) := by
  have hL : 0 < Real.log (N : ℝ) := by
    linarith only [hlog, Real.log_natCast_nonneg Q]
  let D := 8 * (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) /
    (((A : ℝ) + 1) * Real.log N)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hcoord (m : ℕ) (hm : m ∈ Icc 1 Q) :
      |⟪primeChargeWindowVector A B C N, normalizedRamanujanHorizonVector m N⟫| ≤
        D * Q := by
    have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hmQ hD)
    rw [primeChargeWindowVector_inner, abs_div, abs_of_pos hL]
    by_cases hm1 : m = 1
    · subst m
      simp only [normalizedRamanujanMode_one, mul_one_div,
        primeChargeWindowContrast_harmonic_neutral hAB (hBC.trans hCN) hCN,
        abs_zero, zero_div]
      exact mul_nonneg hD (by norm_num)
    · have hb := abs_primeChargeWindowContrast_mode_pairing_le
        (by have := (mem_Icc.mp hm).1; omega : 1 < m) hAB.le hBC hCN
      exact (div_le_div_of_nonneg_right hb hL.le).trans_eq (by
        dsimp only [D]
        field_simp [hL.ne', show (A : ℝ) + 1 ≠ 0 by positivity])
  have hsum : (∑ m ∈ Icc 1 Q,
      ⟪primeChargeWindowVector A B C N, normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤
        (Q : ℝ) * (D * Q) ^ 2 := by
    calc
      _ ≤ ∑ m ∈ Icc 1 Q, (D * Q) ^ 2 := sum_le_sum fun m hm => by
        have h := pow_le_pow_left₀ (abs_nonneg _) (hcoord m hm) 2
        simpa only [sq_abs] using h
      _ = _ := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  refine (primeCharge_conductor_projection_sq_le hQ hQN hlog _).trans
    ((mul_le_mul_of_nonneg_left hsum zero_le_two).trans_eq ?_)
  dsimp only [D]
  field_simp [hL.ne', show (A : ℝ) + 1 ≠ 0 by positivity]
  ring

#print axioms primeChargeWindowContrast_harmonic_neutral
#print axioms abs_primeChargeWindowContrast_mode_pairing_le
#print axioms primeCharge_conductor_projection_sq_le
#print axioms primeChargeWindowVector_projection_sq_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
