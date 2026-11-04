import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeWindows

/-!
# Terminal contrasts on a fixed receiving conductor

The harmonic Gram finite part cancels between both endpoints of a window.
An exactly balanced terminal contrast also cancels its diagonal mean.
Consequently multiplication by any fixed conductor preserves the small
projection onto a growing low-conductor space.
-/

noncomputable section

open Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SuccessorShellArithmetic ArithmeticEffectivityTheory BezoutValuationIncidence
  CompletedArithmeticForms

private theorem window_eq_prefix_sub {A B : ℕ} (hAB : A ≤ B) (f : ℕ → ℝ) :
    (∑ n ∈ Ioc A B, f n) = (∑ n ∈ Icc 1 B, f n) - ∑ n ∈ Icc 1 A, f n := by
  have hs : (Ioc A B : Finset ℕ) = Icc 1 B \ Icc 1 A := by
    ext n
    simp only [mem_Ioc, mem_sdiff, mem_Icc]
    omega
  have hsub : Icc 1 A ⊆ Icc 1 B := Icc_subset_Icc le_rfl hAB
  have hsum := sum_sdiff (f := f) hsub
  rw [← hs] at hsum
  linarith only [hsum]

/-- Centered conductor products have only endpoint error on a terminal harmonic window. -/
theorem abs_modeProduct_harmonic_window_le {m l A B : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hAB : A ≤ B) :
    |(∑ n ∈ Ioc A B,
        normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
      (if m = l then 1 else 0) * primeChargeWindowMass A B| ≤
        8 * (m : ℝ) * l / ((A : ℝ) + 1) := by
  let δ : ℝ := if m = l then 1 else 0
  let I := orbitIntersection m l /
    (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))
  let G (N : ℕ) := ∑ n ∈ Icc 1 N,
    normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)
  have hA : |G A - δ * (harmonic A : ℝ) + I| ≤
      4 * (m : ℝ) * l / ((A : ℝ) + 1) :=
    abs_normalizedRamanujan_harmonicGram_torsion_remainder hm hl A
  have hB : |G B - δ * (harmonic B : ℝ) + I| ≤
      4 * (m : ℝ) * l / ((B : ℝ) + 1) :=
    abs_normalizedRamanujan_harmonicGram_torsion_remainder hm hl B
  have hden : 4 * (m : ℝ) * l / ((B : ℝ) + 1) ≤
      4 * (m : ℝ) * l / ((A : ℝ) + 1) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hAB 1)
  have hmass : primeChargeWindowMass A B = (harmonic B : ℝ) - (harmonic A : ℝ) := by
    rw [primeChargeWindowMass, window_eq_prefix_sub hAB]
    rw [HTGeometry.sum_Icc_one_div_eq_harmonic, HTGeometry.sum_Icc_one_div_eq_harmonic]
  rw [window_eq_prefix_sub hAB, hmass]
  change |G B - G A - δ * ((harmonic B : ℝ) - (harmonic A : ℝ))| ≤ _
  calc
    _ = |(G B - δ * (harmonic B : ℝ) + I) - (G A - δ * (harmonic A : ℝ) + I)| := by
      congr 1
      ring
    _ ≤ _ := (abs_sub _ _).trans ((add_le_add hB hA).trans (by linarith only [hden]))

/-- Exact harmonic balancing removes the diagonal term even after multiplying two modes. -/
theorem abs_primeChargeWindowContrast_modeProduct_pairing_le {m l A B C N : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hAB : A < B) (hBC : B ≤ C) (hCN : C ≤ N) :
    |∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n *
      (normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ))| ≤
      8 * (m : ℝ) * l * (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) /
        ((A : ℝ) + 1) := by
  let δ : ℝ := if m = l then 1 else 0
  let κ := primeChargeWindowMass B C / primeChargeWindowMass A B
  let G (D E : ℕ) := ∑ n ∈ Ioc D E,
    normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)
  have hupper := abs_modeProduct_harmonic_window_le hm hl hBC
  have hlower := abs_modeProduct_harmonic_window_le hm hl hAB.le
  have hden : 8 * (m : ℝ) * l / ((B : ℝ) + 1) ≤
      8 * (m : ℝ) * l / ((A : ℝ) + 1) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hAB.le 1)
  have hcancel : κ * primeChargeWindowMass A B = primeChargeWindowMass B C :=
    div_mul_cancel₀ _ (primeChargeWindowMass_pos hAB).ne'
  rw [primeChargeWindowContrast_sum (hBC.trans hCN) hCN]
  change |G B C - κ * G A B| ≤ _
  calc
    _ = |(G B C - δ * primeChargeWindowMass B C) -
        κ * (G A B - δ * primeChargeWindowMass A B)| := by
      congr 1
      linear_combination δ * hcancel
    _ ≤ |G B C - δ * primeChargeWindowMass B C| +
        |κ| * |G A B - δ * primeChargeWindowMass A B| := by
      simpa only [abs_mul] using abs_sub (G B C - δ * primeChargeWindowMass B C)
        (κ * (G A B - δ * primeChargeWindowMass A B))
    _ ≤ 8 * (m : ℝ) * l / ((A : ℝ) + 1) +
        |κ| * (8 * (m : ℝ) * l / ((A : ℝ) + 1)) :=
      add_le_add (hupper.trans hden) (mul_le_mul_of_nonneg_left hlower (abs_nonneg _))
    _ = _ := by dsimp only [κ]; ring

/-- A terminal contrast carrying one fixed conductor. -/
def fibreChargeWindowVector (m A B C N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ • packetVector
    (fun n => normalizedRamanujanMode m n * primeChargeWindowContrast A B C n) N

/-- A squared contrast has the two disjoint window weights against every scalar sequence. -/
theorem primeChargeWindowContrast_square_sum {A B C N : ℕ}
    (hBN : B ≤ N) (hCN : C ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n ^ 2 * f n) =
      (∑ n ∈ Ioc B C, f n) +
        (primeChargeWindowMass B C / primeChargeWindowMass A B) ^ 2 * ∑ n ∈ Ioc A B, f n := by
  have hpoint (n : ℕ) : primeChargeWindowContrast A B C n ^ 2 * f n =
      (if n ∈ Ioc B C then f n else 0) +
        (primeChargeWindowMass B C / primeChargeWindowMass A B) ^ 2 *
          (if n ∈ Ioc A B then f n else 0) := by
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
  have hwindow {D E : ℕ} (hEN : E ≤ N) :
      (∑ n ∈ Icc 1 N, if n ∈ Ioc D E then f n else 0) = ∑ n ∈ Ioc D E, f n := by
    rw [← sum_filter]
    congr 1
    ext n
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  simp only [hpoint, sum_add_distrib, ← mul_sum]
  rw [hwindow hCN, hwindow hBN]

/-- The fibre contrast norm is the literal mode-square mass on its two windows. -/
theorem fibreChargeWindowVector_norm_sq {A B C N : ℕ} (hBN : B ≤ N) (hCN : C ≤ N) (m : ℕ) :
    ‖fibreChargeWindowVector m A B C N‖ ^ 2 =
      ((∑ n ∈ Ioc B C, normalizedRamanujanMode m n ^ 2 / (n : ℝ)) +
        (primeChargeWindowMass B C / primeChargeWindowMass A B) ^ 2 *
          ∑ n ∈ Ioc A B, normalizedRamanujanMode m n ^ 2 / (n : ℝ)) / Real.log N := by
  rw [fibreChargeWindowVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N), packetVector_norm_sq]
  have hsum : (∑ n ∈ Icc 1 N,
      (normalizedRamanujanMode m n * primeChargeWindowContrast A B C n) ^ 2 / (n : ℝ)) =
      ∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n ^ 2 *
        (normalizedRamanujanMode m n ^ 2 / (n : ℝ)) :=
    sum_congr rfl fun _ _ => by ring
  rw [hsum, primeChargeWindowContrast_square_sum hBN hCN]
  ring

/-- Multiplication by a fixed normalized mode preserves the terminal contrast norm asymptotically. -/
theorem abs_fibreChargeWindowVector_norm_sq_sub_le {m A B C N : ℕ}
    (hm : 0 < m) (hAB : A ≤ B) (hBC : B ≤ C) (hCN : C ≤ N) (hL : 0 < Real.log N) :
    |‖fibreChargeWindowVector m A B C N‖ ^ 2 - ‖primeChargeWindowVector A B C N‖ ^ 2| ≤
      8 * (m : ℝ) ^ 2 *
        (1 + (primeChargeWindowMass B C / primeChargeWindowMass A B) ^ 2) /
          (((A : ℝ) + 1) * Real.log N) := by
  let κ := primeChargeWindowMass B C / primeChargeWindowMass A B
  let D (E F : ℕ) := (∑ n ∈ Ioc E F, normalizedRamanujanMode m n ^ 2 / (n : ℝ)) -
    primeChargeWindowMass E F
  have hupper : |D B C| ≤ 8 * (m : ℝ) ^ 2 / ((B : ℝ) + 1) := by
    simpa only [D, ite_true, one_mul, ← sq, mul_assoc] using
      abs_modeProduct_harmonic_window_le hm hm hBC
  have hlower : |D A B| ≤ 8 * (m : ℝ) ^ 2 / ((A : ℝ) + 1) := by
    simpa only [D, ite_true, one_mul, ← sq, mul_assoc] using
      abs_modeProduct_harmonic_window_le hm hm hAB
  have hden : 8 * (m : ℝ) ^ 2 / ((B : ℝ) + 1) ≤ 8 * (m : ℝ) ^ 2 / ((A : ℝ) + 1) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hAB 1)
  have he : ‖fibreChargeWindowVector m A B C N‖ ^ 2 - ‖primeChargeWindowVector A B C N‖ ^ 2 =
      (D B C + κ ^ 2 * D A B) / Real.log N := by
    rw [fibreChargeWindowVector_norm_sq (hBC.trans hCN) hCN,
      primeChargeWindowVector_norm_sq (hBC.trans hCN) hCN]
    dsimp only [D, κ]
    ring
  rw [he, abs_div, abs_of_pos hL]
  have hsum : |D B C + κ ^ 2 * D A B| ≤
      8 * (m : ℝ) ^ 2 / ((A : ℝ) + 1) + κ ^ 2 * (8 * (m : ℝ) ^ 2 / ((A : ℝ) + 1)) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg κ)]
    exact add_le_add (hupper.trans hden) (mul_le_mul_of_nonneg_left hlower (sq_nonneg κ))
  exact (div_le_div_of_nonneg_right hsum hL.le).trans_eq (by dsimp only [κ]; ring)

theorem fibreChargeWindowVector_inner (m A B C l N : ℕ) :
    ⟪fibreChargeWindowVector m A B C N, normalizedRamanujanHorizonVector l N⟫ =
      (∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n *
        (normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ))) / Real.log N := by
  have hv : ramanujanHorizonVector l N = packetVector (normalizedRamanujanMode l) N := rfl
  rw [fibreChargeWindowVector, normalizedRamanujanHorizonVector, hv,
    real_inner_smul_left, real_inner_smul_right, packetVector_inner]
  have hs : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← mul_assoc, hs]
  have hsum : (∑ n ∈ Icc 1 N,
      (normalizedRamanujanMode m n * primeChargeWindowContrast A B C n) *
        normalizedRamanujanMode l n / (n : ℝ)) =
      ∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n *
        (normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) :=
    sum_congr rfl fun _ _ => by ring
  rw [hsum]
  ring

/-- The projection cost remains cubic in the conductor cutoff, with a fixed fibre factor. -/
theorem fibreChargeWindowVector_projection_sq_le {m Q A B C N : ℕ}
    (hm : 0 < m) (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    (hAB : A < B) (hBC : B ≤ C) (hCN : C ≤ N) :
    ‖(conductorSubspace Q N).starProjection (fibreChargeWindowVector m A B C N)‖ ^ 2 ≤
      128 * (m : ℝ) ^ 2 * (Q : ℝ) ^ 3 *
        (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) ^ 2 /
          (((A : ℝ) + 1) ^ 2 * Real.log N ^ 2) := by
  have hL : 0 < Real.log (N : ℝ) := by
    linarith only [hlog, Real.log_natCast_nonneg Q]
  let D := 8 * (m : ℝ) * (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) /
    (((A : ℝ) + 1) * Real.log N)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hcoord (l : ℕ) (hl : l ∈ Icc 1 Q) :
      |⟪fibreChargeWindowVector m A B C N, normalizedRamanujanHorizonVector l N⟫| ≤ D * Q := by
    have hlQ : (l : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hl).2
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hlQ hD)
    rw [fibreChargeWindowVector_inner, abs_div, abs_of_pos hL]
    have hb := abs_primeChargeWindowContrast_modeProduct_pairing_le
      hm (mem_Icc.mp hl).1 hAB hBC hCN
    exact (div_le_div_of_nonneg_right hb hL.le).trans_eq (by
      dsimp only [D]
      field_simp [hL.ne', show (A : ℝ) + 1 ≠ 0 by positivity])
  have hsum : (∑ l ∈ Icc 1 Q,
      ⟪fibreChargeWindowVector m A B C N, normalizedRamanujanHorizonVector l N⟫ ^ 2) ≤
        (Q : ℝ) * (D * Q) ^ 2 := by
    calc
      _ ≤ ∑ l ∈ Icc 1 Q, (D * Q) ^ 2 := sum_le_sum fun l hl => by
        have h := pow_le_pow_left₀ (abs_nonneg _) (hcoord l hl) 2
        simpa only [sq_abs] using h
      _ = _ := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  refine (primeCharge_conductor_projection_sq_le hQ hQN hlog _).trans
    ((mul_le_mul_of_nonneg_left hsum zero_le_two).trans_eq ?_)
  dsimp only [D]
  field_simp [hL.ne', show (A : ℝ) + 1 ≠ 0 by positivity]
  ring

#print axioms abs_modeProduct_harmonic_window_le
#print axioms abs_primeChargeWindowContrast_modeProduct_pairing_le
#print axioms fibreChargeWindowVector_projection_sq_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
