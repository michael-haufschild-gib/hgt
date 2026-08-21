import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeMatchedQuadrature
import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileTransportProducer

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- One exact prime-quantile reporter transport cell, retaining its orientation. -/
def ccmPrimePolarReporterQuantileCellTransport
    (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n + 1),
    Real.exp (h / 2) * (F (Real.log n) - F h)

/-- Oriented terminal reporter transport from the last quantile boundary to the physical wall. -/
def ccmPrimePolarReporterQuantileTerminalTransport
    (F : ℝ → ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
    Real.exp (h / 2) * (F T - F h)

/-- Cells and terminal seam are added before any absolute value or energy square. -/
def ccmPrimePolarReporterCompletedQuantileTransport
    (F : ℝ → ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N,
      ccmPrimePolarReporterQuantileCellTransport F n) +
    ccmPrimePolarReporterQuantileTerminalTransport F N T

private theorem primeAtom_sub_quantileCell_eq_reporterTransport
    (F : ℝ → ℝ) (hF : Continuous F) (n : ℕ) :
    criticalMellinAtomWeight n * F (Real.log n) -
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) * F h) =
      ccmPrimePolarReporterQuantileCellTransport F n := by
  let lo := ccmOutgoingPrimeQuantileBoundary n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1)
  have hweight : Continuous (fun h : ℝ => Real.exp (h / 2)) := by fun_prop
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * F (Real.log n)) volume lo hi :=
    (hweight.mul continuous_const).intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * F h) volume lo hi :=
    (hweight.mul hF).intervalIntegrable _ _
  have hmass := integral_exp_half_quantileCell_eq_atomWeight n
  have hfirst :
      (∫ h in lo..hi, Real.exp (h / 2) * F (Real.log n)) =
        criticalMellinAtomWeight n * F (Real.log n) := by
    calc
      _ = F (Real.log n) * ∫ h in lo..hi, Real.exp (h / 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro h hh
        ring
      _ = _ := by rw [hmass]; ring
  rw [ccmPrimePolarReporterQuantileCellTransport]
  calc
    criticalMellinAtomWeight n * F (Real.log n) -
        (∫ h in lo..hi, Real.exp (h / 2) * F h) =
      (∫ h in lo..hi, Real.exp (h / 2) * F (Real.log n)) -
        ∫ h in lo..hi, Real.exp (h / 2) * F h := by rw [hfirst]
    _ = ∫ h in lo..hi,
        (Real.exp (h / 2) * F (Real.log n) -
          Real.exp (h / 2) * F h) :=
      (intervalIntegral.integral_sub hconst hvar).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro h hh
      ring

private theorem sum_reporterQuantileCells_eq_prime_sub_polar
    (F : ℝ → ℝ) (hF : Continuous F) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        ccmPrimePolarReporterQuantileCellTransport F n) =
      (∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n * F (Real.log n)) -
        ∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * F h := by
  have hpartition :
      (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * F h) =
        ∑ n ∈ Finset.range N,
          ∫ h in ccmOutgoingPrimeQuantileBoundary n..
              ccmOutgoingPrimeQuantileBoundary (n + 1),
            Real.exp (h / 2) * F h := by
    let G : ℝ → ℝ := fun h => Real.exp (h / 2) * F h
    have hG : Continuous G :=
      (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul hF
    induction N with
    | zero => simp [ccmOutgoingPrimeQuantileBoundary_zero]
    | succ N ih =>
        rw [Finset.sum_range_succ, ← ih]
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hG.intervalIntegrable (μ := volume) 0
            (ccmOutgoingPrimeQuantileBoundary N))
          (hG.intervalIntegrable (μ := volume)
            (ccmOutgoingPrimeQuantileBoundary N)
            (ccmOutgoingPrimeQuantileBoundary (N + 1)))).symm
  rw [hpartition, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact (primeAtom_sub_quantileCell_eq_reporterTransport F hF n).symm

private theorem reporterTerminalTransport_eq_mass_sub_polar
    (F : ℝ → ℝ) (hF : Continuous F) (N : ℕ) (T : ℝ) :
    ccmPrimePolarReporterQuantileTerminalTransport F N T =
      (∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
        Real.exp (h / 2)) * F T -
      ∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
        Real.exp (h / 2) * F h := by
  let lo := ccmOutgoingPrimeQuantileBoundary N
  have hweight : Continuous (fun h : ℝ => Real.exp (h / 2)) := by fun_prop
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * F T) volume lo T :=
    (hweight.mul continuous_const).intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * F h) volume lo T :=
    (hweight.mul hF).intervalIntegrable _ _
  rw [ccmPrimePolarReporterQuantileTerminalTransport]
  calc
    (∫ h in lo..T, Real.exp (h / 2) * (F T - F h)) =
      ∫ h in lo..T,
        (Real.exp (h / 2) * F T - Real.exp (h / 2) * F h) := by
      apply intervalIntegral.integral_congr
      intro h hh
      ring
    _ = (∫ h in lo..T, Real.exp (h / 2) * F T) -
        ∫ h in lo..T, Real.exp (h / 2) * F h :=
      intervalIntegral.integral_sub hconst hvar
    _ = (∫ h in lo..T, Real.exp (h / 2)) * F T -
        ∫ h in lo..T, Real.exp (h / 2) * F h := by
      rw [intervalIntegral.integral_mul_const]

/-- Completed quantile transport equals the finite prime-minus-outgoing-polar reporter plus its
exact terminal mass coefficient. -/
theorem ccmPrimePolarReporterCompletedQuantileTransport_eq
    (F : ℝ → ℝ) (hF : Continuous F) (N : ℕ) (T : ℝ) :
    ccmPrimePolarReporterCompletedQuantileTransport F N T =
      (∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n * F (Real.log n)) -
      (∫ h in (0 : ℝ)..T, Real.exp (h / 2) * F h) +
      (∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
        Real.exp (h / 2)) * F T := by
  let lo := ccmOutgoingPrimeQuantileBoundary N
  let G : ℝ → ℝ := fun h => Real.exp (h / 2) * F h
  have hG : Continuous G :=
    (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul hF
  have hsplit :
      (∫ h in (0 : ℝ)..T, G h) =
        (∫ h in (0 : ℝ)..lo, G h) + ∫ h in lo..T, G h :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG.intervalIntegrable (μ := volume) 0 lo)
      (hG.intervalIntegrable (μ := volume) lo T)).symm
  dsimp only [G, lo] at hsplit
  rw [ccmPrimePolarReporterCompletedQuantileTransport,
    sum_reporterQuantileCells_eq_prime_sub_polar F hF N,
    reporterTerminalTransport_eq_mass_sub_polar F hF N T]
  linarith

/-- Actual third-grade reporter transported cellwise and through its oriented terminal seam. -/
def ccmThirdGradeCesaroCompletedQuantileTransport (b H : ℝ) : ℝ :=
  ccmPrimePolarReporterCompletedQuantileTransport
    (ccmThirdGradeCesaroClippedTriangularWeight b H)
    (Nat.floor (Real.exp H) + 1) H

theorem ccmThirdGradeCesaroClippedTriangularWeight_endpoint
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmThirdGradeCesaroClippedTriangularWeight b H H = 0 := by
  have hH : 0 < H := hb.trans_le hbH
  unfold ccmThirdGradeCesaroClippedTriangularWeight
  rw [max_eq_right hbH]
  simp [ccmGuinandWeilThirdGradeCesaroTriangularWeight,
    ccmGuinandWeilThirdGradeWeight, hH.ne']

/-- The terminal mass mismatch cancels exactly because the triangular reporter vanishes at the
moving wall. No terminal absolute bound is taken. -/
theorem ccmThirdGradeCesaroCompletedQuantileTransport_eq_fullOutgoing
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmThirdGradeCesaroCompletedQuantileTransport b H =
      (∑ n ∈ Finset.range (Nat.floor (Real.exp H) + 1),
        criticalMellinAtomWeight n *
          ccmThirdGradeCesaroClippedTriangularWeight b H (Real.log n)) -
      ∫ h in (0 : ℝ)..H,
        Real.exp (h / 2) * ccmThirdGradeCesaroClippedTriangularWeight b H h := by
  rw [ccmThirdGradeCesaroCompletedQuantileTransport,
    ccmPrimePolarReporterCompletedQuantileTransport_eq
      _ (lipschitzWith_ccmThirdGradeCesaroClippedTriangularWeight hb hbH).continuous]
  rw [ccmThirdGradeCesaroClippedTriangularWeight_endpoint hb hbH]
  ring

/-- Fixed lower-wall outgoing discrepancy introduced by freezing the reporter below `b`. -/
def ccmThirdGradeCesaroLowerOutgoingCorrection (b H : ℝ) : ℝ :=
  ccmGuinandWeilThirdGradeCesaroTriangularWeight H b *
    (criticalMellinPrimeMass b -
      (2 * Real.exp (b / 2) - 2))

private theorem ccmThirdGradeCesaroClippedTriangularWeight_eq_lower
    {b H h : ℝ} (hb : 0 < b) (hbH : b ≤ H) (hhb : h ≤ b) :
    ccmThirdGradeCesaroClippedTriangularWeight b H h =
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H b := by
  have hH : 0 < H := hb.trans_le hbH
  have hfactor : 0 ≤ 1 - b / H := by
    rw [sub_nonneg, div_le_one hH]
    exact hbH
  have hweight : 0 ≤ ccmGuinandWeilThirdGradeCesaroTriangularWeight H b := by
    unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
    positivity
  simp [ccmThirdGradeCesaroClippedTriangularWeight, max_eq_left hhb,
    max_eq_left hweight]

private theorem sum_range_succ_eq_sum_Icc_two
    (N : ℕ) (F : ℕ → ℝ) (h0 : F 0 = 0) (h1 : F 1 = 0) :
    (∑ n ∈ Finset.range (N + 1), F n) =
      ∑ n ∈ Finset.Icc 2 N, F n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro n hnrange hnnot
    simp only [Finset.mem_range] at hnrange
    have hnlt : n < 2 := by
      by_contra h
      have hn2 : 2 ≤ n := Nat.le_of_not_gt h
      exact hnnot (Finset.mem_Icc.mpr ⟨hn2, by omega⟩)
    interval_cases n
    · exact h0
    · exact h1

private theorem ccmThirdGradeCesaro_fullPrimeSum_eq_physical_add_lower
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∑ n ∈ Finset.range (Nat.floor (Real.exp H) + 1),
        criticalMellinAtomWeight n *
          ccmThirdGradeCesaroClippedTriangularWeight b H (Real.log n)) =
      (∑ n ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log n then
          criticalMellinAtomWeight n *
            ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log n)
        else 0) +
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H b *
        criticalMellinPrimeMass b := by
  let N := Nat.floor (Real.exp H)
  let C : ℕ → ℝ := fun n => criticalMellinAtomWeight n *
    ccmThirdGradeCesaroClippedTriangularWeight b H (Real.log n)
  have hrange : (∑ n ∈ Finset.range (N + 1), C n) =
      ∑ n ∈ Finset.Icc 2 N, C n :=
    sum_range_succ_eq_sum_Icc_two N C
      (by simp [C, criticalMellinAtomWeight])
      (by simp [C, criticalMellinAtomWeight])
  have hmass := criticalMellinPrimeMass_eq_commonAtomStep hbH
  change (∑ n ∈ Finset.range (N + 1), C n) = _
  rw [hrange, hmass, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  by_cases hbn : b < Real.log n
  · have hnexp : (n : ℝ) ≤ Real.exp H :=
      (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hn).2
    have hlogH : Real.log n ≤ H :=
      (Real.log_le_iff_le_exp hnpos).mpr hnexp
    have hclip := ccmThirdGradeCesaroClippedTriangularWeight_eq
      hb hbn.le hlogH
    simp [C, hbn, not_le.mpr hbn, hclip]
  · have hlogb : Real.log n ≤ b := le_of_not_gt hbn
    have hclip := ccmThirdGradeCesaroClippedTriangularWeight_eq_lower
      hb hbH hlogb
    simp [C, hbn, hlogb, hclip]
    ring

private theorem ccmThirdGradeCesaro_fullOutgoingIntegral_eq_physical_add_lower
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∫ h in (0 : ℝ)..H,
        Real.exp (h / 2) *
          ccmThirdGradeCesaroClippedTriangularWeight b H h) =
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H b *
          (2 * Real.exp (b / 2) - 2) +
        ∫ h in b..H,
          Real.exp (h / 2) *
            ccmGuinandWeilThirdGradeCesaroTriangularWeight H h := by
  let C := ccmThirdGradeCesaroClippedTriangularWeight b H
  let R := ccmGuinandWeilThirdGradeCesaroTriangularWeight H
  let G : ℝ → ℝ := fun h => Real.exp (h / 2) * C h
  have hC : Continuous C :=
    (lipschitzWith_ccmThirdGradeCesaroClippedTriangularWeight hb hbH).continuous
  have hG : Continuous G :=
    (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul hC
  have hsplit : (∫ h in (0 : ℝ)..H, G h) =
      (∫ h in (0 : ℝ)..b, G h) + ∫ h in b..H, G h :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG.intervalIntegrable (μ := volume) 0 b)
      (hG.intervalIntegrable (μ := volume) b H)).symm
  have hlower : (∫ h in (0 : ℝ)..b, G h) =
      R b * (2 * Real.exp (b / 2) - 2) := by
    calc
      (∫ h in (0 : ℝ)..b, G h) =
          ∫ h in (0 : ℝ)..b, R b * Real.exp (h / 2) := by
        apply intervalIntegral.integral_congr
        intro h hh
        rw [Set.uIcc_of_le hb.le] at hh
        dsimp only [G, C, R]
        rw [ccmThirdGradeCesaroClippedTriangularWeight_eq_lower hb hbH hh.2]
        ring
      _ = R b * ∫ h in (0 : ℝ)..b, Real.exp (h / 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = R b * (2 * Real.exp (b / 2) - 2) := by
        rw [_root_.RHTower.intervalIntegral_exp_half_eq]
        norm_num
  have hphysical : (∫ h in b..H, G h) =
      ∫ h in b..H, Real.exp (h / 2) * R h := by
    apply intervalIntegral.integral_congr
    intro h hh
    rw [Set.uIcc_of_le hbH] at hh
    dsimp only [G, C, R]
    rw [ccmThirdGradeCesaroClippedTriangularWeight_eq hb hh.1 hh.2]
  dsimp only [G, C, R] at hsplit hlower hphysical ⊢
  rw [hsplit, hlower, hphysical]

private theorem integral_triangular_mul_two_cosh_eq_outgoing_add_incoming
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∫ h in b..H,
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
          (2 * Real.cosh (h / 2))) =
      (∫ h in b..H,
        Real.exp (h / 2) *
          ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) +
        ccmThirdGradeCesaroIncomingPolarTail b H := by
  have hF : ContinuousOn
      (ccmGuinandWeilThirdGradeCesaroTriangularWeight H) (Set.uIcc b H) := by
    rw [Set.uIcc_of_le hbH]
    intro h hh
    exact (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
      (ne_of_gt (hb.trans_le hh.1))).continuousAt.continuousWithinAt
  have hplus : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) volume b H :=
    ((by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).continuousOn.mul
      hF).intervalIntegrable
  have hminus : IntervalIntegrable
      (fun h : ℝ => Real.exp (-(h / 2)) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) volume b H :=
    ((by fun_prop : Continuous fun h : ℝ => Real.exp (-(h / 2))).continuousOn.mul
      hF).intervalIntegrable
  rw [ccmThirdGradeCesaroIncomingPolarTail,
    ← intervalIntegral.integral_add hplus hminus]
  apply intervalIntegral.integral_congr
  intro h hh
  change ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
      (2 * Real.cosh (h / 2)) =
    Real.exp (h / 2) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h +
      Real.exp (-(h / 2)) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h
  rw [Real.cosh_eq]
  ring

/-- Exact completed oriented-transport form of the literal RH-bearing triangular window. The
terminal cell stays coupled and its endpoint coefficient vanishes identically. -/
theorem ccmGuinandWeilPrimePolarTriangularWindow_eq_completedQuantileTransport
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H) =
      ccmThirdGradeCesaroCompletedQuantileTransport b H -
        ccmThirdGradeCesaroLowerOutgoingCorrection b H -
          ccmThirdGradeCesaroIncomingPolarTail b H := by
  have hfull := ccmThirdGradeCesaroCompletedQuantileTransport_eq_fullOutgoing hb hbH
  have hprime := ccmThirdGradeCesaro_fullPrimeSum_eq_physical_add_lower hb hbH
  have hint := ccmThirdGradeCesaro_fullOutgoingIntegral_eq_physical_add_lower hb hbH
  have hpolar := integral_triangular_mul_two_cosh_eq_outgoing_add_incoming hb hbH
  rw [hprime, hint] at hfull
  rw [ccmGuinandWeilPrimePolarWeightedWindow,
    ccmThirdGradeCesaroLowerOutgoingCorrection, hpolar]
  linarith

theorem abs_ccmThirdGradeCesaroLowerOutgoingCorrection_le
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    |ccmThirdGradeCesaroLowerOutgoingCorrection b H| ≤
      (32 / b ^ 3) *
        |criticalMellinPrimeMass b - (2 * Real.exp (b / 2) - 2)| := by
  have hH : 0 < H := hb.trans_le hbH
  have hfactor0 : 0 ≤ 1 - b / H := by
    rw [sub_nonneg, div_le_one hH]
    exact hbH
  have hfactor1 : 1 - b / H ≤ 1 := by
    have : 0 ≤ b / H := by positivity
    linarith
  have hraw0 : 0 ≤ ccmGuinandWeilThirdGradeCesaroTriangularWeight H b := by
    unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
    positivity
  have hrawLe : ccmGuinandWeilThirdGradeCesaroTriangularWeight H b ≤ 32 / b ^ 3 := by
    unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
    exact mul_le_of_le_one_right (by positivity) hfactor1
  rw [ccmThirdGradeCesaroLowerOutgoingCorrection, abs_mul,
    abs_of_nonneg hraw0]
  exact mul_le_mul_of_nonneg_right hrawLe (abs_nonneg _)

/-- Uniform boundedness of the literal triangular source is exactly boundedness of one completed,
oriented quantile current. Both terminal and internal transports remain in that current. -/
theorem uniformlyBounded_primePolarTriangularWindow_iff_completedQuantileTransport
    {b : ℝ} (hb : 0 < b) :
    (∃ C : ℝ, ∀ H : ℝ, b ≤ H →
      |ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)| ≤ C) ↔
    (∃ C : ℝ, ∀ H : ℝ, b ≤ H →
      |ccmThirdGradeCesaroCompletedQuantileTransport b H| ≤ C) := by
  let L : ℝ := (32 / b ^ 3) *
    |criticalMellinPrimeMass b - (2 * Real.exp (b / 2) - 2)|
  let I : ℝ := 64 / b ^ 3
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + L + I, ?_⟩
    intro H hbH
    let W := ccmGuinandWeilPrimePolarWeightedWindow b H
      (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)
    let Q := ccmThirdGradeCesaroCompletedQuantileTransport b H
    let B := ccmThirdGradeCesaroLowerOutgoingCorrection b H
    let J := ccmThirdGradeCesaroIncomingPolarTail b H
    have hid :=
      ccmGuinandWeilPrimePolarTriangularWindow_eq_completedQuantileTransport hb hbH
    have hW : |W| ≤ C := hC H hbH
    have hB := abs_ccmThirdGradeCesaroLowerOutgoingCorrection_le hb hbH
    have hJ := abs_ccmThirdGradeCesaroIncomingPolarTail_le hb hbH
    change |B| ≤ L at hB
    change |J| ≤ I at hJ
    change W = Q - B - J at hid
    have hQid : Q = W + B + J := by linarith
    have htri1 : |W + B + J| ≤ |W + B| + |J| := abs_add_le _ _
    have htri2 : |W + B| ≤ |W| + |B| := abs_add_le _ _
    change |Q| ≤ C + L + I
    rw [hQid]
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C + L + I, ?_⟩
    intro H hbH
    let W := ccmGuinandWeilPrimePolarWeightedWindow b H
      (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)
    let Q := ccmThirdGradeCesaroCompletedQuantileTransport b H
    let B := ccmThirdGradeCesaroLowerOutgoingCorrection b H
    let J := ccmThirdGradeCesaroIncomingPolarTail b H
    have hid :=
      ccmGuinandWeilPrimePolarTriangularWindow_eq_completedQuantileTransport hb hbH
    have hQ : |Q| ≤ C := hC H hbH
    have hB := abs_ccmThirdGradeCesaroLowerOutgoingCorrection_le hb hbH
    have hJ := abs_ccmThirdGradeCesaroIncomingPolarTail_le hb hbH
    change |B| ≤ L at hB
    change |J| ≤ I at hJ
    change W = Q - B - J at hid
    have htri1 : |Q - B - J| ≤ |Q - B| + |J| := abs_sub _ _
    have htri2 : |Q - B| ≤ |Q| + |B| := abs_sub _ _
    change |W| ≤ C + L + I
    rw [hid]
    linarith

/-- Exact CCM-FU frontier after completed quantile transport: the anchored moment is uniformly
bounded precisely when the single signed transport current is. -/
theorem uniformlyBounded_thirdGradeCesaroAnchoredErrorMoment_iff_completedQuantileTransport
    {b : ℝ} (hb : 0 < b) :
    (∃ C : ℝ, ∀ H : ℝ, b ≤ H →
      |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| ≤ C) ↔
    (∃ C : ℝ, ∀ H : ℝ, b ≤ H →
      |ccmThirdGradeCesaroCompletedQuantileTransport b H| ≤ C) := by
  rw [← uniformlyBounded_primePolarTriangularWindow_iff_completedQuantileTransport hb]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro H hbH
    rw [← ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_primePolarTriangularWindow
      hb hbH]
    exact hC H hbH
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro H hbH
    rw [ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_primePolarTriangularWindow
      hb hbH]
    exact hC H hbH

end GaloisForLFunctions.RHTower
