import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapConductorFloor

/-!
# The pole conductor minimizes the completed energy

The coprime Fourier repayment series splits into blocks of one conductor period. Every block
pays the corresponding conductor-one term, and its first reduced residue leaves a positive
surplus. Thus conductor one minimizes all completed energies, with a common Fourier-tail gap
above it on every nonpolar conductor. The explicit tilted spline makes this gap strictly positive.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped Real
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.CompletedShell
open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory

/-- Every positive residue block contains exactly `ϕ(m)` reduced residues. -/
private theorem sum_coprime_successor_indicator (m : ℕ) (b : ℝ) :
    (∑ r ∈ range m, if m.Coprime (r + 1) then b else 0) = (m.totient : ℝ) * b := by
  let f : ℕ → ℝ := fun r => if m.Coprime r then b else 0
  have hends : f m = f 0 := by simp only [f, Nat.coprime_self, Nat.coprime_zero_right]
  have hshift := Finset.sum_range_succ' f m
  rw [Finset.sum_range_succ, hends] at hshift
  have heq : (∑ r ∈ range m, f (r + 1)) = ∑ r ∈ range m, f r := by
    linarith only [hshift]
  change (∑ r ∈ range m, f (r + 1)) = _
  rw [heq]
  simp only [f, ← sum_filter, sum_const, nsmul_eq_mul, ← Nat.totient_eq_card_coprime]

/-- The coprime repayment weight before normalization by the totient. -/
private def coprimeTailWeight (m : ℕ) (T : ℝ → ℝ) (n : ℕ) : ℝ :=
  if m.Coprime (n + 1) then
    (m : ℝ) / ((n : ℝ) + 1) * T (((n : ℝ) + 1) / m) else 0

private theorem coprimeTailWeight_nonneg (m : ℕ) (T : ℝ → ℝ) (hT : ∀ x, 0 ≤ T x)
    (n : ℕ) : 0 ≤ coprimeTailWeight m T n := by
  unfold coprimeTailWeight
  split_ifs
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) (hT _)
  · exact le_rfl

private theorem coprimeTailWeight_block_lower {m : ℕ} (hm : 0 < m)
    {T : ℝ → ℝ} (hT : ∀ x, 0 ≤ T x) (hmono : Antitone T) (j r : ℕ) (hr : r < m) :
    (if m.Coprime (r + 1) then T ((j : ℝ) + 1) / ((j : ℝ) + 1) else 0) ≤
      coprimeTailWeight m T (j * m + r) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hrR : (r : ℝ) + 1 ≤ m := by exact_mod_cast (show r + 1 ≤ m by omega)
  have hden : (0 : ℝ) < (j : ℝ) * m + r + 1 := by positivity
  have hupper : (j : ℝ) * m + r + 1 ≤ ((j : ℝ) + 1) * m := by linarith only [hrR]
  have harg : ((j : ℝ) * m + r + 1) / m ≤ (j : ℝ) + 1 :=
    (div_le_iff₀ hmR).mpr hupper
  have hweight : 1 / ((j : ℝ) + 1) ≤ (m : ℝ) / ((j : ℝ) * m + r + 1) := by
    rw [div_le_div_iff₀ hj hden]
    linarith only [hupper]
  have hcop : m.Coprime (j * m + r + 1) ↔ m.Coprime (r + 1) := by
    rw [show j * m + r + 1 = (r + 1) + j * m by omega,
      Nat.coprime_add_mul_right_right]
  unfold coprimeTailWeight
  simp only [hcop]
  split_ifs
  · push_cast
    calc T ((j : ℝ) + 1) / ((j : ℝ) + 1) =
        (1 / ((j : ℝ) + 1)) * T ((j : ℝ) + 1) := by ring
      _ ≤ (m : ℝ) / ((j : ℝ) * m + r + 1) * T (((j : ℝ) * m + r + 1) / m) :=
        mul_le_mul hweight (hmono harg) (hT _) (div_nonneg hmR.le hden.le)
  · exact le_rfl

/-- Grouping positive coprime terms into complete residue blocks preserves the conductor-one
weight and leaves a surplus at the first residue. -/
private theorem coprimeTailWeight_block_surplus {m : ℕ} (hm : 0 < m)
    {T : ℝ → ℝ} (hT : ∀ x, 0 ≤ T x) (hmono : Antitone T) (j : ℕ) :
    (m.totient : ℝ) * (T ((j : ℝ) + 1) / ((j : ℝ) + 1)) +
        (if j = 0 then ((m : ℝ) - 1) * T 1 else 0) ≤
      ∑ r ∈ range m, coprimeTailWeight m T (j * m + r) := by
  by_cases hj : j = 0
  · subst j
    simp only [Nat.cast_zero, zero_add, div_one, if_true, zero_mul]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hfirst : (m : ℝ) * T 1 ≤ coprimeTailWeight m T 0 := by
      unfold coprimeTailWeight
      simp only [zero_add, Nat.coprime_one_right_eq_true, if_true, Nat.cast_zero, div_one]
      exact mul_le_mul_of_nonneg_left (hmono (div_le_self zero_le_one hm1)) hmR.le
    have hsum : (∑ r ∈ range m,
        ((if m.Coprime (r + 1) then T 1 else 0) +
          if r = 0 then ((m : ℝ) - 1) * T 1 else 0)) ≤
        ∑ r ∈ range m, coprimeTailWeight m T r := by
      refine sum_le_sum fun r hr => ?_
      by_cases hr0 : r = 0
      · subst r
        simpa only [zero_add, Nat.coprime_one_right_eq_true, if_true] using
          (show T 1 + ((m : ℝ) - 1) * T 1 ≤ coprimeTailWeight m T 0 by
            nlinarith only [hfirst])
      · rw [if_neg hr0, add_zero]
        simpa only [Nat.cast_zero, zero_add, div_one, zero_mul] using
          coprimeTailWeight_block_lower hm hT hmono 0 r (mem_range.mp hr)
    rw [sum_add_distrib, sum_coprime_successor_indicator] at hsum
    simpa only [sum_ite_eq', mem_range.mpr hm, if_true] using hsum
  · rw [if_neg hj, add_zero, ← sum_coprime_successor_indicator]
    exact sum_le_sum fun r hr => coprimeTailWeight_block_lower hm hT hmono j r (mem_range.mp hr)

private theorem sum_range_blocks (f : ℕ → ℝ) (m L : ℕ) :
    (∑ n ∈ range (L * m), f n) = ∑ j ∈ range L, ∑ r ∈ range m, f (j * m + r) := by
  induction L with
  | zero => simp only [zero_mul, range_zero, sum_empty]
  | succ L ih =>
      rw [Nat.succ_mul, sum_range_add, ih, Finset.sum_range_succ]

private theorem coprimeTailWeight_prefix_surplus {m : ℕ} (hm : 0 < m)
    {T : ℝ → ℝ} (hT : ∀ x, 0 ≤ T x) (hmono : Antitone T) (L : ℕ) :
    (m.totient : ℝ) * (∑ j ∈ range (L + 1), T ((j : ℝ) + 1) / ((j : ℝ) + 1)) +
        ((m : ℝ) - 1) * T 1 ≤ ∑ n ∈ range ((L + 1) * m), coprimeTailWeight m T n := by
  rw [sum_range_blocks]
  have hsum := sum_le_sum (fun j (_ : j ∈ range (L + 1)) =>
    coprimeTailWeight_block_surplus hm hT hmono j)
  rw [sum_add_distrib, ← mul_sum] at hsum
  simpa only [sum_ite_eq', mem_range.mpr (Nat.succ_pos L), if_true] using hsum

/-- Conductor one is exactly the shell-completed pole energy. -/
theorem completedConductorEnergy_one (φ : ℝ → ℝ) (c : ℝ) :
    completedConductorEnergy φ c 1 = completedShellEnergy φ c := by
  simp [completedConductorEnergy]

/-- The reduced-residue blocks retain the whole pole energy and an explicit positive surplus.
This compares completed energies after every signed successor shell has been included. -/
theorem completedConductorEnergy_ge_pole_add_gap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    completedShellEnergy φ c + ((m : ℝ) - 1) / m.totient *
        (2 / (∫ u, φ u ^ 2) * ∫ t in Set.Ioi c, shellSpectrum φ t) ≤
      completedConductorEnergy φ c m := by
  let M : ℝ := ∫ u, φ u ^ 2
  let K : ℝ := 2 / (M * m.totient)
  let T : ℝ → ℝ := fun x => ∫ t in Set.Ioi (c * x), shellSpectrum φ t
  let δ : ℝ := ((m : ℝ) - 1) / m.totient * (2 / M * T 1)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hK : 0 ≤ K := (div_pos zero_lt_two (mul_pos hM htot)).le
  have hcompact := hasCompactSupport_profile hsupp
  have hT : ∀ x, 0 ≤ T x := fun x =>
    setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t
  have hmono : Antitone T := by
    intro x y hxy
    exact setIntegral_mono_set (integrableOn_shellSpectrum_Ioi hφ hcompact (c * x))
      (ae_of_all _ fun t => shellSpectrum_nonneg t)
      (Eventually.of_forall (Set.Ioi_subset_Ioi (mul_le_mul_of_nonneg_left hxy hc.le)))
  have hseries : HasSum (fun n => K * coprimeTailWeight m T n)
      (completedConductorEnergy φ c m) := by
    convert hasSum_completedConductorEnergy hφ hsupp hM hc hm using 1
    funext n
    dsimp only [K, T, M, coprimeTailWeight]
    split_ifs
    · rw [show c * (((n : ℝ) + 1) / m) = ((n : ℝ) + 1) * c / m by ring]
      ring
    · ring
  have hscale : K * (m.totient : ℝ) = 2 / M := by
    dsimp only [K]
    field_simp
  have hpartial : ∀ L : ℕ,
      (∑ j ∈ range (L + 1), 2 / M * (((j : ℝ) + 1)⁻¹ *
        ∫ t in Set.Ioi (((j : ℝ) + 1) * c), shellSpectrum φ t)) + δ ≤
      completedConductorEnergy φ c m := by
    intro L
    have heq : K * ((m.totient : ℝ) *
          (∑ j ∈ range (L + 1), T ((j : ℝ) + 1) / ((j : ℝ) + 1)) +
            ((m : ℝ) - 1) * T 1) =
        (∑ j ∈ range (L + 1), 2 / M * (((j : ℝ) + 1)⁻¹ *
          ∫ t in Set.Ioi (((j : ℝ) + 1) * c), shellSpectrum φ t)) + δ := by
      rw [mul_add, ← mul_assoc, hscale, mul_sum]
      congr 1
      · refine sum_congr rfl fun j _ => ?_
        dsimp only [T]
        rw [mul_comm c]
        ring
      · dsimp only [K, δ]
        ring
    rw [← heq]
    calc K * _ ≤ K * ∑ n ∈ range ((L + 1) * m), coprimeTailWeight m T n :=
          mul_le_mul_of_nonneg_left (coprimeTailWeight_prefix_surplus hm hT hmono L) hK
      _ = ∑ n ∈ range ((L + 1) * m), K * coprimeTailWeight m T n := mul_sum _ _ _
      _ ≤ completedConductorEnergy φ c m := sum_le_hasSum _
          (fun n _ => mul_nonneg hK (coprimeTailWeight_nonneg m T hT n)) hseries
  have hlim := ((hasSum_completedShellEnergy hφ hsupp hM hc).tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)).add_const δ
  have hle := le_of_tendsto hlim (Eventually.of_forall hpartial)
  simpa only [δ, T, M, mul_one] using hle

/-- The pole conductor minimizes every completed conductor family. -/
theorem completedConductorEnergy_one_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy φ c 1 ≤ completedConductorEnergy φ c m := by
  rw [completedConductorEnergy_one]
  have hratio : 0 ≤ ((m : ℝ) - 1) / m.totient :=
    div_nonneg (sub_nonneg.mpr (by exact_mod_cast hm)) (Nat.cast_nonneg _)
  have htail : 0 ≤ 2 / (∫ u, φ u ^ 2) * ∫ t in Set.Ioi c, shellSpectrum φ t :=
    mul_nonneg (div_nonneg zero_le_two hM.le)
      (setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t)
  exact (le_add_of_nonneg_right (mul_nonneg hratio htail)).trans
    (completedConductorEnergy_ge_pole_add_gap hφ hsupp hM hc hm)

/-- Every nonpolar conductor lies a full Fourier tail above the pole conductor. -/
theorem completedConductorEnergy_nonpolar_gap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 1 < m) :
    completedConductorEnergy φ c 1 +
        2 / (∫ u, φ u ^ 2) * ∫ t in Set.Ioi c, shellSpectrum φ t ≤
      completedConductorEnergy φ c m := by
  have hm0 : 0 < m := by omega
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have htotle : (m.totient : ℝ) ≤ (m : ℝ) - 1 := by
    have h : (m.totient : ℝ) + 1 ≤ m := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.totient_lt m hm)
    linarith only [h]
  have hratio : 1 ≤ ((m : ℝ) - 1) / m.totient := (one_le_div htot).mpr htotle
  have htail : 0 ≤ 2 / (∫ u, φ u ^ 2) * ∫ t in Set.Ioi c, shellSpectrum φ t :=
    mul_nonneg (div_nonneg zero_le_two hM.le)
      (setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t)
  rw [completedConductorEnergy_one]
  have hgap := le_mul_of_one_le_left htail hratio
  have hbound := completedConductorEnergy_ge_pole_add_gap hφ hsupp hM hc hm0
  linarith only [hgap, hbound]

/-- The explicit tilted spline has a strictly positive gap above its pole conductor. -/
theorem tiltedUnitSpline_completedConductorEnergy_one_lt {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 1 < m) :
    completedConductorEnergy tiltedUnitSpline c 1 < completedConductorEnergy tiltedUnitSpline c m := by
  have htail : 0 < 2 / (∫ u, tiltedUnitSpline u ^ 2) *
      ∫ t in Set.Ioi c, shellSpectrum tiltedUnitSpline t :=
    mul_pos (div_pos zero_lt_two integral_tiltedUnitSpline_sq_pos)
      (integral_shellSpectrum_tiltedUnitSpline_pos c)
  exact (lt_add_of_pos_right _ htail).trans_le
    (completedConductorEnergy_nonpolar_gap contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos hc hm)

/-- No nonpolar conductor shares the tilted spline's ground energy. -/
theorem tiltedUnitSpline_completedConductorEnergy_eq_ground_iff {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy tiltedUnitSpline c m = completedConductorEnergy tiltedUnitSpline c 1 ↔
      m = 1 := by
  constructor
  · intro h
    by_contra hm1
    exact (ne_of_lt (tiltedUnitSpline_completedConductorEnergy_one_lt hc (by omega))).symm h
  · rintro rfl
    rfl

#print axioms completedConductorEnergy_ge_pole_add_gap
#print axioms completedConductorEnergy_nonpolar_gap
#print axioms tiltedUnitSpline_completedConductorEnergy_eq_ground_iff

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.CompletedShell
