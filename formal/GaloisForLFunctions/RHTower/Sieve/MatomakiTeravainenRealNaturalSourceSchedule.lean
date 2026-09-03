import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRealNaturalBlocks
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricRooted
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedSchedule

/-!
# Real-to-natural blocks on the Matomäki--Teräväinen source schedule

The actual paper width and rooted geometric start force every real unit block to contain at least
one integer and to remain inside one natural dyadic block.  Consequently the exact real factor is
the literal natural Watt block required by the moment theorems.  All scale conditions are selected
eventually from the source schedule; no rounding or moment hypothesis is exposed.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- A rooted geometric level has enough paper-width room for one integer and no more than its
natural floor, provided the width has reached the elementary half-width regime. -/
theorem mtGeometricLevel_unitFloor_conditions
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    {z₀ : ℕ} (hprogress :
      1 ≤ delta * ((z₀ - 1 : ℕ) : ℝ)) (j : ℕ) :
    1 ≤ delta * mtGeometricLevel delta (mtFirstGeometricStart delta z₀) j ∧
      delta * mtGeometricLevel delta (mtFirstGeometricStart delta z₀) j ≤
        (⌊mtGeometricLevel delta (mtFirstGeometricStart delta z₀) j⌋₊ : ℝ) := by
  have hz₀Two : 2 ≤ z₀ := by
    by_contra h
    have hsub : z₀ - 1 = 0 := by omega
    rw [hsub] at hprogress
    norm_num at hprogress
  have hz₀One : 1 ≤ z₀ := by omega
  let M := mtGeometricLevel delta (mtFirstGeometricStart delta z₀) j
  have hfirst := (mtFirstGeometricStart_bracket hdelta hz₀One).1
  have hmono :
      mtGeometricLevel delta (mtFirstGeometricStart delta z₀) 0 ≤ M := by
    exact (mtGeometricLevel_strictMono hdelta _).monotone (Nat.zero_le j)
  have hz₀M : (z₀ : ℝ) < M := hfirst.trans_le hmono
  have hsubM : ((z₀ - 1 : ℕ) : ℝ) ≤ M := by
    have : ((z₀ - 1 : ℕ) : ℝ) ≤ (z₀ : ℝ) := by
      exact_mod_cast Nat.sub_le z₀ 1
    exact this.trans hz₀M.le
  have hlow : 1 ≤ delta * M :=
    hprogress.trans (mul_le_mul_of_nonneg_left hsubM hdelta.le)
  have hMtwo : (2 : ℝ) ≤ M := by
    exact (show (2 : ℝ) ≤ (z₀ : ℝ) by exact_mod_cast hz₀Two).trans hz₀M.le
  have hM0 : 0 ≤ M := zero_le_two.trans hMtwo
  have hMlt : M < (⌊M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one M
  have hhalfFloor : M / 2 ≤ (⌊M⌋₊ : ℝ) := by linarith
  have hhigh : delta * M ≤ (⌊M⌋₊ : ℝ) := by
    calc
      delta * M ≤ (1 / 2 : ℝ) * M :=
        mul_le_mul_of_nonneg_right hdeltaHalf hM0
      _ = M / 2 := by ring
      _ ≤ (⌊M⌋₊ : ℝ) := hhalfFloor
  exact ⟨hlow, hhigh⟩

/-- Every rooted geometric factor at the successor paper width satisfies the exact natural window
conditions eventually.  The result is unconditional in the paper parameter `A`. -/
theorem eventually_mtPaperWidth_succ_geometricLevel_unitFloor_window (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ,
      let delta := mtPaperWidth (A + 1) X
      let M := mtGeometricLevel delta
        (mtFirstGeometricStart delta (mtLowerCutoffNat X)) j
      1 ≤ delta * M ∧ delta * M ≤ (⌊M⌋₊ : ℝ) ∧
        ⌊M⌋₊ < ⌊(1 + delta) * M⌋₊ ∧
          ⌊(1 + delta) * M⌋₊ ≤ 2 * ⌊M⌋₊ := by
  filter_upwards [eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one (A + 1),
    eventually_three_mul_mtPaperWidth_succ_le A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hprogress hreserve hX
  have hlog : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hdeltaPos : 0 < mtPaperWidth (A + 1) X := by
    rw [mtPaperWidth]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hlog) _
  have hwidthA : mtPaperWidth A X ≤ 1 := by
    rw [mtPaperWidth]
    calc
      (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) ≤
          (Real.log X) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog
          (neg_nonpos.mpr (Nat.cast_nonneg _))
      _ = 1 := by simp
  have hdeltaHalf : mtPaperWidth (A + 1) X ≤ 1 / 2 := by linarith
  intro j
  dsimp only
  have hconditions :=
    mtGeometricLevel_unitFloor_conditions hdeltaPos hdeltaHalf hprogress j
  have hM0 := (mtGeometricLevel_pos hdeltaPos
    (mtFirstGeometricStart (mtPaperWidth (A + 1) X) (mtLowerCutoffNat X)) j).le
  exact ⟨hconditions.1, hconditions.2,
    mtRealUnitFloor_window hM0 hconditions.1 hconditions.2⟩

/-- On every actual successor-width geometric factor, the real unit polynomial is exactly the
natural Watt unit block and its natural endpoints satisfy the moment-admission window. -/
theorem eventually_mtPaperWidth_succ_geometricUnit_eq_wattBlock (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ, ∀ t : ℝ,
      let delta := mtPaperWidth (A + 1) X
      let M := mtGeometricLevel delta
        (mtFirstGeometricStart delta (mtLowerCutoffNat X)) j
      perronPoly
          (fun n => mtRealIntervalAF (fun _ => (1 : ℂ)) M ((1 + delta) * M) n)
          ⌈(1 + delta) * M⌉₊ 1 t =
            mtWattUnitBlock ⌊M⌋₊ ⌊(1 + delta) * M⌋₊ t ∧
        ⌊M⌋₊ < ⌊(1 + delta) * M⌋₊ ∧
          ⌊(1 + delta) * M⌋₊ ≤ 2 * ⌊M⌋₊ := by
  filter_upwards [eventually_mtPaperWidth_succ_geometricLevel_unitFloor_window A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hwindow hX
  intro j t
  dsimp only
  let delta := mtPaperWidth (A + 1) X
  let M := mtGeometricLevel delta
    (mtFirstGeometricStart delta (mtLowerCutoffNat X)) j
  have hdeltaM := hwindow j
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta, mtPaperWidth]
    have hlog : 0 ≤ Real.log X := by
      have hmono := Real.log_le_log (Real.exp_pos 1) hX
      have hlogOne : 1 ≤ Real.log X := by
        simpa only [Real.log_exp] using hmono
      exact zero_le_one.trans hlogOne
    exact Real.rpow_nonneg hlog _
  have hM0 : 0 ≤ M := by
    by_contra h
    have hMneg : M < 0 := lt_of_not_ge h
    have : delta * M ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdelta0 hMneg.le
    linarith [hdeltaM.1]
  have hupper0 : 0 ≤ (1 + delta) * M :=
    mul_nonneg (by linarith) hM0
  exact ⟨perronPoly_mtRealUnitInterval_eq_mtWattUnitBlock hM0 hupper0 t,
    hdeltaM.2.2⟩

end

end RHTower.Sieve
