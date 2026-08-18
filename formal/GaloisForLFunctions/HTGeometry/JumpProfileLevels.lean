import GaloisForLFunctions.HTGeometry.TruncatedPowerAntiderivative

/-!
# Repeated integration of a continuous datum plus a finite jump family

The remainder chain of an Andersson-type recursion starts from

`r₁(y) = ∫_1^y q + ∑_{p ≤ y} a_p`,  `r_{j+1}(y) = ∫_1^y r_j`,

a continuous part and a purely atomic part.  Both halves integrate in closed form: the continuous
part becomes an iterated antiderivative, the atomic part becomes the superposition of truncated
powers.  The levels are therefore explicit, and the chain hypothesis of the iterated Mellin step is
satisfied by construction.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The `j`-fold antiderivative of `q` based at `1`. -/
def iteratedAntideriv (q : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => q
  | (j + 1) => fun y => ∫ t in (1:ℝ)..y, iteratedAntideriv q j t

theorem iteratedAntideriv_succ (q : ℝ → ℂ) (j : ℕ) (y : ℝ) :
    iteratedAntideriv q (j + 1) y = ∫ t in (1:ℝ)..y, iteratedAntideriv q j t := rfl

theorem continuous_iteratedAntideriv {q : ℝ → ℂ} (hq : Continuous q) (j : ℕ) :
    Continuous (iteratedAntideriv q j) := by
  induction j with
  | zero => exact hq
  | succ j ih =>
    have hderiv : ∀ y : ℝ, HasDerivAt (fun u : ℝ => ∫ t in (1:ℝ)..u, iteratedAntideriv q j t)
        (iteratedAntideriv q j y) y := fun y =>
      intervalIntegral.integral_hasDerivAt_right (ih.intervalIntegrable _ _)
        (ih.stronglyMeasurableAtFilter _ _) ih.continuousAt
    show Continuous fun y : ℝ => ∫ t in (1:ℝ)..y, iteratedAntideriv q j t
    exact continuous_iff_continuousAt.2 fun y => (hderiv y).continuousAt

theorem intervalIntegrable_truncPowSum {ι : Type*} (S : Finset ι) (node : ι → ℝ) (a : ι → ℂ)
    (j : ℕ) (u v : ℝ) : IntervalIntegrable (truncPowSum S node a j) volume u v := by
  constructor
  · exact MeasureTheory.integrable_finsetSum S fun i _ =>
      ((intervalIntegrable_truncPow_ofReal (node i) j u v).const_mul (a i)).1
  · exact MeasureTheory.integrable_finsetSum S fun i _ =>
      ((intervalIntegrable_truncPow_ofReal (node i) j u v).const_mul (a i)).2

/-- Level `j` of the remainder chain: the `(j+1)`-fold antiderivative of the continuous datum plus
the `j`-fold integrated jump family. -/
def jumpProfile (q : ℝ → ℂ) {ι : Type*} (S : Finset ι) (node : ι → ℝ) (a : ι → ℂ) (j : ℕ)
    (y : ℝ) : ℂ :=
  iteratedAntideriv q (j + 1) y + truncPowSum S node a j y

/-- At level `0` the profile is `∫_1^y q + ∑_{node ≤ y} a`. -/
theorem jumpProfile_zero {q : ℝ → ℂ} {ι : Type*} [DecidableEq ι] (S : Finset ι) (node : ι → ℝ)
    (a : ι → ℂ) (y : ℝ) :
    jumpProfile q S node a 0 y = (∫ t in (1:ℝ)..y, q t) + ∑ i ∈ S with node i ≤ y, a i := by
  rw [jumpProfile, truncPowSum_zero, iteratedAntideriv_succ]
  rfl

/-- **The chain identity.**  Integrating one level of the profile from `1` gives the next level. -/
theorem integral_jumpProfile {q : ℝ → ℂ} (hq : Continuous q) {ι : Type*} {S : Finset ι}
    {node : ι → ℝ} {a : ι → ℂ} (hnode : ∀ i ∈ S, 1 ≤ node i) {y : ℝ} (hy : 1 ≤ y) (j : ℕ) :
    (∫ t in (1:ℝ)..y, jumpProfile q S node a j t) = jumpProfile q S node a (j + 1) y := by
  have hcont : Continuous (iteratedAntideriv q (j + 1)) := continuous_iteratedAntideriv hq (j + 1)
  have hsplit : (∫ t in (1:ℝ)..y, jumpProfile q S node a j t)
      = (∫ t in (1:ℝ)..y, iteratedAntideriv q (j + 1) t)
        + ∫ t in (1:ℝ)..y, truncPowSum S node a j t := by
    simp only [jumpProfile]
    exact intervalIntegral.integral_add (hcont.intervalIntegrable _ _)
      (intervalIntegrable_truncPowSum S node a j 1 y)
  rw [hsplit, integral_truncPowSum hnode hy j, jumpProfile, iteratedAntideriv_succ]

/-- The `j`-fold integrated arithmetic jump family of an infinite source: only the finitely many
nodes below `y` contribute. -/
def arithProfile (a : ℕ → ℂ) (j : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * ((truncPow (n : ℝ) j y : ℝ) : ℂ)

theorem truncPowSum_Icc_eq_arithProfile (a : ℕ → ℂ) (j : ℕ) {N : ℕ} {t : ℝ}
    (hN : ⌊t⌋₊ ≤ N) :
    truncPowSum (Finset.Icc 1 N) (fun n : ℕ => (n : ℝ)) a j t = arithProfile a j t := by
  classical
  rw [truncPowSum, arithProfile]
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hN) ?_).symm
  intro n hn hnot
  have hlow : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hgt : ⌊t⌋₊ < n := by
    by_contra hcon
    exact hnot (Finset.mem_Icc.2 ⟨hlow, le_of_not_gt hcon⟩)
  have hnt : t < (n : ℝ) := by
    have := Nat.lt_floor_add_one t
    have hn1 : (⌊t⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hgt
    linarith
  rw [truncPow_of_lt hnt j]
  simp

theorem arithProfile_zero (a : ℕ → ℂ) (y : ℝ) :
    arithProfile a 0 y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n := by
  rw [arithProfile]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : (n : ℝ) ≤ y := by
    have h1 : n ≤ ⌊y⌋₊ := (Finset.mem_Icc.1 hn).2
    rcases le_or_gt (0:ℝ) y with hy | hy
    · have := Nat.floor_le hy
      have h2 : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h1
      linarith
    · have : ⌊y⌋₊ = 0 := Nat.floor_of_nonpos (le_of_lt hy)
      have h3 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
      omega
  rw [truncPow_of_le hle 0]
  simp

/-- **The chain identity for an infinite arithmetic source.** -/
theorem integral_arithProfile (a : ℕ → ℂ) {y : ℝ} (hy : 1 ≤ y) (j : ℕ) :
    (∫ t in (1:ℝ)..y, arithProfile a j t) = arithProfile a (j + 1) y := by
  have hy0 : (0:ℝ) ≤ y := le_trans zero_le_one hy
  have hcongr : (∫ t in (1:ℝ)..y, arithProfile a j t)
      = ∫ t in (1:ℝ)..y, truncPowSum (Finset.Icc 1 ⌊y⌋₊) (fun n : ℕ => (n : ℝ)) a j t := by
    refine (intervalIntegral.integral_congr ?_)
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    exact (truncPowSum_Icc_eq_arithProfile a j (Nat.floor_le_floor ht.2)).symm
  have hnode : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊, (1:ℝ) ≤ (n : ℝ) := by
    intro n hn
    have : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    exact_mod_cast this
  rw [hcongr, integral_truncPowSum hnode hy j,
    truncPowSum_Icc_eq_arithProfile a (j + 1) (le_refl _)]

/-- The full remainder level: continuous datum plus arithmetic source. -/
def arithJumpProfile (q : ℝ → ℂ) (a : ℕ → ℂ) (j : ℕ) (y : ℝ) : ℂ :=
  iteratedAntideriv q (j + 1) y + arithProfile a j y

theorem arithJumpProfile_zero (q : ℝ → ℂ) (a : ℕ → ℂ) (y : ℝ) :
    arithJumpProfile q a 0 y = (∫ t in (1:ℝ)..y, q t) + ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n := by
  rw [arithJumpProfile, arithProfile_zero, iteratedAntideriv_succ]
  rfl

theorem intervalIntegrable_arithProfile (a : ℕ → ℂ) (j : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    IntervalIntegrable (arithProfile a j) volume 1 y := by
  have hy0 : (0:ℝ) ≤ y := le_trans zero_le_one hy
  refine (intervalIntegrable_truncPowSum (Finset.Icc 1 ⌊y⌋₊) (fun n : ℕ => (n : ℝ)) a j 1
    y).congr ?_
  intro t ht
  rw [Set.uIoc_of_le hy] at ht
  exact truncPowSum_Icc_eq_arithProfile a j (Nat.floor_le_floor ht.2)

/-- **The chain identity for the full remainder level.** -/
theorem integral_arithJumpProfile {q : ℝ → ℂ} (hq : Continuous q) (a : ℕ → ℂ) {y : ℝ}
    (hy : 1 ≤ y) (j : ℕ) :
    (∫ t in (1:ℝ)..y, arithJumpProfile q a j t) = arithJumpProfile q a (j + 1) y := by
  have hcont : Continuous (iteratedAntideriv q (j + 1)) := continuous_iteratedAntideriv hq (j + 1)
  have hsplit : (∫ t in (1:ℝ)..y, arithJumpProfile q a j t)
      = (∫ t in (1:ℝ)..y, iteratedAntideriv q (j + 1) t)
        + ∫ t in (1:ℝ)..y, arithProfile a j t := by
    simp only [arithJumpProfile]
    exact intervalIntegral.integral_add (hcont.intervalIntegrable _ _)
      (intervalIntegrable_arithProfile a j hy)
  rw [hsplit, integral_arithProfile a hy j, arithJumpProfile, iteratedAntideriv_succ]

theorem arithProfile_eq_truncPowSum (a : ℕ → ℂ) (j : ℕ) {N : ℕ} {t : ℝ} (hN : ⌊t⌋₊ ≤ N) :
    arithProfile a j t = truncPowSum (Finset.Icc 1 N) (fun n : ℕ => (n : ℝ)) a j t :=
  (truncPowSum_Icc_eq_arithProfile a j hN).symm

/-- **The window decomposition.**  Past the base point `x`, the level-`j` arithmetic profile is the
Taylor image of the levels at `x` plus the contribution of the nodes inside the window. -/
theorem arithProfile_window (a : ℕ → ℂ) (j : ℕ) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    arithProfile a j y
      = (∑ m ∈ Finset.range (j + 1),
          (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ) * arithProfile a m x)
        + ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  classical
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
  have hy : (1:ℝ) ≤ y := le_trans hx hxy
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hIcc : ∀ N : ℕ, Finset.Icc 1 N = Finset.Ioc 0 N := fun N => Finset.val_inj.mp rfl
  have hsplit : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * ((truncPow (n : ℝ) j y : ℝ) : ℂ))
      + (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, a n * ((truncPow (n : ℝ) j y : ℝ) : ℂ))
      = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, a n * ((truncPow (n : ℝ) j y : ℝ) : ℂ) :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl
  have hbase : arithProfile a j y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, a n * ((truncPow (n : ℝ) j y : ℝ) : ℂ) := by
    rw [arithProfile, hIcc]
  have hold : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * ((truncPow (n : ℝ) j y : ℝ) : ℂ))
      = ∑ m ∈ Finset.range (j + 1),
          (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ) * arithProfile a m x := by
    have hnode : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ≤ x := by
      intro n hn
      have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.1 hn).2
      have h2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
      exact le_trans h2 (Nat.floor_le hx0)
    have hshift := truncPowSum_shift (S := Finset.Icc 1 ⌊x⌋₊) (node := fun n : ℕ => (n : ℝ))
      (a := a) hnode hxy j
    rw [← hIcc, ← truncPowSum]
    rw [hshift]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← arithProfile_eq_truncPowSum a m (le_refl _)]
  have hnew : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, a n * ((truncPow (n : ℝ) j y : ℝ) : ℂ))
      = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have h1 : n ≤ ⌊y⌋₊ := (Finset.mem_Ioc.1 hn).2
    have hny : (n : ℝ) ≤ y := by
      have h2 : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h1
      exact le_trans h2 (Nat.floor_le (le_trans zero_le_one hy))
    rw [truncPow_of_le hny j]
  rw [hbase, ← hsplit, hold, hnew]

/-- Replacing the source on a window. -/
def updateWindow (a : ℕ → ℂ) (S : Finset ℕ) (c : ℕ → ℂ) : ℕ → ℂ :=
  fun n => if n ∈ S then c n else a n

/-- Values assigned inside a window do not change the levels at the base point. -/
theorem arithProfile_updateWindow_base (a c : ℕ → ℂ) {S : Finset ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hS : ∀ n ∈ S, x < (n : ℝ)) (m : ℕ) :
    arithProfile (updateWindow a S c) m x = arithProfile a m x := by
  classical
  rw [arithProfile, arithProfile]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : (n : ℝ) ≤ x := by
    have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.1 hn).2
    have h2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    exact le_trans h2 (Nat.floor_le hx)
  have hnot : n ∉ S := fun hmem => absurd hle (not_le_of_gt (hS n hmem))
  rw [updateWindow, if_neg hnot]

/-- **The window step.**  After assigning the values `c` on the window `(x, y]`, the level-`j`
profile at `y` is the Taylor image of the old levels at `x` plus the new window moment. -/
theorem arithProfile_updateWindow_step (a c : ℕ → ℂ) (j : ℕ) {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x ≤ y) :
    arithProfile (updateWindow a (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) c) j y
      = (∑ m ∈ Finset.range (j + 1),
          (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ) * arithProfile a m x)
        + ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            c n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  classical
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
  have hS : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, x < (n : ℝ) := by
    intro n hn
    have h1 : ⌊x⌋₊ < n := (Finset.mem_Ioc.1 hn).1
    have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
    have h3 := Nat.lt_floor_add_one x
    linarith
  rw [arithProfile_window (updateWindow a (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) c) j hx hxy]
  congr 1
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [arithProfile_updateWindow_base a c hx0 hS m]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [updateWindow, if_pos hn]

end GaloisForLFunctions.HTGeometry

end
