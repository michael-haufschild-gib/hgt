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

theorem intervalIntegrable_iteratedAntideriv {q : ℝ → ℂ}
    (hq : ∀ a b : ℝ, IntervalIntegrable q volume a b) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (iteratedAntideriv q j) volume a b := by
  induction j generalizing a b with
  | zero => exact hq a b
  | succ j ih =>
    have hcont : Continuous (iteratedAntideriv q (j + 1)) := by
      show Continuous fun y : ℝ => ∫ t in (1:ℝ)..y, iteratedAntideriv q j t
      exact intervalIntegral.continuous_primitive (fun u v => ih u v) 1
    exact hcont.intervalIntegrable _ _

theorem continuous_iteratedAntideriv {q : ℝ → ℂ}
    (hq : ∀ a b : ℝ, IntervalIntegrable q volume a b) (j : ℕ) :
    Continuous (iteratedAntideriv q (j + 1)) := by
  show Continuous fun y : ℝ => ∫ t in (1:ℝ)..y, iteratedAntideriv q j t
  exact intervalIntegral.continuous_primitive
    (fun u v => intervalIntegrable_iteratedAntideriv hq j u v) 1

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
theorem integral_jumpProfile {q : ℝ → ℂ} (hq : ∀ a b : ℝ, IntervalIntegrable q volume a b)
    {ι : Type*} {S : Finset ι}
    {node : ι → ℝ} {a : ι → ℂ} (hnode : ∀ i ∈ S, 1 ≤ node i) {y : ℝ} (hy : 1 ≤ y) (j : ℕ) :
    (∫ t in (1:ℝ)..y, jumpProfile q S node a j t) = jumpProfile q S node a (j + 1) y := by
  have hcont : Continuous (iteratedAntideriv q (j + 1)) := continuous_iteratedAntideriv hq j
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
theorem integral_arithJumpProfile {q : ℝ → ℂ}
    (hq : ∀ a b : ℝ, IntervalIntegrable q volume a b) (a : ℕ → ℂ) {y : ℝ}
    (hy : 1 ≤ y) (j : ℕ) :
    (∫ t in (1:ℝ)..y, arithJumpProfile q a j t) = arithJumpProfile q a (j + 1) y := by
  have hcont : Continuous (iteratedAntideriv q (j + 1)) := continuous_iteratedAntideriv hq j
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

/-- **The next level grows by at most the travelled length times the current level bound.** -/
theorem norm_arithProfile_succ_le {a : ℕ → ℂ} {b x G : ℝ} (hb : 1 ≤ b) (hbx : b ≤ x) (j : ℕ)
    (hbound : ∀ t ∈ Set.uIcc b x, ‖arithProfile a j t‖ ≤ G) :
    ‖arithProfile a (j + 1) x‖ ≤ ‖arithProfile a (j + 1) b‖ + (x - b) * G := by
  have hb0 : (1:ℝ) ≤ x := le_trans hb hbx
  have hsplit : (∫ t in (1:ℝ)..b, arithProfile a j t) + ∫ t in b..x, arithProfile a j t
      = ∫ t in (1:ℝ)..x, arithProfile a j t :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_arithProfile a j hb)
      ((intervalIntegrable_arithProfile a j hb).symm.trans
        (intervalIntegrable_arithProfile a j hb0))
  have hdiff : arithProfile a (j + 1) x - arithProfile a (j + 1) b
      = ∫ t in b..x, arithProfile a j t := by
    rw [← integral_arithProfile a hb0 j, ← integral_arithProfile a hb j, ← hsplit]
    ring
  have hnorm : ‖∫ t in b..x, arithProfile a j t‖ ≤ (x - b) * G := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := b) (b := x) (C := G) (f := fun t => arithProfile a j t) ?_
    · calc ‖∫ t in b..x, arithProfile a j t‖ ≤ G * |x - b| := this
        _ = (x - b) * G := by
            rw [abs_of_nonneg (by linarith)]
            ring
    · intro t ht
      exact hbound t (by
        rw [Set.uIoc_of_le hbx] at ht
        rw [Set.uIcc_of_le hbx]
        exact ⟨le_of_lt ht.1, ht.2⟩)
  calc ‖arithProfile a (j + 1) x‖
      = ‖arithProfile a (j + 1) b + (arithProfile a (j + 1) x - arithProfile a (j + 1) b)‖ := by
        ring_nf
    _ ≤ ‖arithProfile a (j + 1) b‖ + ‖arithProfile a (j + 1) x - arithProfile a (j + 1) b‖ :=
        norm_add_le _ _
    _ ≤ ‖arithProfile a (j + 1) b‖ + (x - b) * G := by
        rw [hdiff]
        linarith [hnorm]

/-! ## Taylor expansion of the continuous part -/

/-- The `j`-fold antiderivative of `q` based at `c`. -/
def iteratedAntiderivFrom (q : ℝ → ℂ) (c : ℝ) : ℕ → ℝ → ℂ
  | 0 => q
  | (j + 1) => fun y => ∫ t in c..y, iteratedAntiderivFrom q c j t

theorem iteratedAntiderivFrom_succ (q : ℝ → ℂ) (c : ℝ) (j : ℕ) (y : ℝ) :
    iteratedAntiderivFrom q c (j + 1) y = ∫ t in c..y, iteratedAntiderivFrom q c j t := rfl

theorem intervalIntegrable_iteratedAntiderivFrom {q : ℝ → ℂ}
    (hq : ∀ a b : ℝ, IntervalIntegrable q volume a b) (c : ℝ) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (iteratedAntiderivFrom q c j) volume a b := by
  induction j generalizing a b with
  | zero => exact hq a b
  | succ j ih =>
    have hcont : Continuous (iteratedAntiderivFrom q c (j + 1)) := by
      show Continuous fun y : ℝ => ∫ t in c..y, iteratedAntiderivFrom q c j t
      exact intervalIntegral.continuous_primitive (fun u v => ih u v) c
    exact hcont.intervalIntegrable _ _

/-- The interval integral of a normalized power. -/
theorem integral_sub_pow (x y : ℝ) (k : ℕ) :
    (∫ t in x..y, ((t - x) ^ k : ℝ)) = (y - x) ^ (k + 1) / ((k : ℝ) + 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun u => u ^ k) x, integral_pow]
  simp

set_option maxHeartbeats 1000000 in
/-- **Taylor expansion of an iterated antiderivative.**  The remainder is again an iterated
antiderivative, based at the expansion point. -/
theorem iteratedAntideriv_window {q : ℝ → ℂ}
    (hq : ∀ a b : ℝ, IntervalIntegrable q volume a b) (x : ℝ) :
    ∀ (j : ℕ) (y : ℝ), iteratedAntideriv q (j + 1) y
      = (∑ m ∈ Finset.range (j + 1),
          (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
            * iteratedAntideriv q (m + 1) x)
        + iteratedAntiderivFrom q x (j + 1) y := by
  intro j
  induction j with
  | zero =>
      intro y
      have hsplit : (∫ t in (1:ℝ)..x, q t) + ∫ t in x..y, q t = ∫ t in (1:ℝ)..y, q t :=
        intervalIntegral.integral_add_adjacent_intervals (hq 1 x) (hq x y)
      have hL : iteratedAntideriv q 1 y = ∫ t in (1:ℝ)..y, q t := rfl
      have hLx : iteratedAntideriv q 1 x = ∫ t in (1:ℝ)..x, q t := rfl
      have hR : iteratedAntiderivFrom q x 1 y = ∫ t in x..y, q t := rfl
      rw [hL, hR, Finset.sum_range_one]
      norm_num
      rw [hLx]
      exact hsplit.symm
  | succ j ih =>
      intro y
      have hsplit : (∫ t in (1:ℝ)..x, iteratedAntideriv q (j + 1) t)
          + ∫ t in x..y, iteratedAntideriv q (j + 1) t
          = ∫ t in (1:ℝ)..y, iteratedAntideriv q (j + 1) t :=
        intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_iteratedAntideriv hq (j + 1) 1 x)
          (intervalIntegrable_iteratedAntideriv hq (j + 1) x y)
      have hcontsum : Continuous (fun t : ℝ => ∑ m ∈ Finset.range (j + 1),
          (((t - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
            * iteratedAntideriv q (m + 1) x) := by
        refine continuous_finsetSum _ fun m _ => ?_
        exact (Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const
      have hinner : (∫ t in x..y, iteratedAntideriv q (j + 1) t)
          = (∑ m ∈ Finset.range (j + 1),
              (((y - x) ^ (j + 1 - m) / (((j + 1 - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
                * iteratedAntideriv q (m + 1) x)
            + ∫ t in x..y, iteratedAntiderivFrom q x (j + 1) t := by
        have hcongr : (∫ t in x..y, iteratedAntideriv q (j + 1) t)
            = ∫ t in x..y, ((∑ m ∈ Finset.range (j + 1),
                (((t - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
                  * iteratedAntideriv q (m + 1) x)
              + iteratedAntiderivFrom q x (j + 1) t) :=
          intervalIntegral.integral_congr (fun t _ => ih t)
        rw [hcongr, intervalIntegral.integral_add (hcontsum.intervalIntegrable _ _)
          (intervalIntegrable_iteratedAntiderivFrom hq x (j + 1) x y)]
        congr 1
        have hint : ∀ m ∈ Finset.range (j + 1), IntervalIntegrable
            (fun t : ℝ => (((t - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
              * iteratedAntideriv q (m + 1) x) volume x y := by
          intro m _
          refine Continuous.intervalIntegrable ?_ _ _
          exact (Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const
        rw [intervalIntegral.integral_finsetSum hint]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [intervalIntegral.integral_mul_const]
        congr 1
        have hreal : (∫ t in x..y, ((t - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ))
            = (y - x) ^ (j + 1 - m) / (((j + 1 - m).factorial : ℕ) : ℝ) := by
          rw [intervalIntegral.integral_div, integral_sub_pow]
          have hmj : m ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
          have hexp : j + 1 - m = (j - m) + 1 := by omega
          rw [hexp, Nat.factorial_succ]
          push_cast
          have hfac : (0:ℝ) < (((j - m).factorial : ℕ) : ℝ) := by
            exact_mod_cast Nat.factorial_pos (j - m)
          field_simp
        rw [← hreal, ← intervalIntegral.integral_ofReal]
      rw [iteratedAntideriv_succ, iteratedAntiderivFrom_succ, ← hsplit, hinner]
      conv_rhs => rw [Finset.sum_range_succ]
      have hlast : (((y - x) ^ (j + 1 - (j + 1)) / (((j + 1 - (j + 1)).factorial : ℕ) : ℝ) : ℝ)
          : ℂ) * iteratedAntideriv q (j + 1 + 1) x
          = ∫ t in (1:ℝ)..x, iteratedAntideriv q (j + 1) t := by
        simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
          Complex.ofReal_one, one_mul]
        rfl
      rw [hlast]
      ring

/-- **The window decomposition of the full remainder chain.**  Both halves expand: the continuous
datum by Taylor with an antiderivative remainder, the arithmetic source by its jumps. -/
theorem arithJumpProfile_window {q : ℝ → ℂ}
    (hq : ∀ a b : ℝ, IntervalIntegrable q volume a b) (a : ℕ → ℂ) (j : ℕ) {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) :
    arithJumpProfile q a j y
      = (∑ m ∈ Finset.range (j + 1),
          (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
            * arithJumpProfile q a m x)
        + iteratedAntiderivFrom q x (j + 1) y
        + ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            a n * (((y - (n : ℝ)) ^ j / ((j.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hq' := iteratedAntideriv_window hq x j y
  have ha := arithProfile_window a j hx hxy
  rw [arithJumpProfile, hq', ha]
  have hsum : (∑ m ∈ Finset.range (j + 1),
      (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
        * arithJumpProfile q a m x)
      = (∑ m ∈ Finset.range (j + 1),
          (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
            * iteratedAntideriv q (m + 1) x)
        + ∑ m ∈ Finset.range (j + 1),
            (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ)
              * arithProfile a m x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [arithJumpProfile]
    ring
  rw [hsum]
  ring

theorem arithJumpProfile_updateWindow_base {q : ℝ → ℂ} (a c : ℕ → ℂ) {S : Finset ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hS : ∀ n ∈ S, x < (n : ℝ)) (m : ℕ) :
    arithJumpProfile q (updateWindow a S c) m x = arithJumpProfile q a m x := by
  rw [arithJumpProfile, arithJumpProfile, arithProfile_updateWindow_base a c hx hS m]

/-- The Taylor remainder of the continuous datum is small on the window. -/
theorem norm_iteratedAntiderivFrom_le {q : ℝ → ℂ} {Mq : ℝ} {c y : ℝ}
    (hbound : ∀ t ∈ Set.Icc c y, ‖q t‖ ≤ Mq) (hcy : c ≤ y) (j : ℕ) :
    ‖iteratedAntiderivFrom q c j y‖ ≤ Mq * (y - c) ^ j / ((j.factorial : ℕ) : ℝ) := by
  have hMq : 0 ≤ Mq := le_trans (norm_nonneg _) (hbound c ⟨le_rfl, hcy⟩)
  have key : ∀ (j : ℕ), ∀ z ∈ Set.Icc c y,
      ‖iteratedAntiderivFrom q c j z‖ ≤ Mq * (z - c) ^ j / ((j.factorial : ℕ) : ℝ) := by
    intro j
    induction j with
    | zero =>
        intro z hz
        have := hbound z hz
        simpa [iteratedAntiderivFrom] using this
    | succ j ih =>
        intro z hz
        have hcz : c ≤ z := hz.1
        rw [iteratedAntiderivFrom_succ]
        have hfacj : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
        have hg : IntervalIntegrable (fun t : ℝ => Mq * (t - c) ^ j / ((j.factorial : ℕ) : ℝ))
            volume c z := by
          refine Continuous.intervalIntegrable ?_ _ _
          fun_prop
        have hnorm := intervalIntegral.norm_integral_le_of_norm_le
          (f := iteratedAntiderivFrom q c j)
          (g := fun t : ℝ => Mq * (t - c) ^ j / ((j.factorial : ℕ) : ℝ)) hcz
          (Filter.Eventually.of_forall (fun t (ht : t ∈ Set.Ioc c z) =>
            ih t ⟨le_of_lt ht.1, le_trans ht.2 hz.2⟩)) hg
        have hint : (∫ t in c..z, Mq * (t - c) ^ j / ((j.factorial : ℕ) : ℝ))
            = Mq * (z - c) ^ (j + 1) / (((j + 1).factorial : ℕ) : ℝ) := by
          have hrw : (fun t : ℝ => Mq * (t - c) ^ j / ((j.factorial : ℕ) : ℝ))
              = fun t : ℝ => (Mq / ((j.factorial : ℕ) : ℝ)) * (t - c) ^ j := by
            funext t
            ring
          rw [hrw, intervalIntegral.integral_const_mul, integral_sub_pow, Nat.factorial_succ]
          push_cast
          field_simp
        rw [hint] at hnorm
        exact hnorm
  exact key j y ⟨hcy, le_rfl⟩

/-- The chain's antiderivatives are the antiderivatives based at `1`. -/
theorem iteratedAntideriv_eq_from (q : ℝ → ℂ) (j : ℕ) (y : ℝ) :
    iteratedAntideriv q j y = iteratedAntiderivFrom q 1 j y := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
      rw [iteratedAntideriv_succ, iteratedAntiderivFrom_succ]
      exact intervalIntegral.integral_congr (fun t _ => ih t)

/-- The `(m+1)`-fold antiderivative of a bounded datum, based at `1`. -/
theorem norm_iteratedAntideriv_le {q : ℝ → ℂ} {Mq : ℝ} {x : ℝ} (hx : 1 ≤ x)
    (hbound : ∀ t ∈ Set.Icc (1:ℝ) x, ‖q t‖ ≤ Mq) (m : ℕ) :
    ‖iteratedAntideriv q (m + 1) x‖ ≤ (x ^ m / ((m.factorial : ℕ) : ℝ)) * (Mq * x) := by
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
  have hMq : 0 ≤ Mq := le_trans (norm_nonneg _) (hbound 1 ⟨le_rfl, hx⟩)
  have hfac : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hfacs : (0:ℝ) < (((m + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m + 1)
  have hfacle : ((m.factorial : ℕ) : ℝ) ≤ (((m + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ m)
  rw [iteratedAntideriv_eq_from]
  refine le_trans (norm_iteratedAntiderivFrom_le hbound hx (m + 1)) ?_
  have hpowle : (x - 1) ^ (m + 1) ≤ x ^ (m + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hR : (x ^ m / ((m.factorial : ℕ) : ℝ)) * (Mq * x)
      = Mq * x ^ (m + 1) / ((m.factorial : ℕ) : ℝ) := by
    field_simp
    ring
  rw [hR, div_le_div_iff₀ hfacs hfac]
  have step1 : Mq * (x - 1) ^ (m + 1) ≤ Mq * x ^ (m + 1) := mul_le_mul_of_nonneg_left hpowle hMq
  have hB : 0 ≤ Mq * x ^ (m + 1) := by positivity
  have e1 : Mq * (x - 1) ^ (m + 1) * ((m.factorial : ℕ) : ℝ)
      ≤ Mq * x ^ (m + 1) * ((m.factorial : ℕ) : ℝ) := mul_le_mul_of_nonneg_right step1 hfac.le
  have e2 : Mq * x ^ (m + 1) * ((m.factorial : ℕ) : ℝ)
      ≤ Mq * x ^ (m + 1) * (((m + 1).factorial : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hfacle hB
  linarith

/-- Every level of the full chain is interval integrable on `[1, y]`. -/
theorem intervalIntegrable_arithJumpProfile {q : ℝ → ℂ}
    (hq : ∀ a b : ℝ, IntervalIntegrable q volume a b) (a : ℕ → ℂ) (j : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    IntervalIntegrable (arithJumpProfile q a j) volume 1 y := by
  have h1 := intervalIntegrable_iteratedAntideriv hq (j + 1) 1 y
  have h2 := intervalIntegrable_arithProfile a j hy
  exact h1.add h2

/-- **Growth of the full chain.**  A bound on level `j` over `[b, x]` controls the growth of
level `j + 1` linearly. -/
theorem norm_arithJumpProfile_succ_le {q : ℝ → ℂ}
    (hq : ∀ u v : ℝ, IntervalIntegrable q volume u v) {a : ℕ → ℂ} {b x G : ℝ} (hb : 1 ≤ b)
    (hbx : b ≤ x) (j : ℕ)
    (hbound : ∀ t ∈ Set.uIcc b x, ‖arithJumpProfile q a j t‖ ≤ G) :
    ‖arithJumpProfile q a (j + 1) x‖ ≤ ‖arithJumpProfile q a (j + 1) b‖ + (x - b) * G := by
  have hb0 : (1:ℝ) ≤ x := le_trans hb hbx
  have hsplit : (∫ t in (1:ℝ)..b, arithJumpProfile q a j t)
      + ∫ t in b..x, arithJumpProfile q a j t
      = ∫ t in (1:ℝ)..x, arithJumpProfile q a j t :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_arithJumpProfile hq a j hb)
      ((intervalIntegrable_arithJumpProfile hq a j hb).symm.trans
        (intervalIntegrable_arithJumpProfile hq a j hb0))
  have hdiff : arithJumpProfile q a (j + 1) x - arithJumpProfile q a (j + 1) b
      = ∫ t in b..x, arithJumpProfile q a j t := by
    rw [← integral_arithJumpProfile hq a hb0 j, ← integral_arithJumpProfile hq a hb j, ← hsplit]
    ring
  have hnorm : ‖∫ t in b..x, arithJumpProfile q a j t‖ ≤ (x - b) * G := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := b) (b := x) (C := G) (f := fun t => arithJumpProfile q a j t) ?_
    · calc ‖∫ t in b..x, arithJumpProfile q a j t‖ ≤ G * |x - b| := this
        _ = (x - b) * G := by
            rw [abs_of_nonneg (by linarith)]
            ring
    · intro t ht
      exact hbound t (by
        rw [Set.uIoc_of_le hbx] at ht
        rw [Set.uIcc_of_le hbx]
        exact ⟨le_of_lt ht.1, ht.2⟩)
  calc ‖arithJumpProfile q a (j + 1) x‖
      = ‖arithJumpProfile q a (j + 1) b
          + (arithJumpProfile q a (j + 1) x - arithJumpProfile q a (j + 1) b)‖ := by
        ring_nf
    _ ≤ ‖arithJumpProfile q a (j + 1) b‖
        + ‖arithJumpProfile q a (j + 1) x - arithJumpProfile q a (j + 1) b‖ := norm_add_le _ _
    _ ≤ ‖arithJumpProfile q a (j + 1) b‖ + (x - b) * G := by
        rw [hdiff]
        linarith [hnorm]

/-- Negating the datum negates every level. -/
theorem iteratedAntideriv_neg (q : ℝ → ℂ) :
    ∀ (j : ℕ) (y : ℝ), iteratedAntideriv (fun t => -q t) j y = -(iteratedAntideriv q j y) := by
  intro j
  induction j with
  | zero => intro y; rfl
  | succ j ih =>
      intro y
      rw [iteratedAntideriv_succ, iteratedAntideriv_succ, ← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr (fun t _ => ih t)

theorem arithProfile_neg (a : ℕ → ℂ) (j : ℕ) (y : ℝ) :
    arithProfile (fun n => -a n) j y = -(arithProfile a j y) := by
  rw [arithProfile, arithProfile, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Negating both the datum and the source negates the whole chain. -/
theorem arithJumpProfile_neg (q : ℝ → ℂ) (a : ℕ → ℂ) (j : ℕ) (y : ℝ) :
    arithJumpProfile (fun t => -q t) (fun n => -a n) j y = -(arithJumpProfile q a j y) := by
  rw [arithJumpProfile, arithJumpProfile, iteratedAntideriv_neg, arithProfile_neg]
  ring

end GaloisForLFunctions.HTGeometry

end
