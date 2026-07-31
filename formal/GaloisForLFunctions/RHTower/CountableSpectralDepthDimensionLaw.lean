import GaloisForLFunctions.RHTower.CountableSpectralDepthFirstReturnLaw

/-!
# Running spectral dimension of a countable recurrence packet

At logarithmic resolution `L`, only weights at least `exp (-L)` contribute
to the water entropy. For every summable packet this visible set is finite.
Between successive visibility thresholds, spectral-depth entropy grows
linearly with slope one half of the visible coordinate count.
-/

noncomputable section

namespace RHTower

/-- Spectral coordinates visible at logarithmic resolution `L`. -/
def countableSpectralVisibleSet
    (p : ℕ → ℝ) (L : ℝ) : Set ℕ :=
  {k | Real.exp (-L) ≤ p k}

/-- Every fixed positive resolution sees only finitely many coordinates of
a summable nonnegative packet. -/
theorem countableSpectralVisibleSet_finite
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (L : ℝ) :
    (countableSpectralVisibleSet p L).Finite := by
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp hsum.tendsto_atTop_zero)
      (Real.exp (-L)) (Real.exp_pos (-L))
  apply (Set.finite_lt_nat N).subset
  intro k hk
  by_contra hnot
  have hkN : N ≤ k := Nat.le_of_not_gt hnot
  have hsmall := hN k hkN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hp k)] at hsmall
  exact (not_lt_of_ge hk) hsmall

/-- Number of spectral coordinates visible at logarithmic resolution `L`. -/
def countableSpectralVisibleCount
    (p : ℕ → ℝ) (L : ℝ) : ℕ :=
  (countableSpectralVisibleSet p L).ncard

/--
Infinite-packet spectral-depth entropy. The defining sum is finite at every
fixed resolution because summability makes the visible set finite.
-/
def countableSpectralDepthProfileEntropy
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (L : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ k ∈ (countableSpectralVisibleSet_finite p hp hsum L).toFinset,
      (L + Real.log (p k))

/--
Once a finite head contains every coordinate visible at resolution `L`,
its fixed-water entropy is exactly the intrinsic countable profile entropy.
Thus the profile is independent of arbitrary truncation after the visible
support has entered the head.
-/
theorem countableSpectralDepthEntropy_eq_profile_of_visible_subset
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (L : ℝ) (M : ℕ)
    (hvisibleHead :
      countableSpectralVisibleSet p L ⊆ {k | k < M}) :
    countableSpectralDepthEntropy p M (Real.exp L) =
      countableSpectralDepthProfileEntropy p hp hsum L := by
  let A :=
    (countableSpectralVisibleSet_finite p hp hsum L).toFinset
  have hA_range : A ⊆ Finset.range M := by
    intro k hk
    rw [Finset.mem_range]
    apply hvisibleHead
    simpa only [A, Set.Finite.mem_toFinset] using hk
  have hactive (k : ℕ) (hk : k ∈ A) :
      Real.log (max 1 (Real.exp L * p k)) =
        L + Real.log (p k) := by
    have hkVisible :
        Real.exp (-L) ≤ p k := by
      simpa only [A, Set.Finite.mem_toFinset,
        countableSpectralVisibleSet, Set.mem_setOf_eq] using hk
    have hprod : 1 ≤ Real.exp L * p k := by
      have hmul :=
        mul_le_mul_of_nonneg_left hkVisible (Real.exp_pos L).le
      calc
        1 = Real.exp L * Real.exp (-L) := by
          rw [← Real.exp_add]
          simp
        _ ≤ Real.exp L * p k := hmul
    rw [max_eq_right hprod,
      Real.log_mul (Real.exp_ne_zero L)
        (ne_of_gt ((Real.exp_pos (-L)).trans_le hkVisible)),
      Real.log_exp]
  have hinactive (k : ℕ) (hkM : k ∈ Finset.range M)
      (hk : k ∉ A) :
      Real.log (max 1 (Real.exp L * p k)) = 0 := by
    have hkNotVisible :
        p k < Real.exp (-L) := by
      dsimp only [A] at hk
      rw [Set.Finite.mem_toFinset,
        countableSpectralVisibleSet, Set.mem_setOf_eq] at hk
      exact lt_of_not_ge hk
    have hprod : Real.exp L * p k ≤ 1 := by
      have hmul :=
        mul_lt_mul_of_pos_left hkNotVisible (Real.exp_pos L)
      calc
        Real.exp L * p k ≤
            Real.exp L * Real.exp (-L) := hmul.le
        _ = 1 := by
          rw [← Real.exp_add]
          simp
    rw [max_eq_left hprod, Real.log_one]
  have hrestrict :
      (∑ k ∈ A,
          Real.log (max 1 (Real.exp L * p k))) =
        ∑ k ∈ Finset.range M,
          Real.log (max 1 (Real.exp L * p k)) :=
    Finset.sum_subset hA_range hinactive
  have hfin :
      (∑ i : Fin M,
          Real.log (max 1 (Real.exp L * p i))) =
        ∑ k ∈ Finset.range M,
          Real.log (max 1 (Real.exp L * p k)) :=
    Fin.sum_univ_eq_sum_range
      (fun k : ℕ =>
        Real.log (max 1 (Real.exp L * p k))) M
  rw [countableSpectralDepthEntropy,
    countableSpectralDepthProfileEntropy, hfin]
  change (1 / 2 : ℝ) *
      (∑ k ∈ Finset.range M,
        Real.log (max 1 (Real.exp L * p k))) =
    (1 / 2 : ℝ) * ∑ k ∈ A, (L + Real.log (p k))
  congr 1
  rw [← hrestrict]
  apply Finset.sum_congr rfl
  intro k hk
  exact hactive k hk

/--
On every interval containing no visibility threshold, spectral-depth
entropy has exact slope one half of the visible spectral count.
-/
theorem countableSpectralDepthProfileEntropy_increment
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) {L₁ L₂ : ℝ}
    (hvisible :
      countableSpectralVisibleSet p L₁ =
        countableSpectralVisibleSet p L₂) :
    countableSpectralDepthProfileEntropy p hp hsum L₂ -
        countableSpectralDepthProfileEntropy p hp hsum L₁ =
      (1 / 2 : ℝ) *
        (countableSpectralVisibleCount p L₁ : ℝ) *
          (L₂ - L₁) := by
  let A :=
    (countableSpectralVisibleSet_finite p hp hsum L₁).toFinset
  have hA₂ :
      (countableSpectralVisibleSet_finite p hp hsum L₂).toFinset = A := by
    ext k
    simpa only [Set.Finite.mem_toFinset, A] using
      Set.ext_iff.mp hvisible.symm k
  have hcard :
      countableSpectralVisibleCount p L₁ = A.card := by
    rw [countableSpectralVisibleCount,
      Set.ncard_eq_toFinset_card
        (countableSpectralVisibleSet p L₁)
        (countableSpectralVisibleSet_finite p hp hsum L₁)]
  rw [countableSpectralDepthProfileEntropy,
    countableSpectralDepthProfileEntropy, hA₂, hcard]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hsum :
      (∑ k ∈ A,
          ((L₂ + Real.log (p k)) -
            (L₁ + Real.log (p k)))) =
        (A.card : ℝ) * (L₂ - L₁) := by
    calc
      (∑ k ∈ A,
          ((L₂ + Real.log (p k)) -
            (L₁ + Real.log (p k)))) =
          ∑ _k ∈ A, (L₂ - L₁) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (A.card : ℝ) * (L₂ - L₁) := by
        simp
        ring
  rw [hsum]
  ring

end RHTower
