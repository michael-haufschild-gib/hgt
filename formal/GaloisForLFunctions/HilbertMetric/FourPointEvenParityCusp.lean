import GaloisForLFunctions.HilbertMetric.SixthJetRaywiseCoalescedCone

/-!
# The local even wall of a palindromic four-point kernel

For an even-at-the-center `C⁴` radial profile, the reflection-even block of the equispaced
four-point Gram kernel has its first nonzero jet at order four.  Its coefficient is exactly the
strict fourth Hankel margin already governing the three-point coalesced cusp.  This separates the
even four-point obstruction from the genuinely new reflection-odd one.
-/

open Set

namespace HilbertMetric

noncomputable section

/-- Determinant of the reflection-even block on equispaced four-point data. -/
def fourPointEvenWall (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f 0 + f (3 * t)) * (f 0 + f t) - (f t + f (2 * t)) ^ 2

private def scalarJetProductAtZero
    (n : ℕ) (P Q : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    n.choose i * iteratedDeriv i P 0 * iteratedDeriv (n - i) Q 0

private theorem iteratedDeriv_mul_zero_eq_scalarJetProductAtZero
    {P Q : ℝ → ℝ} {n : ℕ}
    (hP : ContDiff ℝ n P) (hQ : ContDiff ℝ n Q) :
    iteratedDeriv n (P * Q) 0 = scalarJetProductAtZero n P Q := by
  exact iteratedDeriv_mul hP.contDiffAt hQ.contDiffAt

private theorem iteratedDeriv_fourPointEvenFactor_zero
    {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (c : ℝ) :
    iteratedDeriv n (fun t => f 0 + f (c * t)) 0 =
      if n = 0 then 2 * f 0 else c ^ n * iteratedDeriv n f 0 := by
  cases n with
  | zero => simp; ring
  | succ n =>
      rw [iteratedDeriv_const_add (Nat.succ_pos n)]
      rw [iteratedDeriv_comp_const_mul hf c]
      simp

private theorem iteratedDeriv_fourPointSumFactor_zero
    {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (c d : ℝ) :
    iteratedDeriv n (fun t => f (c * t) + f (d * t)) 0 =
      if n = 0 then 2 * f 0 else
        (c ^ n + d ^ n) * iteratedDeriv n f 0 := by
  cases n with
  | zero => simp; ring
  | succ n =>
      let hc : ContDiff ℝ (n + 1) (fun t : ℝ => c * t) := by fun_prop
      let hd : ContDiff ℝ (n + 1) (fun t : ℝ => d * t) := by fun_prop
      change iteratedDeriv (n + 1)
        ((f ∘ fun t : ℝ => c * t) + f ∘ fun t : ℝ => d * t) 0 = _
      rw [iteratedDeriv_add (hf.comp hc).contDiffAt (hf.comp hd).contDiffAt]
      change iteratedDeriv (n + 1) (fun t : ℝ => f (c * t)) 0 +
          iteratedDeriv (n + 1) (fun t : ℝ => f (d * t)) 0 = _
      rw [iteratedDeriv_comp_const_mul hf c,
        iteratedDeriv_comp_const_mul hf d]
      simp
      ring

/-- The even wall's fourth jet is exactly ninety-six times the fourth Hankel margin. -/
theorem iteratedDeriv_four_fourPointEvenWall_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f)
    (h₁ : iteratedDeriv 1 f 0 = 0)
    (h₃ : iteratedDeriv 3 f 0 = 0) :
    iteratedDeriv 4 (fourPointEvenWall f) 0 =
      96 * (f 0 * iteratedDeriv 4 f 0 - iteratedDeriv 2 f 0 ^ 2) := by
  let L : ℝ → ℝ := fun t => f 0 + f (3 * t)
  let R : ℝ → ℝ := fun t => f 0 + f t
  let M : ℝ → ℝ := fun t => f t + f (2 * t)
  have hL : ContDiff ℝ 4 L := by
    dsimp only [L]
    have h3 : ContDiff ℝ 4 (fun t : ℝ => 3 * t) := by fun_prop
    exact contDiff_const.add (hf.comp h3)
  have hR : ContDiff ℝ 4 R := by
    dsimp only [R]
    exact contDiff_const.add hf
  have hM : ContDiff ℝ 4 M := by
    dsimp only [M]
    have h2 : ContDiff ℝ 4 (fun t : ℝ => 2 * t) := by fun_prop
    exact hf.add (hf.comp h2)
  have hLjet (n : ℕ) (hn : n ≤ 4) :
      iteratedDeriv n L 0 =
        if n = 0 then 2 * f 0 else 3 ^ n * iteratedDeriv n f 0 := by
    simpa only [L] using iteratedDeriv_fourPointEvenFactor_zero
      (hf.of_le (by exact_mod_cast hn)) 3
  have hRjet (n : ℕ) (hn : n ≤ 4) :
      iteratedDeriv n R 0 =
        if n = 0 then 2 * f 0 else iteratedDeriv n f 0 := by
    simpa [R] using iteratedDeriv_fourPointEvenFactor_zero
      (hf.of_le (by exact_mod_cast hn)) 1
  have hMjet (n : ℕ) (hn : n ≤ 4) :
      iteratedDeriv n M 0 =
        if n = 0 then 2 * f 0 else (1 + 2 ^ n) * iteratedDeriv n f 0 := by
    simpa [M] using iteratedDeriv_fourPointSumFactor_zero
      (hf.of_le (by exact_mod_cast hn)) 1 2
  have hLR : iteratedDeriv 4 (L * R) 0 = scalarJetProductAtZero 4 L R :=
    iteratedDeriv_mul_zero_eq_scalarJetProductAtZero hL hR
  have hMM : iteratedDeriv 4 (M * M) 0 = scalarJetProductAtZero 4 M M :=
    iteratedDeriv_mul_zero_eq_scalarJetProductAtZero hM hM
  rw [show fourPointEvenWall f = L * R - M * M by
    funext t
    have h3 : f (3 * t) = f (t * 3) := by
      congr 1
      ring
    have h2 : f (2 * t) = f (t * 2) := by
      congr 1
      ring
    simp only [fourPointEvenWall, L, R, M, Pi.sub_apply, Pi.mul_apply]
    rw [h3, h2, pow_two]]
  calc
    iteratedDeriv 4 (L * R - M * M) 0 =
        iteratedDeriv 4 (L * R) 0 - iteratedDeriv 4 (M * M) 0 :=
      iteratedDeriv_sub (hL.mul hR).contDiffAt (hM.mul hM).contDiffAt
    _ = scalarJetProductAtZero 4 L R - scalarJetProductAtZero 4 M M := by
      rw [hLR, hMM]
    _ = _ := by
      norm_num [scalarJetProductAtZero, Finset.sum_range_succ, Nat.choose,
        hLjet, hRjet, hMjet, h₁, h₃]
      ring

/-- All lower even-wall jets vanish at the coalesced endpoint. -/
theorem iteratedDeriv_fourPointEvenWall_zero_of_lt_four
    {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f)
    (h₁ : iteratedDeriv 1 f 0 = 0)
    (h₃ : iteratedDeriv 3 f 0 = 0)
    {n : ℕ} (hn : n < 4) :
    iteratedDeriv n (fourPointEvenWall f) 0 = 0 := by
  let L : ℝ → ℝ := fun t => f 0 + f (3 * t)
  let R : ℝ → ℝ := fun t => f 0 + f t
  let M : ℝ → ℝ := fun t => f t + f (2 * t)
  have hL : ContDiff ℝ n L := by
    dsimp only [L]
    have h3 : ContDiff ℝ n (fun t : ℝ => 3 * t) := by fun_prop
    exact contDiff_const.add ((hf.of_le (by exact_mod_cast hn.le)).comp h3)
  have hR : ContDiff ℝ n R := by
    dsimp only [R]
    exact contDiff_const.add (hf.of_le (by exact_mod_cast hn.le))
  have hM : ContDiff ℝ n M := by
    dsimp only [M]
    have h2 : ContDiff ℝ n (fun t : ℝ => 2 * t) := by fun_prop
    exact (hf.of_le (by exact_mod_cast hn.le)).add
      ((hf.of_le (by exact_mod_cast hn.le)).comp h2)
  have hLjet (j : ℕ) (hj : j ≤ n) :
      iteratedDeriv j L 0 =
        if j = 0 then 2 * f 0 else 3 ^ j * iteratedDeriv j f 0 := by
    simpa only [L] using iteratedDeriv_fourPointEvenFactor_zero
      (hf.of_le (by exact_mod_cast hj.trans hn.le)) 3
  have hRjet (j : ℕ) (hj : j ≤ n) :
      iteratedDeriv j R 0 =
        if j = 0 then 2 * f 0 else iteratedDeriv j f 0 := by
    simpa [R] using iteratedDeriv_fourPointEvenFactor_zero
      (hf.of_le (by exact_mod_cast hj.trans hn.le)) 1
  have hMjet (j : ℕ) (hj : j ≤ n) :
      iteratedDeriv j M 0 =
        if j = 0 then 2 * f 0 else (1 + 2 ^ j) * iteratedDeriv j f 0 := by
    simpa [M] using iteratedDeriv_fourPointSumFactor_zero
      (hf.of_le (by exact_mod_cast hj.trans hn.le)) 1 2
  have hLR : iteratedDeriv n (L * R) 0 = scalarJetProductAtZero n L R :=
    iteratedDeriv_mul_zero_eq_scalarJetProductAtZero hL hR
  have hMM : iteratedDeriv n (M * M) 0 = scalarJetProductAtZero n M M :=
    iteratedDeriv_mul_zero_eq_scalarJetProductAtZero hM hM
  rw [show fourPointEvenWall f = L * R - M * M by
    funext t
    have h3 : f (3 * t) = f (t * 3) := by
      congr 1
      ring
    have h2 : f (2 * t) = f (t * 2) := by
      congr 1
      ring
    simp only [fourPointEvenWall, L, R, M, Pi.sub_apply, Pi.mul_apply]
    rw [h3, h2, pow_two]]
  calc
    iteratedDeriv n (L * R - M * M) 0 =
        iteratedDeriv n (L * R) 0 - iteratedDeriv n (M * M) 0 :=
      iteratedDeriv_sub (hL.mul hR).contDiffAt (hM.mul hM).contDiffAt
    _ = scalarJetProductAtZero n L R - scalarJetProductAtZero n M M := by
      rw [hLR, hMM]
    _ = 0 := by
      interval_cases n
      all_goals
        norm_num [scalarJetProductAtZero, Finset.sum_range_succ, Nat.choose,
          hLjet, hRjet, hMjet, h₁, h₃]
      all_goals ring

/-- A strict fourth Hankel margin opens the even four-point wall to the right of the center. -/
theorem exists_fourPointEvenWall_pos_right
    {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f)
    (h₁ : iteratedDeriv 1 f 0 = 0)
    (h₃ : iteratedDeriv 3 f 0 = 0)
    (h₄ : 0 < f 0 * iteratedDeriv 4 f 0 - iteratedDeriv 2 f 0 ^ 2) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < fourPointEvenWall f t := by
  let W := fourPointEvenWall f
  have hW : ContDiff ℝ 4 W := by
    dsimp only [W]
    unfold fourPointEvenWall
    fun_prop
  have hchain : ∀ n : ℕ, n < 4 → ∀ x : ℝ,
      HasDerivAt (iteratedDeriv n W) (iteratedDeriv (n + 1) W x) x := by
    intro n hn x
    have hd := hW.differentiable_iteratedDeriv n (by exact_mod_cast hn)
    simpa only [iteratedDeriv_succ] using (hd x).hasDerivAt
  have hzero : ∀ n : ℕ, n < 4 → iteratedDeriv n W 0 = 0 := by
    intro n hn
    exact iteratedDeriv_fourPointEvenWall_zero_of_lt_four hf h₁ h₃ hn
  have hfour : 0 < iteratedDeriv 4 W 0 := by
    rw [iteratedDeriv_four_fourPointEvenWall_zero hf h₁ h₃]
    positivity
  have hW4cont : Continuous (iteratedDeriv 4 W) :=
    hW.continuous_iteratedDeriv 4 (by norm_num)
  rcases exists_pos_right_of_secondJet_pos
      (hchain 2 (by norm_num)) (hchain 3 (by norm_num)) hW4cont
      (hzero 2 (by norm_num)) (hzero 3 (by norm_num)) hfour with
    ⟨delta, hdelta, hW2pos⟩
  refine ⟨delta, hdelta, ?_⟩
  exact pos_right_of_secondJet_posOn
    (hchain 0 (by norm_num)) (hchain 1 (by norm_num))
    (hzero 0 (by norm_num)) (hzero 1 (by norm_num)) hdelta fun t ht => by
      have ht' : 0 < t ∧ t < delta := by
        simpa [interior_Icc, hdelta.ne'] using ht
      exact hW2pos t ht'.1 ht'.2

end

end HilbertMetric
