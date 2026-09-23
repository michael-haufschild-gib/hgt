import GaloisForLFunctions.HilbertMetric.FourPointEvenParityCusp

open Set

namespace HilbertMetric

noncomputable section

/-- Determinant of the reflection-odd block on equispaced four-point data. -/
def fourPointOddWall (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f 0 - f (3 * t)) * (f 0 - f t) - (f t - f (2 * t)) ^ (2 : ℕ)

private def oddScalarJetProductAtZero
    (n : ℕ) (P Q : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    n.choose i * iteratedDeriv i P 0 * iteratedDeriv (n - i) Q 0

private theorem iteratedDeriv_mul_zero_eq_oddScalarJetProductAtZero
    {P Q : ℝ → ℝ} {n : ℕ}
    (hP : ContDiff ℝ n P) (hQ : ContDiff ℝ n Q) :
    iteratedDeriv n (P * Q) 0 = oddScalarJetProductAtZero n P Q := by
  exact iteratedDeriv_mul hP.contDiffAt hQ.contDiffAt

private theorem iteratedDeriv_fourPointOddFactor_zero
    {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (c : ℝ) :
    iteratedDeriv n (fun t => f 0 - f (c * t)) 0 =
      if n = 0 then 0 else -(c ^ n * iteratedDeriv n f 0) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [iteratedDeriv_const_sub (Nat.succ_pos n)]
      rw [iteratedDeriv_neg]
      rw [iteratedDeriv_comp_const_mul hf c]
      simp

private theorem iteratedDeriv_fourPointDifferenceFactor_zero
    {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (c d : ℝ) :
    iteratedDeriv n (fun t => f (c * t) - f (d * t)) 0 =
      if n = 0 then 0 else
        (c ^ n - d ^ n) * iteratedDeriv n f 0 := by
  cases n with
  | zero => simp
  | succ n =>
      let hc : ContDiff ℝ (n + 1) (fun t : ℝ => c * t) := by fun_prop
      let hd : ContDiff ℝ (n + 1) (fun t : ℝ => d * t) := by fun_prop
      change iteratedDeriv (n + 1)
        ((f ∘ fun t : ℝ => c * t) - f ∘ fun t : ℝ => d * t) 0 = _
      rw [iteratedDeriv_sub (hf.comp hc).contDiffAt (hf.comp hd).contDiffAt]
      change iteratedDeriv (n + 1) (fun t : ℝ => f (c * t)) 0 -
          iteratedDeriv (n + 1) (fun t : ℝ => f (d * t)) 0 = _
      rw [iteratedDeriv_comp_const_mul hf c,
        iteratedDeriv_comp_const_mul hf d]
      simp
      ring

/-- Odd wall's eighth jet is exactly `10080` times second--sixth Hankel margin. -/
theorem iteratedDeriv_eight_fourPointOddWall_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 8 f)
    (h₁ : iteratedDeriv 1 f 0 = 0)
    (h₃ : iteratedDeriv 3 f 0 = 0)
    (h₅ : iteratedDeriv 5 f 0 = 0)
    (h₇ : iteratedDeriv 7 f 0 = 0) :
    iteratedDeriv 8 (fourPointOddWall f) 0 =
      10080 * (iteratedDeriv 2 f 0 * iteratedDeriv 6 f 0 -
        iteratedDeriv 4 f 0 ^ (2 : ℕ)) := by
  let L : ℝ → ℝ := fun t => f 0 - f (3 * t)
  let R : ℝ → ℝ := fun t => f 0 - f t
  let M : ℝ → ℝ := fun t => f t - f (2 * t)
  have hL : ContDiff ℝ 8 L := by
    dsimp only [L]
    have h3 : ContDiff ℝ 8 (fun t : ℝ => 3 * t) := by fun_prop
    exact contDiff_const.sub (hf.comp h3)
  have hR : ContDiff ℝ 8 R := by
    dsimp only [R]
    exact contDiff_const.sub hf
  have hM : ContDiff ℝ 8 M := by
    dsimp only [M]
    have h2 : ContDiff ℝ 8 (fun t : ℝ => 2 * t) := by fun_prop
    exact hf.sub (hf.comp h2)
  have hLjet (n : ℕ) (hn : n ≤ 8) :
      iteratedDeriv n L 0 =
        if n = 0 then 0 else -(3 ^ n * iteratedDeriv n f 0) := by
    simpa only [L] using iteratedDeriv_fourPointOddFactor_zero
      (hf.of_le (by exact_mod_cast hn)) 3
  have hRjet (n : ℕ) (hn : n ≤ 8) :
      iteratedDeriv n R 0 =
        if n = 0 then 0 else -iteratedDeriv n f 0 := by
    simpa [R] using iteratedDeriv_fourPointOddFactor_zero
      (hf.of_le (by exact_mod_cast hn)) 1
  have hMjet (n : ℕ) (hn : n ≤ 8) :
      iteratedDeriv n M 0 =
        if n = 0 then 0 else (1 - 2 ^ n) * iteratedDeriv n f 0 := by
    simpa [M] using iteratedDeriv_fourPointDifferenceFactor_zero
      (hf.of_le (by exact_mod_cast hn)) 1 2
  have hLR : iteratedDeriv 8 (L * R) 0 = oddScalarJetProductAtZero 8 L R :=
    iteratedDeriv_mul_zero_eq_oddScalarJetProductAtZero hL hR
  have hMM : iteratedDeriv 8 (M * M) 0 = oddScalarJetProductAtZero 8 M M :=
    iteratedDeriv_mul_zero_eq_oddScalarJetProductAtZero hM hM
  rw [show fourPointOddWall f = L * R - M * M by
    funext t
    simp only [fourPointOddWall, L, R, M, Pi.sub_apply, Pi.mul_apply]
    rw [pow_two]]
  calc
    iteratedDeriv 8 (L * R - M * M) 0 =
        iteratedDeriv 8 (L * R) 0 - iteratedDeriv 8 (M * M) 0 :=
      iteratedDeriv_sub (hL.mul hR).contDiffAt (hM.mul hM).contDiffAt
    _ = oddScalarJetProductAtZero 8 L R - oddScalarJetProductAtZero 8 M M := by
      rw [hLR, hMM]
    _ = _ := by
      norm_num [oddScalarJetProductAtZero, Finset.sum_range_succ, Nat.choose,
        hLjet, hRjet, hMjet, h₁, h₃, h₅, h₇]
      ring

/-- All lower odd-wall jets vanish at coalesced endpoint. -/
theorem iteratedDeriv_fourPointOddWall_zero_of_lt_eight
    {f : ℝ → ℝ} (hf : ContDiff ℝ 8 f)
    (h₁ : iteratedDeriv 1 f 0 = 0)
    (h₃ : iteratedDeriv 3 f 0 = 0)
    (h₅ : iteratedDeriv 5 f 0 = 0)
    (h₇ : iteratedDeriv 7 f 0 = 0)
    {n : ℕ} (hn : n < 8) :
    iteratedDeriv n (fourPointOddWall f) 0 = 0 := by
  let L : ℝ → ℝ := fun t => f 0 - f (3 * t)
  let R : ℝ → ℝ := fun t => f 0 - f t
  let M : ℝ → ℝ := fun t => f t - f (2 * t)
  have hfn : ContDiff ℝ n f := hf.of_le (by exact_mod_cast hn.le)
  have hL : ContDiff ℝ n L := by
    dsimp only [L]
    have h3 : ContDiff ℝ n (fun t : ℝ => 3 * t) := by fun_prop
    exact contDiff_const.sub (hfn.comp h3)
  have hR : ContDiff ℝ n R := by
    dsimp only [R]
    exact contDiff_const.sub hfn
  have hM : ContDiff ℝ n M := by
    dsimp only [M]
    have h2 : ContDiff ℝ n (fun t : ℝ => 2 * t) := by fun_prop
    exact hfn.sub (hfn.comp h2)
  have hLjet (j : ℕ) (hj : j ≤ n) :
      iteratedDeriv j L 0 =
        if j = 0 then 0 else -(3 ^ j * iteratedDeriv j f 0) := by
    simpa only [L] using iteratedDeriv_fourPointOddFactor_zero
      (hf.of_le (by exact_mod_cast hj.trans hn.le)) 3
  have hRjet (j : ℕ) (hj : j ≤ n) :
      iteratedDeriv j R 0 =
        if j = 0 then 0 else -iteratedDeriv j f 0 := by
    simpa [R] using iteratedDeriv_fourPointOddFactor_zero
      (hf.of_le (by exact_mod_cast hj.trans hn.le)) 1
  have hMjet (j : ℕ) (hj : j ≤ n) :
      iteratedDeriv j M 0 =
        if j = 0 then 0 else (1 - 2 ^ j) * iteratedDeriv j f 0 := by
    simpa [M] using iteratedDeriv_fourPointDifferenceFactor_zero
      (hf.of_le (by exact_mod_cast hj.trans hn.le)) 1 2
  have hLR : iteratedDeriv n (L * R) 0 = oddScalarJetProductAtZero n L R :=
    iteratedDeriv_mul_zero_eq_oddScalarJetProductAtZero hL hR
  have hMM : iteratedDeriv n (M * M) 0 = oddScalarJetProductAtZero n M M :=
    iteratedDeriv_mul_zero_eq_oddScalarJetProductAtZero hM hM
  rw [show fourPointOddWall f = L * R - M * M by
    funext t
    simp only [fourPointOddWall, L, R, M, Pi.sub_apply, Pi.mul_apply]
    rw [pow_two]]
  calc
    iteratedDeriv n (L * R - M * M) 0 =
        iteratedDeriv n (L * R) 0 - iteratedDeriv n (M * M) 0 :=
      iteratedDeriv_sub (hL.mul hR).contDiffAt (hM.mul hM).contDiffAt
    _ = oddScalarJetProductAtZero n L R - oddScalarJetProductAtZero n M M := by
      rw [hLR, hMM]
    _ = 0 := by
      interval_cases n
      all_goals
        norm_num [oddScalarJetProductAtZero, Finset.sum_range_succ, Nat.choose,
          hLjet, hRjet, hMjet, h₁, h₃, h₅, h₇]
      all_goals ring

/-- Strict second--sixth Hankel margin opens odd four-point wall to right. -/
theorem exists_fourPointOddWall_pos_right
    {f : ℝ → ℝ} (hf : ContDiff ℝ 8 f)
    (h₁ : iteratedDeriv 1 f 0 = 0)
    (h₃ : iteratedDeriv 3 f 0 = 0)
    (h₅ : iteratedDeriv 5 f 0 = 0)
    (h₇ : iteratedDeriv 7 f 0 = 0)
    (h₆ : 0 < iteratedDeriv 2 f 0 * iteratedDeriv 6 f 0 -
      iteratedDeriv 4 f 0 ^ (2 : ℕ)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < fourPointOddWall f t := by
  let W := fourPointOddWall f
  have hW : ContDiff ℝ 8 W := by
    dsimp only [W]
    unfold fourPointOddWall
    fun_prop
  have hchain : ∀ n : ℕ, n < 8 → ∀ x : ℝ,
      HasDerivAt (iteratedDeriv n W) (iteratedDeriv (n + 1) W x) x := by
    intro n hn x
    have hd := hW.differentiable_iteratedDeriv n (by exact_mod_cast hn)
    simpa only [iteratedDeriv_succ] using (hd x).hasDerivAt
  have hzero : ∀ n : ℕ, n < 8 → iteratedDeriv n W 0 = 0 := by
    intro n hn
    exact iteratedDeriv_fourPointOddWall_zero_of_lt_eight
      hf h₁ h₃ h₅ h₇ hn
  have height : 0 < iteratedDeriv 8 W 0 := by
    rw [iteratedDeriv_eight_fourPointOddWall_zero hf h₁ h₃ h₅ h₇]
    positivity
  have hW8cont : Continuous (iteratedDeriv 8 W) :=
    hW.continuous_iteratedDeriv 8 (by norm_num)
  rcases exists_pos_right_of_secondJet_pos
      (hchain 6 (by norm_num)) (hchain 7 (by norm_num)) hW8cont
      (hzero 6 (by norm_num)) (hzero 7 (by norm_num)) height with
    ⟨delta, hdelta, hW6pos⟩
  have hW4pos : ∀ t : ℝ, 0 < t → t < delta →
      0 < iteratedDeriv 4 W t := by
    intro t ht htδ
    apply pos_right_of_secondJet_posOn
      (hchain 4 (by norm_num)) (hchain 5 (by norm_num))
      (hzero 4 (by norm_num)) (hzero 5 (by norm_num)) hdelta
    intro s hs
    have hs' : 0 < s ∧ s < delta := by
      simpa [interior_Icc, hdelta.ne'] using hs
    exact hW6pos s hs'.1 hs'.2
    · exact ht
    · exact htδ
  have hW2pos : ∀ t : ℝ, 0 < t → t < delta →
      0 < iteratedDeriv 2 W t := by
    intro t ht htδ
    apply pos_right_of_secondJet_posOn
      (hchain 2 (by norm_num)) (hchain 3 (by norm_num))
      (hzero 2 (by norm_num)) (hzero 3 (by norm_num)) hdelta
    intro s hs
    have hs' : 0 < s ∧ s < delta := by
      simpa [interior_Icc, hdelta.ne'] using hs
    exact hW4pos s hs'.1 hs'.2
    · exact ht
    · exact htδ
  refine ⟨delta, hdelta, ?_⟩
  intro t ht htδ
  apply pos_right_of_secondJet_posOn
    (hchain 0 (by norm_num)) (hchain 1 (by norm_num))
    (hzero 0 (by norm_num)) (hzero 1 (by norm_num)) hdelta
  intro s hs
  have hs' : 0 < s ∧ s < delta := by
    simpa [interior_Icc, hdelta.ne'] using hs
  exact hW2pos s hs'.1 hs'.2
  · exact ht
  · exact htδ

end

end HilbertMetric
