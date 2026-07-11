import GaloisForLFunctions.EllipticThetaLogGlobalMeromorphic

/-!
# Exact global analytic locus of the constructed theta logarithmic kernel

The multiplicative nome orbit is the only possible polar divisor. Orbit-freeness is invariant
under integral nome scaling, while the intrinsic quasiperiod equation transports analyticity to
and from the wider fundamental annulus. Consequently the constructed logarithmic theta kernel is
analytic at every nonzero point outside the nome orbit.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-- Avoiding the full integral nome orbit is invariant under any integral nome rescaling. -/
theorem nomeOrbitFree_zpow_mul_iff {q x : ℂ} (hq0 : q ≠ 0) (k : ℤ) :
    (∀ N : ℤ, q ^ k * x ≠ q ^ N) ↔ (∀ N : ℤ, x ≠ q ^ N) := by
  constructor
  · intro h N hx
    apply h (k + N)
    rw [hx, zpow_add₀ hq0]
  · intro h N hx
    apply h (N - k)
    rw [zpow_sub₀ hq0]
    apply (eq_div_iff (zpow_ne_zero k hq0)).2
    simpa [mul_comm] using hx

/-- Natural nome scaling preserves avoidance of the integral nome orbit. -/
theorem nomeOrbitFree_nat_pow_mul_iff {q x : ℂ} (hq0 : q ≠ 0) (k : ℕ) :
    (∀ N : ℤ, q ^ k * x ≠ q ^ N) ↔ (∀ N : ℤ, x ≠ q ^ N) := by
  simpa only [zpow_natCast] using nomeOrbitFree_zpow_mul_iff
    (q := q) (x := x) hq0 (k : ℤ)

/-- Division by a natural nome power preserves avoidance of the integral nome orbit. -/
theorem nomeOrbitFree_div_nat_pow_iff {q x : ℂ} (hq0 : q ≠ 0) (k : ℕ) :
    (∀ N : ℤ, x / q ^ k ≠ q ^ N) ↔ (∀ N : ℤ, x ≠ q ^ N) := by
  have hz := nomeOrbitFree_zpow_mul_iff (q := q) (x := x) hq0 (- (k : ℤ))
  simpa only [zpow_neg, zpow_natCast, inv_mul_eq_div] using hz

/-- Exact global regular-locus theorem: outside zero and the full integral nome orbit, the
constructed theta logarithmic kernel is analytic. -/
theorem analyticAt_ellipticThetaLogKernel_of_nomeOrbitFree
    {q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hx0 : x ≠ 0)
    (hfree : ∀ N : ℤ, x ≠ q ^ N) :
    AnalyticAt ℂ (ellipticThetaLogKernel q) x := by
  have havoid_of_free : ∀ {w : ℂ}, (∀ N : ℤ, w ≠ q ^ N) →
      ∀ k : ℕ, q ^ k * w ≠ 1 := by
    intro w hw k hkw
    apply hw (- (k : ℤ))
    rw [zpow_neg, zpow_natCast]
    exact ((mul_eq_one_iff_inv_eq₀ (pow_ne_zero k hq0)).mp hkw).symm
  let a : ℝ := ‖q‖
  let b : ℝ := ‖x‖
  have ha0 : 0 < a := by simpa [a] using norm_pos_iff.mpr hq0
  have ha1 : a < 1 := by simpa [a] using hq
  have hb0 : 0 < b := by simpa [b] using norm_pos_iff.mpr hx0
  by_cases hb1 : b < 1
  · by_cases hwide : a ^ 2 < b
    · have hxq : x ≠ q := by simpa using hfree 1
      exact analyticAt_ellipticThetaLogKernel_of_norm_sq_between_of_ne
        hq0 (by simpa [a, b] using hwide) (by simpa [b] using hb1) hxq
    · have hpowExists : ∃ n : ℕ, a ^ n < b := exists_pow_lt_of_lt_one hb0 ha1
      let n := Nat.find hpowExists
      have hn : a ^ n < b := Nat.find_spec hpowExists
      have hn0 : n ≠ 0 := by
        intro hnzero
        have honeb : (1 : ℝ) < b := by simpa [hnzero] using hn
        exact (not_lt_of_ge hb1.le) honeb
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      rw [hm] at hn
      have hprev : b ≤ a ^ m := by
        have hmlt : m < n := by rw [hm]; exact Nat.lt_succ_self m
        have hnot : ¬ a ^ m < b := Nat.find_min hpowExists hmlt
        exact le_of_not_gt hnot
      let y : ℂ := x / q ^ m
      have hqm0 : q ^ m ≠ 0 := pow_ne_zero _ hq0
      have hy0 : y ≠ 0 := div_ne_zero hx0 hqm0
      have hxy : q ^ m * y = x := by dsimp [y]; field_simp [hqm0]
      have hyfree : ∀ N : ℤ, y ≠ q ^ N := by
        exact (nomeOrbitFree_div_nat_pow_iff hq0 m).mpr hfree
      have hnormY : ‖y‖ = b / a ^ m := by simp [y, a, b]
      have hpowm0 : 0 < a ^ m := pow_pos ha0 m
      have hYan : AnalyticAt ℂ (ellipticThetaLogKernel q) y := by
        by_cases heq : b = a ^ m
        · have hynorm : ‖y‖ = 1 := by rw [hnormY, heq, div_self hpowm0.ne']
          have hqynorm : ‖q * y‖ = a := by simp [hynorm, a]
          have hqwide : ‖q‖ ^ 2 < ‖q * y‖ := by
            rw [hqynorm]
            dsimp [a]
            nlinarith
          have hqy1 : ‖q * y‖ < 1 := by rw [hqynorm]; exact ha1
          have hy1 : y ≠ 1 := by simpa using hyfree 0
          have hqyq : q * y ≠ q := by
            intro h
            apply hy1
            apply mul_left_cancel₀ hq0
            simpa using h
          have hqyA := analyticAt_ellipticThetaLogKernel_of_norm_sq_between_of_ne
            hq0 hqwide hqy1 hqyq
          exact (analyticAt_ellipticThetaLogKernel_mul_nome_iff
            hq0 hq hy0 hy1).mp hqyA
        · have hbm : b < a ^ m := lt_of_le_of_ne hprev heq
          have hy1norm : ‖y‖ < 1 := by
            rw [hnormY, div_lt_one hpowm0]
            exact hbm
          have haley : a < ‖y‖ := by
            rw [hnormY, lt_div_iff₀ hpowm0]
            simpa [pow_succ, mul_comm] using hn
          have ha2y : ‖q‖ ^ 2 < ‖y‖ := by
            dsimp [a] at ha0 ha1 ⊢
            nlinarith
          have hyq : y ≠ q := by simpa using hyfree 1
          exact analyticAt_ellipticThetaLogKernel_of_norm_sq_between_of_ne
            hq0 ha2y hy1norm hyq
      have htransport := analyticAt_ellipticThetaLogKernel_pow_mul_iff
        (q := q) (x := y) hq0 hq hy0 m
          (fun k _ => havoid_of_free hyfree k)
      rw [hxy] at htransport
      exact htransport.mpr hYan
  · have hbge : 1 ≤ b := le_of_not_gt hb1
    have honeDiv : 0 < 1 / b := one_div_pos.mpr hb0
    obtain ⟨n, hnsmall⟩ := exists_pow_lt_of_lt_one honeDiv ha1
    have hP : a ^ n * b < 1 := by
      rw [lt_div_iff₀ hb0] at hnsmall
      simpa [mul_comm] using hnsmall
    let P : ℕ → Prop := fun k => a ^ k * b < 1
    have hPexists : ∃ k, P k := ⟨n, hP⟩
    let N := Nat.find hPexists
    have hN : a ^ N * b < 1 := Nat.find_spec hPexists
    have hN0 : N ≠ 0 := by
      intro hzero
      have hbsmall : b < 1 := by simpa [hzero] using hN
      exact (not_lt_of_ge hbge) hbsmall
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN0
    rw [hm] at hN
    have hprev : 1 ≤ a ^ m * b := by
      have hmlt : m < N := by rw [hm]; exact Nat.lt_succ_self m
      have hnot : ¬ a ^ m * b < 1 := Nat.find_min hPexists hmlt
      exact le_of_not_gt hnot
    let y : ℂ := q ^ (m + 1) * x
    have hyfree : ∀ K : ℤ, y ≠ q ^ K := by
      exact (nomeOrbitFree_nat_pow_mul_iff hq0 (m + 1)).mpr hfree
    have hynorm : ‖y‖ = a ^ (m + 1) * b := by simp [y, a, b]
    have hy1norm : ‖y‖ < 1 := by simpa [hynorm] using hN
    have ha2y : ‖q‖ ^ 2 < ‖y‖ := by
      have haY : a ≤ a ^ (m + 1) * b := by
        calc
          a = a * 1 := by ring
          _ ≤ a * (a ^ m * b) := mul_le_mul_of_nonneg_left hprev ha0.le
          _ = a ^ (m + 1) * b := by rw [pow_succ]; ring
      rw [hynorm]
      dsimp [a] at ha0 ha1 haY ⊢
      nlinarith
    have hyq : y ≠ q := by simpa using hyfree 1
    have hY := analyticAt_ellipticThetaLogKernel_of_norm_sq_between_of_ne
      hq0 ha2y hy1norm hyq
    have htransport := analyticAt_ellipticThetaLogKernel_pow_mul_iff
      (q := q) (x := x) hq0 hq hx0 (m + 1)
        (fun k _ => havoid_of_free hfree k)
    change AnalyticAt ℂ (ellipticThetaLogKernel q) y ↔
      AnalyticAt ℂ (ellipticThetaLogKernel q) x at htransport
    exact htransport.mp hY

end

end GaloisForLFunctions
