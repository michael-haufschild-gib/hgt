import GaloisForLFunctions.EllipticThetaLogNomeTransport

/-!
# Global meromorphicity of the constructed theta logarithmic kernel

For every nonzero nome in the open unit disc, the constructed theta logarithmic kernel is
meromorphic on the punctured multiplicative plane. A minimal-power argument reduces each nonzero
point to the wider one-pole annulus, and the intrinsic nome functional equation transports the
meromorphic germ bidirectionally.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions

noncomputable section

theorem meromorphicOn_ellipticThetaLogKernel_compl_zero {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    MeromorphicOn (ellipticThetaLogKernel q) ({0}ᶜ : Set ℂ) := by
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  let a : ℝ := ‖q‖
  let b : ℝ := ‖x‖
  have ha0 : 0 < a := by simpa [a] using norm_pos_iff.mpr hq0
  have ha1 : a < 1 := by simpa [a] using hq
  have hb0 : 0 < b := by simpa [b] using norm_pos_iff.mpr hx0
  by_cases hb1 : b < 1
  · by_cases hwide : a ^ 2 < b
    · exact meromorphicAt_ellipticThetaLogKernel_of_norm_sq_between
        hq0 (by simpa [a, b] using hwide) (by simpa [b] using hb1)
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
      have hnormY : ‖y‖ = b / a ^ m := by simp [y, a, b]
      have hpowm0 : 0 < a ^ m := pow_pos ha0 m
      have hYmero : MeromorphicAt (ellipticThetaLogKernel q) y := by
        by_cases heq : b = a ^ m
        · have hynorm : ‖y‖ = 1 := by rw [hnormY, heq, div_self hpowm0.ne']
          have hqynorm : ‖q * y‖ = a := by simp [hynorm, a]
          have hqwide : ‖q‖ ^ 2 < ‖q * y‖ := by
            rw [hqynorm]
            dsimp [a]
            nlinarith
          have hqy1 : ‖q * y‖ < 1 := by rw [hqynorm]; exact ha1
          have hqyM := meromorphicAt_ellipticThetaLogKernel_of_norm_sq_between
            hq0 hqwide hqy1
          exact (meromorphicAt_ellipticThetaLogKernel_mul_nome_iff hq0 hq).mp hqyM
        · have hbm : b < a ^ m := lt_of_le_of_ne hprev heq
          have hy1 : ‖y‖ < 1 := by
            rw [hnormY, div_lt_one hpowm0]
            exact hbm
          have haley : a < ‖y‖ := by
            rw [hnormY, lt_div_iff₀ hpowm0]
            simpa [pow_succ, mul_comm] using hn
          have ha2y : ‖q‖ ^ 2 < ‖y‖ := by
            dsimp [a] at ha0 ha1 ⊢
            nlinarith
          exact meromorphicAt_ellipticThetaLogKernel_of_norm_sq_between hq0 ha2y hy1
      have htransport := meromorphicAt_ellipticThetaLogKernel_pow_mul_iff
        (q := q) (x := y) hq0 hq m
      rw [hxy] at htransport
      exact htransport.mpr hYmero
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
    have hynorm : ‖y‖ = a ^ (m + 1) * b := by simp [y, a, b]
    have hy1 : ‖y‖ < 1 := by simpa [hynorm] using hN
    have ha2y : ‖q‖ ^ 2 < ‖y‖ := by
      have haY : a ≤ a ^ (m + 1) * b := by
        calc
          a = a * 1 := by ring
          _ ≤ a * (a ^ m * b) := mul_le_mul_of_nonneg_left hprev ha0.le
          _ = a ^ (m + 1) * b := by rw [pow_succ]; ring
      rw [hynorm]
      dsimp [a] at ha0 ha1 haY ⊢
      nlinarith
    have hY := meromorphicAt_ellipticThetaLogKernel_of_norm_sq_between hq0 ha2y hy1
    exact (meromorphicAt_ellipticThetaLogKernel_pow_mul_iff hq0 hq (m + 1)).mp hY

/-- The additively normalized pullback is globally meromorphic on the entire additive plane. -/
theorem meromorphicOn_ellipticThetaAdditiveLogKernel
    {τ : ℂ} (hτ : 0 < τ.im) :
    MeromorphicOn (ellipticThetaAdditiveLogKernel τ) Set.univ := by
  intro z _
  have hmult := meromorphicOn_ellipticThetaLogKernel_compl_zero
    (ellipticNome_ne_zero τ) (norm_ellipticNome_lt_one hτ)
    (ellipticThetaCoordinate τ z) (by simp [ellipticThetaCoordinate_ne_zero])
  have hcomp := hmult.comp_analyticAt (analyticAt_ellipticThetaCoordinate τ z)
  have hc : MeromorphicAt (fun _ : ℂ => (2 * Real.pi * I : ℂ)) z :=
    analyticAt_const.meromorphicAt
  simpa [ellipticThetaAdditiveLogKernel, Function.comp_def] using hc.mul hcomp

end

end GaloisForLFunctions
