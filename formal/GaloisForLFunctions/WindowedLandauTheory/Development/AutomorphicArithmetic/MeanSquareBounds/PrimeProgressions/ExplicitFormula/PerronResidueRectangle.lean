import GaloisForLFunctions.HTGeometry.RectangleResidueTheorem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronResidues
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveZeroWindow

/-! The truncated Perron rectangle encloses the origin, the principal pole, and the critical-strip zeros. -/

open Complex DirichletCharacter Filter Finset Set Topology
open GaloisForLFunctions.HTGeometry

open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

theorem primitive_perron_rectangle {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {u c T : ℝ} (hu : 0 < u) (hc : 1 < c) (hT : 0 < T)
    {m : ℕ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (he : logDeriv χ.LFunction =ᶠ[𝓝[≠] (0 : ℂ)] fun s => (m : ℂ) / s + g s)
    (hhor : ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ c → |s.im| = T → χ.LFunction s ≠ 0) :
    RectangleIntegral' (primitivePerronIntegrand χ u) ⟨-(1 / 2), -T⟩ ⟨c, T⟩ =
      (if χ = 1 then (u : ℂ) else 0) -
        (∑ᶠ ρ ∈ primitiveInteriorZeros χ T, (analyticOrderNatAt χ.LFunction ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
        ((m : ℂ) * (Real.log u : ℂ) + g 0) := by
  classical
  let a : ℂ := ⟨-(1 / 2), -T⟩
  let b : ℂ := ⟨c, T⟩
  have hab : a.re ≤ b.re := by change -(1 / 2 : ℝ) ≤ c; linarith only [hc]
  have hab' : a.im ≤ b.im := by change -T ≤ T; linarith only [hT]
  let Z := (primitiveInteriorZeros_finite hχ T).toFinset
  let S := insert (1 : ℂ) (insert 0 Z)
  let F := primitivePerronIntegrand χ u
  have hZ (ρ : ℂ) : ρ ∈ Z ↔ ρ ∈ primitiveInteriorZeros χ T := Set.Finite.mem_toFinset _
  have h₀ : (0 : ℂ) ∉ Z := by rw [hZ]; simp [primitiveInteriorZeros]
  have h₁ : (1 : ℂ) ∉ Z := by rw [hZ]; simp [primitiveInteriorZeros]
  have h₁S : (1 : ℂ) ∉ insert 0 Z := by simp [h₁]
  have inside : ∀ p ∈ S, Rectangle a b ∈ 𝓝 p := by
    intro p hp
    rw [rectangle_mem_nhds_iff, mem_reProdIm, uIoo_of_le hab, uIoo_of_le hab']
    change p.re ∈ Ioo (-(1 / 2 : ℝ)) c ∧ p.im ∈ Ioo (-T) T
    rcases mem_insert.mp hp with rfl | hp
    · simp only [one_re, one_im, Set.mem_Ioo]
      exact ⟨⟨by norm_num, hc⟩, by linarith only [hT], hT⟩
    rcases mem_insert.mp hp with rfl | hp
    · simp only [zero_re, zero_im, Set.mem_Ioo]
      exact ⟨⟨by norm_num, by linarith only [hc]⟩, by linarith only [hT], hT⟩
    have h := (hZ p).1 hp
    exact ⟨⟨by linarith only [h.2.1.1], h.2.1.2.trans hc⟩, abs_lt.mp h.2.2⟩
  have zeroRes := perron_origin_residue (χ := χ) hu hg he
  have oneRes := perron_one_residue χ hu
  have otherRes (p : ℂ) (hp : p ∈ Z) :=
    perron_zero_residue (χ := χ) hu (fun e => h₀ (e ▸ hp)) (fun e => h₁ (e ▸ hp))
  have hmero : ∀ p ∈ S, MeromorphicAt F p := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact oneRes.1
    rcases mem_insert.mp hp with rfl | hp
    · exact zeroRes.1
    · exact (otherRes p hp).1
  have hoff : ∀ s ∈ Rectangle a b, s ∉ S → AnalyticAt ℂ F s := by
    intro s hs hS
    have hs₀ : s ≠ 0 := fun e => hS (by simp [S, e])
    have hs₁ : s ≠ 1 := fun e => hS (by simp [S, e])
    have hsZ : s ∉ Z := fun hz => hS (mem_insert_of_mem (mem_insert_of_mem hz))
    change s ∈ uIcc a.re b.re ×ℂ uIcc a.im b.im at hs
    rw [mem_reProdIm, uIcc_of_le hab, uIcc_of_le hab'] at hs
    change s.re ∈ Icc (-(1 / 2 : ℝ)) c ∧ s.im ∈ Icc (-T) T at hs
    have hL : χ.LFunction s ≠ 0 := by
      intro h
      by_cases h' : 1 ≤ s.re
      · exact LFunction_ne_zero_of_one_le_re χ (.inr hs₁) h' h
      by_cases h'' : s.re ≤ 0
      · exact hs₀ (eq_zero_and_order_of_primitive_zero_left hχ (by linarith only [hs.1.1]) h'' h).1
      have him : |s.im| < T := by
        refine lt_of_le_of_ne (abs_le.mpr hs.2) ?_
        exact fun e => hhor s hs.1.1 hs.1.2 e h
      exact hsZ ((hZ s).2 ⟨h, ⟨lt_of_not_ge h'', lt_of_not_ge h'⟩, him⟩)
    exact analyticAt_primitivePerronIntegrand hu hs₀ hs₁ hL
  have e := rectangleIntegral'_eq_sum_laurentCoeff (f := F) hab hab' inside hmero hoff
  have hsum : (∑ p ∈ Z, laurentCoeff F p (-1)) =
      -(∑ p ∈ Z, (analyticOrderNatAt χ.LFunction p : ℂ) * ((u : ℂ) ^ p / p)) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun p hp => (otherRes p hp).2
  change RectangleIntegral' F a b = _
  rw [e, show S = insert 1 (insert 0 Z) by rfl, sum_insert h₁S, sum_insert h₀,
    oneRes.2, zeroRes.2, hsum,
    finsum_mem_eq_finite_toFinset_sum _ (primitiveInteriorZeros_finite hχ T)]
  ring

end QH.PrimeProgressions
