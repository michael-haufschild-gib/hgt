import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalOnset

/-!
# The depth-resolved exceptional-point index

Fix shadow-free heights `T₁ < T₂` and a depth `h > 0` with `Re ξ(½ + h + iT_j) ≠ 0`.

**Theorem** (`two_mul_shallow_mass_le_exceptional_mass`). Either infinitely many depths in
`(0, h]` carry an exceptional point in `[T₁, T₂]`, or for finitely many such depths `F`,
`2·#{ξ(ρ) = 0 : ½ < Re ρ < ½ + h, Im ρ ∈ [T₁, T₂]} ≤ Σ_{h' ∈ F} M(h') + 2`.
Zeros are counted with multiplicity, and `M` is the exceptional mass.

So the exceptional mass accumulated up to depth `h` accounts for every off-line zero shallower
than `h`, up to one. The onset law (`offline_mass_below_onset_le_one`) is the case `F = ∅`.

**Proof.** Moving to greater depth, the defect count `D` drops across a depth `t` by at most the
exceptional mass `M(t)` (`exists_local_windowDefectCount`). Real induction gives
`D(a) ≤ D(h) + Σ M` (`le_add_sum_of_local_jumps`). Then compare `D(0) ≥ 2·#{off-line}` with the
transport law `D(h) ≤ 2·#{Re ρ ≥ ½ + h} + 2`.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **Real induction with jumps, relative form.** Under the hypotheses of `le_sum_of_local_jumps`
without `D b = 0`: `D a ≤ D b + Σ_{f ∈ F} M f`. -/
theorem le_add_sum_of_local_jumps {D M : ℝ → ℕ} {a b : ℝ} (hab : a ≤ b) (F : Finset ℝ)
    (hF : ∀ t ∈ Icc a b, M t ≠ 0 → t ∈ F)
    (hlsc : ∀ t ∈ Icc a b, ∃ δ > 0, ∀ s, |s - t| < δ → D t ≤ D s)
    (hjump : ∀ t ∈ Icc a b, ∃ δ > 0, ∀ s, |s - t| < δ → D s ≤ D t + M t) :
    D a ≤ D b + ∑ f ∈ F, M f := by
  classical
  set D' : ℝ → ℕ := fun t => D t - D b with hD'
  -- shift by `D b`: apply the absolute form to `t ↦ D t - D b` on `[a, b]`
  have hmain := le_sum_of_local_jumps (D := D') (M := M) hab F hF (by simp [hD'])
    (fun t ht => by
      obtain ⟨δ, hδ, h⟩ := hlsc t ht
      exact ⟨δ, hδ, fun s hs => Nat.sub_le_sub_right (h s hs) _⟩)
    (fun t ht => by
      obtain ⟨δ, hδ, h⟩ := hjump t ht
      refine ⟨δ, hδ, fun s hs => ?_⟩
      have := h s hs
      simp only [hD']
      omega)
  simp only [hD'] at hmain
  omega

/-- **The depth-resolved index law.** -/
theorem two_mul_shallow_mass_le_exceptional_mass {T₁ T₂ h : ℝ} (hT : T₁ < T₂) (hh : 0 < h)
    (hg₁ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₁ - v.re) ^ 2)
    (hg₂ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₂ - v.re) ^ 2)
    (hA₁ : (xi (((1 / 2 + h : ℝ) : ℂ) + T₁ * I)).re ≠ 0)
    (hA₂ : (xi (((1 / 2 + h : ℝ) : ℂ) + T₂ * I)).re ≠ 0) :
    {t : ℝ | t ∈ Ioc 0 h ∧ windowEPMass T₁ T₂ t ≠ 0}.Infinite ∨
      ∃ F : Finset ℝ, (∀ t ∈ F, t ∈ Ioc 0 h ∧ windowEPMass T₁ T₂ t ≠ 0) ∧
        ∀ Z : Finset ℂ,
          (∀ ρ ∈ Z, xi ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 / 2 + h ∧ ρ.im ∈ Icc T₁ T₂) →
          2 * ∑ ρ ∈ Z, (analyticOrderAt xi ρ).toNat ≤ ∑ t ∈ F, windowEPMass T₁ T₂ t + 2 := by
  classical
  by_cases hinf : {t : ℝ | t ∈ Ioc 0 h ∧ windowEPMass T₁ T₂ t ≠ 0}.Infinite
  · exact Or.inl hinf
  right
  have hfin : {t : ℝ | t ∈ Ioc 0 h ∧ windowEPMass T₁ T₂ t ≠ 0}.Finite := Set.not_infinite.mp hinf
  set F := hfin.toFinset with hF
  refine ⟨F, fun t ht => by rw [hF, Set.Finite.mem_toFinset] at ht; exact ht, fun Z hZ => ?_⟩
  -- `D(0) ≤ D(a)` for a small depth `a`
  obtain ⟨δ₀, hδ₀, h0loc⟩ := exists_local_windowDefectCount (h := 0) hT le_rfl hg₁ hg₂
  set a : ℝ := min (δ₀ / 2) h with ha
  have hapos : 0 < a := lt_min (by linarith) hh
  have hah : a ≤ h := min_le_right _ _
  have h0a : windowDefectCount T₁ T₂ 0 ≤ windowDefectCount T₁ T₂ a :=
    (h0loc a (by rw [sub_zero, abs_of_pos hapos]; linarith [min_le_left (δ₀ / 2) h])).1
  -- `D(a) ≤ D(h) + Σ M`
  have hah' : windowDefectCount T₁ T₂ a ≤
      windowDefectCount T₁ T₂ h + ∑ t ∈ F, windowEPMass T₁ T₂ t := by
    refine le_add_sum_of_local_jumps (M := windowEPMass T₁ T₂) hah F ?_ ?_ ?_
    · intro t ht hM
      rw [hF, Set.Finite.mem_toFinset]
      exact ⟨⟨lt_of_lt_of_le hapos ht.1, ht.2⟩, hM⟩
    · intro t ht
      obtain ⟨δ, hδ, hloc⟩ :=
        exists_local_windowDefectCount hT (lt_of_lt_of_le hapos ht.1).le hg₁ hg₂
      exact ⟨δ, hδ, fun s hs => (hloc s hs).1⟩
    · intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hapos ht.1
      obtain ⟨δ, hδ, hloc⟩ := exists_local_windowDefectCount hT htpos.le hg₁ hg₂
      exact ⟨δ, hδ, fun s hs => (hloc s hs).2 htpos⟩
  -- transport at depth `h`, and the count at depth `0`
  obtain ⟨Zξ, hZξ, hD⟩ := windowDefectCount_le_transport hh hT hg₁ hg₂ hA₁ hA₂
  have hdisj : Disjoint Z Zξ := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    have := ((hZξ ρ).mp h2).2.2
    linarith [(hZ ρ h1).2.2.1]
  have hS : ∀ ρ ∈ Z ∪ Zξ, xi ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.im ∈ Icc T₁ T₂ := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h1 | h1
    · obtain ⟨h0, hre, -, him⟩ := hZ ρ h1
      exact ⟨h0, hre, him⟩
    · obtain ⟨hR, h0, hre⟩ := (hZξ ρ).mp h1
      exact ⟨h0, by linarith, (mem_reProdIm.mp hR).2⟩
  have h1 := two_mul_sum_le_windowDefectCount_zero (T₁ := T₁) (T₂ := T₂) (Z ∪ Zξ) hS
  rw [Finset.sum_union hdisj] at h1
  omega

end

end RHTower
