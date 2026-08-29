import GaloisForLFunctions.HTGeometry.LatticeZeroCounting
import GaloisForLFunctions.HTGeometry.ZeroFreeRadius

/-!
# Finitely many zeros give a logarithmic counting function

A divisor supported on a finite set is a finite sum of point masses, and the counting function of a
point mass is `log r − log ‖u‖`.  Hence an entire function with finitely many zeros has

```text
N(r, 0, f) ≤ M · log r + C
```

with `M` the total zero multiplicity.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real Set Filter ValueDistribution MeromorphicOn Function

/-- **The counting function of a function with finitely many zeros is logarithmic.** -/
theorem exists_logCounting_le_of_finite_zeros {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgo : ∀ z, meromorphicOrderAt g z ≠ ⊤) (hfin : {z : ℂ | g z = 0}.Finite) :
    ∃ M C R₀ : ℝ, 0 ≤ M ∧ 1 ≤ R₀ ∧ ∀ r : ℝ, R₀ ≤ r →
      ValueDistribution.logCounting g 0 r ≤ M * Real.log r + C := by
  classical
  set S : Finset ℂ := hfin.toFinset with hS
  set D : Function.locallyFinsupp ℂ ℤ := (divisor g Set.univ)⁺ with hD
  -- the divisor is supported on the zero set
  have hsupp : ∀ z : ℂ, z ∉ S → D z = 0 := by
    intro z hz
    have hne : g z ≠ 0 := by
      intro hcon
      exact hz (by simp [hS, hfin.mem_toFinset, hcon])
    have h0 : divisor g Set.univ z = 0 :=
      divisor_eq_zero_of_ne_zero hg hgo (Set.mem_univ z) hne
    change max (divisor g Set.univ z) 0 = 0
    rw [h0]
    rfl
  have hDnonneg : ∀ z : ℂ, 0 ≤ D z := fun z => le_max_right _ _
  -- compare with the sum of point masses
  set E : Function.locallyFinsupp ℂ ℤ :=
    ∑ u ∈ S, Function.locallyFinsuppWithin.single u (D u) with hE
  have hDE : D ≤ E := by
    intro z
    have hEz : E z = ∑ u ∈ S, (if z = u then D u else 0) := by
      rw [hE]
      simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
        Function.locallyFinsuppWithin.single_apply]
    rw [hEz]
    by_cases hz : z ∈ S
    · rw [Finset.sum_eq_single z]
      · simp
      · intro b _ hb
        rw [if_neg (fun hcon => hb hcon.symm)]
      · intro hcon
        exact absurd hz hcon
    · rw [hsupp z hz]
      refine Finset.sum_nonneg ?_
      intro u _
      by_cases hzu : z = u
      · rw [if_pos hzu]
        exact hDnonneg u
      · rw [if_neg hzu]
  -- the radius beyond which every point mass contributes its logarithm
  set R₀ : ℝ := max 1 (∑ u ∈ S, ‖u‖) with hR₀
  have hR₀1 : (1 : ℝ) ≤ R₀ := le_max_left _ _
  have hnormle : ∀ u ∈ S, ‖u‖ ≤ R₀ := by
    intro u hu
    refine le_trans ?_ (le_max_right (1 : ℝ) (∑ v ∈ S, ‖v‖))
    exact Finset.single_le_sum (fun v _ => norm_nonneg v) hu
  refine ⟨∑ u ∈ S, (D u : ℝ), -∑ u ∈ S, (D u : ℝ) * Real.log ‖u‖, R₀,
    Finset.sum_nonneg fun u _ => by exact_mod_cast hDnonneg u, hR₀1, ?_⟩
  intro r hr
  have hr1 : (1 : ℝ) ≤ r := le_trans hR₀1 hr
  have hgD : ValueDistribution.logCounting g 0 r
      = Function.locallyFinsuppWithin.logCounting D r := by
    rw [hD]
    simp [ValueDistribution.logCounting]
  have hle := Function.locallyFinsuppWithin.logCounting_le hDE hr1
  have hEval : Function.locallyFinsuppWithin.logCounting E r
      = ∑ u ∈ S, (D u : ℝ) * (Real.log r - Real.log ‖u‖) := by
    rw [hE, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro u hu
    exact Function.locallyFinsuppWithin.logCounting_single_eq_log_sub_const
      (le_trans (hnormle u hu) hr)
  rw [hgD]
  refine le_trans hle ?_
  rw [hEval]
  have hsplit : ∑ u ∈ S, (D u : ℝ) * (Real.log r - Real.log ‖u‖)
      = (∑ u ∈ S, (D u : ℝ)) * Real.log r - ∑ u ∈ S, (D u : ℝ) * Real.log ‖u‖ := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro u _
    ring
  rw [hsplit]
  ring_nf
  rfl

end GaloisForLFunctions.HTGeometry
