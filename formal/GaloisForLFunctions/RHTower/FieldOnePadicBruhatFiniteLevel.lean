import GaloisForLFunctions.RHTower.FieldOnePadicCyclicHaarQuadrature
import GaloisForLFunctions.RHTower.CompactlySupportedLocallyConstantTranslationStabilizer

/-!
# Finite-level control of `p`-adic Bruhat functions

Every compactly supported locally constant function on `ℚ_p` has two finite
depths: a denominator depth containing its full topological support, and a
translation depth under which it is globally invariant.  Together these
depths reduce the entire function, not selected samples, to finite cyclic
harmonic analysis.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Filter Set Topology

variable (p : ℕ) [Fact p.Prime]

/-- Every denominator stage `p⁻ⁿℤ_p` is open. -/
theorem fieldOnePadicDenominatorStage_isOpen (n : ℕ) :
    IsOpen (fieldOnePadicDenominatorStage p n : Set ℚ_[p]) := by
  change IsOpen {x : ℚ_[p] |
    (p : ℚ_[p]) ^ n * x ∈ fieldOnePadicIntegralAddSubgroup p}
  exact (fieldOnePadicIntegralAddSubgroup_isOpen p).preimage
    (continuous_const.mul continuous_id)

/-- One denominator stage contains an arbitrary compact subset of `ℚ_p`. -/
theorem fieldOnePadic_isCompact_exists_commonDenominatorStage
    {K : Set ℚ_[p]} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ fieldOnePadicDenominatorStage p n := by
  let U : ℕ → Set ℚ_[p] := fun n => fieldOnePadicDenominatorStage p n
  have hcover : K ⊆ ⋃ n, U n := by
    intro x _
    obtain ⟨n, hn⟩ := fieldOnePadic_exists_denominatorStage p x
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U
    (fun n => fieldOnePadicDenominatorStage_isOpen p n) hcover
  refine ⟨t.sup id, fun x hx => ?_⟩
  have hxu := ht hx
  rw [Set.mem_iUnion] at hxu
  obtain ⟨n, hxu⟩ := hxu
  rw [Set.mem_iUnion] at hxu
  obtain ⟨hnt, hxn⟩ := hxu
  exact fieldOnePadicDenominatorStage_mono p
    (Finset.le_sup (f := id) hnt) hxn

/-- Every open additive subgroup of `ℚ_p` contains a full prime-power
lattice `p^mℤ_p`. -/
theorem fieldOnePadicOpenAddSubgroup_exists_primePowerLattice
    (V : OpenAddSubgroup ℚ_[p]) :
    ∃ m : ℕ, ∀ z : ℤ_[p],
      (p : ℚ_[p]) ^ m * (z : ℚ_[p]) ∈ V := by
  have hVnhds : (V : Set ℚ_[p]) ∈ 𝓝 (0 : ℚ_[p]) :=
    V.isOpen.mem_nhds (zero_mem V)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hVnhds
  have htendsto : Tendsto (fun m : ℕ => ‖(p : ℚ_[p])‖ ^ m)
      atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (norm_nonneg _) (Padic.norm_p_lt_one (p := p))
  have heventually : ∀ᶠ m : ℕ in atTop, ‖(p : ℚ_[p])‖ ^ m < ε :=
    (tendsto_order.1 htendsto).2 ε hε
  obtain ⟨m, hm⟩ := heventually.exists
  refine ⟨m, fun z => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow]
  exact lt_of_le_of_lt
    (mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) z.property) hm

/-- Every literal `p`-adic Bruhat function admits simultaneous support and
translation depths. -/
theorem fieldOnePadicBruhat_exists_finiteLevel
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    ∃ n m : ℕ,
      tsupport (f.1 : ℚ_[p] → ℂ) ⊆ fieldOnePadicDenominatorStage p n ∧
      ∀ x : ℚ_[p], ∀ z : ℤ_[p],
        f.1 (x + (p : ℚ_[p]) ^ m * (z : ℚ_[p])) = f.1 x := by
  obtain ⟨n, hn⟩ :=
    fieldOnePadic_isCompact_exists_commonDenominatorStage p f.2
  obtain ⟨V, hV⟩ :=
    compactlySupportedLocallyConstant_exists_openAddSubgroup_stabilizer
      ℚ_[p] ℂ f.1 f.1.isLocallyConstant f.2
  obtain ⟨m, hm⟩ :=
    fieldOnePadicOpenAddSubgroup_exists_primePowerLattice p V
  refine ⟨n, m, hn, fun x z => ?_⟩
  exact hV x ⟨(p : ℚ_[p]) ^ m * (z : ℚ_[p]), hm z⟩

end

end GaloisForLFunctions.RHTower
