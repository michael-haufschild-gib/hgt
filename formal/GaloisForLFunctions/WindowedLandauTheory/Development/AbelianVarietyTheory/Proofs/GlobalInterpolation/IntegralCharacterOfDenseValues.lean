import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefficientEmbeddingReflectsContinuity

/-! A continuous rank-one representation of a compact group has an integral
model when its values on a dense set belong to the coefficient field. -/

noncomputable section

open Filter IsLocalRing
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.N
open GlobalTheory.TeichPlace GlobalTheory.LadicPlace

namespace WindowedLandauTheory.NormalizedTypes

private theorem norm_eq_one_of_compact_character {Γ K : Type*} [Group Γ]
    [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (d : Γ →* K) (hd : Continuous d) (g : Γ) : ‖d g‖ = 1 := by
  obtain ⟨M, hM⟩ := (isCompact_range (continuous_norm.comp hd)).bddAbove
  have hle (a : Γ) : ‖d a‖ ≤ 1 := by
    by_contra! ha
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M ha
    have h := hM ⟨a ^ n, rfl⟩
    change ‖d (a ^ n)‖ ≤ M at h
    rw [map_pow, norm_pow] at h
    exact hn.not_ge h
  refine le_antisymm (hle g) ?_
  have h := mul_le_mul_of_nonneg_left (hle g⁻¹) (norm_nonneg (d g))
  simpa only [mul_one, ← norm_mul, ← map_mul, mul_inv_cancel, map_one, norm_one] using h

/-- The image of the coefficient order is compact, by finite generation
over the compact ring of p-adic integers. -/
theorem isClosed_range_iotaOQ (D : D7) (i : D.nd.Loc) :
    IsClosed (Set.range (iotaOQ D.nd D.naut i)) := by
  let p := D.nd.l i
  letI : Fact p.Prime := D.nd.lPrime i
  let j := iotaOQ D.nd D.naut i
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := D.nd.O i)
  let f (c : s → ℤ_[p]) : PadicAlgCl p :=
    ∑ y : s, algebraMap ℚ_[p] (PadicAlgCl p) (c y : ℚ_[p]) * j y
  have hf : Continuous f := by
    refine continuous_finsetSum _ fun y _ => ?_
    exact ((continuous_algebraMap ℚ_[p] (PadicAlgCl p)).comp
      (continuous_subtype_val.comp (continuous_apply y))).mul continuous_const
  have hmap (z : ℤ_[p]) (y : D.nd.O i) :
      j (z • y) = algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]) * j y := by
    rw [Algebra.smul_def, map_mul]
    exact congrArg (· * j y) (D.naut.iotaQ_alg i z)
  have hset : Set.range j = Set.range f := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      have ha : a ∈ Submodule.span ℤ_[p] (s : Set (D.nd.O i)) := hs ▸ Submodule.mem_top
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.mp ha
      refine ⟨fun y => c y, ?_⟩
      rw [map_sum]
      simp only [f, hmap]
      exact Finset.sum_coe_sort s (fun y : D.nd.O i =>
        algebraMap ℚ_[p] (PadicAlgCl p) (c y : ℚ_[p]) * j y)
    · rintro ⟨c, rfl⟩
      refine ⟨∑ y : s, c y • (y : D.nd.O i), ?_⟩
      rw [map_sum]
      simp only [f, hmap]
  change IsClosed (Set.range j)
  rw [hset]
  exact (isCompact_range hf).isClosed

/-- The image of the coefficient order consists of the fraction-field
values of norm at most one. -/
theorem iotaQ_mem_range_iotaOQ_iff (D : D7) (i : D.nd.Loc) (x : Kf D.nd i) :
    D.naut.iotaQ i x ∈ Set.range (iotaOQ D.nd D.naut i) ↔ ‖D.naut.iotaQ i x‖ ≤ 1 := by
  let p := D.nd.l i
  letI : Fact p.Prime := D.nd.lPrime i
  let j := iotaOQ D.nd D.naut i
  obtain ⟨κ, hred⟩ := exists_eq_residue_of_integral_order p j (D.naut.iotaQ_alg i) (D.naut.kFbar i)
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact (mem_padicAlgClIntegers_iff _).mp (hred y).choose
  intro hx
  by_cases hx₀ : x = 0
  · subst x
    exact ⟨0, by simp⟩
  have hι₀ : D.naut.iotaQ i x ≠ 0 := (map_ne_zero (D.naut.iotaQ i)).mpr hx₀
  rcases ValuationRing.isInteger_or_isInteger (D.nd.O i) x with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact ⟨y, congrArg (D.naut.iotaQ i) hy⟩
  obtain ⟨hmem, hredy⟩ := hred y
  have hyj : j y = (D.naut.iotaQ i x)⁻¹ := by
    change D.naut.iotaQ i (algebraMap (D.nd.O i) (Kf D.nd i) y) = _
    rw [hy, map_inv₀]
  have hunit : IsUnit y := by
    by_contra h
    have hymax : y ∈ maximalIdeal (D.nd.O i) := (mem_maximalIdeal y).mpr h
    have hz : residue (D.nd.O i) y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hymax
    rw [hz, map_zero] at hredy
    have hz' := (Ideal.Quotient.eq_zero_iff_mem).mp
      ((κ.injective (hredy.trans (map_zero κ).symm)) :
        residue (padicAlgClIntegers p) ⟨j y, hmem⟩ = 0)
    rw [Valuation.mem_maximalIdeal_iff, ← NNReal.coe_lt_coe, PadicAlgCl.valuation_coe,
      NNReal.coe_one] at hz'
    change ‖j y‖ < 1 at hz'
    rw [hyj, norm_inv] at hz'
    exact (not_lt_of_ge ((one_le_inv₀ (norm_pos_iff.mpr hι₀)).mpr hx)) hz'
  obtain ⟨u, rfl⟩ := hunit
  refine ⟨(↑u⁻¹ : D.nd.O i), ?_⟩
  have e : j (u : D.nd.O i) * j (↑u⁻¹ : D.nd.O i) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  change j (↑u⁻¹ : D.nd.O i) = D.naut.iotaQ i x
  rw [hyj] at e
  exact ((inv_mul_eq_one₀ hι₀).mp e).symm

/-- Dense fraction-field values of a compact rank-one representation
descend to a continuous unit-valued character of the coefficient order. -/
theorem exists_integral_character (D : D7) (i : D.nd.Loc)
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    (d : Γ →* PadicAlgCl (D.nd.l i)) (hd : Continuous d)
    {S : Set Γ} (hS : Dense S) (hval : ∀ s ∈ S, d s ∈ Set.range (D.naut.iotaQ i)) :
    ∃ ξ : Γ →* (D.nd.O i)ˣ, Continuous (fun g => (ξ g : D.nd.O i)) ∧
      ∀ g, iotaOQ D.nd D.naut i (ξ g : D.nd.O i) = d g := by
  let j := iotaOQ D.nd D.naut i
  have hj : Function.Injective j := (D.naut.iotaQ i).injective.comp
    (IsFractionRing.injective (D.nd.O i) (Kf D.nd i))
  have hsub : S ⊆ d ⁻¹' Set.range j := by
    intro s hs
    obtain ⟨x, hx⟩ := hval s hs
    rw [Set.mem_preimage, ← hx]
    apply (iotaQ_mem_range_iotaOQ_iff D i x).mpr
    rw [hx]
    exact (norm_eq_one_of_compact_character d hd s).le
  have hall (g : Γ) : d g ∈ Set.range j :=
    closure_minimal hsub ((isClosed_range_iotaOQ D i).preimage hd) (hS g)
  choose z hz using hall
  let ξ : Γ →* D.nd.O i :=
    { toFun := z
      map_one' := hj (by rw [hz, map_one, map_one])
      map_mul' := fun a b => hj (by rw [hz, map_mul, map_mul, hz, hz]) }
  refine ⟨ξ.toHomUnits, continuous_of_continuous_iotaOQ D i ?_, hz⟩
  change Continuous fun g => j (z g)
  simpa only [hz] using hd

end WindowedLandauTheory.NormalizedTypes
