import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCriterion
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDiscreteEnergy
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The admissible dampings of the Möbius receiver accumulate above the zeros

The damped Möbius receiver `E_T(ε) = Σ_{n ≤ T} A_ε(n)²/(n(n+1))`, with `A_ε` the centred prefix of
`(μ(d) d^{−ε}) ∗ 1`, is a one-parameter family in the damping `ε`. Its admissible parameters are
the dampings with a horizon-uniform budget.

* `receiverDampings`: `{ε > 0 | ∃ B, ∀ T, E_T(ε) ≤ B}`. It contains `[½, ∞)` unconditionally
  (`Ici_half_subset_receiverDampings`), and admissibility is `L²`-admission of the power-damped
  Fermi source (`mem_receiverDampings_iff_memLp`).
* `riemannZeta_sub_eq_zero_of_mem_receiverDampings`: a budget at damping `ε ≤ ½` translates every
  zero of real part in `(½ + ε, 1)` down by `ε`.
* `re_le_of_accPt_receiverDampings`: if the admissible dampings accumulate at `ε₀`, every zero in
  the strip has `Re ρ ≤ ½ + ε₀`. Admissible dampings `ε` near `ε₀` translate a zero of real part
  `> ½ + ε₀` onto zeros `ρ − ε` accumulating at `ρ − ε₀`, where the residue unit `(s − 1)ζ(s)` is
  analytic and not identically zero.
* `riemannHypothesis_of_accPt_zero_receiverDampings`: accumulation at `0` is RH. Accumulation at
  `0` is the cofinal budget hypothesis (`accPt_zero_receiverDampings_iff`), so the cofinal
  criterion `riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget` is the case `ε₀ = 0`.
* `re_le_of_Ioo_subset_receiverDampings`: admissibility on an interval `(a, b)` bounds every zero
  in the strip by `½ + a`.
* `receiverDampingRate`: the infimum of the accumulation points of the admissible dampings. It lies
  in `[zetaZeroAbscissa − ½, ½]` (`zetaZeroAbscissa_le_half_add_receiverDampingRate`,
  `receiverDampingRate_le_half`), and it vanishes iff the admissible dampings accumulate at `0`
  (`receiverDampingRate_eq_zero_iff_accPt_zero`, the derived set being closed), which is RH.

A single admissible damping only translates zeros; it is the accumulation of admissible dampings
that confines them, because a nonzero analytic function has isolated zeros.
-/

open Complex Set Filter Topology MeasureTheory

noncomputable section

namespace RHTower

/-- The admissible dampings: `ε > 0` at which the damped Möbius receiver has a horizon-uniform
budget. -/
def receiverDampings : Set ℝ :=
  {ε : ℝ | 0 < ε ∧ ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B}

theorem receiverDampings_subset_Ioi : receiverDampings ⊆ Ioi 0 := fun _ h => h.1

/-- Admissibility of the damping is `L²`-admission of the power-damped Fermi source. -/
theorem mem_receiverDampings_iff_memLp {ε : ℝ} (hε : 0 < ε) :
    ε ∈ receiverDampings ↔ MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0)) := by
  rw [pmPowerDampedFermiSource_memLp_iff_discrete_budget hε]
  exact ⟨fun h => h.2, fun h => ⟨hε, h⟩⟩

/-- Every damping `ε ≥ ½` is admissible: half damping is the trivial rate of the family. -/
theorem Ici_half_subset_receiverDampings : Ici (1 / 2 : ℝ) ⊆ receiverDampings := fun ε hε =>
  ⟨by linarith [mem_Ici.mp hε],
    exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le (mem_Ici.mp hε)⟩

/-- A budget at damping `ε ≤ ½` translates every zero of real part in `(½ + ε, 1)` down by `ε`. -/
theorem riemannZeta_sub_eq_zero_of_mem_receiverDampings {ε : ℝ} (hε : ε ∈ receiverDampings)
    (hε2 : ε ≤ 1 / 2) {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) : riemannZeta (ρ - (ε : ℂ)) = 0 :=
  pmPowerDamped_zero_translation ε hε.1 hε2 ((mem_receiverDampings_iff_memLp hε.1).mp hε) hρ hρ1
    hzero

/-- The residue unit `(s − 1)ζ(s)` is nonzero on a punctured neighbourhood of every point. -/
theorem eventually_zetaResidueUnit_ne_zero (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, zetaResidueUnit w ≠ 0 :=
  (analyticAt_zetaResidueUnit z).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    fun h => Sieve.zetaResidueUnit_order_ne_top z (analyticOrderAt_eq_top.mpr h)

/-- The left endpoint of an interval inside `S` is an accumulation point of `S`. -/
theorem accPt_of_Ioo_subset {S : Set ℝ} {a b : ℝ} (hab : a < b) (h : Ioo a b ⊆ S) :
    AccPt a (𝓟 S) := by
  refine AccPt.mono ?_ (principal_mono.mpr h)
  rw [accPt_iff_frequently]
  haveI := nhdsGT_neBot a
  have hmem : ∀ᶠ x in 𝓝[>] a, x ≠ a ∧ x ∈ Ioo a b := by
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact ⟨hx.1.ne', hx⟩
  exact hmem.frequently.filter_mono nhdsWithin_le_nhds

/-- Every damping `ε ≥ ½` is an accumulation point of the admissible dampings. -/
theorem accPt_receiverDampings_of_half_le {ε : ℝ} (hε : 1 / 2 ≤ ε) :
    AccPt ε (𝓟 receiverDampings) :=
  accPt_of_Ioo_subset (lt_add_one ε) fun x hx =>
    Ici_half_subset_receiverDampings (mem_Ici.mpr (by linarith [hx.1]))

/-- Accumulation points of the admissible dampings are nonnegative. -/
theorem nonneg_of_accPt_receiverDampings {ε₀ : ℝ} (h : AccPt ε₀ (𝓟 receiverDampings)) :
    0 ≤ ε₀ := by
  by_contra hneg
  obtain ⟨ε, ⟨-, hεS⟩, hlt⟩ :=
    ((accPt_iff_frequently.mp h).and_eventually (eventually_lt_nhds (not_le.mp hneg))).exists
  linarith [hεS.1]

/-- **Accumulating dampings confine the zeros.** If the admissible dampings accumulate at `ε₀`,
every zero of `ζ` in the strip has `Re ρ ≤ ½ + ε₀`. -/
theorem re_le_of_accPt_receiverDampings {ε₀ : ℝ} (h : AccPt ε₀ (𝓟 receiverDampings))
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (hρ1 : ρ.re < 1) : ρ.re ≤ 1 / 2 + ε₀ := by
  by_contra hgt
  have hgt' : 1 / 2 + ε₀ < ρ.re := not_le.mp hgt
  -- the translates `ρ − ε` of admissible `ε` near `ε₀` are zeros accumulating at `ρ − ε₀`
  have htend : Tendsto (fun ε : ℝ => ρ - (ε : ℂ)) (𝓝[≠] ε₀) (𝓝[≠] (ρ - (ε₀ : ℂ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_const.sub Complex.continuous_ofReal).tendsto ε₀).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [mem_compl_singleton_iff] at hε ⊢
      intro heq
      exact hε (by exact_mod_cast (sub_right_inj.mp heq))
  have hne : ∀ᶠ (ε : ℝ) in 𝓝[≠] ε₀, zetaResidueUnit (ρ - (ε : ℂ)) ≠ 0 :=
    htend.eventually (eventually_zetaResidueUnit_ne_zero _)
  have hwin : ∀ᶠ ε in 𝓝[≠] ε₀, ε < ρ.re - 1 / 2 ∧ ε < 1 / 2 :=
    ((eventually_lt_nhds (by linarith)).and (eventually_lt_nhds (by linarith))).filter_mono
      nhdsWithin_le_nhds
  have hfreq : ∃ᶠ ε in 𝓝[≠] ε₀, ε ∈ receiverDampings :=
    frequently_nhdsWithin_iff.mpr ((accPt_iff_frequently.mp h).mono fun _ hε => ⟨hε.2, hε.1⟩)
  obtain ⟨ε, hεS, hεne, hεlt, hεhalf⟩ := (hfreq.and_eventually (hne.and hwin)).exists
  have hz := riemannZeta_sub_eq_zero_of_mem_receiverDampings hεS hεhalf.le (by linarith) hρ1 hzero
  have hne1 : ρ - (ε : ℂ) ≠ 1 := fun h1 => by
    have := congrArg Complex.re h1
    simp only [sub_re, ofReal_re, one_re] at this
    linarith [hεS.1]
  exact hεne (by rw [zetaResidueUnit, Function.update_of_ne hne1, hz, mul_zero])

/-- Admissibility on an interval `(a, b)` bounds every zero in the strip by `½ + a`. -/
theorem re_le_of_Ioo_subset_receiverDampings {a b : ℝ} (hab : a < b)
    (h : Ioo a b ⊆ receiverDampings) {ρ : ℂ} (hzero : riemannZeta ρ = 0) (hρ1 : ρ.re < 1) :
    ρ.re ≤ 1 / 2 + a :=
  re_le_of_accPt_receiverDampings (accPt_of_Ioo_subset hab h) hzero hρ1

/-- Accumulation of the admissible dampings at `0` is the cofinal budget hypothesis. -/
theorem accPt_zero_receiverDampings_iff :
    AccPt (0 : ℝ) (𝓟 receiverDampings) ↔
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
        ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B := by
  rw [accPt_iff_frequently]
  constructor
  · intro h δ hδ
    obtain ⟨ε, ⟨-, hε⟩, hlt⟩ := (h.and_eventually (eventually_lt_nhds hδ)).exists
    exact ⟨ε, hε.1, hlt, hε.2⟩
  · intro h
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨ε, hε0, hεδ, hB⟩ := h δ hδ
    refine ⟨ε, hball ?_, hε0.ne', hε0, hB⟩
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε0]
    exact hεδ

/-- **Accumulation at `0` is RH**: a zero off the line would be confined to the line. -/
theorem riemannHypothesis_of_accPt_zero_receiverDampings
    (h : AccPt (0 : ℝ) (𝓟 receiverDampings)) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hzero, hρ0, hρ1⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  have := re_le_of_accPt_receiverDampings h hzero hρ1
  linarith

/-- Every accumulation point of the admissible dampings bounds the zero abscissa. -/
theorem zetaZeroAbscissa_le_of_accPt_receiverDampings {ε₀ : ℝ}
    (h : AccPt ε₀ (𝓟 receiverDampings)) : zetaZeroAbscissa ≤ 1 / 2 + ε₀ := by
  refine csSup_le zetaZeroReSet_nonempty ?_
  rintro _ ⟨ρ, hzero, rfl⟩
  rcases lt_or_ge ρ.re 1 with hρ1 | hρ1
  · exact re_le_of_accPt_receiverDampings h hzero hρ1
  · exact absurd hzero (riemannZeta_ne_zero_of_one_le_re hρ1)

/-! ### The receiver damping rate -/

/-- The receiver damping rate: the infimum of the accumulation points of the admissible
dampings. -/
def receiverDampingRate : ℝ := sInf (derivedSet receiverDampings)

theorem bddBelow_derivedSet_receiverDampings : BddBelow (derivedSet receiverDampings) :=
  ⟨0, fun _ h => nonneg_of_accPt_receiverDampings (mem_derivedSet.mp h)⟩

theorem half_mem_derivedSet_receiverDampings : (1 / 2 : ℝ) ∈ derivedSet receiverDampings :=
  mem_derivedSet.mpr (accPt_receiverDampings_of_half_le le_rfl)

theorem receiverDampingRate_nonneg : 0 ≤ receiverDampingRate :=
  le_csInf ⟨_, half_mem_derivedSet_receiverDampings⟩ fun _ h =>
    nonneg_of_accPt_receiverDampings (mem_derivedSet.mp h)

/-- The receiver damping rate is at most the trivial rate `½`. -/
theorem receiverDampingRate_le_half : receiverDampingRate ≤ 1 / 2 :=
  csInf_le bddBelow_derivedSet_receiverDampings half_mem_derivedSet_receiverDampings

/-- The receiver damping rate dominates the zero abscissa excess `Θ − ½`. -/
theorem zetaZeroAbscissa_le_half_add_receiverDampingRate :
    zetaZeroAbscissa ≤ 1 / 2 + receiverDampingRate := by
  have h : zetaZeroAbscissa - 1 / 2 ≤ receiverDampingRate :=
    le_csInf ⟨_, half_mem_derivedSet_receiverDampings⟩ fun _ h => by
      linarith [zetaZeroAbscissa_le_of_accPt_receiverDampings (mem_derivedSet.mp h)]
  linarith

/-- The rate vanishes iff the admissible dampings accumulate at `0`: the set of accumulation
points is closed, so its infimum is attained. -/
theorem receiverDampingRate_eq_zero_iff_accPt_zero :
    receiverDampingRate = 0 ↔ AccPt (0 : ℝ) (𝓟 receiverDampings) := by
  constructor
  · intro h
    have hmem : receiverDampingRate ∈ derivedSet receiverDampings :=
      (isClosed_derivedSet receiverDampings).csInf_mem ⟨_, half_mem_derivedSet_receiverDampings⟩
        bddBelow_derivedSet_receiverDampings
    rw [h] at hmem
    exact mem_derivedSet.mp hmem
  · intro h
    exact le_antisymm (csInf_le bddBelow_derivedSet_receiverDampings (mem_derivedSet.mpr h))
      receiverDampingRate_nonneg

/-- A vanishing receiver damping rate is RH. -/
theorem riemannHypothesis_of_receiverDampingRate_eq_zero (h : receiverDampingRate = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_accPt_zero_receiverDampings (receiverDampingRate_eq_zero_iff_accPt_zero.mp h)

/-- The rate vanishes iff receiver budgets exist at dampings tending to `0`: the cofinal criterion
in the language of the rate. -/
theorem receiverDampingRate_eq_zero_iff_cofinal_budget :
    receiverDampingRate = 0 ↔
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
        ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B :=
  receiverDampingRate_eq_zero_iff_accPt_zero.trans accPt_zero_receiverDampings_iff

end RHTower
