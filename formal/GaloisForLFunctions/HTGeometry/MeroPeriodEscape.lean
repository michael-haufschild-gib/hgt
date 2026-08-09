import GaloisForLFunctions.HTGeometry.MeroPeriodQuotient
import GaloisForLFunctions.HTGeometry.ClosedSubgroupIdentityComponent

/-!
# The period group of a hypertranscendental meromorphic germ is an escape subgroup

For a global meromorphic germ `x = A / B` the translation identity `x(· + h) = x` cross-multiplies
to the pointwise identity `A(z + h) B(z) = A(z) B(z + h)`, so the period group is an intersection of
closed conditions and is closed.  If it contained a whole real line, the entire function `A - c B`
would vanish along that line for the value `c` of `x` at a regular point, hence vanish identically,
and then *every* complex number would be a period — in particular two `ℝ`-independent ones, making
the germ differentially algebraic.

* **`mem_meroPeriodSubgroup_iff`** — the pointwise cross-multiplied criterion;
* **`isClosed_meroPeriodSubgroup`**;
* **`lineSubmodule_meroPeriodSubgroup_eq_bot`** — a hypertranscendental germ has no line of periods;
* **`isEscapeSubgroup_meroPeriodSubgroup`** — its period group satisfies all three period-escape
  conditions.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance meroEscapeDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meroEscapeDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance meroEscapeRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

/-! ## The pointwise criterion -/

/-- **Cross-multiplied period criterion.**  A complex number is a period of `A / B` exactly when the
translated numerator and denominator cross-multiply identically. -/
theorem mem_meroPeriodSubgroup_iff
    {a b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0)
    {A B : ℂ → ℂ}
    (hAa : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) A = (a : Germ (𝓟 Set.univ) ℂ))
    (hBb : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) B = (b : Germ (𝓟 Set.univ) ℂ))
    (h : ℂ) :
    h ∈ meroPeriodSubgroup
        (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
          algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b) ↔
      ∀ z : ℂ, A (z + h) * B z = A z * B (z + h) := by
  have hinj : Function.Injective
      (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)) :=
    IsFractionRing.injective _ _
  have hb0 : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b ≠ 0 := by
    simpa [map_eq_zero_iff _ hinj] using hb
  have hσb : addTranslationAnalyticEquiv h b ≠ 0 := by
    intro hz
    apply hb
    have := congrArg (addTranslationAnalyticEquiv h).symm hz
    rwa [RingEquiv.symm_apply_apply, map_zero] at this
  have hσb0 : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (addTranslationAnalyticEquiv h b) ≠ 0 := by
    simpa [map_eq_zero_iff _ hinj] using hσb
  have hL : ((addTranslationAnalyticEquiv h a * b : analyticSubring (Set.univ : Set ℂ)) :
      Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
      = Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (fun z => A (z + h) * B z) := by
    rw [show ((addTranslationAnalyticEquiv h a * b : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
        = ((addTranslationAnalyticEquiv h a : analyticSubring (Set.univ : Set ℂ)) :
            Germ (𝓟 (Set.univ : Set ℂ)) ℂ) * (b : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) from rfl,
      ← addTranslationAnalyticEquiv_rep h hAa, ← hBb, ← map_mul]
    rfl
  have hR : ((a * addTranslationAnalyticEquiv h b : analyticSubring (Set.univ : Set ℂ)) :
      Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
      = Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (fun z => A z * B (z + h)) := by
    rw [show ((a * addTranslationAnalyticEquiv h b : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
        = (a : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) *
          ((addTranslationAnalyticEquiv h b : analyticSubring (Set.univ : Set ℂ)) :
            Germ (𝓟 (Set.univ : Set ℂ)) ℂ) from rfl,
      ← addTranslationAnalyticEquiv_rep h hBb, ← hAa, ← map_mul]
    rfl
  rw [mem_meroPeriodSubgroup, map_div₀, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap, div_eq_div_iff hσb0 hb0, ← map_mul, ← map_mul,
    hinj.eq_iff, Subtype.ext_iff, hL, hR]
  change (↑(fun z => A (z + h) * B z) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
      = ↑(fun z => A z * B (z + h)) ↔ _
  rw [Germ.coe_eq, EventuallyEq, eventually_principal]
  exact ⟨fun hz z => hz z (Set.mem_univ z), fun hz z _ => hz z⟩

/-! ## Closedness -/

/-- **The period group of a global meromorphic germ is closed.**  It is the intersection, over all
evaluation points, of the closed conditions of the cross-multiplied criterion. -/
theorem isClosed_meroPeriodSubgroup (x : meroField (Set.univ : Set ℂ)) :
    IsClosed ((meroPeriodSubgroup x : Set ℂ)) := by
  obtain ⟨a, b, hbmem, rfl⟩ := IsFractionRing.div_surjective (analyticSubring Set.univ) x
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  obtain ⟨A, hA, hAa⟩ := a.2
  obtain ⟨B, hB, hBb⟩ := b.2
  have hAcont : Continuous A := continuousOn_univ.mp hA.continuousOn
  have hBcont : Continuous B := continuousOn_univ.mp hB.continuousOn
  have hset : (meroPeriodSubgroup
      (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b) : Set ℂ)
      = ⋂ z : ℂ, {h : ℂ | A (z + h) * B z = A z * B (z + h)} := by
    ext h
    simp only [SetLike.mem_coe, mem_meroPeriodSubgroup_iff hb hAa hBb, Set.mem_iInter,
      Set.mem_setOf_eq]
  rw [hset]
  refine isClosed_iInter fun z => ?_
  have hc1 : Continuous fun h : ℂ => A (z + h) * B z :=
    (hAcont.comp (continuous_const.add continuous_id)).mul continuous_const
  have hc2 : Continuous fun h : ℂ => A z * B (z + h) :=
    continuous_const.mul (hBcont.comp (continuous_const.add continuous_id))
  exact isClosed_eq hc1 hc2

/-! ## No line of periods -/

/-- `1` and `i` are `ℝ`-independent. -/
theorem linearIndependent_one_I : LinearIndependent ℝ ![(1 : ℂ), Complex.I] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
  simp only [Complex.real_smul, mul_one] at hst
  have hre := congrArg Complex.re hst
  have him := congrArg Complex.im hst
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.zero_re, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.zero_im] at hre him
  constructor <;> linarith

/-- **A hypertranscendental germ has no real line of periods.**  A line of periods forces the germ
to be a constant ratio, hence every complex number to be a period, hence two `ℝ`-independent
periods and differential algebraicity. -/
theorem lineSubmodule_meroPeriodSubgroup_eq_bot
    {x : meroField (Set.univ : Set ℂ)} (hx : HypertranscendentalOver (RatFunc ℂ) x) :
    lineSubmodule (meroPeriodSubgroup x) = ⊥ := by
  refine Submodule.eq_bot_iff _ |>.mpr fun v hv => ?_
  by_contra hv0
  obtain ⟨a, b, hbmem, rfl⟩ := IsFractionRing.div_surjective (analyticSubring Set.univ) x
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  obtain ⟨A, hA, hAa⟩ := a.2
  obtain ⟨B, hB, hBb⟩ := b.2
  -- a regular point of the denominator
  have hBne : ∃ z₀ : ℂ, B z₀ ≠ 0 := by
    by_contra hcon
    apply hb
    have hBz : B = 0 := by
      funext z
      by_contra hz
      exact hcon ⟨z, hz⟩
    have : (b : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = 0 := by
      rw [← hBb, hBz]
      exact map_zero _
    exact Subtype.ext this
  obtain ⟨z₀, hz₀⟩ := hBne
  set c : ℂ := A z₀ / B z₀ with hc
  set G : ℂ → ℂ := fun w => A w - c * B w with hG
  have hGanal : AnalyticOnNhd ℂ G (Set.univ : Set ℂ) := hA.sub (analyticOnNhd_const.mul hB)
  -- the line of periods makes `G` vanish along the line
  have hline : ∀ t : ℝ, G (z₀ + (t : ℂ) * v) = 0 := by
    intro t
    have hmem : (t : ℝ) • v ∈ meroPeriodSubgroup
        (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
          algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b) :=
      (mem_lineSubmodule.mp hv) t
    have hpt := (mem_meroPeriodSubgroup_iff hb hAa hBb ((t : ℝ) • v)).mp hmem z₀
    have hsmul : ((t : ℝ) • v) = (t : ℂ) * v := by
      rw [Complex.real_smul]
    rw [hsmul] at hpt
    show A (z₀ + (t : ℂ) * v) - c * B (z₀ + (t : ℂ) * v) = 0
    rw [hc, sub_eq_zero, div_mul_eq_mul_div, eq_div_iff hz₀]
    exact hpt
  -- the identity theorem
  have hfreq : ∃ᶠ w in 𝓝[≠] z₀, G w = 0 := by
    have hcontmap : Tendsto (fun t : ℝ => z₀ + (t : ℂ) * v) (𝓝[≠] (0 : ℝ)) (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hcont : Continuous fun t : ℝ => z₀ + (t : ℂ) * v := by fun_prop
        have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
        intro hcon
        have : (t : ℂ) * v = 0 := by
          have := hcon
          linear_combination this
        rcases mul_eq_zero.mp this with h1 | h1
        · exact ht (by exact_mod_cast h1)
        · exact hv0 h1
    exact hcontmap.frequently (Frequently.of_forall hline)
  have hzero : Set.EqOn G 0 (Set.univ : Set ℂ) :=
    hGanal.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ z₀) hfreq
  have hAB : ∀ w : ℂ, A w = c * B w := by
    intro w
    have := hzero (Set.mem_univ w)
    simp only [hG, Pi.zero_apply, sub_eq_zero] at this
    exact this
  -- every complex number is then a period
  have hall : ∀ h : ℂ, h ∈ meroPeriodSubgroup
      (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b) := by
    intro h
    refine (mem_meroPeriodSubgroup_iff hb hAa hBb h).mpr fun z => ?_
    rw [hAB (z + h), hAB z]
    ring
  exact hx (differentialAlgebraicOver_of_translation_fixed linearIndependent_one_I
    (hall 1) (hall Complex.I))

/-! ## The escape property -/

/-- **The period group of a hypertranscendental global meromorphic germ is an escape subgroup.**
It is closed, its identity component is the trivial complex subspace, and its quotient is
noncompact. -/
theorem isEscapeSubgroup_meroPeriodSubgroup
    {x : meroField (Set.univ : Set ℂ)} (hx : HypertranscendentalOver (RatFunc ℂ) x) :
    IsEscapeSubgroup (meroPeriodSubgroup x) := by
  refine isEscapeSubgroup_of_isClosed (isClosed_meroPeriodSubgroup x) ?_
    (not_compactSpace_quotient_meroPeriodSubgroup hx)
  intro v hv
  rw [lineSubmodule_meroPeriodSubgroup_eq_bot hx] at hv ⊢
  rw [Submodule.mem_bot] at hv ⊢
  rw [hv]
  simp

end

end GaloisForLFunctions.HTGeometry
