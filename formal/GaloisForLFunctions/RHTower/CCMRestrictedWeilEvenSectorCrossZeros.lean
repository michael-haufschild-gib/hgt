import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundParityCrossing

/-!
# Even-sector polar Weil ground states with transform zeros on `ℝ ∪ iℝ`

Fix a positive aperture `a`.  Restrict the CCM restricted Weil form `Q` to the closed subspace of
reflection-even polar vectors and let `μᵉ_a` be its ground energy (`evenGroundEnergy`).  An even
ground state is an even polar vector with `Q(u) = μᵉ_a ‖J u‖²`.

**Theorem** (`exists_crossRooted_evenGround`).  At every aperture `μᵉ_a` is attained, and some
nonzero even ground state has a transform `f̂_u` all of whose zeros other than the polar points
`w_{±1/2}` lie on the real or on the imaginary axis.  No simplicity of any ground level and no
ordering between the even and the odd ground energies is assumed.

**Proof.**
* Reflection acts on transforms by `w ↦ −w` on all of `ℂ` (`unitaryLaplace_reflection`), so the
  zeros of an even transform are symmetric under `w ↦ −w`.
* Attainment (`exists_evenGround`): normalized even near-minimizers have bounded form norm; the
  compact embedding `J` gives a limit, which is polar, even (reflection is continuous and `J` is
  injective) and lies in every sublevel set.
* Even division (`exists_evenGround_div`): at a zero `z` with `Im(z²) ≠ 0`, divide twice to get
  `v` with `f̂_v = f̂_u/((w − z)(w + z))`; `v` is even and polar.  With `c = z²`, on `ℝ`
  `|f̂_u|² = |(t² − Re c) f̂_v|² + (Im c)² |f̂_v|²`.  Both pieces are even polar vectors, so
  `Q − μᵉ_a ‖J ·‖² ≥ 0` splits additively and `v` is an even ground state.
* The even ground states form a finite-dimensional subspace (parallelogram law for `Q`, and the
  antilipschitz compact embedding).  If every nonzero even ground state had a zero off the two
  axes and off `w_{±1/2}`, iterated even division would produce linearly independent ground states
  `f̂₀/∏_{l<k}(t² − z_l²)` for every `k`.

Since the completed zeta function does not vanish on the imaginary axis of the strip, real-rooted
and imaginary-rooted zeros play the same role in a Hurwitz limit argument towards `Ξ`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct Real

namespace RHTower.CCMEvenSector

open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open RHTower.CCMRealRootedGround RHTower.CCMGroundStructure

variable (a : SuzukiPositiveAperture)

/-! ## Reflection on time functions and transforms -/

theorem timeRep_reflection_ae (u : CCMArchimedeanFormDomain a) :
    timeRep a (ccmArchimedeanFormReflection a u) =ᵐ[volume] fun x => timeRep a u (-x) := by
  have h3 : (((ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u) :
      suzukiApertureHilbert a) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) :
        ℝ → ℂ) (-x) := by
    rw [ccmArchimedeanFormToAperture_reflection]
    exact l2Reflection_ae _
  filter_upwards [h3] with x hx
  unfold timeRep
  by_cases hm : x ∈ centralInterval a.1
  · have hm' : -x ∈ centralInterval a.1 := by
      unfold centralInterval at hm ⊢
      simp only [mem_Icc] at hm ⊢
      constructor <;> linarith [hm.1, hm.2]
    rw [indicator_of_mem hm, indicator_of_mem hm', hx]
  · have hm' : -x ∉ centralInterval a.1 := by
      unfold centralInterval at hm ⊢
      simp only [mem_Icc, not_and_or, not_le] at hm ⊢
      rcases hm with h | h
      · right; linarith
      · left; linarith
    rw [indicator_of_notMem hm, indicator_of_notMem hm']

/-- Reflection acts on transforms by `w ↦ −w` on all of `ℂ`. -/
theorem unitaryLaplace_reflection (u : CCMArchimedeanFormDomain a) (w : ℂ) :
    unitaryLaplace (timeRep a (ccmArchimedeanFormReflection a u)) w =
      unitaryLaplace (timeRep a u) (-w) := by
  unfold unitaryLaplace
  rw [integral_congr_ae ((timeRep_reflection_ae a u).mono fun x hx => by rw [hx])]
  rw [← integral_neg_eq_self (fun x : ℝ => cexp (-(2 * π * I * (-w) * x)) * timeRep a u x)
    volume]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ofReal_neg]
  ring_nf

/-! ## Even vectors -/

/-- A reflection-even form-domain vector. -/
def IsEven (u : CCMArchimedeanFormDomain a) : Prop := ccmArchimedeanFormReflection a u = u

theorem IsEven.transform_neg {u : CCMArchimedeanFormDomain a} (hu : IsEven a u) (w : ℂ) :
    unitaryLaplace (timeRep a u) (-w) = unitaryLaplace (timeRep a u) w := by
  rw [← unitaryLaplace_reflection, hu]

theorem isEven_of_transform {u : CCMArchimedeanFormDomain a}
    (h : ∀ t : ℝ, unitaryLaplace (timeRep a u) (-(t : ℂ)) = unitaryLaplace (timeRep a u) t) :
    IsEven a u := by
  refine eq_of_transform_eq a fun t => ?_
  rw [unitaryLaplace_reflection, h]

theorem isEven_zero : IsEven a 0 := map_zero _

theorem IsEven.add {u v : CCMArchimedeanFormDomain a} (hu : IsEven a u) (hv : IsEven a v) :
    IsEven a (u + v) := by
  unfold IsEven at *
  rw [map_add, hu, hv]

theorem IsEven.smul {u : CCMArchimedeanFormDomain a} (hu : IsEven a u) (c : ℂ) :
    IsEven a (c • u) := by
  unfold IsEven at *
  rw [map_smul, hu]

theorem IsEven.sub {u v : CCMArchimedeanFormDomain a} (hu : IsEven a u) (hv : IsEven a v) :
    IsEven a (u - v) := by
  unfold IsEven at *
  rw [map_sub, hu, hv]

/-- A nonzero even polar vector exists at every aperture. -/
theorem exists_even_polar_ne_zero :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧ IsEven a u ∧
      ccmArchimedeanFormToAperture a u ≠ 0 := by
  set g := polarCorrectedSource (polarCenterBump a) with hgdef
  set u := g.toCCMFormVector with hudef
  have hpol : IsPolarConstrained a u := isPolarConstrained_polarCorrectedSource _
  refine ⟨ccmRestrictedWeilEvenPart a u, hpol.evenPart,
    ccmArchimedeanFormReflection_evenPart a u, ?_⟩
  intro hJ
  have he0 : ccmRestrictedWeilEvenPart a u = 0 :=
    ccmArchimedeanFormToAperture_injective a (by rw [hJ, map_zero])
  have hRu : ccmArchimedeanFormReflection a u = -u := by
    have h1 := ccmRestrictedWeilEvenPart_sub_oddPart a u
    have h2 := ccmRestrictedWeilEvenPart_add_oddPart a u
    rw [he0, zero_sub] at h1
    rw [he0, zero_add] at h2
    rw [← h1, h2]
  have hcoe := g.toCCMFormVector_physical_coeFn
  have hrefl : (((ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u) :
      suzukiApertureHilbert a) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) :
        ℝ → ℂ) (-x) := by
    rw [ccmArchimedeanFormToAperture_reflection]
    exact l2Reflection_ae _
  have hneg : (((ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u) :
      suzukiApertureHilbert a) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => -(((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) :
        ℝ → ℂ) x := by
    rw [hRu, map_neg]
    exact Lp.coeFn_neg _
  have hcomp := hcoe.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hae : (fun x : ℝ => g (-x)) =ᵐ[volume] fun x => -g x := by
    filter_upwards [hrefl, hneg, hcomp, hcoe] with x h1 h2 h3 h4
    simp only [Function.comp_apply] at h3
    rw [← h3, ← h1, h2, h4]
  have hfun := (Continuous.ae_eq_iff_eq volume (g.continuous.comp continuous_neg)
    g.continuous.neg).mp hae
  have h0 := congrFun hfun 0
  simp only [Function.comp_apply, neg_zero] at h0
  have hg0 : g 0 = 1 := polarCorrectedSource_polarCenterBump_zero a
  norm_num [hg0] at h0

/-! ## The even polar ground energy -/

/-- Rayleigh quotients of nonzero even polar vectors. -/
def evenRayleighSet : Set ℝ :=
  {r | ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧ IsEven a u ∧
    ccmArchimedeanFormToAperture a u ≠ 0 ∧
    r = ccmRestrictedWeilSourceQuadratic a u / ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ)}

/-- The even polar ground energy `μᵉ_a`. -/
def evenGroundEnergy : ℝ := sInf (evenRayleighSet a)

theorem evenRayleighSet_nonempty : (evenRayleighSet a).Nonempty := by
  obtain ⟨u, hp, he, hne⟩ := exists_even_polar_ne_zero a
  exact ⟨_, u, hp, he, hne, rfl⟩

theorem evenRayleighSet_bddBelow : BddBelow (evenRayleighSet a) :=
  ⟨_, fun _ ⟨u, hp, _, hne, hr⟩ =>
    ccmRestrictedWeilGroundEnergy_mem_lowerBounds a ⟨u, hp, hne, hr⟩⟩

/-- **The even Rayleigh floor.** -/
theorem evenGroundEnergy_mul_le (v : CCMArchimedeanFormDomain a) (hv : IsPolarConstrained a v)
    (he : IsEven a v) :
    evenGroundEnergy a * ‖ccmArchimedeanFormToAperture a v‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a v := by
  by_cases hJ : ccmArchimedeanFormToAperture a v = 0
  · have hv0 : v = 0 := ccmArchimedeanFormToAperture_injective a (by rw [hJ, map_zero])
    rw [hJ, norm_zero, hv0, source_zero]
    simp
  · have hpos : 0 < ‖ccmArchimedeanFormToAperture a v‖ ^ 2 := by
      have := norm_pos_iff.mpr hJ; positivity
    have hle := csInf_le (evenRayleighSet_bddBelow a) (⟨v, hv, he, hJ, rfl⟩ :
      ccmRestrictedWeilSourceQuadratic a v / ‖ccmArchimedeanFormToAperture a v‖ ^ (2 : ℕ) ∈
        evenRayleighSet a)
    rw [le_div_iff₀ hpos] at hle
    exact hle

/-- Normalized even polar near-minimizers. -/
theorem exists_even_normalized_near_min {ε : ℝ} (hε : 0 < ε) :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧ IsEven a u ∧
      ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧
      ccmRestrictedWeilSourceQuadratic a u < evenGroundEnergy a + ε := by
  obtain ⟨r, ⟨v, hv, hev, hne, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (evenRayleighSet_nonempty a)
    (show sInf (evenRayleighSet a) < evenGroundEnergy a + ε by
      unfold evenGroundEnergy; linarith)
  have hr0 : 0 < ‖ccmArchimedeanFormToAperture a v‖ := norm_pos_iff.mpr hne
  refine ⟨((‖ccmArchimedeanFormToAperture a v‖ : ℂ)⁻¹) • v, hv.smul _, hev.smul a _, ?_, ?_⟩
  · rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact inv_mul_cancel₀ hr0.ne'
  · rw [ccmRestrictedWeilSourceQuadratic_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, inv_pow]
    have hpos : 0 < ‖ccmArchimedeanFormToAperture a v‖ ^ (2 : ℕ) := pow_pos hr0 2
    rw [inv_mul_lt_iff₀ hpos]
    have := hr
    rw [div_lt_iff₀ hpos] at this
    linarith

/-- **Attainment of the even polar ground energy.** -/
theorem exists_evenGround :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧ IsEven a u ∧
      ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧
      ccmRestrictedWeilSourceQuadratic a u = evenGroundEnergy a := by
  have hseq : ∀ n : ℕ, ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      IsEven a u ∧ ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧
      ccmRestrictedWeilSourceQuadratic a u < evenGroundEnergy a + 1 / ((n : ℝ) + 1) :=
    fun n => exists_even_normalized_near_min a (by positivity)
  choose u huc hue hun huQ using hseq
  set μ := evenGroundEnergy a with hμ
  let radius := Real.sqrt (max 0 (μ + 1 + ‖ccmRestrictedWeilBoundedRemainder a‖))
  have hbound : ∀ n, ‖u n‖ ≤ radius := by
    intro n
    have hb := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass a (u n)
    rw [hun n] at hb
    simp only [one_pow, mul_one] at hb
    have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsq : ‖(u n).1‖ ^ (2 : ℕ) ≤ max 0 (μ + 1 + ‖ccmRestrictedWeilBoundedRemainder a‖) :=
      hb.trans (le_max_of_le_right (by linarith [huQ n]))
    have hnonneg : 0 ≤ max 0 (μ + 1 + ‖ccmRestrictedWeilBoundedRemainder a‖) := le_max_left _ _
    have hsqrt : 0 ≤ radius := Real.sqrt_nonneg _
    change ‖(u n).1‖ ≤ radius
    nlinarith [Real.sq_sqrt hnonneg, norm_nonneg (u n).1, hsqrt]
  have hmem : ∀ n, ccmArchimedeanFormToAperture a (u n) ∈
      closure (ccmArchimedeanFormToAperture a '' Metric.closedBall
        (0 : CCMArchimedeanFormDomain a) radius) := by
    intro n
    apply subset_closure
    refine ⟨u n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbound n
  obtain ⟨fstar, -, phi, hphi, hconv⟩ :=
    (isCompactOperator_ccmArchimedeanFormToAperture a
      |>.isCompact_closure_image_closedBall radius).tendsto_subseq hmem
  have hnorm : ‖fstar‖ = 1 := by
    have h1 : Tendsto (fun n => ‖ccmArchimedeanFormToAperture a (u (phi n))‖) atTop
        (𝓝 ‖fstar‖) := (continuous_norm.tendsto fstar).comp hconv
    have h2 : Tendsto (fun n => ‖ccmArchimedeanFormToAperture a (u (phi n))‖) atTop (𝓝 1) := by
      simp only [hun]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hlimc : ∀ s : ℝ, (∀ k, inner ℂ (ccmPolarApertureVector a s)
      (ccmArchimedeanFormToAperture a (u k)) = 0) →
      inner ℂ (ccmPolarApertureVector a s) fstar = 0 := by
    intro s hs
    have h1 : Tendsto (fun n => inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (u (phi n)))) atTop
        (𝓝 (inner ℂ (ccmPolarApertureVector a s) fstar)) :=
      (continuous_const.inner continuous_id).tendsto fstar |>.comp hconv
    have h2 : Tendsto (fun n => inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (u (phi n)))) atTop (𝓝 0) := by
      simp only [hs]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- the limit is reflection-fixed in the aperture Hilbert space
  have hlimR : l2Reflection (fstar : SoninL2) = (fstar : SoninL2) := by
    have hc : Continuous fun f : suzukiApertureHilbert a => (f : SoninL2) := continuous_subtype_val
    have h1 : Tendsto (fun n => l2Reflection
        ((ccmArchimedeanFormToAperture a (u (phi n)) : suzukiApertureHilbert a) : SoninL2))
        atTop (𝓝 (l2Reflection (fstar : SoninL2))) :=
      (l2Reflection.continuous.tendsto _).comp ((hc.tendsto fstar).comp hconv)
    have h2 : Tendsto (fun n => l2Reflection
        ((ccmArchimedeanFormToAperture a (u (phi n)) : suzukiApertureHilbert a) : SoninL2))
        atTop (𝓝 (fstar : SoninL2)) := by
      have heq : ∀ n, l2Reflection
          ((ccmArchimedeanFormToAperture a (u (phi n)) : suzukiApertureHilbert a) : SoninL2) =
          ((ccmArchimedeanFormToAperture a (u (phi n)) : suzukiApertureHilbert a) : SoninL2) :=
        fun n => by
          rw [← ccmArchimedeanFormToAperture_reflection, hue (phi n)]
      simp only [heq]
      exact (hc.tendsto fstar).comp hconv
    exact tendsto_nhds_unique h1 h2
  have hlevel : ∀ k : ℕ, ∃ w : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormToAperture a w = fstar ∧
        ccmRestrictedWeilSourceQuadratic a w ≤ μ + 1 / ((k : ℝ) + 1) := by
    intro k
    refine (isClosed_ccmRestrictedWeilSource_sublevel a (μ + 1 / ((k : ℝ) + 1))).mem_of_tendsto
      hconv ?_
    rw [Filter.eventually_atTop]
    refine ⟨k, fun n hn => ⟨u (phi n), rfl, ?_⟩⟩
    have hφ : (k : ℝ) ≤ (phi n : ℝ) := by
      exact_mod_cast hn.trans (hphi.id_le n)
    have h1 : 1 / ((phi n : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith [huQ (phi n)]
  obtain ⟨w, hwJ, -⟩ := hlevel 0
  have hwQ : ccmRestrictedWeilSourceQuadratic a w ≤ μ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨w', hw'J, hw'Q⟩ := hlevel k
    have hww : w' = w := ccmArchimedeanFormToAperture_injective a (by rw [hw'J, hwJ])
    rw [hww] at hw'Q
    linarith
  have hwc : IsPolarConstrained a w := by
    unfold IsPolarConstrained
    rw [hwJ]
    exact ⟨hlimc _ fun k => (huc k).1, hlimc _ fun k => (huc k).2⟩
  have hwe : IsEven a w := by
    apply ccmArchimedeanFormToAperture_injective a
    apply Subtype.ext
    rw [ccmArchimedeanFormToAperture_reflection, hwJ, hlimR]
  have hwn : ‖ccmArchimedeanFormToAperture a w‖ = 1 := by rw [hwJ, hnorm]
  refine ⟨w, hwc, hwe, hwn, le_antisymm hwQ ?_⟩
  have := evenGroundEnergy_mul_le a w hwc hwe
  rw [hwn, one_pow, mul_one] at this
  exact this

/-! ## Even ground states -/

/-- An even ground state: even, polar, with Rayleigh value the even ground energy. -/
def IsEvenGround (u : CCMArchimedeanFormDomain a) : Prop :=
  IsPolarConstrained a u ∧ IsEven a u ∧ ccmRestrictedWeilSourceQuadratic a u =
    evenGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2

theorem isEvenGround_smul {v : CCMArchimedeanFormDomain a} (hv : IsEvenGround a v) (c : ℂ) :
    IsEvenGround a (c • v) := by
  refine ⟨hv.1.smul c, hv.2.1.smul a c, ?_⟩
  rw [ccmRestrictedWeilSourceQuadratic_smul, hv.2.2, map_smul, norm_smul]
  ring

theorem isEvenGround_add {v w : CCMArchimedeanFormDomain a} (hv : IsEvenGround a v)
    (hw : IsEvenGround a w) : IsEvenGround a (v + w) := by
  have hpa : IsPolarConstrained a (v + w) := (ccmPolarConstraintSubmodule a).add_mem hv.1 hw.1
  have hps : IsPolarConstrained a (v - w) := (ccmPolarConstraintSubmodule a).sub_mem hv.1 hw.1
  have hpar := ccmRestrictedWeilSourceQuadratic_parallelogram a v w
  have hnpar := parallelogram_law_with_norm ℂ (ccmArchimedeanFormToAperture a v)
    (ccmArchimedeanFormToAperture a w)
  rw [← map_add, ← map_sub] at hnpar
  have hs := evenGroundEnergy_mul_le a (v + w) hpa (hv.2.1.add a hw.2.1)
  have hd := evenGroundEnergy_mul_le a (v - w) hps (hv.2.1.sub a hw.2.1)
  refine ⟨hpa, hv.2.1.add a hw.2.1, ?_⟩
  have key : evenGroundEnergy a * ‖ccmArchimedeanFormToAperture a (v + w)‖ ^ 2 +
      evenGroundEnergy a * ‖ccmArchimedeanFormToAperture a (v - w)‖ ^ 2 =
      2 * (evenGroundEnergy a * ‖ccmArchimedeanFormToAperture a v‖ ^ 2) +
        2 * (evenGroundEnergy a * ‖ccmArchimedeanFormToAperture a w‖ ^ 2) := by
    linear_combination evenGroundEnergy a * hnpar
  linarith [hv.2.2, hw.2.2]

theorem isEvenGround_zero : IsEvenGround a 0 :=
  ⟨isPolarConstrained_zero a, isEven_zero a, by rw [source_zero, map_zero, norm_zero]; ring⟩

/-- The even ground states form a subspace of the form domain. -/
def evenGroundSubmodule : Submodule ℂ (CCMArchimedeanFormDomain a) where
  carrier := {u | IsEvenGround a u}
  add_mem' := fun hv hw => isEvenGround_add a hv hw
  zero_mem' := isEvenGround_zero a
  smul_mem' := fun c _ hv => isEvenGround_smul a hv c

theorem isClosed_evenGroundSubmodule :
    IsClosed (evenGroundSubmodule a : Set (CCMArchimedeanFormDomain a)) := by
  set J := ccmArchimedeanFormToAperture a
  have hset : (evenGroundSubmodule a : Set (CCMArchimedeanFormDomain a)) =
      (({u | inner ℂ (ccmPolarApertureVector a (1 / 2)) (J u) = 0} ∩
        {u | inner ℂ (ccmPolarApertureVector a (-1 / 2)) (J u) = 0}) ∩
        {u | ccmArchimedeanFormReflection a u = u}) ∩
        {u | (ccmRestrictedWeilForm a u u).re - evenGroundEnergy a * ‖J u‖ ^ 2 = 0} := by
    ext u
    simp only [SetLike.mem_coe, evenGroundSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, mem_setOf_eq, IsEvenGround, IsPolarConstrained, IsEven,
      mem_inter_iff, ccmRestrictedWeilForm_self_re_eq_source, sub_eq_zero, J, and_assoc]
  rw [hset]
  have hJ : Continuous J := J.continuous
  have hform : Continuous fun u : CCMArchimedeanFormDomain a => ccmRestrictedWeilForm a u u := by
    unfold ccmRestrictedWeilForm
    exact (continuous_id.inner continuous_id).add
      (((ccmRestrictedWeilBoundedRemainder a).continuous.comp hJ).inner hJ)
  refine (((isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_const)).inter
    (isClosed_eq (ccmArchimedeanFormReflection a).continuous continuous_id)).inter
    (isClosed_eq ?_ continuous_const)
  · exact continuous_const.inner hJ
  · exact continuous_const.inner hJ
  · exact (Complex.continuous_re.comp hform).sub (continuous_const.mul (hJ.norm.pow 2))

/-- **The even ground level has finite multiplicity.** -/
theorem finiteDimensional_evenGroundSubmodule :
    FiniteDimensional ℂ (evenGroundSubmodule a) := by
  haveI : CompleteSpace (evenGroundSubmodule a) :=
    (isClosed_evenGroundSubmodule a).completeSpace_coe
  set J := ccmArchimedeanFormToAperture a with hJdef
  set T : evenGroundSubmodule a →L[ℂ] suzukiApertureHilbert a :=
    J.comp (evenGroundSubmodule a).subtypeL with hTdef
  set C : ℝ := evenGroundEnergy a + ‖ccmRestrictedWeilBoundedRemainder a‖
  have hbound : ∀ x : evenGroundSubmodule a,
      ‖x‖ ≤ ((Real.sqrt (max C 0)).toNNReal : ℝ) * ‖T x‖ := by
    intro x
    have hx : IsEvenGround a (x : CCMArchimedeanFormDomain a) := x.2
    have h1 := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass a x
    rw [hx.2.2] at h1
    have h2 : ‖x‖ ^ 2 ≤ max C 0 * ‖T x‖ ^ 2 := by
      have hTx : T x = J x := rfl
      have hnx : ‖x‖ = ‖(x : CCMArchimedeanFormDomain a).1‖ := rfl
      rw [hTx, hnx]
      calc ‖(x : CCMArchimedeanFormDomain a).1‖ ^ 2 ≤ C * ‖J x‖ ^ 2 := by
            simp only [C]; linarith
        _ ≤ max C 0 * ‖J x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    have h3 : ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h3, ← Real.sqrt_sq (norm_nonneg (T x)), ← Real.sqrt_mul (le_max_right _ _)]
    exact Real.sqrt_le_sqrt h2
  have hanti := T.antilipschitz_of_bound hbound
  have hemb := hanti.isClosedEmbedding T.uniformContinuous
  have hK := (isCompactOperator_ccmArchimedeanFormToAperture a).isCompact_closure_image_closedBall 1
  have hpre := hemb.isCompact_preimage hK
  refine FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos
    (hpre.of_isClosed_subset Metric.isClosed_closedBall ?_)
  intro x hx
  show T x ∈ closure (J '' Metric.closedBall 0 1)
  refine subset_closure ⟨(x : CCMArchimedeanFormDomain a), ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  exact hx

/-! ## Even division at zeros off the two axes -/

theorem im_sq_ne_zero_iff (z : ℂ) : (z ^ 2).im ≠ 0 ↔ z.re ≠ 0 ∧ z.im ≠ 0 := by
  rw [sq, Complex.mul_im]
  constructor
  · intro h
    refine ⟨fun h0 => h (by rw [h0]; ring), fun h0 => h (by rw [h0]; ring)⟩
  · rintro ⟨h1, h2⟩
    have : z.re * z.im + z.im * z.re = 2 * (z.re * z.im) := by ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero h1 h2)

/-- On the real line `|(t² − c) F|² = |(t² − Re c) F|² + |Im c · F|²`. -/
theorem sq_norm_quadratic_split (F : ℂ) (t : ℝ) (c : ℂ) :
    ‖((t : ℂ) ^ 2 - c) * F‖ ^ 2 =
      ‖(((t : ℂ) ^ 2 - c) + I * c.im) * F‖ ^ 2 + ‖(c.im : ℂ) * F‖ ^ 2 := by
  have hre : ((t : ℂ) ^ 2 - c) + I * c.im = ((t ^ 2 - c.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [sq]
  rw [hre, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_pow, mul_pow, mul_pow, sq_abs, sq_abs, Complex.sq_norm (_ - c),
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, ← ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Even division.**  An even ground state with a zero `z` off both axes and off the polar
points has an even ground quotient by `(w − z)(w + z)`. -/
theorem exists_evenGround_div {u : CCMArchimedeanFormDomain a} (hu : IsEvenGround a u) {z : ℂ}
    (hz : unitaryLaplace (timeRep a u) z = 0) (him : (z ^ 2).im ≠ 0)
    (hp : z ≠ polarPoint (1 / 2)) (hm : z ≠ polarPoint (-1 / 2)) :
    ∃ v : CCMArchimedeanFormDomain a, IsEvenGround a v ∧ ∀ w : ℂ, w ≠ z → w ≠ -z →
      unitaryLaplace (timeRep a v) w = unitaryLaplace (timeRep a u) w / ((w - z) * (w + z)) := by
  obtain ⟨hpolu, heu, hQ⟩ := hu
  obtain ⟨hzre, hzim⟩ := (im_sq_ne_zero_iff z).mp him
  have hz0 : z ≠ 0 := fun h => hzre (by rw [h, Complex.zero_re])
  have hzneg : -z ≠ z := fun h => hz0 (by linear_combination -h / 2)
  have hzm : unitaryLaplace (timeRep a u) (-z) = 0 := by rw [heu.transform_neg, hz]
  obtain ⟨v₁, hv₁⟩ := exists_div a u hz
  have hv₁m : unitaryLaplace (timeRep a v₁) (-z) = 0 := by
    rw [hv₁ _ hzneg, hzm, zero_div]
  obtain ⟨v, hv⟩ := exists_div a v₁ hv₁m
  have hvform : ∀ w : ℂ, w ≠ z → w ≠ -z →
      unitaryLaplace (timeRep a v) w = unitaryLaplace (timeRep a u) w / ((w - z) * (w + z)) := by
    intro w hwz hwm
    rw [hv w hwm, hv₁ w hwz, div_div, sub_neg_eq_add]
  have hreal : ∀ t : ℝ, (t : ℂ) ≠ z ∧ (t : ℂ) ≠ -z := by
    intro t
    constructor
    · intro h
      apply hzim
      rw [← h, Complex.ofReal_im]
    · intro h
      apply hzim
      have := congrArg Complex.im h
      simp only [Complex.ofReal_im, Complex.neg_im] at this
      linarith
  have hpol := (isPolarConstrained_iff a u).mp hpolu
  have hpp : polarPoint (1 / 2) ≠ -z := by
    intro h
    apply hm
    rw [← neg_neg z, ← h]
    unfold polarPoint
    push_cast
    ring
  have hmm : polarPoint (-1 / 2) ≠ -z := by
    intro h
    apply hp
    rw [← neg_neg z, ← h]
    unfold polarPoint
    push_cast
    ring
  have hvpol : IsPolarConstrained a v := by
    rw [isPolarConstrained_iff, hvform _ (Ne.symm hp) hpp, hvform _ (Ne.symm hm) hmm, hpol.1,
      hpol.2, zero_div, zero_div]
    exact ⟨rfl, rfl⟩
  have hvev : IsEven a v := by
    refine isEven_of_transform a fun t => ?_
    obtain ⟨ht1, ht2⟩ := hreal t
    have hn1 : -(t : ℂ) ≠ z := fun h => ht2 (by rw [← h, neg_neg])
    have hn2 : -(t : ℂ) ≠ -z := fun h => ht1 (by rw [← neg_neg (t : ℂ), h, neg_neg])
    rw [hvform _ hn1 hn2, hvform _ ht1 ht2, heu.transform_neg]
    congr 1
    ring
  -- the quadratic splitting
  set c : ℂ := z ^ 2 with hc
  set h₁ := u + (I * c.im) • v with hh₁
  set h₂ := (c.im : ℂ) • v with hh₂
  have hT₁ : ∀ w, unitaryLaplace (timeRep a h₁) w =
      unitaryLaplace (timeRep a u) w + (I * c.im) * unitaryLaplace (timeRep a v) w :=
    unitaryLaplace_timeRep_add_smul a u v _
  have hT₂ : ∀ w, unitaryLaplace (timeRep a h₂) w =
      (c.im : ℂ) * unitaryLaplace (timeRep a v) w := unitaryLaplace_timeRep_smul a v _
  have hvp := (isPolarConstrained_iff a v).mp hvpol
  have hpol₁ : IsPolarConstrained a h₁ := by
    rw [isPolarConstrained_iff, hT₁, hT₁, hpol.1, hpol.2, hvp.1, hvp.2]
    simp
  have hpol₂ : IsPolarConstrained a h₂ := by
    rw [isPolarConstrained_iff, hT₂, hT₂, hvp.1, hvp.2]
    simp
  have he₁ : IsEven a h₁ := heu.add a (hvev.smul a _)
  have he₂ : IsEven a h₂ := hvev.smul a _
  have hF : ∀ t : ℝ, unitaryLaplace (timeRep a u) t =
      ((t : ℂ) ^ 2 - c) * unitaryLaplace (timeRep a v) t := by
    intro t
    obtain ⟨ht1, ht2⟩ := hreal t
    rw [hvform _ ht1 ht2]
    have h1 : (t : ℂ) - z ≠ 0 := sub_ne_zero.mpr ht1
    have h2 : (t : ℂ) + z ≠ 0 := fun h => ht2 (by linear_combination h)
    rw [hc]
    field_simp
    ring
  have hsplit : ∀ t : ℝ, ‖unitaryLaplace (timeRep a u) t‖ ^ 2 =
      ‖unitaryLaplace (timeRep a h₁) t‖ ^ 2 + ‖unitaryLaplace (timeRep a h₂) t‖ ^ 2 := by
    intro t
    rw [hT₁, hT₂, hF t]
    have := sq_norm_quadratic_split (unitaryLaplace (timeRep a v) t) t c
    rw [this, add_mul]
  have hNsum : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 =
      ‖ccmArchimedeanFormToAperture a h₁‖ ^ 2 + ‖ccmArchimedeanFormToAperture a h₂‖ ^ 2 := by
    rw [← integral_norm_sq_eq, ← integral_norm_sq_eq, ← integral_norm_sq_eq,
      ← integral_add (integrable_norm_sq_unitaryLaplace a h₁)
        (integrable_norm_sq_unitaryLaplace a h₂)]
    exact integral_congr_ae (Eventually.of_forall hsplit)
  have hQsum : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilSourceQuadratic a h₁ + ccmRestrictedWeilSourceQuadratic a h₂ := by
    rw [source_eq_integral a u hpolu, source_eq_integral a h₁ hpol₁,
      source_eq_integral a h₂ hpol₂, ← integral_add (integrable_levelSymbol_mul a h₁)
        (integrable_levelSymbol_mul a h₂)]
    exact integral_congr_ae (Eventually.of_forall fun ξ => by simp only [hsplit ξ, mul_add])
  have hl₁ := evenGroundEnergy_mul_le a h₁ hpol₁ he₁
  have hl₂ := evenGroundEnergy_mul_le a h₂ hpol₂ he₂
  have heq₂ : ccmRestrictedWeilSourceQuadratic a h₂ =
      evenGroundEnergy a * ‖ccmArchimedeanFormToAperture a h₂‖ ^ 2 := by
    rw [hQsum, hNsum, mul_add] at hQ
    linarith
  have hcim : c.im ≠ 0 := him
  refine ⟨v, ⟨hvpol, hvev, ?_⟩, hvform⟩
  rw [hh₂, ccmRestrictedWeilSourceQuadratic_smul, map_smul, norm_smul, mul_pow] at heq₂
  have hpos : (0 : ℝ) < ‖(c.im : ℂ)‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    positivity
  have h' : ‖(c.im : ℂ)‖ ^ 2 * ccmRestrictedWeilSourceQuadratic a v =
      ‖(c.im : ℂ)‖ ^ 2 * (evenGroundEnergy a * ‖ccmArchimedeanFormToAperture a v‖ ^ 2) := by
    rw [heq₂]; ring
  exact mul_left_cancel₀ hpos.ne' h'

/-! ## Zeros on the cross -/

theorem sum_range_spread {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n + 1), (if j % 2 = 0 then f (j / 2) else 0) =
      ∑ k ∈ Finset.range (n + 1), f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ (n := n + 1)]
    have h1 : (2 * n + 1) % 2 = 1 := by omega
    have h2 : (2 * n + 1 + 1) % 2 = 0 := by omega
    have h3 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    simp only [h1, h2, h3, one_ne_zero, if_false, if_true, add_zero]

/-- The interleaved sequence `z₀, −z₀, z₁, −z₁, …`. -/
def interleave (zs : ℕ → ℂ) (j : ℕ) : ℂ := if j % 2 = 0 then zs (j / 2) else -zs (j / 2)

theorem prod_interleave (zs : ℕ → ℂ) (t : ℂ) (k : ℕ) :
    ∏ l ∈ Finset.range (2 * k), (t - interleave zs l) =
      ∏ l ∈ Finset.range k, ((t - zs l) * (t + zs l)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ,
      ih, Finset.prod_range_succ (n := k), mul_assoc]
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    have h3 : (2 * k) / 2 = k := by omega
    have h4 : (2 * k + 1) / 2 = k := by omega
    simp only [interleave, h1, h2, h3, h4, if_true, one_ne_zero, if_false, sub_neg_eq_add]

/-- **Even ground states with transform zeros on `ℝ ∪ iℝ` exist at every aperture.** -/
theorem exists_crossRooted_evenGround :
    ∃ u : CCMArchimedeanFormDomain a, IsEvenGround a u ∧
      ccmArchimedeanFormToAperture a u ≠ 0 ∧
      ∀ w : ℂ, unitaryLaplace (timeRep a u) w = 0 → w ≠ polarPoint (1 / 2) →
        w ≠ polarPoint (-1 / 2) → w.re = 0 ∨ w.im = 0 := by
  classical
  obtain ⟨u₀, hpol₀, he₀, hn₀, hQ₀⟩ := exists_evenGround a
  have hg₀ : IsEvenGround a u₀ := ⟨hpol₀, he₀, by rw [hQ₀, hn₀]; ring⟩
  have hne₀ : ccmArchimedeanFormToAperture a u₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn₀
    exact zero_ne_one hn₀
  by_contra hcon
  push Not at hcon
  let S := {u : CCMArchimedeanFormDomain a //
    IsEvenGround a u ∧ ccmArchimedeanFormToAperture a u ≠ 0}
  have hstep : ∀ s : S, ∃ w : ℂ, ∃ v : S, (w ^ 2).im ≠ 0 ∧
      ∀ t : ℝ, unitaryLaplace (timeRep a v.1) t =
        unitaryLaplace (timeRep a s.1) t / (((t : ℂ) - w) * ((t : ℂ) + w)) := by
    intro s
    obtain ⟨w, hw, hp, hm, hre, him⟩ := hcon s.1 s.2.1 s.2.2
    have hsq : (w ^ 2).im ≠ 0 := (im_sq_ne_zero_iff w).mpr ⟨hre, him⟩
    obtain ⟨v, hgv, hv⟩ := exists_evenGround_div a s.2.1 hw hsq hp hm
    have hrw : ∀ t : ℝ, (t : ℂ) ≠ w ∧ (t : ℂ) ≠ -w := fun t =>
      ⟨fun h => him (by rw [← h, Complex.ofReal_im]),
        fun h => him (by
          have := congrArg Complex.im h
          simp only [Complex.ofReal_im, Complex.neg_im] at this
          linarith)⟩
    have hnv : ccmArchimedeanFormToAperture a v ≠ 0 := by
      intro h0
      obtain ⟨t, ht⟩ := exists_real_ne_zero a s.2.2
      have hv0 : v = 0 := ccmArchimedeanFormToAperture_injective a (by rw [h0, map_zero])
      have h1 := hv t (hrw t).1 (hrw t).2
      rw [hv0, unitaryLaplace_timeRep_zero, eq_comm, div_eq_zero_iff] at h1
      refine ht (h1.resolve_right ?_)
      exact mul_ne_zero (sub_ne_zero.mpr (hrw t).1)
        (fun h => (hrw t).2 (by linear_combination h))
    exact ⟨w, ⟨v, hgv, hnv⟩, hsq, fun t => hv t (hrw t).1 (hrw t).2⟩
  choose zf nx hsqf hnx using hstep
  let chain : ℕ → S := fun k => nx^[k] ⟨u₀, hg₀, hne₀⟩
  let zs : ℕ → ℂ := fun k => zf (chain k)
  have hsucc : ∀ k, chain (k + 1) = nx (chain k) := fun k =>
    Function.iterate_succ_apply' nx k _
  have hform : ∀ (k : ℕ) (t : ℝ), unitaryLaplace (timeRep a (chain k).1) t =
      unitaryLaplace (timeRep a u₀) t /
        ∏ l ∈ Finset.range k, (((t : ℂ) - zs l) * ((t : ℂ) + zs l)) := by
    intro k t
    induction k with
    | zero => simp [chain]
    | succ k ih => rw [hsucc, hnx, ih, Finset.prod_range_succ, div_div]
  haveI := finiteDimensional_evenGroundSubmodule a
  set d := Module.finrank ℂ (evenGroundSubmodule a)
  let g : Fin (d + 1) → evenGroundSubmodule a := fun i => ⟨(chain i).1, (chain i).2.1⟩
  let T : evenGroundSubmodule a →ₗ[ℂ] (ℝ → ℂ) :=
    { toFun := fun u => fun t : ℝ =>
        unitaryLaplace (timeRep a (u : CCMArchimedeanFormDomain a)) t
      map_add' := fun u v => by
        funext t
        have h := unitaryLaplace_timeRep_add_smul a u v 1 t
        rw [one_smul, one_mul] at h
        simpa only [Submodule.coe_add, Pi.add_apply] using h
      map_smul' := fun c u => by
        funext t
        simpa only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul] using
          unitaryLaplace_timeRep_smul a u c t }
  have hli : LinearIndependent ℂ g := by
    apply LinearIndependent.of_comp T
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    let ck : ℕ → ℂ := fun j => if h : j < d + 1 then c ⟨j, h⟩ else 0
    let c' : ℕ → ℂ := fun j => if j % 2 = 0 then ck (j / 2) else 0
    have hzim : ∀ k, (zs k).im ≠ 0 := fun k => ((im_sq_ne_zero_iff _).mp (hsqf (chain k))).2
    have hreal : ∀ j < 2 * d, ∀ t : ℝ, (t : ℂ) - interleave zs j ≠ 0 := by
      intro j _ t h
      unfold interleave at h
      split_ifs at h
      · exact hzim _ (by
          have := congrArg Complex.im h
          simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
          linarith)
      · exact hzim _ (by
          have := congrArg Complex.im h
          simp only [Complex.sub_im, Complex.ofReal_im, Complex.neg_im, Complex.zero_im] at this
          linarith)
    have hsum : ∀ t : ℝ, ∑ j ∈ Finset.range (2 * d + 1), c' j *
        (unitaryLaplace (timeRep a u₀) t /
          ∏ l ∈ Finset.range j, ((t : ℂ) - interleave zs l)) = 0 := by
      intro t
      have h0 := congrFun hc t
      simp only [Finset.sum_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at h0
      have hsp := sum_range_spread (fun k => ck k * (unitaryLaplace (timeRep a u₀) t /
        ∏ l ∈ Finset.range (2 * k), ((t : ℂ) - interleave zs l))) d
      have hlhs : ∑ j ∈ Finset.range (2 * d + 1), c' j *
          (unitaryLaplace (timeRep a u₀) t / ∏ l ∈ Finset.range j, ((t : ℂ) - interleave zs l)) =
          ∑ j ∈ Finset.range (2 * d + 1), (if j % 2 = 0 then ck (j / 2) *
            (unitaryLaplace (timeRep a u₀) t /
              ∏ l ∈ Finset.range (2 * (j / 2)), ((t : ℂ) - interleave zs l)) else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j % 2 = 0
        · have hj2 : 2 * (j / 2) = j := by omega
          simp only [c', hj, if_true, hj2]
        · simp only [c', hj, if_false, zero_mul]
      rw [hlhs, hsp, ← h0, ← Fin.sum_univ_eq_sum_range (fun k => ck k *
        (unitaryLaplace (timeRep a u₀) t /
          ∏ l ∈ Finset.range (2 * k), ((t : ℂ) - interleave zs l)))]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [ck, dif_pos k.isLt, Fin.eta]
      rw [prod_interleave, ← hform k t]
      rfl
    have := eq_zero_of_sum_div_prod (infinite_real_ne_zero a hne₀) (interleave zs) (2 * d)
      hreal c' hsum (2 * i) (by omega)
    have h2i : (2 * (i : ℕ)) % 2 = 0 := by omega
    have h2i' : (2 * (i : ℕ)) / 2 = i := by omega
    simp only [c', ck, h2i, h2i', if_true, dif_pos i.isLt, Fin.eta] at this
    exact this
  have hcard := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

end RHTower.CCMEvenSector
