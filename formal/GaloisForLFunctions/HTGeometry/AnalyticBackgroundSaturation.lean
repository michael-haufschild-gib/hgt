import GaloisForLFunctions.HTGeometry.PerturbedOuterFamilyFreeness
import GaloisForLFunctions.HTGeometry.OuterCauchyOrbitBoundary
import GaloisForLFunctions.HTGeometry.BohrOrbitHaarLaw
import GaloisForLFunctions.HTGeometry.FamilyPowerGauge

/-!
# Analytic-background saturation by maximal translation hypertranscendence
-/

namespace GaloisForLFunctions.HTGeometry

open Filter MeasureTheory Set Topology Metric

noncomputable section

/-- The grafted source `G_{u,B} = S_u + B`, translated by `t i`. -/
def graftedFamily (x ε : ℕ → ℝ) (u : MassParameter) (B : ℂ → ℂ) {r : ℕ}
    (t : Fin r → ℝ) (i : Fin r) : ℂ → ℂ :=
  perturbedOuterFamily x ε u 1 B t i

theorem graftedFamily_apply (x ε : ℕ → ℝ) (u : MassParameter) (B : ℂ → ℂ) {r : ℕ}
    (t : Fin r → ℝ) (i : Fin r) (w : ℂ) :
    graftedFamily x ε u B t i w
      = massOuterBackground x ε u (w + (t i : ℂ)) + B (w + (t i : ℂ)) := by
  simp [graftedFamily, perturbedOuterFamily]

/-- **Analytic-background saturation.**  For every fixed analytic background `B` on the upper half
plane, a residual set of bounded mass parameters makes the real-translation orbit of `S_u + B`
differentially algebraically independent. -/
theorem residual_backgroundSaturation (m' : ℕ) {t : Fin (m' + 1) → ℝ}
    (ht : Function.Injective t) {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ}
    (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) {B : ℂ → ℂ}
    (hB : DifferentiableOn ℂ B {ζ : ℂ | 0 < ζ.im}) :
    {u : MassParameter | ¬ FamilyDifferentiallyAlgebraicOn
        (graftedFamily x ε u B t) {ζ : ℂ | 0 < ζ.im}} ∈ residual MassParameter := by
  refine residual_not_familyDifferentiallyAlgebraicOn_perturbedOuterFamily m' ht hx hεpos hε 1 ?_
  intro ζ hζ
  exact ((hB.analyticOnNhd isOpen_upperHalfSet) ζ hζ).contDiffAt

/-- The saturating mass parameters are dense. -/
theorem dense_backgroundSaturation (m' : ℕ) {t : Fin (m' + 1) → ℝ}
    (ht : Function.Injective t) {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ}
    (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) {B : ℂ → ℂ}
    (hB : DifferentiableOn ℂ B {ζ : ℂ | 0 < ζ.im}) :
    Dense {u : MassParameter | ¬ FamilyDifferentiallyAlgebraicOn
        (graftedFamily x ε u B t) {ζ : ℂ | 0 < ζ.im}} :=
  dense_of_mem_residual (residual_backgroundSaturation m' ht hx hεpos hε hB)

/-! ## The two-sided modulus bound `(2)` -/

theorem norm_cayleyOuter_lt {w : ℂ} (hw : 0 < w.im) : ‖cayleyOuter w‖ < Real.exp 1 := by
  have hne : w + Complex.I ≠ 0 := by
    intro hc
    have him := congrArg Complex.im hc
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
    linarith
  have hlt : ‖(w - Complex.I) / (w + Complex.I)‖ < 1 := by
    rw [norm_div, div_lt_one (by positivity)]
    exact norm_sub_I_lt_norm_add_I hw
  have hre : ((w - Complex.I) / (w + Complex.I)).re < 1 := by
    have hbound := Complex.abs_re_le_norm ((w - Complex.I) / (w + Complex.I))
    have habs := le_abs_self (((w - Complex.I) / (w + Complex.I)).re)
    linarith
  rw [cayleyOuter, Complex.norm_exp]
  exact Real.exp_lt_exp.mpr hre

theorem norm_outerBackground_lt (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    {z : ℂ} (hz : 0 < z.im) : ‖outerBackground ν z‖ < Real.exp 1 :=
  norm_cayleyOuter_lt (im_cauchyTransform_pos_of_ne_zero ν hν hz)

theorem norm_outerBackground_gt (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    {z : ℂ} (hz : 0 < z.im) : Real.exp (-1) < ‖outerBackground ν z‖ :=
  norm_cayleyOuter_gt (im_cauchyTransform_pos_of_ne_zero ν hν hz)

theorem massMeasure_ne_zero {x ε : ℕ → ℝ} (hx : Function.Injective x) (hεpos : ∀ k, 0 < ε k)
    (u : MassParameter) : massMeasure x ε u ≠ 0 := by
  intro hc
  have hval : massMeasure x ε u {x 0} = ENNReal.ofReal (ε 0 * Real.exp (u 0)) :=
    _root_.HTGeometry.countableWeightedDirac_singleton _ hx 0
  rw [hc] at hval
  simp only [Measure.coe_zero, Pi.zero_apply] at hval
  have hpos : 0 < ε 0 * Real.exp (u 0) := mul_pos (hεpos 0) (Real.exp_pos _)
  rw [eq_comm, ENNReal.ofReal_eq_zero] at hval
  linarith

/-! ## The invertible outer cage -/

/-- **The invertible outer cage.**  A background of sup-norm below `exp (-1)` keeps the grafted
source bounded away from zero, so both it and its reciprocal are bounded on the upper half plane. -/
theorem norm_grafted_ge {x ε : ℕ → ℝ} (hx : Function.Injective x) (hεpos : ∀ k, 0 < ε k)
    (hε : Summable ε) (u : MassParameter) {B : ℂ → ℂ} {b : ℝ}
    (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b)
    {z : ℂ} (hz : 0 < z.im) :
    Real.exp (-1) - b ≤ ‖massOuterBackground x ε u z + B z‖ := by
  haveI := isFiniteMeasure_massMeasure (x := x) hεpos hε u
  have hgt : Real.exp (-1) < ‖massOuterBackground x ε u z‖ :=
    norm_outerBackground_gt _ (massMeasure_ne_zero hx hεpos u) hz
  have hle : ‖B z‖ ≤ b := hb z hz
  have hsub : ‖massOuterBackground x ε u z‖ - ‖B z‖
      ≤ ‖massOuterBackground x ε u z + B z‖ := by
    have h := norm_sub_norm_le (massOuterBackground x ε u z) (-(B z))
    simpa [sub_neg_eq_add] using h
  linarith

/-- **The cage is invertible.**  A background of sup-norm strictly below `exp (-1)` cannot cancel
the outer core, so the grafted source never vanishes above the real axis. -/
theorem norm_grafted_pos {x ε : ℕ → ℝ} (hx : Function.Injective x) (hεpos : ∀ k, 0 < ε k)
    (hε : Summable ε) (u : MassParameter) {B : ℂ → ℂ} {b : ℝ}
    (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b) (hblt : b < Real.exp (-1))
    {z : ℂ} (hz : 0 < z.im) :
    0 < ‖massOuterBackground x ε u z + B z‖ :=
  lt_of_lt_of_le (by linarith) (norm_grafted_ge hx hεpos hε u hb hz)

/-- The grafted source never vanishes above the real axis. -/
theorem grafted_ne_zero {x ε : ℕ → ℝ} (hx : Function.Injective x) (hεpos : ∀ k, 0 < ε k)
    (hε : Summable ε) (u : MassParameter) {B : ℂ → ℂ} {b : ℝ}
    (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b) (hblt : b < Real.exp (-1))
    {z : ℂ} (hz : 0 < z.im) :
    massOuterBackground x ε u z + B z ≠ 0 :=
  norm_pos_iff.1 (norm_grafted_pos hx hεpos hε u hb hblt hz)

/-- The grafted source is bounded above on the upper half plane. -/
theorem norm_grafted_le {x ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε)
    (u : MassParameter) {B : ℂ → ℂ} {b : ℝ}
    (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b) {z : ℂ} (hz : 0 < z.im) :
    ‖massOuterBackground x ε u z + B z‖ ≤ Real.exp 1 + b := by
  haveI := isFiniteMeasure_massMeasure (x := x) hεpos hε u
  have hlt : ‖massOuterBackground x ε u z‖ < Real.exp 1 := by
    by_cases hzero : massMeasure x ε u = 0
    · rw [massOuterBackground, outerBackground, hzero]
      have : cauchyTransform (0 : Measure ℝ) z = 0 := by
        simp [cauchyTransform]
      rw [this, cayleyOuter_zero, Complex.norm_exp]
      simp only [Complex.neg_re, Complex.one_re]
      exact Real.exp_lt_exp.mpr (by norm_num)
    · exact norm_outerBackground_lt _ hzero hz
  have := norm_add_le (massOuterBackground x ε u z) (B z)
  have hle : ‖B z‖ ≤ b := hb z hz
  linarith

/-! ## Exact asymptotic transfer -/

/-- **Equation `(7)`.**  The grafted orbit differs from the translated background plus the scalar
`exp (-1)` by an error tending to zero uniformly on every compact subset of the upper half plane. -/
theorem tendstoUniformlyOn_grafted_sub {x ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε)
    (u : MassParameter) (B : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K) (hKH : ∀ z ∈ K, 0 < z.im) :
    TendstoUniformlyOn
      (fun (τ : ℝ) (z : ℂ) =>
        (massOuterBackground x ε u (z + (τ : ℂ)) + B (z + (τ : ℂ)))
          - (Complex.exp (-1) + B (z + (τ : ℂ))))
      (fun _ => (0 : ℂ)) (cocompact ℝ) K := by
  haveI := isFiniteMeasure_massMeasure (x := x) hεpos hε u
  have hbase := tendstoUniformlyOn_outerBackground_translate (massMeasure x ε u) hK hKH
  rw [Metric.tendstoUniformlyOn_iff] at hbase ⊢
  intro δ hδ
  filter_upwards [hbase δ hδ] with τ hτ z hz
  have h := hτ z hz
  rw [Complex.dist_eq] at h ⊢
  have hrw : (0 : ℂ) - (massOuterBackground x ε u (z + (τ : ℂ)) + B (z + (τ : ℂ))
      - (Complex.exp (-1) + B (z + (τ : ℂ))))
      = Complex.exp (-1) - massOuterBackground x ε u (z + (τ : ℂ)) := by
    rw [massOuterBackground]
    ring
  rw [hrw]
  exact h

/-! ## Infinite cluster sets -/

theorem tendstoUniformlyOn_comp_seq {ι κ : Type*} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {p : Filter ι}
    {q : Filter κ} {s : Set ℂ} (h : TendstoUniformlyOn F f p s) {g : κ → ι}
    (hg : Tendsto g q p) : TendstoUniformlyOn (fun k => F (g k)) f q s :=
  fun u hu => hg.eventually (h u hu)

theorem tendsto_cocompact_of_abs_atTop {τ : ℕ → ℝ} (h : Tendsto (fun j => |τ j|) atTop atTop) :
    Tendsto τ atTop (cocompact ℝ) := by
  rw [Filter.tendsto_def]
  intro s hs
  rw [Filter.mem_cocompact] at hs
  obtain ⟨t, htc, hts⟩ := hs
  obtain ⟨M, hM⟩ := htc.isBounded.subset_closedBall 0
  have hev := h.eventually_ge_atTop (M + 1)
  filter_upwards [hev] with j hj
  refine hts ?_
  intro hmem
  have := hM hmem
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
  linarith

/-- The infinite-parameter cluster set of a real translation orbit, in the compact-open sense on
the upper half plane. -/
def infiniteClusterSet (F : ℝ → ℂ → ℂ) : Set (ℂ → ℂ) :=
  {G | ∃ τ : ℕ → ℝ, Tendsto (fun j => |τ j|) atTop atTop ∧
    ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 0 < z.im) →
      TendstoUniformlyOn (fun j z => F (τ j) z) G atTop K}

theorem tendstoUniformlyOn_const' {ι : Type*} {p : Filter ι} {s : Set ℂ} (c : ℂ) :
    TendstoUniformlyOn (fun (_ : ι) (_ : ℂ) => c) (fun _ => c) p s := by
  intro v hv
  filter_upwards with j
  intro z _
  exact refl_mem_uniformity hv

/-- **Equation `(8)`.**  Grafting the maximal hypertranscendence layer translates the infinite
cluster set of the background by the single scalar `exp (-1)`. -/
theorem infiniteClusterSet_grafted {x ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε)
    (u : MassParameter) (B : ℂ → ℂ) :
    infiniteClusterSet (fun τ z => massOuterBackground x ε u (z + (τ : ℂ)) + B (z + (τ : ℂ)))
      = (fun G : ℂ → ℂ => fun z => Complex.exp (-1) + G z) ''
        infiniteClusterSet (fun τ z => B (z + (τ : ℂ))) := by
  ext H
  constructor
  · rintro ⟨τ, hτ, hconv⟩
    refine ⟨fun z => H z - Complex.exp (-1), ⟨τ, hτ, fun K hK hKH => ?_⟩, ?_⟩
    · have hS := tendstoUniformlyOn_comp_seq
        (tendstoUniformlyOn_grafted_sub (x := x) hεpos hε u B hK hKH)
        (tendsto_cocompact_of_abs_atTop hτ)
      have hG := hconv K hK hKH
      have hcB : TendstoUniformlyOn
          (fun (j : ℕ) (z : ℂ) => Complex.exp (-1) + B (z + (τ j : ℂ))) H atTop K := by
        have hdiff := hG.sub hS
        refine hdiff.congr ?_ |>.congr_right ?_
        · filter_upwards with j
          intro z _
          show massOuterBackground x ε u (z + (τ j : ℂ)) + B (z + (τ j : ℂ))
              - (massOuterBackground x ε u (z + (τ j : ℂ)) + B (z + (τ j : ℂ))
                - (Complex.exp (-1) + B (z + (τ j : ℂ))))
              = Complex.exp (-1) + B (z + (τ j : ℂ))
          ring
        · intro z _
          show H z - 0 = H z
          ring
      have hfin := hcB.sub (tendstoUniformlyOn_const' (ι := ℕ) (p := atTop) (s := K)
        (Complex.exp (-1)))
      refine hfin.congr ?_ |>.congr_right ?_
      · filter_upwards with j
        intro z _
        show Complex.exp (-1) + B (z + (τ j : ℂ)) - Complex.exp (-1) = B (z + (τ j : ℂ))
        ring
      · intro z _
        rfl
    · funext z
      ring
  · rintro ⟨G, ⟨τ, hτ, hconv⟩, rfl⟩
    refine ⟨τ, hτ, fun K hK hKH => ?_⟩
    have hS := tendstoUniformlyOn_comp_seq
      (tendstoUniformlyOn_grafted_sub (x := x) hεpos hε u B hK hKH)
      (tendsto_cocompact_of_abs_atTop hτ)
    have hcG : TendstoUniformlyOn
        (fun (j : ℕ) (z : ℂ) => Complex.exp (-1) + B (z + (τ j : ℂ)))
        (fun z => Complex.exp (-1) + G z) atTop K := by
      have := (tendstoUniformlyOn_const' (ι := ℕ) (p := atTop) (s := K)
        (Complex.exp (-1))).add (hconv K hK hKH)
      exact this
    have hsum := hcG.add hS
    refine hsum.congr ?_ |>.congr_right ?_
    · filter_upwards with j
      intro z _
      show Complex.exp (-1) + B (z + (τ j : ℂ))
          + (massOuterBackground x ε u (z + (τ j : ℂ)) + B (z + (τ j : ℂ))
            - (Complex.exp (-1) + B (z + (τ j : ℂ))))
          = massOuterBackground x ε u (z + (τ j : ℂ)) + B (z + (τ j : ℂ))
      ring
    · intro z _
      show Complex.exp (-1) + G z + 0 = Complex.exp (-1) + G z
      ring

/-! ## Limiting-measure transfer -/

open GaloisForLFunctions in
/-- The grafted source, translated, as a continuous map on the upper half plane. -/
def graftedOrbit {S B : ℂ → ℂ} (hS : ContinuousOn S {z : ℂ | 0 < z.im})
    (hB : ContinuousOn B {z : ℂ | 0 < z.im}) (t : ℝ) : C(UpperPlane, ℂ) :=
  ⟨fun z => S ((z : ℂ) + (t : ℂ)) + B ((z : ℂ) + (t : ℂ)), by
    refine Continuous.add ?_ ?_
    · exact hS.comp_continuous (continuous_subtype_val.add continuous_const)
        fun z => upperPlane_add_ofReal z t
    · exact hB.comp_continuous (continuous_subtype_val.add continuous_const)
        fun z => upperPlane_add_ofReal z t⟩

open GaloisForLFunctions in
/-- The translated background shifted by the collapse scalar. -/
def shiftedBackground (c : ℂ) {B : ℂ → ℂ} (hB : ContinuousOn B {z : ℂ | 0 < z.im}) (t : ℝ) :
    C(UpperPlane, ℂ) :=
  ⟨fun z => c + B ((z : ℂ) + (t : ℂ)), by
    refine Continuous.add continuous_const ?_
    exact hB.comp_continuous (continuous_subtype_val.add continuous_const)
      fun z => upperPlane_add_ofReal z t⟩

open GaloisForLFunctions in
/-- Real translation is continuous into the compact-open topology: the grafted orbit is a
continuous path of continuous maps. -/
theorem continuous_graftedOrbit {S B : ℂ → ℂ} (hS : ContinuousOn S {z : ℂ | 0 < z.im})
    (hB : ContinuousOn B {z : ℂ | 0 < z.im}) :
    Continuous fun t => graftedOrbit hS hB t := by
  have hg : Continuous fun p : ℝ × UpperPlane => ((p.2 : ℂ) + (p.1 : ℂ)) :=
    (continuous_subtype_val.comp continuous_snd).add
      (Complex.continuous_ofReal.comp continuous_fst)
  have hmem : ∀ p : ℝ × UpperPlane, ((p.2 : ℂ) + (p.1 : ℂ)) ∈ {z : ℂ | 0 < z.im} :=
    fun p => upperPlane_add_ofReal p.2 p.1
  have hF : Continuous fun p : ℝ × UpperPlane =>
      S ((p.2 : ℂ) + (p.1 : ℂ)) + B ((p.2 : ℂ) + (p.1 : ℂ)) :=
    (hS.comp_continuous hg hmem).add (hB.comp_continuous hg hmem)
  refine ((ContinuousMap.curry (⟨_, hF⟩ : C(ℝ × UpperPlane, ℂ))).continuous).congr ?_
  intro t
  exact ContinuousMap.ext fun z => rfl

open GaloisForLFunctions in
/-- The shifted background is a continuous path of continuous maps. -/
theorem continuous_shiftedBackground (c : ℂ) {B : ℂ → ℂ}
    (hB : ContinuousOn B {z : ℂ | 0 < z.im}) :
    Continuous fun t => shiftedBackground c hB t := by
  have hg : Continuous fun p : ℝ × UpperPlane => ((p.2 : ℂ) + (p.1 : ℂ)) :=
    (continuous_subtype_val.comp continuous_snd).add
      (Complex.continuous_ofReal.comp continuous_fst)
  have hmem : ∀ p : ℝ × UpperPlane, ((p.2 : ℂ) + (p.1 : ℂ)) ∈ {z : ℂ | 0 < z.im} :=
    fun p => upperPlane_add_ofReal p.2 p.1
  have hF : Continuous fun p : ℝ × UpperPlane => c + B ((p.2 : ℂ) + (p.1 : ℂ)) :=
    continuous_const.add (hB.comp_continuous hg hmem)
  refine ((ContinuousMap.curry (⟨_, hF⟩ : C(ℝ × UpperPlane, ℂ))).continuous).congr ?_
  intro t
  exact ContinuousMap.ext fun z => rfl

open GaloisForLFunctions in
/-- **Equation `(7)` in the compact-open uniformity.**  The grafted orbit is asymptotic to the
translated background shifted by the collapse scalar. -/
theorem tendsto_uniformity_graftedOrbit {S B : ℂ → ℂ} (hS : ContinuousOn S {z : ℂ | 0 < z.im})
    (hB : ContinuousOn B {z : ℂ | 0 < z.im}) {c : ℂ} {l : Filter ℝ}
    (hcollapse : ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 0 < z.im) →
      TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => S (z + (t : ℂ))) (fun _ => c) l K) :
    Tendsto (fun t => (shiftedBackground c hB t, graftedOrbit hS hB t)) l
      (uniformity C(UpperPlane, ℂ)) := by
  refine tendsto_uniformity_continuousMap fun K hK δ hδ => ?_
  have hKim : IsCompact ((fun z : UpperPlane => (z : ℂ)) '' K) := hK.image continuous_subtype_val
  have hKpos : ∀ z ∈ (fun z : UpperPlane => (z : ℂ)) '' K, 0 < z.im := by
    rintro z ⟨w, _, rfl⟩
    exact w.2
  have huc := hcollapse _ hKim hKpos
  rw [Metric.tendstoUniformlyOn_iff] at huc
  filter_upwards [huc δ hδ] with t ht z hz
  have hzim : (z : ℂ) ∈ (fun z : UpperPlane => (z : ℂ)) '' K := ⟨z, hz, rfl⟩
  have hd := ht _ hzim
  show dist (c + B ((z : ℂ) + (t : ℂ)))
    (S ((z : ℂ) + (t : ℂ)) + B ((z : ℂ) + (t : ℂ))) < δ
  rw [Complex.dist_eq] at hd ⊢
  have hrw : c + B ((z : ℂ) + (t : ℂ)) - (S ((z : ℂ) + (t : ℂ)) + B ((z : ℂ) + (t : ℂ)))
      = c - S ((z : ℂ) + (t : ℂ)) := by ring
  rw [hrw]
  exact hd

open GaloisForLFunctions in
/-- **Equation `(10)`.**  Every limiting time distribution of the background transfers exactly to
the grafted maximally hypertranscendental orbit, shifted by the collapse scalar. -/
theorem tendsto_windowAverage_graftedOrbit {S B : ℂ → ℂ}
    (hS : ContinuousOn S {z : ℂ | 0 < z.im}) (hB : ContinuousOn B {z : ℂ | 0 < z.im}) {c : ℂ}
    (hcollapse : ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 0 < z.im) →
      TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => S (z + (t : ℂ))) (fun _ => c) (cocompact ℝ) K)
    {test : C(UpperPlane, ℂ) → ℂ} (htest : UniformContinuous test)
    {L : ℂ} (hL : Tendsto (windowAverage fun t => test (shiftedBackground c hB t)) atTop
      (nhds L)) :
    Tendsto (windowAverage fun t => test (graftedOrbit hS hB t)) atTop (nhds L) := by
  refine tendsto_windowAverage_of_tendsto_sub_zero
    (htest.continuous.comp (continuous_graftedOrbit hS hB))
    (htest.continuous.comp (continuous_shiftedBackground c hB)) ?_ hL
  have hasym := tendsto_uniformity_graftedOrbit hS hB hcollapse
  have hpair : Tendsto (fun t => (test (shiftedBackground c hB t),
      test (graftedOrbit hS hB t))) (cocompact ℝ) (uniformity ℂ) :=
    Filter.Tendsto.comp htest hasym
  have hatTop : (atTop : Filter ℝ) ≤ cocompact ℝ := by
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_right
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro δ hδ
  have hev := hpair (Metric.dist_mem_uniformity hδ)
  filter_upwards [hatTop hev] with t ht
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at ht
  rw [Complex.dist_eq] at ht
  show ‖test (graftedOrbit hS hB t) - test (shiftedBackground c hB t)‖ < δ
  rw [norm_sub_rev]
  exact ht


/-- The grafted source is smooth at every point of the upper half plane. -/
theorem contDiffAt_graftedFamily {x ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε)
    (u : MassParameter) {B : ℂ → ℂ} (hB : DifferentiableOn ℂ B {ζ : ℂ | 0 < ζ.im}) {r : ℕ}
    (t : Fin r → ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin r) :
    ContDiffAt ℂ (⊤ : ℕ∞) (graftedFamily x ε u B t i) z := by
  have hznode : 0 < (z + (t i : ℂ)).im := by simpa using hz
  have hS : ContDiffAt ℂ (⊤ : ℕ∞)
      (fun w => massOuterBackground x ε u (w + (t i : ℂ))) z :=
    contDiffAt_comp_add_const (contDiffAt_massOuterBackground hεpos hε u hznode)
  have hBt : ContDiffAt ℂ (⊤ : ℕ∞) (fun w => B (w + (t i : ℂ))) z :=
    contDiffAt_comp_add_const (((hB.analyticOnNhd isOpen_upperHalfSet) _ hznode).contDiffAt)
  exact hS.add (contDiffAt_const.mul hBt)

/-- **Equation `(6)`.**  A function is algebraic over each of its nonzero powers, so adjoining the
roots cannot raise the differential transcendence degree.  Hence one and the same residual set of
mass parameters makes *every* positive power of the grafted translation packet differentially
algebraically independent. -/
theorem residual_backgroundSaturation_pow (m' : ℕ) {t : Fin (m' + 1) → ℝ}
    (ht : Function.Injective t) {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ}
    (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) {B : ℂ → ℂ}
    (hB : DifferentiableOn ℂ B {ζ : ℂ | 0 < ζ.im}) :
    {u : MassParameter | ∀ N : ℕ, N ≠ 0 → ¬ FamilyDifferentiallyAlgebraicOn
        (fun i w => graftedFamily x ε u B t i w ^ N) {ζ : ℂ | 0 < ζ.im}}
      ∈ residual MassParameter := by
  refine Filter.mem_of_superset (residual_backgroundSaturation m' ht hx hεpos hε hB) ?_
  intro u hu N hN
  exact not_familyDifferentiallyAlgebraicOn_pow _ hN
    (fun z hz i => contDiffAt_graftedFamily hεpos hε u hB t hz i) hu

open GaloisForLFunctions in
/-- The set of sequential limits of a real-parameter orbit of continuous maps, in the compact-open
topology. -/
def orbitSeqClosure (F : ℝ → C(UpperPlane, ℂ)) : Set C(UpperPlane, ℂ) :=
  {L | ∃ τ : ℕ → ℝ, Tendsto (fun j => F (τ j)) atTop (nhds L)}

open GaloisForLFunctions in
/-- The infinite-parameter cluster set of a real-parameter orbit of continuous maps. -/
def orbitInfiniteCluster (F : ℝ → C(UpperPlane, ℂ)) : Set C(UpperPlane, ℂ) :=
  {L | ∃ τ : ℕ → ℝ, Tendsto (fun j => |τ j|) atTop atTop ∧
    Tendsto (fun j => F (τ j)) atTop (nhds L)}

open GaloisForLFunctions in
/-- **Equation `(9)`.**  The sequential closure of the grafted translation orbit splits into the
orbit itself and the infinite cluster set of the shifted background: a parameter sequence either has
a bounded subsequence, whose limit lies on the orbit by continuity of translation, or escapes to
infinity, where `(7)` identifies the limit with a background cluster point.  No relative compactness
is needed, and the two pieces need not be disjoint. -/
theorem orbitSeqClosure_graftedOrbit {S B : ℂ → ℂ} (hS : ContinuousOn S {z : ℂ | 0 < z.im})
    (hB : ContinuousOn B {z : ℂ | 0 < z.im}) {c : ℂ}
    (hcollapse : ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 0 < z.im) →
      TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => S (z + (t : ℂ))) (fun _ => c) (cocompact ℝ) K) :
    orbitSeqClosure (graftedOrbit hS hB)
      = Set.range (graftedOrbit hS hB) ∪ orbitInfiniteCluster (shiftedBackground c hB) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro L ⟨τ, hτ⟩
    by_cases hinf : Tendsto (fun j => |τ j|) atTop atTop
    · refine Or.inr ⟨τ, hinf, ?_⟩
      have h := (tendsto_uniformity_graftedOrbit hS hB hcollapse).comp
        (tendsto_cocompact_of_abs_atTop hinf)
      exact hτ.congr_uniformity (tendsto_swap_uniformity.comp h)
    · refine Or.inl ?_
      rw [tendsto_atTop_atTop] at hinf
      push Not at hinf
      obtain ⟨M, hM⟩ := hinf
      have hfreq : ∃ᶠ j in atTop, |τ j| ≤ M := by
        rw [frequently_atTop]
        intro a
        obtain ⟨b, hb, hlt⟩ := hM a
        exact ⟨b, hb, hlt.le⟩
      obtain ⟨φ, hφ, hφM⟩ := extraction_of_frequently_atTop hfreq
      obtain ⟨t₀, -, ψ, hψ, hlim⟩ :=
        (isCompact_Icc (a := -M) (b := M)).tendsto_subseq (x := fun j => τ (φ j))
          (fun j => Set.mem_Icc.2 (abs_le.1 (hφM j)))
      have h1 : Tendsto (fun j => graftedOrbit hS hB (τ (φ (ψ j)))) atTop
          (nhds (graftedOrbit hS hB t₀)) :=
        ((continuous_graftedOrbit hS hB).continuousAt.tendsto).comp hlim
      have h2 : Tendsto (fun j => graftedOrbit hS hB (τ (φ (ψ j)))) atTop (nhds L) :=
        hτ.comp (hφ.comp hψ).tendsto_atTop
      exact ⟨t₀, tendsto_nhds_unique h1 h2⟩
  · rintro L (⟨t, rfl⟩ | ⟨τ, hinf, hconv⟩)
    · exact ⟨fun _ => t, tendsto_const_nhds⟩
    · exact ⟨τ, hconv.congr_uniformity ((tendsto_uniformity_graftedOrbit hS hB hcollapse).comp
        (tendsto_cocompact_of_abs_atTop hinf))⟩

open GaloisForLFunctions in
/-- **Relative compactness transfers.**  If every real parameter sequence of the shifted background
has a convergent subsequence, so does every parameter sequence of the grafted orbit. -/
theorem exists_subseq_tendsto_graftedOrbit {S B : ℂ → ℂ} (hS : ContinuousOn S {z : ℂ | 0 < z.im})
    (hB : ContinuousOn B {z : ℂ | 0 < z.im}) {c : ℂ}
    (hcollapse : ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 0 < z.im) →
      TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => S (z + (t : ℂ))) (fun _ => c) (cocompact ℝ) K)
    (hseq : ∀ σ : ℕ → ℝ, ∃ L, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun j => shiftedBackground c hB (σ (ψ j))) atTop (nhds L))
    (τ : ℕ → ℝ) :
    ∃ L, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun j => graftedOrbit hS hB (τ (ψ j))) atTop (nhds L) := by
  by_cases hinf : Tendsto (fun j => |τ j|) atTop atTop
  · obtain ⟨L, ψ, hψ, hL⟩ := hseq τ
    refine ⟨L, ψ, hψ, hL.congr_uniformity ?_⟩
    exact (tendsto_uniformity_graftedOrbit hS hB hcollapse).comp
      (tendsto_cocompact_of_abs_atTop (hinf.comp hψ.tendsto_atTop))
  · rw [tendsto_atTop_atTop] at hinf
    push Not at hinf
    obtain ⟨M, hM⟩ := hinf
    have hfreq : ∃ᶠ j in atTop, |τ j| ≤ M := by
      rw [frequently_atTop]
      intro a
      obtain ⟨b, hb, hlt⟩ := hM a
      exact ⟨b, hb, hlt.le⟩
    obtain ⟨φ, hφ, hφM⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨t₀, -, ψ, hψ, hlim⟩ :=
      (isCompact_Icc (a := -M) (b := M)).tendsto_subseq (x := fun j => τ (φ j))
        (fun j => Set.mem_Icc.2 (abs_le.1 (hφM j)))
    exact ⟨graftedOrbit hS hB t₀, φ ∘ ψ, hφ.comp hψ,
      ((continuous_graftedOrbit hS hB).continuousAt.tendsto).comp hlim⟩

end

end GaloisForLFunctions.HTGeometry