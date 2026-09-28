import GaloisForLFunctions.HTGeometry.ClockSeriesDerivative
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Relatively compact real translates on a horizontal strip

A function `f` on the horizontal strip `|Im z| < η` is *uniformly almost periodic* when, on every
closed smaller strip `|Im z| ≤ r`, its real translates `z ↦ f (z + t)` form a relatively compact set
for the uniform distance.  Relative compactness is stated as total boundedness: for every `ε` there
are finitely many translates within `ε` of every translate.

From this hypothesis alone:

* every closed substrip carries relatively dense sets of `ε`-almost periods (a translate close to a
  sample translate differs from the identity by the difference of the two translation times);
* a continuous `f` is bounded on the closed substrip;
* every sequence of real translates has a subsequence converging uniformly on the closed substrip
  (the translates are points of the complete space of bounded continuous functions there);
* **maximum principle for translates**: if `|f|` on the closed substrip never exceeds its supremum on
  the real line, then `f` is constant on the open substrip.  A subsequence of translates realising
  the supremum on the line converges to a holomorphic function attaining its maximum modulus at an
  interior point; that limit is constant, and translation invariance of the uniform distance
  transfers constancy back to `f`.
-/

open Filter Topology Metric Set

namespace GaloisForLFunctions.HTGeometry

/-- The closed horizontal strip of half-width `r`. -/
def closedImStrip (r : ℝ) : Set ℂ := {z : ℂ | |z.im| ≤ r}

theorem mem_closedImStrip {r : ℝ} {z : ℂ} : z ∈ closedImStrip r ↔ |z.im| ≤ r := Iff.rfl

theorem closedImStrip_subset_imStrip {r η : ℝ} (h : r < η) : closedImStrip r ⊆ imStrip η :=
  fun _ hz => lt_of_le_of_lt hz h

theorem imStrip_subset_closedImStrip (r : ℝ) : imStrip r ⊆ closedImStrip r :=
  fun _ hz => mem_closedImStrip.mpr (le_of_lt (mem_imStrip.mp hz))

theorem convex_closedImStrip (r : ℝ) : Convex ℝ (closedImStrip r) := by
  have hEq : closedImStrip r = Complex.imLm ⁻¹' Set.Icc (-r) r := by
    ext z
    exact ⟨fun hz => Set.mem_Icc.mpr (abs_le.mp hz), fun hz => abs_le.mpr (Set.mem_Icc.mp hz)⟩
  rw [hEq]
  exact (convex_Icc (-r) r).linear_preimage Complex.imLm

theorem add_ofReal_mem_closedImStrip {r : ℝ} {z : ℂ} (hz : z ∈ closedImStrip r) (t : ℝ) :
    z + t ∈ closedImStrip r := by
  simpa [mem_closedImStrip] using hz

theorem add_ofReal_mem_imStrip {r : ℝ} {z : ℂ} (hz : z ∈ imStrip r) (t : ℝ) :
    z + t ∈ imStrip r := by
  simpa [mem_imStrip] using hz

/-- The real translates of `f` are totally bounded for the uniform distance on the closed strip of
half-width `r`: for every `ε > 0` finitely many translates are `ε`-close to every translate. -/
def HasCompactImStripTranslates (f : ℂ → ℂ) (r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℝ, ∀ t : ℝ, ∃ s ∈ S, ∀ z : ℂ, |z.im| ≤ r →
    ‖f (z + t) - f (z + s)‖ ≤ ε

/-- Uniform almost periodicity on the strip `|Im z| < η`: relatively compact real translates on
every closed smaller strip. -/
def IsImStripUniformlyAlmostPeriodic (f : ℂ → ℂ) (η : ℝ) : Prop :=
  ∀ r : ℝ, r < η → HasCompactImStripTranslates f r

variable {f : ℂ → ℂ} {r η : ℝ}

theorem HasCompactImStripTranslates.nonempty (h : HasCompactImStripTranslates f r) {ε : ℝ}
    (hε : 0 < ε) : ∃ S : Finset ℝ, S.Nonempty ∧ ∀ t : ℝ, ∃ s ∈ S, ∀ z : ℂ, |z.im| ≤ r →
      ‖f (z + t) - f (z + s)‖ ≤ ε := by
  obtain ⟨S, hS⟩ := h ε hε
  obtain ⟨s, hs, -⟩ := hS 0
  exact ⟨S, ⟨s, hs⟩, hS⟩

/-- **Relatively dense almost periods.**  Every window `[a, a + L]` contains a real `τ` moving `f`
by at most `ε` uniformly on the closed strip. -/
theorem HasCompactImStripTranslates.exists_almostPeriod (h : HasCompactImStripTranslates f r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ, ∃ τ ∈ Icc a (a + L), ∀ z : ℂ, |z.im| ≤ r →
      ‖f (z + τ) - f z‖ ≤ ε := by
  obtain ⟨S, hne, hS⟩ := h.nonempty hε
  set M := S.max' hne with hM
  set m := S.min' hne with hm
  have hmM : m ≤ M := Finset.min'_le S M (Finset.max'_mem S hne)
  refine ⟨M - m + 1, by linarith, fun a => ?_⟩
  obtain ⟨s, hs, hts⟩ := hS (a + M)
  have hsM : s ≤ M := Finset.le_max' S s hs
  have hms : m ≤ s := Finset.min'_le S s hs
  refine ⟨a + M - s, ⟨by linarith, by linarith⟩, fun z hz => ?_⟩
  have hz' : |(z - (s : ℂ)).im| ≤ r := by simpa using hz
  have h1 := hts (z - s) hz'
  have e1 : z - (s : ℂ) + ((a + M : ℝ) : ℂ) = z + ((a + M - s : ℝ) : ℂ) := by push_cast; ring
  have e2 : z - (s : ℂ) + (s : ℂ) = z := by ring
  rwa [e1, e2] at h1

/-- A continuous function with relatively compact translates is bounded on the closed strip. -/
theorem HasCompactImStripTranslates.exists_bound (h : HasCompactImStripTranslates f r)
    (hc : ContinuousOn f (closedImStrip r)) :
    ∃ B : ℝ, ∀ z : ℂ, |z.im| ≤ r → ‖f z‖ ≤ B := by
  obtain ⟨S, hne, hS⟩ := h.nonempty one_pos
  set M := S.max' hne
  set m := S.min' hne
  set K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) '' (Icc m M ×ˢ Icc (-r) r)
    with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hKsub : K ⊆ closedImStrip r := by
    rintro _ ⟨p, hp, rfl⟩
    have him : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
    rw [mem_closedImStrip, him]
    exact abs_le.mpr (Set.mem_Icc.mp hp.2)
  obtain ⟨B₀, hB₀⟩ := hKc.exists_bound_of_continuousOn (hc.mono hKsub)
  refine ⟨B₀ + 1, fun z hz => ?_⟩
  set b : ℂ := (z.im : ℂ) * Complex.I with hb
  have hbim : |b.im| ≤ r := by simpa [hb] using hz
  obtain ⟨s, hs, hts⟩ := hS z.re
  have h1 := hts b hbim
  have hbz : b + (z.re : ℂ) = z := by
    rw [hb, add_comm]; exact Complex.re_add_im z
  rw [hbz] at h1
  have hbs : b + (s : ℂ) ∈ K := by
    refine ⟨(s, z.im), ⟨⟨Finset.min'_le S s hs, Finset.le_max' S s hs⟩, abs_le.mp hz⟩, ?_⟩
    simp [hb, add_comm]
  have h2 := hB₀ _ hbs
  calc ‖f z‖ ≤ ‖f (b + s)‖ + ‖f z - f (b + s)‖ := norm_le_insert' _ _
    _ ≤ B₀ + 1 := by linarith

/-- **Cauchy's estimate on nested closed strips.** -/
theorem norm_deriv_le_of_closedImStrip_bound {r r' B : ℝ} (hr : r < r') (hr' : r' < η)
    (hf : DifferentiableOn ℂ f (imStrip η)) (hB : ∀ z : ℂ, |z.im| ≤ r' → ‖f z‖ ≤ B)
    {z : ℂ} (hz : |z.im| ≤ r) : ‖deriv f z‖ ≤ 2 * B / (r' - r) :=
  norm_deriv_le_on_imStrip hr (hf.mono (imStrip_mono hr'.le))
    (fun w hw => hB w (le_of_lt hw)) hz

/-- **Lipschitz bound on a closed strip** from a bound on a wider closed strip. -/
theorem exists_lipschitz_closedImStrip {r r' : ℝ} (hr : r < r') (hr' : r' < η)
    (hf : DifferentiableOn ℂ f (imStrip η)) {B : ℝ} (hB : ∀ z : ℂ, |z.im| ≤ r' → ‖f z‖ ≤ B) :
    ∀ z w : ℂ, |z.im| ≤ r → |w.im| ≤ r → ‖f w - f z‖ ≤ (2 * B / (r' - r)) * ‖w - z‖ := by
  intro z w hz hw
  refine (convex_closedImStrip r).norm_image_sub_le_of_norm_deriv_le (fun x hx => ?_)
    (fun x hx => norm_deriv_le_of_closedImStrip_bound hr hr' hf hB hx) hz hw
  exact hf.differentiableAt ((isOpen_imStrip η).mem_nhds
    (closedImStrip_subset_imStrip (hr.trans hr') hx))

/-- The translate `z ↦ f (z + t)` as a bounded continuous function on the closed strip. -/
noncomputable def imStripTranslateBCF (hc : ContinuousOn f (closedImStrip r)) {B : ℝ}
    (hB : ∀ z : ℂ, |z.im| ≤ r → ‖f z‖ ≤ B) (t : ℝ) :
    BoundedContinuousFunction (closedImStrip r) ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => f ((z : ℂ) + t), hc.comp_continuous (continuous_subtype_val.add continuous_const)
      fun z => add_ofReal_mem_closedImStrip z.2 t⟩
    (2 * B) fun z w => by
      have h1 := hB _ (add_ofReal_mem_closedImStrip z.2 t)
      have h2 := hB _ (add_ofReal_mem_closedImStrip w.2 t)
      calc dist (f ((z : ℂ) + t)) (f ((w : ℂ) + t))
          ≤ ‖f ((z : ℂ) + t)‖ + ‖f ((w : ℂ) + t)‖ := dist_le_norm_add_norm _ _
        _ ≤ 2 * B := by linarith

theorem imStripTranslateBCF_apply (hc : ContinuousOn f (closedImStrip r)) {B : ℝ}
    (hB : ∀ z : ℂ, |z.im| ≤ r → ‖f z‖ ≤ B) (t : ℝ) (z : closedImStrip r) :
    imStripTranslateBCF hc hB t z = f ((z : ℂ) + t) := rfl

/-- **Sequential compactness of real translates.**  Every sequence of real translates has a
subsequence converging uniformly on the closed strip. -/
theorem HasCompactImStripTranslates.exists_subseq_tendstoUniformlyOn
    (h : HasCompactImStripTranslates f r) (hc : ContinuousOn f (closedImStrip r)) (x : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ,
      TendstoUniformlyOn (fun n z => f (z + x (φ n))) g atTop (closedImStrip r) := by
  classical
  obtain ⟨B, hB⟩ := h.exists_bound hc
  set T := imStripTranslateBCF hc hB with hT
  have htb : TotallyBounded (range T) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨S, hS⟩ := h (ε / 2) (by linarith)
    refine ⟨T '' S, S.finite_toSet.image T, ?_⟩
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, hs, hts⟩ := hS t
    refine mem_iUnion₂.mpr ⟨T s, mem_image_of_mem T hs, ?_⟩
    rw [mem_ball]
    refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (C := ε / 2) (by linarith)).mpr
      fun z => ?_) (by linarith)
    rw [dist_eq_norm]
    show ‖f ((z : ℂ) + t) - f ((z : ℂ) + s)‖ ≤ ε / 2
    exact hts z z.2
  have hK : IsCompact (closure (range T)) :=
    isCompact_iff_totallyBounded_isComplete.mpr ⟨htb.closure, isClosed_closure.isComplete⟩
  obtain ⟨G, -, φ, hφ, hlim⟩ :=
    hK.tendsto_subseq (x := fun n => T (x n)) fun n => subset_closure (mem_range_self _)
  refine ⟨φ, hφ, fun z => if hz : z ∈ closedImStrip r then G ⟨z, hz⟩ else 0, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp hlim) ε hε
  filter_upwards [hev] with n hn z hz
  rw [dif_pos hz, dist_comm]
  exact lt_of_le_of_lt
    (BoundedContinuousFunction.dist_coe_le_dist (f := T (x (φ n))) (g := G) ⟨z, hz⟩) hn

/-- **Maximum principle for translates.**  If the modulus of `f` on the closed strip never exceeds
its supremum on the real line, `f` is constant on the open strip. -/
theorem HasCompactImStripTranslates.exists_const_of_norm_le_iSup
    (h : HasCompactImStripTranslates f r) (hr0 : 0 < r) (hr : r < η)
    (hf : DifferentiableOn ℂ f (imStrip η)) (hbdd : BddAbove (range fun x : ℝ => ‖f x‖))
    (hle : ∀ z : ℂ, |z.im| ≤ r → ‖f z‖ ≤ ⨆ x : ℝ, ‖f x‖) :
    ∃ c : ℂ, ∀ z ∈ imStrip r, f z = c := by
  set M₀ := ⨆ x : ℝ, ‖f x‖ with hM₀
  have hc : ContinuousOn f (closedImStrip r) :=
    hf.continuousOn.mono (closedImStrip_subset_imStrip hr)
  obtain ⟨u, -, hu, humem⟩ := exists_seq_tendsto_sSup (range_nonempty fun x : ℝ => ‖f x‖) hbdd
  choose x hx using humem
  obtain ⟨φ, hφ, g, hg⟩ := h.exists_subseq_tendstoUniformlyOn hc x
  have hgo : TendstoUniformlyOn (fun n z => f (z + x (φ n))) g atTop (imStrip r) :=
    hg.mono (imStrip_subset_closedImStrip r)
  have hgd : DifferentiableOn ℂ g (imStrip r) := by
    refine TendstoLocallyUniformlyOn.differentiableOn hgo.tendstoLocallyUniformlyOn
      (Eventually.of_forall fun n => ?_) (isOpen_imStrip r)
    intro z hz
    have hzη : z + x (φ n) ∈ imStrip η :=
      imStrip_mono hr.le (add_ofReal_mem_imStrip hz _)
    exact ((hf.differentiableAt ((isOpen_imStrip η).mem_nhds hzη)).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hgle : ∀ z ∈ imStrip r, ‖g z‖ ≤ M₀ := by
    intro z hz
    refine le_of_tendsto ((hgo.tendsto_at hz).norm) (Eventually.of_forall fun n => ?_)
    exact hle _ (by simpa using (le_of_lt hz : |z.im| ≤ r))
  have h0 : (0 : ℂ) ∈ imStrip r := by simpa [mem_imStrip] using hr0
  have hg0 : ‖g 0‖ = M₀ := by
    have ht := (hgo.tendsto_at h0).norm
    have hsub : Tendsto (fun n => ‖f (0 + (x (φ n) : ℂ))‖) atTop (𝓝 M₀) := by
      have : (fun n => ‖f (0 + (x (φ n) : ℂ))‖) = u ∘ φ := by
        funext n; simp [hx]
      rw [this, hM₀, iSup]
      exact hu.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique ht hsub
  have hmax : IsMaxOn (norm ∘ g) (imStrip r) 0 := by
    intro z hz
    simp only [mem_setOf_eq, Function.comp_apply, hg0]
    exact hgle z hz
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (isPreconnected_imStrip r)
    (isOpen_imStrip r) hgd h0 hmax
  refine ⟨g 0, fun w hw => ?_⟩
  refine eq_of_forall_dist_le fun ε hε => ?_
  rw [Metric.tendstoUniformlyOn_iff] at hgo
  obtain ⟨n, hn⟩ := (hgo ε hε).exists
  have hwn : w - x (φ n) ∈ imStrip r := by
    simpa [mem_imStrip] using hw
  have h1 := hn _ hwn
  rw [hconst hwn, Function.const_apply, sub_add_cancel, dist_comm] at h1
  exact h1.le

end GaloisForLFunctions.HTGeometry
