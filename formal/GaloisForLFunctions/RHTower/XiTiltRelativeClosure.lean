import GaloisForLFunctions.RHTower.XiTiltPuncturedMonodromy
import GaloisForLFunctions.HTGeometry.RootLocusOverCovering
import GaloisForLFunctions.HTGeometry.RootBranchPolynomial
import GaloisForLFunctions.HTGeometry.TranscendentalMonicRelation
import GaloisForLFunctions.HTGeometry.MeromorphicPlaneAlgebra
import GaloisForLFunctions.HTGeometry.CoveringComponentRestriction
import GaloisForLFunctions.RHTower.XiPolynomialLeftFactors
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# The tilted Xi coordinate is relatively algebraically closed

Let `d = d_a = ξ e^{-as}` in the field `M(ℂ)` of global meromorphic functions.  Every meromorphic
`g` algebraic over `ℂ(d)` lies in `ℂ(d)`.

After clearing denominators, `G = y(d) g` is an entire root of a monic `P(d, ·)` whose fibre
discriminant vanishes only on a finite set `B`.  The root locus of `P` over `V = ℂ ∖ ({0} ∪ B)` is a
finite covering, and `s ↦ (d(s), G(s))` is a section of its pullback over `U = d⁻¹(V)` landing in
one connected component `Y₀`.  The finite-cover monodromy theorem makes the pullback of `Y₀`
connected; a section of a covering has open and closed image, so the whole pullback is the
graph of the section.  Since `d` takes every nonzero value, every fibre of `Y₀` is one point and
`Y₀` is the graph of a continuous root branch on `V`, which is a polynomial `Q`.  Thus
`G = Q(d)` and `g = Q(d)/y(d)`.
-/

open Set Filter Topology Polynomial
open GaloisForLFunctions.HTGeometry RHTower.XiMarkedMonodromy
open scoped IntermediateField

namespace RHTower.XiTiltMonodromy

noncomputable section

/-- `d_a` in the global meromorphic field. -/
def tiltElement (a : ℝ) : MeromorphicPlane :=
  ofMeromorphic (value a) (fun z => ((value_differentiable a).analyticAt z).meromorphicAt)

theorem aeval_tiltElement (a : ℝ) (q : ℂ[X]) :
    aeval (tiltElement a) q = ofMeromorphic (fun s => q.eval (value a s))
      (fun z => ((q.differentiable.comp (value_differentiable a)).analyticAt z).meromorphicAt) :=
  aeval_ofMeromorphic q _

/-- An entire function that vanishes in the meromorphic field vanishes everywhere. -/
private theorem eq_zero_of_ofMeromorphic_eq_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h : ofMeromorphic F (fun z => (hF.analyticAt z).meromorphicAt) = 0) (z : ℂ) : F z = 0 := by
  have h0 : (0 : MeromorphicPlane) = ofMeromorphic (fun _ => (0 : ℂ))
      (fun z => MeromorphicAt.const 0 z) := rfl
  rw [h0, ofMeromorphic_eq_iff] at h
  exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hF.continuous.continuousAt continuousAt_const).mp (h z)).eq_of_nhds

/-- `d_a` is transcendental over `ℂ`: it takes every nonzero value. -/
theorem tiltElement_transcendental (a : ℝ) : Transcendental ℂ (tiltElement a) := by
  rintro ⟨q, hq0, hq⟩
  rw [aeval_tiltElement] at hq
  have hz := eq_zero_of_ofMeromorphic_eq_zero
    (q.differentiable.comp (value_differentiable a)) hq
  have hfin : (q.roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
  obtain ⟨c, hc, hc0⟩ : ∃ c : ℂ, c ∉ (q.roots.toFinset : Set ℂ) ∧ c ≠ 0 := by
    have hinf : (({0} : Set ℂ)ᶜ).Infinite := (Set.finite_singleton 0).infinite_compl
    obtain ⟨c, hc, hcr⟩ := (hinf.sdiff hfin).nonempty
    exact ⟨c, hcr, hc⟩
  obtain ⟨s, -, hs⟩ := exists_xi_tilt_eq_of_nonzero a 1 le_rfl hc0
  apply hc
  have := hz s
  simp only [Function.comp_apply] at this
  change q.eval (xi s * Complex.exp (-(a : ℂ) * s)) = 0 at this
  rw [hs] at this
  simpa [Polynomial.mem_roots hq0] using this

private theorem ofMeromorphic_congr {f g : ℂ → ℂ} (hfg : f = g) (hf : ∀ z, MeromorphicAt f z)
    (hg : ∀ z, MeromorphicAt g z) : ofMeromorphic f hf = ofMeromorphic g hg := by
  subst hfg; rfl

private theorem ofMeromorphic_pow {h : ℂ → ℂ} (hh : ∀ z, MeromorphicAt h z) (n : ℕ) :
    ofMeromorphic h hh ^ n = ofMeromorphic (fun s => h s ^ n) (fun z => (hh z).pow n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    apply MeromorphicPlane.germ_injective
    rw [germ_one, germ_ofMeromorphic]
    rfl
  | succ n ih =>
    rw [pow_succ, ih, ofMeromorphic_mul]
    exact ofMeromorphic_congr (funext fun s => (pow_succ (h s) n).symm) _ _

theorem biEval_add' (p q : ℂ[X][X]) (x : ℂ × ℂ) : biEval (p + q) x = biEval p x + biEval q x := by
  simp [biEval, Polynomial.eval₂_add]

theorem biEval_monomial' (n : ℕ) (c : ℂ[X]) (x : ℂ × ℂ) :
    biEval (Polynomial.monomial n c) x = c.eval x.1 * x.2 ^ n := by
  simp [biEval, Polynomial.eval₂_monomial]

theorem meromorphicAt_biEval_comp (a : ℝ) (P : ℂ[X][X]) {h : ℂ → ℂ}
    (hh : ∀ z, MeromorphicAt h z) (z : ℂ) :
    MeromorphicAt (fun s => biEval P (value a s, h s)) z := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [biEval_add']
    exact hp.add hq
  | monomial n c =>
    simp only [biEval_monomial']
    exact (((c.differentiable.comp (value_differentiable a)).analyticAt z).meromorphicAt).mul
      ((hh z).pow n)

/-- Two-variable evaluation at germs is the germ of pointwise two-variable evaluation. -/
theorem evalAt₂_tiltElement (a : ℝ) (P : ℂ[X][X]) {h : ℂ → ℂ} (hh : ∀ z, MeromorphicAt h z) :
    evalAt₂ (tiltElement a) P (ofMeromorphic h hh) =
      ofMeromorphic (fun s => biEval P (value a s, h s)) (meromorphicAt_biEval_comp a P hh) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [evalAt₂, Polynomial.map_add, Polynomial.eval_add]
    change evalAt₂ _ p _ + evalAt₂ _ q _ = _
    rw [hp, hq, ofMeromorphic_add]
    exact ofMeromorphic_congr (funext fun s => (biEval_add' p q _).symm) _ _
  | monomial n c =>
    rw [evalAt₂, Polynomial.map_monomial, Polynomial.eval_monomial]
    change aeval (tiltElement a) c * _ = _
    rw [aeval_tiltElement, ofMeromorphic_pow, ofMeromorphic_mul]
    exact ofMeromorphic_congr (funext fun s => (biEval_monomial' n c (value a s, h s)).symm) _ _

/-- **Entire representative.**  An element satisfying a monic relation over `ℂ[d]` is entire. -/
theorem exists_entire_rep_of_monic (a : ℝ) {P : ℂ[X][X]} (hP : P.Monic) (hdeg : 0 < P.natDegree)
    {x : MeromorphicPlane} (hx : evalAt₂ (tiltElement a) P x = 0) :
    ∃ (G : ℂ → ℂ) (hG : Differentiable ℂ G),
      ofMeromorphic G (fun z => (hG.analyticAt z).meromorphicAt) = x ∧
        ∀ s, biEval P (value a s, G s) = 0 := by
  obtain ⟨h, hh, rfl⟩ := x.exists_rep
  rw [evalAt₂_tiltElement] at hx
  have h0 : (0 : MeromorphicPlane) =
      ofMeromorphic (fun _ => (0 : ℂ)) (fun z => MeromorphicAt.const 0 z) := rfl
  rw [h0, ofMeromorphic_eq_iff] at hx
  have hord : ∀ z, 0 ≤ meromorphicOrderAt h z := by
    intro z
    by_contra hneg
    push Not at hneg
    have ht := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
    set M := cauchyBound P (value a z) + 1
    have hev1 : ∀ᶠ s in 𝓝[≠] z, M < ‖h s‖ :=
      (tendsto_norm_atTop_iff_cobounded.mpr ht).eventually_gt_atTop M
    have hc : ContinuousAt (fun s => cauchyBound P (value a s)) z :=
      ((continuous_cauchyBound P).comp (value_differentiable a).continuous).continuousAt
    have hev2 : ∀ᶠ s in 𝓝[≠] z, cauchyBound P (value a s) < M :=
      nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (lt_add_one _)))
    obtain ⟨s, h1, h2, h3⟩ := (hev1.and (hev2.and (hx z))).exists
    have := norm_le_cauchyBound hP hdeg (t := value a s) (w := h s) h3
    linarith
  let G := toMeromorphicNFOn h Set.univ
  have hfon : MeromorphicOn h Set.univ := fun z _ => hh z
  have hGeq (z : ℂ) : G =ᶠ[𝓝[≠] z] h :=
    hfon.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have han (z : ℂ) : AnalyticAt ℂ G z := by
    apply ((meromorphicNFOn_toMeromorphicNFOn h Set.univ)
      (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hfon (Set.mem_univ z)]
    exact hord z
  have hGd : Differentiable ℂ G := fun z => (han z).differentiableAt
  refine ⟨G, hGd, (ofMeromorphic_eq_iff _ hh).mpr hGeq, fun z => ?_⟩
  have hcont : ContinuousAt (fun s => biEval P (value a s, G s)) z :=
    ((continuous_biEval P).comp ((value_differentiable a).continuous.prodMk
      hGd.continuous)).continuousAt
  have he : (fun s => biEval P (value a s, G s)) =ᶠ[𝓝[≠] z] fun _ => (0 : ℂ) := by
    filter_upwards [hGeq z, hx z] with s hs hr
    rw [hs]; exact hr
  exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcont
    continuousAt_const).mp he).eq_of_nhds

/-- Every nonzero value outside the puncture set is taken on the source. -/
theorem exists_psource_of_ptarget (a : ℝ) (B : Finset ℂ) (t : PTarget B) :
    ∃ s : PSource a B, ptilt a B s = t := by
  obtain ⟨s, -, hs⟩ := exists_xi_tilt_eq_of_nonzero a 1 le_rfl t.2.1
  have hval : value a s = t := hs
  have hsrc : s ∈ psourceSet a B := by
    refine ⟨fun h0 => t.2.1 ?_, fun c hc _ hvc => t.2.2 ?_⟩
    · rw [← hval, value, h0, zero_mul]
    · rw [← hval, hvc]; exact hc
  exact ⟨⟨s, hsrc⟩, Subtype.ext hval⟩

/-- **Relative algebraic closedness.**  A global meromorphic function algebraic over `ℂ(d_a)` lies
in `ℂ(d_a)`. -/
theorem mem_adjoin_of_isAlgebraic (a : ℝ) {g : MeromorphicPlane}
    (hg : IsAlgebraic ℂ⟮tiltElement a⟯ g) : g ∈ ℂ⟮tiltElement a⟯ := by
  classical
  obtain ⟨y, P, hy0, hmon, hdeg, hres, hrel⟩ :=
    exists_monic_separable_relation (tiltElement_transcendental a) hg
  obtain ⟨G, hGd, hGx, hGroot⟩ := exists_entire_rep_of_monic a hmon hdeg hrel
  set B : Finset ℂ := (biResultant P).roots.toFinset with hB
  have hsepB : ∀ t, t ∉ B → (biFibre P t).Separable := by
    intro t ht
    have hne : (biResultant P).eval t ≠ 0 := by
      intro h0
      apply ht
      rw [hB, Multiset.mem_toFinset, Polynomial.mem_roots hres]
      exact h0
    rw [biResultant_eval hmon t] at hne
    exact (separable_iff_resultant_ne_zero (biFibre_monic hmon t)).mpr hne
  set V : Set ℂ := {t | t ≠ 0 ∧ t ∉ B} with hV
  have hVopen : IsOpen V := ptarget_isOpen B
  have hcov : IsCoveringMap (rootProjOver (f := P) (V := V)) :=
    isCoveringMap_rootProjOver hmon hdeg hVopen (fun t ht => hsepB t ht.2)
  haveI : LocallyPathConnectedSpace V := hVopen.locallyPathConnectedSpace
  haveI : LocallyPathConnectedSpace (RootLocusOver P V) :=
    locallyPathConnectedSpace_of_isCoveringMap hcov
  -- the section `s ↦ (d(s), G(s))`
  let σ : C(PSource a B, RootLocusOver P V) :=
    ⟨fun s => ⟨(value a s, G s), hGroot s, (ptilt a B s).2⟩,
      (((value_differentiable a).continuous.comp continuous_subtype_val).prodMk
        (hGd.continuous.comp continuous_subtype_val)).subtype_mk _⟩
  set Y₀ := connectedComponent (σ (pbase a B))
  have hcov₀ := isCoveringMap_connectedComponent hcov (σ (pbase a B))
  haveI : ConnectedSpace Y₀ := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let p₀ : Y₀ → PTarget B := fun y => rootProjOver (y : RootLocusOver P V)
  have hcovp : IsCoveringMap p₀ := hcov₀
  have hfin : ∀ x, Finite (p₀ ⁻¹' {x}) := by
    intro x
    haveI := finite_fibre_rootProjOver (f := P) (V := V) hmon x
    refine Finite.of_injective (β := (rootProjOver (f := P) (V := V)) ⁻¹' {x})
      (fun y => ⟨(y.1 : RootLocusOver P V), y.2⟩) ?_
    intro y₁ y₂ h
    exact Subtype.ext (Subtype.ext (congrArg (fun z => (z.1 : RootLocusOver P V)) h))
  have hZ := ptiltPullback_isPathConnected a B hcovp hfin
  -- the section lands in `Y₀`
  have hσ₀mem : ∀ s, σ s ∈ Y₀ := fun s =>
    (isPreconnected_range σ.continuous).subset_connectedComponent (mem_range_self _)
      (mem_range_self s)
  let σ₀ : PSource a B → Y₀ := fun s => ⟨σ s, hσ₀mem s⟩
  have hσ₀c : Continuous σ₀ := σ.continuous.subtype_mk _
  have hσ₀p : ∀ s, p₀ (σ₀ s) = ptilt a B s := fun s => rfl
  -- the pullback is the graph of the section
  have hgraph : ∀ (s : PSource a B) (yy : Y₀), ptilt a B s = p₀ yy → yy = σ₀ s := by
    haveI : PreconnectedSpace (ptiltPullback a B p₀) :=
      isPreconnected_iff_preconnectedSpace.mp hZ.isConnected.isPreconnected
    let T : Set (ptiltPullback a B p₀) := {z | z.1.2 = σ₀ z.1.1}
    have hTclosed : IsClosed T :=
      isClosed_eq (continuous_snd.comp continuous_subtype_val)
        (hσ₀c.comp (continuous_fst.comp continuous_subtype_val))
    have hTopen : IsOpen T := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      obtain ⟨U, hU, hzU, hinjU⟩ := hcovp.isLocalHomeomorph.isLocallyInjective z.1.2
      have h1 : ∀ᶠ w in 𝓝 z, (w.1.2 : Y₀) ∈ U :=
        (continuous_snd.comp continuous_subtype_val).continuousAt.preimage_mem_nhds
          (hU.mem_nhds hzU)
      have h2 : ∀ᶠ w in 𝓝 z, σ₀ (w.1.1) ∈ U := by
        have hz' : σ₀ z.1.1 ∈ U := by
          have : z.1.2 = σ₀ z.1.1 := hz
          rw [← this]; exact hzU
        exact (hσ₀c.comp (continuous_fst.comp continuous_subtype_val)).continuousAt
          |>.preimage_mem_nhds (hU.mem_nhds hz')
      filter_upwards [h1, h2] with w hw1 hw2
      exact hinjU hw1 hw2 (by rw [hσ₀p]; exact w.2.symm)
    have hTne : T.Nonempty :=
      ⟨⟨(pbase a B, σ₀ (pbase a B)), (hσ₀p _).symm⟩, rfl⟩
    have hTuniv := IsClopen.eq_univ ⟨hTclosed, hTopen⟩ hTne
    intro s yy hsy
    have hmem : (⟨(s, yy), hsy⟩ : ptiltPullback a B p₀) ∈ T := by rw [hTuniv]; trivial
    exact hmem
  -- every fibre of `Y₀` is one point
  have hsurj : Function.Surjective p₀ := by
    intro t
    obtain ⟨s, hs⟩ := exists_psource_of_ptarget a B t
    exact ⟨σ₀ s, (hσ₀p s).trans hs⟩
  have hinj : Function.Injective p₀ := by
    intro y₁ y₂ h
    obtain ⟨s, hs⟩ := exists_psource_of_ptarget a B (p₀ y₁)
    rw [hgraph s y₁ hs, hgraph s y₂ (hs.trans h)]
  let e : Y₀ ≃ₜ PTarget B :=
    (Equiv.ofBijective p₀ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcovp.continuous
      hcovp.isLocalHomeomorph.isOpenMap
  have he_symm : ∀ s : PSource a B, e.symm (ptilt a B s) = σ₀ s := by
    intro s
    rw [Homeomorph.symm_apply_eq]
    exact (hσ₀p s).symm
  -- the root branch
  let φ : ℂ → ℂ := fun t => if ht : t ≠ 0 ∧ t ∉ B then
    (((e.symm ⟨t, ht⟩ : Y₀) : RootLocusOver P V) : ℂ × ℂ).2 else 0
  have hfst : ∀ (t : ℂ) (ht : t ≠ 0 ∧ t ∉ B),
      (((e.symm ⟨t, ht⟩ : Y₀) : RootLocusOver P V) : ℂ × ℂ).1 = t := by
    intro t ht
    have := congrArg Subtype.val (e.apply_symm_apply ⟨t, ht⟩)
    exact this
  have hnotin : ∀ t, t ∉ insert 0 B → t ≠ 0 ∧ t ∉ B := by
    intro t ht
    simp only [Finset.mem_insert, not_or] at ht
    exact ht
  have hφroot : ∀ t, t ∉ insert 0 B → biEval P (t, φ t) = 0 := by
    intro t ht
    have ht' := hnotin t ht
    have hq := (((e.symm ⟨t, ht'⟩ : Y₀) : RootLocusOver P V)).2.1
    simp only [φ, dif_pos ht']
    have hpair : (t, (((e.symm ⟨t, ht'⟩ : Y₀) : RootLocusOver P V) : ℂ × ℂ).2) =
        (((e.symm ⟨t, ht'⟩ : Y₀) : RootLocusOver P V) : ℂ × ℂ) :=
      Prod.ext (hfst t ht').symm rfl
    rw [hpair]
    exact hq
  have hφc : ContinuousOn φ ((insert 0 B : Finset ℂ) : Set ℂ)ᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous (fun t : ↥(((insert 0 B : Finset ℂ) : Set ℂ)ᶜ) =>
        (((e.symm ⟨t, hnotin t t.2⟩ : Y₀) : RootLocusOver P V) : ℂ × ℂ).2) :=
      continuous_snd.comp (continuous_subtype_val.comp (continuous_subtype_val.comp
        (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))))
    refine hc.congr fun t => ?_
    simp only [Set.restrict_apply, φ, dif_pos (hnotin t t.2)]
  obtain ⟨Q, hQ⟩ := exists_polynomial_of_root_branch hmon hdeg (insert 0 B)
    (fun t ht => hsepB t (hnotin t ht).2) hφc hφroot
  have hGQ : ∀ s : PSource a B, G s = Q.eval (value a s) := by
    intro s
    have hvs : value a s ∉ insert 0 B := by
      simp only [Finset.mem_insert, not_or]
      exact (ptilt a B s).2
    rw [← hQ _ hvs]
    have hpt : (⟨value a s, hnotin _ hvs⟩ : PTarget B) = ptilt a B s := rfl
    simp only [φ, dif_pos (hnotin _ hvs), hpt, he_symm]
    rfl
  have hall : G = fun s => Q.eval (value a s) := by
    have hU : psourceSet a B ∈ 𝓝 ((pbase a B : ℂ)) :=
      (isOpen_psourceSet a B).mem_nhds (pbase a B).2
    have heq : G =ᶠ[𝓝 ((pbase a B : ℂ))] fun s => Q.eval (value a s) := by
      filter_upwards [hU] with s hs using hGQ ⟨s, hs⟩
    exact AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hGd.analyticAt z)
      (fun z _ => (Q.differentiable.comp (value_differentiable a)).analyticAt z) heq
  have hk : aeval (tiltElement a) y * g = aeval (tiltElement a) Q := by
    rw [← hGx, aeval_tiltElement]
    exact ofMeromorphic_congr hall _ _
  rw [IntermediateField.mem_adjoin_simple_iff]
  exact ⟨Q, y, by rw [← hk]; field_simp⟩

/-- Monic factors over `M(ℂ)` of monic polynomials over `ℂ(d_a)` are defined over `ℂ(d_a)`. -/
theorem exists_lift_of_monic_dvd (a : ℝ) {p : (ℂ⟮tiltElement a⟯)[X]} (hp : p.Monic)
    {q : MeromorphicPlane[X]} (hq : q.Monic)
    (hdvd : q ∣ p.map (algebraMap ℂ⟮tiltElement a⟯ MeromorphicPlane)) :
    ∃ q₁ : (ℂ⟮tiltElement a⟯)[X], q₁.map (algebraMap ℂ⟮tiltElement a⟯ MeromorphicPlane) = q := by
  have hmem : ∀ i, q.coeff i ∈ ℂ⟮tiltElement a⟯ := fun i =>
    mem_adjoin_of_isAlgebraic a
      (Polynomial.isIntegral_coeff_of_dvd p q hp hq hdvd i).isAlgebraic
  have hlifts : q ∈ Polynomial.lifts (algebraMap ℂ⟮tiltElement a⟯ MeromorphicPlane) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hmem i⟩, rfl⟩
  obtain ⟨q₁, hq₁⟩ := hlifts
  exact ⟨q₁, hq₁⟩

/-- **Irreducibility is preserved.**  An irreducible polynomial over `ℂ(d_a)` stays irreducible over
the field of global meromorphic functions. -/
theorem irreducible_map_of_irreducible (a : ℝ) {p : (ℂ⟮tiltElement a⟯)[X]} (hp : Irreducible p) :
    Irreducible (p.map (algebraMap ℂ⟮tiltElement a⟯ MeromorphicPlane)) := by
  classical
  set ι := algebraMap ℂ⟮tiltElement a⟯ MeromorphicPlane
  have hι : Function.Injective ι := ι.injective
  have hp0 : p ≠ 0 := hp.ne_zero
  set c := p.leadingCoeff
  have hc : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  set pm := p * Polynomial.C c⁻¹
  have hpm : pm.Monic := Polynomial.monic_mul_leadingCoeff_inv hp0
  have hassoc : Associated p pm :=
    associated_mul_unit_right p _
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hc)))
  have hpmirr : Irreducible pm := hassoc.irreducible hp
  have hmapassoc : Associated (pm.map ι) (p.map ι) := by
    have : pm.map ι = p.map ι * Polynomial.C (ι c⁻¹) := by
      rw [Polynomial.map_mul, Polynomial.map_C]
    rw [this]
    exact (associated_mul_unit_right _ _ (Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr ((map_ne_zero ι).mpr (inv_ne_zero hc))))).symm
  refine hmapassoc.irreducible ?_
  have hpmK : (pm.map ι).Monic := hpm.map ι
  have hmapinj : Function.Injective (Polynomial.map ι) := Polynomial.map_injective ι hι
  have hne1 : pm.map ι ≠ 1 := by
    intro h1
    apply hpmirr.not_isUnit
    have : pm = 1 := hmapinj (by rw [h1, Polynomial.map_one])
    rw [this]; exact isUnit_one
  rw [Polynomial.irreducible_of_monic hpmK hne1]
  intro f g hf hg hfg
  obtain ⟨f₁, hf₁⟩ := exists_lift_of_monic_dvd a hpm hf ⟨g, hfg.symm⟩
  obtain ⟨g₁, hg₁⟩ := exists_lift_of_monic_dvd a hpm hg ⟨f, by rw [mul_comm]; exact hfg.symm⟩
  have hmon_of : ∀ {u : (ℂ⟮tiltElement a⟯)[X]} {v : MeromorphicPlane[X]},
      u.map ι = v → v.Monic → u.Monic := by
    intro u v huv hv
    have h := Polynomial.leadingCoeff_map_of_injective hι u
    rw [huv, hv.leadingCoeff] at h
    exact hι (by rw [← h, map_one])
  have hf₁m := hmon_of hf₁ hf
  have hg₁m := hmon_of hg₁ hg
  have hprod : f₁ * g₁ = pm := hmapinj (by rw [Polynomial.map_mul, hf₁, hg₁, hfg])
  have hpm1 : pm ≠ 1 := fun h1 => hpmirr.not_isUnit (by rw [h1]; exact isUnit_one)
  rcases (Polynomial.irreducible_of_monic hpm hpm1).mp hpmirr f₁ g₁ hf₁m hg₁m hprod with h | h
  · left; rw [← hf₁, h, Polynomial.map_one]
  · right; rw [← hg₁, h, Polynomial.map_one]

end

end RHTower.XiTiltMonodromy
