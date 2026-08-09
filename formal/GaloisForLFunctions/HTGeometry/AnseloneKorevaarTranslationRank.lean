import GaloisForLFunctions.HTGeometry.RealConstantCoefficientAnnihilator

/-!
# Finite translation rank is exponential-polynomial type

For a function `f : ℝ → ℂ` write `τ_a f` for the translate `x ↦ f (x − a)` and let
`translationSpan f` be the `ℂ`-linear span of all translates of `f`.  Its dimension is the
*translation rank* of `f`.

The theorem of Anselone and Korevaar is that a continuous function of finite translation rank is
an exponential polynomial, and conversely:

* `differentiable_of_mem_translationSpan` — finite rank plus continuity already forces
  differentiability.  Integrating the coordinate functions of the translate family produces the
  differences `P − τ_ε P` of a primitive `P` of `f`; these lie in the span, and their coordinate
  vectors span it because the coordinate curve is their derivative.
* `deriv_mem_translationSpan` — a finite-dimensional subspace of `ℝ → ℂ` is closed for pointwise
  convergence, so difference quotients of its members converge inside it.
* `contDiff_of_mem_translationSpan` — hence every member is smooth.
* `exists_nonzero_realConstCoeffOp_of_finrank` — the jets of `f` then lie in a finite-dimensional
  space, so they satisfy a nonzero constant-coefficient linear relation.
* `mem_expPolySpace_iff_finiteDimensional_translationSpan` — the resulting equivalence
  `rank_tr f < ∞ ↔ f is a continuous exponential polynomial`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators
open Filter Topology

/-! ## Translation and the translation span -/

/-- Translation of a function on the real line, `τ_a f (x) = f (x − a)`. -/
def realTranslate (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun x => f (x - a)

theorem realTranslate_apply (a : ℝ) (f : ℝ → ℂ) (x : ℝ) : realTranslate a f x = f (x - a) := rfl

theorem realTranslate_zero (f : ℝ → ℂ) : realTranslate 0 f = f := by
  funext x; simp [realTranslate]

theorem realTranslate_realTranslate (a b : ℝ) (f : ℝ → ℂ) :
    realTranslate a (realTranslate b f) = realTranslate (a + b) f := by
  funext x; simp [realTranslate, sub_sub]

/-- Translation as a linear endomorphism of the function space. -/
def realTranslateLM (a : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun := realTranslate a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem realTranslateLM_apply (a : ℝ) (f : ℝ → ℂ) : realTranslateLM a f = realTranslate a f := rfl

/-- The span of all translates of `f`; its dimension is the translation rank of `f`. -/
def translationSpan (f : ℝ → ℂ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (Set.range fun a : ℝ => realTranslate a f)

theorem realTranslate_mem_translationSpan (f : ℝ → ℂ) (a : ℝ) :
    realTranslate a f ∈ translationSpan f := Submodule.subset_span ⟨a, rfl⟩

theorem self_mem_translationSpan (f : ℝ → ℂ) : f ∈ translationSpan f := by
  have h := realTranslate_mem_translationSpan f 0
  rwa [realTranslate_zero] at h

/-- The translation span is translation invariant. -/
theorem realTranslate_mem_of_mem_translationSpan {f g : ℝ → ℂ} (hg : g ∈ translationSpan f)
    (a : ℝ) : realTranslate a g ∈ translationSpan f := by
  have hmap : Submodule.map (realTranslateLM a) (translationSpan f) ≤ translationSpan f := by
    rw [translationSpan, Submodule.map_span, Submodule.span_le]
    rintro u ⟨v, ⟨c, rfl⟩, rfl⟩
    rw [realTranslateLM_apply, realTranslate_realTranslate]
    exact realTranslate_mem_translationSpan f _
  exact hmap ⟨g, hg, rfl⟩

theorem continuous_of_mem_translationSpan {f : ℝ → ℂ} (hf : Continuous f) {g : ℝ → ℂ}
    (hg : g ∈ translationSpan f) : Continuous g := by
  induction hg using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, rfl⟩ := hu
      exact hf.comp (continuous_id.sub continuous_const)
  | zero => exact continuous_const
  | add u v _ _ hu hv => exact hu.add hv
  | smul c u _ hu => exact hu.const_smul c

/-! ## Separating evaluation points for a finite-dimensional function space -/

private theorem exists_eval_separating_aux :
    ∀ (d : ℕ) (V : Submodule ℂ (ℝ → ℂ)), FiniteDimensional ℂ V → Module.finrank ℂ V ≤ d →
      ∃ (n : ℕ) (x : Fin n → ℝ), ∀ v ∈ V, (∀ k, v (x k) = 0) → v = 0 := by
  intro d
  induction d with
  | zero =>
      intro V hV hle
      have hbot : V = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hle)
      exact ⟨0, Fin.elim0, fun v hv _ => by rw [hbot] at hv; simpa using hv⟩
  | succ d ih =>
      intro V hV hle
      by_cases hbot : V = ⊥
      · exact ⟨0, Fin.elim0, fun v hv _ => by rw [hbot] at hv; simpa using hv⟩
      obtain ⟨v₀, hv₀V, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, v₀ x₀ ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hv₀ (funext hc)
      set W : Submodule ℂ (ℝ → ℂ) :=
        V ⊓ LinearMap.ker (LinearMap.proj x₀ : (ℝ → ℂ) →ₗ[ℂ] ℂ) with hWdef
      have hWle : W ≤ V := inf_le_left
      haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWle
      have hWlt : W < V := by
        refine lt_of_le_of_ne hWle ?_
        intro hEq
        apply hx₀
        have hv₀W : v₀ ∈ W := by rw [hEq]; exact hv₀V
        exact hv₀W.2
      have hWrank : Module.finrank ℂ W ≤ d := by
        have hlt := Submodule.finrank_lt_finrank_of_lt hWlt
        omega
      obtain ⟨m, x, hx⟩ := ih W inferInstance hWrank
      refine ⟨m + 1, Fin.cons x₀ x, ?_⟩
      intro v hvV hzero
      have h0 : v x₀ = 0 := by simpa using hzero 0
      have hvW : v ∈ W := ⟨hvV, h0⟩
      refine hx v hvW ?_
      intro k
      simpa using hzero k.succ

/-- **A finite-dimensional space of functions is separated by finitely many evaluations.** -/
theorem exists_eval_separating (V : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ V] :
    ∃ (n : ℕ) (x : Fin n → ℝ), ∀ v ∈ V, (∀ k, v (x k) = 0) → v = 0 :=
  exists_eval_separating_aux (Module.finrank ℂ V) V inferInstance le_rfl

/-! ## Finite translation rank forces differentiability -/

private theorem real_smul_pi {d : ℕ} (r : ℝ) (v : Fin d → ℂ) : r • v = ((r : ℂ)) • v := by
  funext j
  simp [Complex.real_smul]

/-- **Anselone–Korevaar, regularity step.**  A continuous function of finite translation rank has
a differentiable translation span. -/
theorem differentiable_of_mem_translationSpan {f : ℝ → ℂ} (hf : Continuous f)
    (hfin : FiniteDimensional ℂ (translationSpan f)) {g : ℝ → ℂ} (hg : g ∈ translationSpan f) :
    Differentiable ℝ g := by
  classical
  haveI := hfin
  set V : Submodule ℂ (ℝ → ℂ) := translationSpan f with hVdef
  set d : ℕ := Module.finrank ℂ V with hddef
  set b : Module.Basis (Fin d) ℂ V := Module.finBasis ℂ V with hbdef
  obtain ⟨n, xs, hxs⟩ := exists_eval_separating V
  set ev : V →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun v k => (v : ℝ → ℂ) (xs k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hevdef
  have hkerev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    refine hxs (v : ℝ → ℂ) v.2 ?_
    intro k
    exact congrFun hv k
  obtain ⟨Lft, hLft⟩ := ev.exists_leftInverse_of_injective hkerev
  have hLev : ∀ v : V, Lft (ev v) = v := fun v => LinearMap.congr_fun hLft v
  set Θ : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ) := b.equivFun.toLinearMap.comp Lft with hΘdef
  have hΘcont : Continuous Θ := LinearMap.continuous_of_finiteDimensional Θ
  set coord : ℝ → (Fin d → ℂ) :=
    fun a => b.equivFun ⟨realTranslate a f, realTranslate_mem_translationSpan f a⟩ with hcoorddef
  have hcoordΘ : ∀ a : ℝ, coord a = Θ (fun k => f (xs k - a)) := by
    intro a
    have hevv : ev ⟨realTranslate a f, realTranslate_mem_translationSpan f a⟩
        = fun k => f (xs k - a) := rfl
    rw [hcoorddef, hΘdef]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hevv, hLev]
  have hcoordcont : Continuous coord := by
    have hbase : Continuous fun a : ℝ => (fun k => f (xs k - a) : Fin n → ℂ) :=
      continuous_pi fun k => hf.comp (continuous_const.sub continuous_id)
    have hcomp : Continuous (Θ ∘ fun a : ℝ => (fun k => f (xs k - a) : Fin n → ℂ)) :=
      hΘcont.comp hbase
    have heq : coord = Θ ∘ fun a : ℝ => (fun k => f (xs k - a) : Fin n → ℂ) := funext hcoordΘ
    rw [heq]
    exact hcomp
  have hcoordj : ∀ j, Continuous fun t : ℝ => coord t j := fun j =>
    (continuous_apply j).comp hcoordcont
  have hexpand : ∀ a s : ℝ, f (s - a) = ∑ j, coord a j * ((b j : V) : ℝ → ℂ) s := by
    intro a s
    set v : V := ⟨realTranslate a f, realTranslate_mem_translationSpan f a⟩ with hvdef
    have hsum : ∑ j, b.equivFun v j • b j = v := by
      rw [← Module.Basis.equivFun_symm_apply]
      exact b.equivFun.symm_apply_apply v
    have hval := congrArg (fun w : V => (w : ℝ → ℂ) s) hsum
    simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hval
    rw [hcoorddef]
    exact hval.symm
  -- the primitive of `f`
  set P : ℝ → ℂ := fun s => ∫ t in (0 : ℝ)..s, f t with hPdef
  have hPderiv : ∀ s : ℝ, HasDerivAt P (f s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 s)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have hPdiff : Differentiable ℝ P := fun s => (hPderiv s).differentiableAt
  -- the integrated coordinate curve
  set F : ℝ → (Fin d → ℂ) := fun ε j => ∫ t in (0 : ℝ)..ε, coord t j with hFdef
  have hFderiv : ∀ ε : ℝ, HasDerivAt F (coord ε) ε := by
    intro ε
    rw [hasDerivAt_pi]
    intro j
    exact intervalIntegral.integral_hasDerivAt_right ((hcoordj j).intervalIntegrable 0 ε)
      ((hcoordj j).stronglyMeasurableAtFilter _ _) (hcoordj j).continuousAt
  have hwF : ∀ ε s : ℝ, P s - P (s - ε) = ∑ j, F ε j * ((b j : V) : ℝ → ℂ) s := by
    intro ε s
    have h1 : ∑ j, F ε j * ((b j : V) : ℝ → ℂ) s
        = ∫ t in (0 : ℝ)..ε, ∑ j, coord t j * ((b j : V) : ℝ → ℂ) s := by
      rw [intervalIntegral.integral_finsetSum
        (f := fun j (t : ℝ) => coord t j * ((b j : V) : ℝ → ℂ) s)
        (fun j _ => ((hcoordj j).mul continuous_const).intervalIntegrable 0 ε)]
      exact Finset.sum_congr rfl fun j _ => (intervalIntegral.integral_mul_const _ _).symm
    have h2 : ∫ t in (0 : ℝ)..ε, ∑ j, coord t j * ((b j : V) : ℝ → ℂ) s
        = ∫ t in (0 : ℝ)..ε, f (s - t) :=
      intervalIntegral.integral_congr fun t _ => (hexpand t s).symm
    have h3 : ∫ t in (0 : ℝ)..ε, f (s - t) = ∫ y in (s - ε)..(s - 0), f y :=
      intervalIntegral.integral_comp_sub_left f s
    have h4 : P s - P (s - ε) = ∫ y in (s - ε)..s, f y :=
      intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable 0 s)
        (hf.intervalIntegrable 0 (s - ε))
    rw [h1, h2, h3, sub_zero, ← h4]
  set Wv : ℝ → V := fun ε => b.equivFun.symm (F ε) with hWvdef
  have hWvcoe : ∀ ε : ℝ, ((Wv ε : V) : ℝ → ℂ) = fun s => P s - P (s - ε) := by
    intro ε
    funext s
    rw [hWvdef]
    simp only [Module.Basis.equivFun_symm_apply, Submodule.coe_sum, SetLike.val_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (hwF ε s).symm
  have hWvdiff : ∀ ε : ℝ, Differentiable ℝ ((Wv ε : V) : ℝ → ℂ) := by
    intro ε
    rw [hWvcoe]
    exact hPdiff.sub (hPdiff.comp (differentiable_id.sub_const ε))
  -- the coordinate vectors of the differences span everything
  have hspancoord : Submodule.span ℂ (Set.range coord) = ⊤ := by
    have hgen : Submodule.span ℂ (Set.range
        (fun a : ℝ => (⟨realTranslate a f, realTranslate_mem_translationSpan f a⟩ : V))) = ⊤ := by
      apply Submodule.map_injective_of_injective (Submodule.subtype_injective V)
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      rfl
    have hmapeq : Submodule.span ℂ (Set.range coord)
        = Submodule.map b.equivFun.toLinearMap (Submodule.span ℂ (Set.range
            (fun a : ℝ => (⟨realTranslate a f, realTranslate_mem_translationSpan f a⟩ : V)))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmapeq, hgen, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr b.equivFun.surjective
  have hspanF : Submodule.span ℂ (Set.range F) = ⊤ := by
    have hle : Submodule.span ℂ (Set.range coord) ≤ Submodule.span ℂ (Set.range F) := by
      refine Submodule.span_le.mpr ?_
      rintro u ⟨ε, rfl⟩
      have hclosed : IsClosed
          ((Submodule.span ℂ (Set.range F) : Submodule ℂ (Fin d → ℂ)) : Set (Fin d → ℂ)) :=
        Submodule.closed_of_finiteDimensional _
      refine hclosed.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.mp (hFderiv ε)) ?_
      filter_upwards with y
      have hsl : slope F ε y = ((((y - ε)⁻¹ : ℝ) : ℂ)) • (F y - F ε) := by
        have h0 : slope F ε y = ((y - ε)⁻¹ : ℝ) • (F y - F ε) := by
          simp [slope, vsub_eq_sub]
        rw [h0, real_smul_pi]
      rw [hsl]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨y, rfl⟩)
        (Submodule.subset_span ⟨ε, rfl⟩))
    have := hspancoord ▸ hle
    exact top_le_iff.mp this
  have hspanW : Submodule.span ℂ (Set.range Wv) = (⊤ : Submodule ℂ V) := by
    have hmapeq : Submodule.span ℂ (Set.range Wv)
        = Submodule.map b.equivFun.symm.toLinearMap (Submodule.span ℂ (Set.range F)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmapeq, hspanF, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr b.equivFun.symm.surjective
  have hall : ∀ v : V, v ∈ Submodule.span ℂ (Set.range Wv) → Differentiable ℝ ((v : V) : ℝ → ℂ) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem u hu => obtain ⟨ε, rfl⟩ := hu; exact hWvdiff ε
    | zero => simp
    | add u w _ _ hu hw => simpa using hu.add hw
    | smul c u _ hu => simpa using hu.const_smul c
  have := hall ⟨g, hg⟩ (by rw [hspanW]; trivial)
  simpa using this

/-! ## The span is closed under differentiation -/

theorem deriv_mem_translationSpan {f : ℝ → ℂ} (hf : Continuous f)
    (hfin : FiniteDimensional ℂ (translationSpan f)) {g : ℝ → ℂ} (hg : g ∈ translationSpan f) :
    deriv g ∈ translationSpan f := by
  haveI := hfin
  have hgdiff : Differentiable ℝ g := differentiable_of_mem_translationSpan hf hfin hg
  have hclosed : IsClosed ((translationSpan f : Submodule ℂ (ℝ → ℂ)) : Set (ℝ → ℂ)) :=
    Submodule.closed_of_finiteDimensional _
  set u : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hudef
  have hune : ∀ m, u m ≠ 0 := by
    intro m
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    exact ne_of_gt this
  have hu0 : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set q : ℕ → (ℝ → ℂ) := fun m => (((u m : ℝ) : ℂ))⁻¹ • (realTranslate (-(u m)) g - g) with hqdef
  have hqmem : ∀ m, q m ∈ translationSpan f := fun m =>
    Submodule.smul_mem _ _
      (Submodule.sub_mem _ (realTranslate_mem_of_mem_translationSpan hg _) hg)
  have hqtend : Tendsto q atTop (𝓝 (deriv g)) := by
    rw [tendsto_pi_nhds]
    intro x
    have hslope : Tendsto (slope g x) (𝓝[≠] x) (𝓝 (deriv g x)) :=
      hasDerivAt_iff_tendsto_slope.mp (hgdiff x).hasDerivAt
    have hcomp : Tendsto (fun m => x + u m) atTop (𝓝[≠] x) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using tendsto_const_nhds.add hu0
      · filter_upwards with m
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hc
        exact hune m (by linarith [hc])
    have hlim := hslope.comp hcomp
    refine hlim.congr ?_
    intro m
    have hs : slope g x (x + u m) = (((u m)⁻¹ : ℝ)) • (g (x + u m) - g x) := by
      simp [slope, vsub_eq_sub]
    simp only [Function.comp_apply]
    rw [hs]
    simp only [hqdef, Pi.smul_apply, Pi.sub_apply, realTranslate, smul_eq_mul,
      Complex.real_smul]
    rw [show x - -u m = x + u m by ring]
    push_cast
    ring
  exact hclosed.mem_of_tendsto hqtend (Filter.Eventually.of_forall hqmem)

/-! ## Smoothness -/

theorem contDiff_of_mem_translationSpan {f : ℝ → ℂ} (hf : Continuous f)
    (hfin : FiniteDimensional ℂ (translationSpan f)) {g : ℝ → ℂ} (hg : g ∈ translationSpan f) :
    ContDiff ℝ (⊤ : ℕ∞) g := by
  rw [contDiff_infty]
  intro N
  induction N generalizing g with
  | zero =>
      exact contDiff_zero.2 (differentiable_of_mem_translationSpan hf hfin hg).continuous
  | succ N ih =>
      have hcast : ((N + 1 : ℕ) : WithTop ℕ∞) = ((N : ℕ) : WithTop ℕ∞) + 1 := by
        push_cast; ring
      rw [hcast]
      refine contDiff_succ_iff_deriv.2 ⟨differentiable_of_mem_translationSpan hf hfin hg, ?_, ?_⟩
      · intro hc; exact absurd hc (by simp)
      · exact ih (deriv_mem_translationSpan hf hfin hg)

/-! ## The constant-coefficient annihilator -/

theorem exists_nonzero_realConstCoeffOp_of_finrank {f : ℝ → ℂ} (hf : Continuous f)
    (hfin : FiniteDimensional ℂ (translationSpan f)) :
    ∃ L : Polynomial ℂ, L ≠ 0 ∧ realConstCoeffOp L f = 0 := by
  classical
  haveI := hfin
  set V : Submodule ℂ (ℝ → ℂ) := translationSpan f with hVdef
  have hjet : ∀ m : ℕ, iteratedDeriv m f ∈ V := by
    intro m
    induction m with
    | zero => simpa [iteratedDeriv_zero] using self_mem_translationSpan f
    | succ m ih => rw [iteratedDeriv_succ]; exact deriv_mem_translationSpan hf hfin ih
  have hnotli : ¬ LinearIndependent ℂ (fun m : ℕ => iteratedDeriv m f) := by
    intro hli
    have hjetsli : LinearIndependent ℂ (fun m : ℕ => (⟨iteratedDeriv m f, hjet m⟩ : V)) := by
      have hcomp : (⇑V.subtype ∘ fun m : ℕ => (⟨iteratedDeriv m f, hjet m⟩ : V))
          = fun m : ℕ => iteratedDeriv m f := rfl
      apply LinearIndependent.of_comp V.subtype
      rw [hcomp]
      exact hli
    have hfinli : LinearIndependent ℂ
        (fun i : Fin (Module.finrank ℂ V + 1) => (⟨iteratedDeriv (i : ℕ) f, hjet i⟩ : V)) :=
      hjetsli.comp (fun i : Fin (Module.finrank ℂ V + 1) => (i : ℕ)) Fin.val_injective
    have hbound := hfinli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hbound
    omega
  rw [linearIndependent_iff] at hnotli
  push_neg at hnotli
  obtain ⟨l, hl0, hlne⟩ := hnotli
  set L : Polynomial ℂ := ∑ i ∈ l.support, Polynomial.C (l i) * Polynomial.X ^ i with hLdef
  have hcoeff : ∀ m : ℕ, L.coeff m = l m := by
    intro m
    rw [hLdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq l.support m (fun i => l i)]
    by_cases hm : m ∈ l.support
    · simp [hm]
    · have hlm : l m = 0 := by
        by_contra hne
        exact hm (Finsupp.mem_support_iff.mpr hne)
      simp [hm, hlm]
  have hLne : L ≠ 0 := by
    obtain ⟨m, hm⟩ := Finsupp.ne_iff.mp hlne
    intro hz
    apply hm
    rw [← hcoeff m, hz, Polynomial.coeff_zero]
    simp
  refine ⟨L, hLne, ?_⟩
  have hsupp : L.support = l.support := by
    ext m
    rw [Polynomial.mem_support_iff, hcoeff, Finsupp.mem_support_iff]
  funext x
  have hzero : ∑ j ∈ l.support, l j * iteratedDeriv j f x = 0 := by
    rw [Finsupp.linearCombination_apply] at hl0
    have h := congrFun hl0 x
    simpa [Finsupp.sum] using h
  rw [realConstCoeffOp, Polynomial.sum_def, hsupp]
  simp only [hcoeff]
  simpa using hzero

/-! ## Exponential polynomials have finite translation rank -/

/-- The span of the monomial blocks `xᵏ·e^{μ x}` with `k ≤ N` and `μ ∈ S`. -/
def expMonomialSpace (N : ℕ) (S : Finset ℂ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ ((fun p : ℕ × ℂ => polyExp (Polynomial.X ^ p.1) p.2) ''
    ((Finset.range (N + 1) ×ˢ S : Finset (ℕ × ℂ)) : Set (ℕ × ℂ)))

instance finiteDimensional_expMonomialSpace (N : ℕ) (S : Finset ℂ) :
    FiniteDimensional ℂ (expMonomialSpace N S) :=
  Module.Finite.span_of_finite ℂ (Set.Finite.image _ (Finset.finite_toSet _))

theorem expMonomialSpace_mono {N₁ N₂ : ℕ} {S₁ S₂ : Finset ℂ} (hN : N₁ ≤ N₂) (hS : S₁ ⊆ S₂) :
    expMonomialSpace N₁ S₁ ≤ expMonomialSpace N₂ S₂ := by
  refine Submodule.span_mono ?_
  rintro u ⟨p, hp, rfl⟩
  refine ⟨p, ?_, rfl⟩
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hS hp.2⟩

/-- Every block of degree at most `N` and frequency in `S` lies in the monomial span. -/
theorem polyExp_mem_expMonomialSpace {P : Polynomial ℂ} {μ : ℂ} {N : ℕ} {S : Finset ℂ}
    (hdeg : P.natDegree ≤ N) (hμ : μ ∈ S) : polyExp P μ ∈ expMonomialSpace N S := by
  have hP : P = ∑ i ∈ Finset.range (N + 1), Polynomial.C (P.coeff i) * Polynomial.X ^ i := by
    conv_lhs => rw [Polynomial.as_sum_range' P (N + 1) (by omega)]
    exact Finset.sum_congr rfl fun i _ => Polynomial.C_mul_X_pow_eq_monomial.symm
  have hsum : polyExp P μ
      = ∑ i ∈ Finset.range (N + 1), P.coeff i • polyExp (Polynomial.X ^ i) μ := by
    funext x
    conv_lhs => rw [hP]
    simp only [polyExp, polyExpC, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ⟨(i, μ), ?_, rfl⟩
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
  exact ⟨hi, hμ⟩

theorem realTranslate_polyExp (a : ℝ) (P : Polynomial ℂ) (μ : ℂ) :
    realTranslate a (polyExp P μ)
      = polyExp (Polynomial.C (Complex.exp (-(μ * (a : ℂ)))) *
          P.comp (Polynomial.X - Polynomial.C (a : ℂ))) μ := by
  funext x
  simp only [realTranslate, polyExp, polyExpC, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X]
  rw [Complex.ofReal_sub]
  rw [show μ * ((x : ℂ) - (a : ℂ)) = -(μ * (a : ℂ)) + μ * (x : ℂ) by ring, Complex.exp_add]
  ring

theorem expMonomialSpace_translate_mem {N : ℕ} {S : Finset ℂ} {g : ℝ → ℂ}
    (hg : g ∈ expMonomialSpace N S) (a : ℝ) : realTranslate a g ∈ expMonomialSpace N S := by
  have hmap : Submodule.map (realTranslateLM a) (expMonomialSpace N S) ≤ expMonomialSpace N S := by
    rw [expMonomialSpace, Submodule.map_span, Submodule.span_le]
    rintro u ⟨v, ⟨p, hp, rfl⟩, rfl⟩
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp
    rw [realTranslateLM_apply, realTranslate_polyExp]
    refine polyExp_mem_expMonomialSpace ?_ hp.2
    have hdeg : (Polynomial.C (Complex.exp (-(p.2 * (a : ℂ)))) *
        (Polynomial.X ^ p.1).comp (Polynomial.X - Polynomial.C (a : ℂ))).natDegree ≤ p.1 := by
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_comp]
      simp
    omega
  exact hmap ⟨g, hg, rfl⟩

theorem exists_expMonomialSpace_of_mem_expPolySpace {g : ℝ → ℂ} (hg : g ∈ expPolySpace) :
    ∃ (N : ℕ) (S : Finset ℂ), g ∈ expMonomialSpace N S := by
  classical
  induction hg using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨p, rfl⟩ := hu
      exact ⟨p.1.natDegree, {p.2}, polyExp_mem_expMonomialSpace le_rfl (Finset.mem_singleton_self _)⟩
  | zero => exact ⟨0, ∅, Submodule.zero_mem _⟩
  | add u v _ _ hu hv =>
      obtain ⟨N₁, S₁, h₁⟩ := hu
      obtain ⟨N₂, S₂, h₂⟩ := hv
      refine ⟨max N₁ N₂, S₁ ∪ S₂, Submodule.add_mem _ ?_ ?_⟩
      · exact expMonomialSpace_mono (le_max_left _ _) Finset.subset_union_left h₁
      · exact expMonomialSpace_mono (le_max_right _ _) Finset.subset_union_right h₂
  | smul c u _ hu =>
      obtain ⟨N, S, h⟩ := hu
      exact ⟨N, S, Submodule.smul_mem _ c h⟩

/-- **Exponential polynomials have finite translation rank.** -/
theorem finiteDimensional_translationSpan_of_mem_expPolySpace {f : ℝ → ℂ}
    (hf : f ∈ expPolySpace) : FiniteDimensional ℂ (translationSpan f) := by
  obtain ⟨N, S, hmem⟩ := exists_expMonomialSpace_of_mem_expPolySpace hf
  have hle : translationSpan f ≤ expMonomialSpace N S := by
    rw [translationSpan, Submodule.span_le]
    rintro u ⟨a, rfl⟩
    exact expMonomialSpace_translate_mem hmem a
  exact Submodule.finiteDimensional_of_le hle

/-! ## The Anselone–Korevaar equivalence -/

/-- **Anselone–Korevaar.**  A continuous function has finite translation rank exactly when it is an
exponential polynomial. -/
theorem mem_expPolySpace_iff_finiteDimensional_translationSpan {f : ℝ → ℂ} (hf : Continuous f) :
    f ∈ expPolySpace ↔ FiniteDimensional ℂ (translationSpan f) := by
  constructor
  · exact finiteDimensional_translationSpan_of_mem_expPolySpace
  · intro hfin
    obtain ⟨L, hL, hzero⟩ := exists_nonzero_realConstCoeffOp_of_finrank hf hfin
    exact mem_expPolySpace_of_realConstCoeffOp_eq_zero
      (contDiff_of_mem_translationSpan hf hfin (self_mem_translationSpan f)) hL hzero

end

end GaloisForLFunctions.HTGeometry
