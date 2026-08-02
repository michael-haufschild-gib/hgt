import GaloisForLFunctions.HTGeometry.SchwartzSeminormOscillator

/-!
# Schwartz space is complete

The seminorms of a Cauchy sequence of Schwartz functions are uniformly bounded, and each iterated
derivative converges uniformly.  The limit of the derivatives is the derivative of the limit, so the
limit function is smooth; the uniform bounds pass to the limit, so it is Schwartz; and the Cauchy
estimates pass to the limit, so the sequence converges to it in the Schwartz topology.

Since the uniformity of `𝓢(ℝ, ℂ)` is countably generated, sequential completeness is completeness.

* `schwartzCauchyLimit` : the limit of a Cauchy sequence, as a Schwartz map.
* `tendsto_schwartzCauchyLimit` : the sequence converges to it.
* `instCompleteSpaceSchwartzMap` : **`𝓢(ℝ, ℂ)` is complete.**
-/

open scoped Real SchwartzMap ContDiff Topology Uniformity
open Filter Complex

noncomputable section

namespace GaloisForLFunctions

/-! ## The iterated derivative as a continuous operator -/

/-- The `n`-th derivative, as a continuous linear operator on Schwartz space. -/
def derivPowSCLM : ℕ → (𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))
  | 0 => ContinuousLinearMap.id ℂ _
  | (n + 1) => (derivPowSCLM n).comp derivSCLM

theorem derivPowSCLM_apply (n : ℕ) (f : 𝓢(ℝ, ℂ)) : derivPowSCLM n f = (derivSCLM^[n]) f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    show derivPowSCLM n (derivSCLM f) = _
    rw [ih, Function.iterate_succ_apply]

theorem coe_derivPowSCLM_apply (n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (derivPowSCLM n f) x = iteratedDeriv n ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x := by
  rw [derivPowSCLM_apply, coe_derivSCLM_iterate]

theorem norm_derivPowSCLM_le_seminorm (n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖(derivPowSCLM n f) x‖ ≤ SchwartzMap.seminorm ℂ 0 n f := by
  have h := SchwartzMap.le_seminorm' ℂ 0 n f x
  rw [pow_zero, one_mul] at h
  rw [coe_derivPowSCLM_apply]
  exact h

theorem abs_pow_mul_norm_derivPowSCLM_le_seminorm (k n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    |x| ^ k * ‖(derivPowSCLM n f) x‖ ≤ SchwartzMap.seminorm ℂ k n f := by
  have h := SchwartzMap.le_seminorm' ℂ k n f x
  rw [coe_derivPowSCLM_apply]
  exact h

/-! ## Countably generated uniformity -/

instance schwartzUniformityCountablyGenerated : IsCountablyGenerated (𝓤 𝓢(ℝ, ℂ)) := by
  rw [uniformity_eq_comap_nhds_zero]
  infer_instance

/-! ## Cauchy sequences in the seminorms -/

theorem exists_seminorm_lt_of_cauchySeq {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (k n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ l ≥ N, SchwartzMap.seminorm ℂ k n (f m - f l) < ε := by
  classical
  set q : Seminorm ℂ 𝓢(ℝ, ℂ) :=
    ({(k, n)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ ℝ ℂ) with hq
  have hqval : q = SchwartzMap.seminorm ℂ k n := by
    rw [hq, Finset.sup_singleton]
    rfl
  have hbasis := (schwartz_withSeminorms ℂ ℝ ℂ).hasBasis_ball (x := (0 : 𝓢(ℝ, ℂ)))
  have hmem : q.ball 0 ε ∈ 𝓝 (0 : 𝓢(ℝ, ℂ)) :=
    hbasis.mem_of_mem (i := (({(k, n)} : Finset (ℕ × ℕ)), ε)) hε
  have hV : {p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) | p.2 - p.1 ∈ q.ball 0 ε} ∈ 𝓤 𝓢(ℝ, ℂ) := by
    rw [uniformity_eq_comap_nhds_zero]
    exact ⟨q.ball 0 ε, hmem, subset_rfl⟩
  obtain ⟨N, hN⟩ := cauchySeq_iff.mp hf _ hV
  refine ⟨N, fun m hm l hl => ?_⟩
  have h := hN m hm l hl
  have hball : q (f l - f m) < ε := by
    have := h
    rwa [Set.mem_setOf_eq, Seminorm.mem_ball_zero] at this
  have hsymm : q (f m - f l) = q (f l - f m) := by
    rw [← neg_sub (f l) (f m), map_neg_eq_map]
  rw [← hqval]
  rw [hsymm]
  exact hball

theorem exists_seminorm_bound_of_cauchySeq {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (k n : ℕ) :
    ∃ C : ℝ, ∀ m, SchwartzMap.seminorm ℂ k n (f m) ≤ C := by
  classical
  obtain ⟨N, hN⟩ := exists_seminorm_lt_of_cauchySeq hf k n (ε := 1) one_pos
  set M : ℝ := (Finset.range (N + 1)).sup' (by simp)
    (fun j => SchwartzMap.seminorm ℂ k n (f j)) with hM
  refine ⟨max M (1 + SchwartzMap.seminorm ℂ k n (f N)), fun m => ?_⟩
  rcases le_or_gt m N with hle | hgt
  · refine le_trans ?_ (le_max_left _ _)
    rw [hM]
    exact Finset.le_sup' (fun j => SchwartzMap.seminorm ℂ k n (f j))
      (Finset.mem_range.mpr (by omega))
  · refine le_trans ?_ (le_max_right _ _)
    have hsplit : SchwartzMap.seminorm ℂ k n (f m)
        ≤ SchwartzMap.seminorm ℂ k n (f m - f N) + SchwartzMap.seminorm ℂ k n (f N) := by
      have h := map_add_le_add (SchwartzMap.seminorm ℂ k n) (f m - f N) (f N)
      rwa [sub_add_cancel] at h
    have hlt := hN m (by omega) N (le_refl N)
    linarith

theorem exists_schwartzSup_lt_of_cauchySeq {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f)
    (K : Finset (ℕ × ℕ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ l ≥ N, (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (f m - f l) < ε := by
  classical
  choose N hN using fun i : ℕ × ℕ => exists_seminorm_lt_of_cauchySeq hf i.1 i.2 hε
  refine ⟨K.sup N, fun m hm l hl => ?_⟩
  refine Seminorm.finset_sup_apply_lt hε fun i hi => ?_
  have hle : N i ≤ K.sup N := Finset.le_sup hi
  have hfam : (schwartzSeminormFamily ℂ ℝ ℂ i) (f m - f l)
      = SchwartzMap.seminorm ℂ i.1 i.2 (f m - f l) := rfl
  rw [hfam]
  exact hN i m (le_trans hle hm) l (le_trans hle hl)

/-- A sequence whose seminorm differences are eventually small is Cauchy. -/
theorem cauchySeq_of_seminorm {f : ℕ → 𝓢(ℝ, ℂ)}
    (h : ∀ (k n : ℕ) (ε : ℝ), 0 < ε → ∃ N, ∀ m ≥ N, ∀ l ≥ N,
      SchwartzMap.seminorm ℂ k n (f m - f l) < ε) : CauchySeq f := by
  classical
  refine cauchySeq_iff.mpr fun V hV => ?_
  rw [uniformity_eq_comap_nhds_zero] at hV
  obtain ⟨U, hU, hUV⟩ := hV
  obtain ⟨⟨K, ε⟩, hε, hball⟩ := (schwartz_withSeminorms ℂ ℝ ℂ).hasBasis_ball.mem_iff.mp hU
  choose N hN using fun i : ℕ × ℕ => h i.1 i.2 ε hε
  refine ⟨K.sup N, fun m hm l hl => ?_⟩
  refine hUV ?_
  show f l - f m ∈ U
  refine hball ?_
  rw [Seminorm.mem_ball_zero]
  refine Seminorm.finset_sup_apply_lt hε fun i hi => ?_
  have hle : N i ≤ K.sup N := Finset.le_sup hi
  have hfam : (schwartzSeminormFamily ℂ ℝ ℂ i) (f l - f m)
      = SchwartzMap.seminorm ℂ i.1 i.2 (f l - f m) := rfl
  rw [hfam]
  exact hN i l (le_trans hle hl) m (le_trans hle hm)

/-! ## The pointwise limit of the derivatives -/

/-- The pointwise limit of the `n`-th derivatives of a sequence of Schwartz functions. -/
def schwartzLimitDeriv (f : ℕ → 𝓢(ℝ, ℂ)) (n : ℕ) (x : ℝ) : ℂ :=
  limUnder atTop (fun m => (derivPowSCLM n (f m)) x)

theorem cauchySeq_derivPow_apply {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (n : ℕ) (x : ℝ) :
    CauchySeq (fun m => (derivPowSCLM n (f m)) x) := by
  refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_seminorm_lt_of_cauchySeq hf 0 n hε
  refine ⟨N, fun m hm l hl => ?_⟩
  have hsub : (derivPowSCLM n (f m)) x - (derivPowSCLM n (f l)) x
      = (derivPowSCLM n (f m - f l)) x := by
    rw [map_sub]
    rfl
  have hnorm : ‖(derivPowSCLM n (f m - f l)) x‖ ≤ SchwartzMap.seminorm ℂ 0 n (f m - f l) :=
    norm_derivPowSCLM_le_seminorm n _ x
  have hlt := hN m hm l hl
  rw [dist_eq_norm, hsub]
  linarith

theorem tendsto_schwartzLimitDeriv {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (n : ℕ) (x : ℝ) :
    Tendsto (fun m => (derivPowSCLM n (f m)) x) atTop (𝓝 (schwartzLimitDeriv f n x)) :=
  (cauchySeq_derivPow_apply hf n x).tendsto_limUnder

theorem tendstoUniformly_schwartzLimitDeriv {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (n : ℕ) :
    TendstoUniformly (fun m x => (derivPowSCLM n (f m)) x) (schwartzLimitDeriv f n) atTop := by
  have hcauchy : UniformCauchySeqOn (fun m x => (derivPowSCLM n (f m)) x) atTop Set.univ := by
    refine Metric.uniformCauchySeqOn_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_seminorm_lt_of_cauchySeq hf 0 n hε
    refine ⟨N, fun m hm l hl x _ => ?_⟩
    have hsub : (derivPowSCLM n (f m)) x - (derivPowSCLM n (f l)) x
        = (derivPowSCLM n (f m - f l)) x := by
      rw [map_sub]
      rfl
    have hnorm : ‖(derivPowSCLM n (f m - f l)) x‖ ≤ SchwartzMap.seminorm ℂ 0 n (f m - f l) :=
      norm_derivPowSCLM_le_seminorm n _ x
    have hlt := hN m hm l hl
    rw [dist_eq_norm, hsub]
    linarith
  have huniv := hcauchy.tendstoUniformlyOn_of_tendsto
    (fun x _ => tendsto_schwartzLimitDeriv hf n x)
  rwa [tendstoUniformlyOn_univ] at huniv

/-! ## The limit is smooth -/

theorem hasDerivAt_schwartzLimitDeriv {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (n : ℕ) (x : ℝ) :
    HasDerivAt (schwartzLimitDeriv f n) (schwartzLimitDeriv f (n + 1) x) x := by
  have huniform : TendstoUniformlyOn (fun m y => (derivPowSCLM (n + 1) (f m)) y)
      (schwartzLimitDeriv f (n + 1)) atTop Set.univ := by
    rw [tendstoUniformlyOn_univ]
    exact tendstoUniformly_schwartzLimitDeriv hf (n + 1)
  have hderiv : ∀ᶠ m in atTop, ∀ y ∈ Set.univ,
      HasDerivAt (fun z => (derivPowSCLM n (f m)) z) ((derivPowSCLM (n + 1) (f m)) y) y := by
    filter_upwards with m y _
    have hval : (derivPowSCLM (n + 1) (f m)) y
        = deriv ((derivPowSCLM n (f m) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y := by
      rw [derivPowSCLM_apply, derivPowSCLM_apply, Function.iterate_succ_apply', derivSCLM_apply]
    rw [hval]
    exact (derivPowSCLM n (f m)).hasDerivAt y
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_univ huniform hderiv
    (fun y _ => tendsto_schwartzLimitDeriv hf n y) (Set.mem_univ x)

theorem deriv_schwartzLimitDeriv {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (n : ℕ) :
    deriv (schwartzLimitDeriv f n) = schwartzLimitDeriv f (n + 1) := by
  funext x
  exact (hasDerivAt_schwartzLimitDeriv hf n x).deriv

theorem contDiff_nat_schwartzLimitDeriv {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (j : ℕ) (n : ℕ) :
    ContDiff ℝ j (schwartzLimitDeriv f n) := by
  induction j generalizing n with
  | zero =>
    have hdiff : Differentiable ℝ (schwartzLimitDeriv f n) := fun x =>
      (hasDerivAt_schwartzLimitDeriv hf n x).differentiableAt
    have h : ContDiff ℝ 0 (schwartzLimitDeriv f n) := contDiff_zero.mpr hdiff.continuous
    simpa using h
  | succ j ih =>
    have hcast : ((j + 1 : ℕ) : WithTop ℕ∞) = (j : WithTop ℕ∞) + 1 := by
      push_cast
      ring
    rw [hcast]
    refine contDiff_succ_iff_deriv.mpr ⟨fun x =>
      (hasDerivAt_schwartzLimitDeriv hf n x).differentiableAt, ?_, ?_⟩
    · intro hω
      exact absurd hω (by simp)
    · rw [deriv_schwartzLimitDeriv hf n]
      exact ih (n + 1)

theorem contDiff_schwartzLimitDeriv {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (n : ℕ) :
    ContDiff ℝ ∞ (schwartzLimitDeriv f n) :=
  contDiff_infty.mpr fun j => contDiff_nat_schwartzLimitDeriv hf j n

theorem iteratedDeriv_schwartzLimitDeriv {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (n : ℕ) :
    iteratedDeriv n (schwartzLimitDeriv f 0) = schwartzLimitDeriv f n := by
  induction n with
  | zero => rw [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, deriv_schwartzLimitDeriv hf n]

/-! ## The limit is Schwartz -/

theorem abs_pow_mul_norm_schwartzLimitDeriv_le {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ k * ‖schwartzLimitDeriv f n x‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_seminorm_bound_of_cauchySeq hf k n
  refine ⟨C, fun x => ?_⟩
  have htend : Tendsto (fun m => |x| ^ k * ‖(derivPowSCLM n (f m)) x‖) atTop
      (𝓝 (|x| ^ k * ‖schwartzLimitDeriv f n x‖)) := by
    exact ((tendsto_schwartzLimitDeriv hf n x).norm).const_mul _
  refine le_of_tendsto htend ?_
  filter_upwards with m
  exact le_trans (abs_pow_mul_norm_derivPowSCLM_le_seminorm k n (f m) x) (hC m)

/-- **The limit of a Cauchy sequence of Schwartz functions**, as a Schwartz map. -/
def schwartzCauchyLimit {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) : 𝓢(ℝ, ℂ) where
  toFun := schwartzLimitDeriv f 0
  smooth' := contDiff_schwartzLimitDeriv hf 0
  decay' k n := by
    obtain ⟨C, hC⟩ := abs_pow_mul_norm_schwartzLimitDeriv_le hf k n
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_schwartzLimitDeriv hf n,
      Real.norm_eq_abs]
    exact hC x

@[simp] theorem schwartzCauchyLimit_apply {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) (x : ℝ) :
    schwartzCauchyLimit hf x = schwartzLimitDeriv f 0 x := rfl

/-! ## Convergence to the limit -/

theorem tendsto_schwartzCauchyLimit {f : ℕ → 𝓢(ℝ, ℂ)} (hf : CauchySeq f) :
    Tendsto f atTop (𝓝 (schwartzCauchyLimit hf)) := by
  rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds_atTop]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨N, hN⟩ := exists_seminorm_lt_of_cauchySeq hf k n (half_pos hε)
  refine ⟨N, fun m hm => ?_⟩
  have hfam : (schwartzSeminormFamily ℂ ℝ ℂ (k, n)) (f m - schwartzCauchyLimit hf)
      = SchwartzMap.seminorm ℂ k n (f m - schwartzCauchyLimit hf) := rfl
  rw [hfam]
  have hbound : SchwartzMap.seminorm ℂ k n (f m - schwartzCauchyLimit hf) ≤ ε / 2 := by
    refine SchwartzMap.seminorm_le_bound' ℂ k n _ (by positivity) fun x => ?_
    have hlim : ∀ y : ℝ,
        (derivPowSCLM n (schwartzCauchyLimit hf)) y = schwartzLimitDeriv f n y := by
      intro y
      rw [coe_derivPowSCLM_apply]
      have hfun : ((schwartzCauchyLimit hf : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = schwartzLimitDeriv f 0 := rfl
      rw [hfun, iteratedDeriv_schwartzLimitDeriv hf n]
    have hcoe : iteratedDeriv n ((f m - schwartzCauchyLimit hf : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x
        = (derivPowSCLM n (f m)) x - schwartzLimitDeriv f n x := by
      rw [← coe_derivPowSCLM_apply, map_sub]
      show (derivPowSCLM n (f m)) x - (derivPowSCLM n (schwartzCauchyLimit hf)) x = _
      rw [hlim x]
    rw [hcoe]
    have htend : Tendsto (fun l => |x| ^ k * ‖(derivPowSCLM n (f m)) x
        - (derivPowSCLM n (f l)) x‖) atTop
        (𝓝 (|x| ^ k * ‖(derivPowSCLM n (f m)) x - schwartzLimitDeriv f n x‖)) := by
      exact (((tendsto_schwartzLimitDeriv hf n x).const_sub _).norm).const_mul _
    refine le_of_tendsto htend ?_
    filter_upwards [Filter.eventually_ge_atTop N] with l hl
    have hsub : (derivPowSCLM n (f m)) x - (derivPowSCLM n (f l)) x
        = (derivPowSCLM n (f m - f l)) x := by
      rw [map_sub]
      rfl
    rw [hsub]
    have hle := abs_pow_mul_norm_derivPowSCLM_le_seminorm k n (f m - f l) x
    have hlt := hN m hm l hl
    linarith
  linarith

/-- **Schwartz space is complete.** -/
instance instCompleteSpaceSchwartzMap : CompleteSpace 𝓢(ℝ, ℂ) :=
  UniformSpace.complete_of_cauchySeq_tendsto fun _ hf =>
    ⟨schwartzCauchyLimit hf, tendsto_schwartzCauchyLimit hf⟩

/-- **Schwartz space is metrizable**: its uniformity is countably generated and it is separated. -/
instance instMetrizableSpaceSchwartzMap : TopologicalSpace.MetrizableSpace 𝓢(ℝ, ℂ) :=
  UniformSpace.metrizableSpace

end GaloisForLFunctions

end
