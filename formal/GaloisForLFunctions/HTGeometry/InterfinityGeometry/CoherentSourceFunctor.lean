import Mathlib

/-!
# The coherent source functor

A source-time cocycle `b_V` valued in the dual of a complex test space produces the coherent
functionals `S_V(f) = exp ⟨f, b_V⟩`.  This file proves that three conditions coincide:

1. `b_V` is the coboundary of a primitive `η` which is annihilated in the future;
2. `b_V` converges weak-star;
3. the coherent functionals converge locally uniformly on every finite-dimensional subspace of the
   test space.

The equivalence `1 ↔ 2` is the stable-primitive argument for the transposed time semigroup; the
equivalence `2 ↔ 3` rests on the fact that pointwise convergence of complex numbers is exactly
locally uniform convergence of the associated exponential characters, whose derivative at the
origin recovers the number.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open Filter Topology NNReal

/-! ## Exponential characters detect their exponents -/

/-- Locally uniform convergence is preserved by the complex exponential when the limit is
continuous: on a compact set the limit character is bounded, and `‖exp w − 1‖ ≤ 2‖w‖` for small
`w`. -/
theorem tendstoLocallyUniformly_exp {ι α : Type*} [TopologicalSpace α] [LocallyCompactSpace α]
    {l : Filter ι} {c : ι → α → ℂ} {C : α → ℂ} (hC : Continuous C)
    (h : TendstoLocallyUniformly c C l) :
    TendstoLocallyUniformly (fun V x => Complex.exp (c V x)) (fun x => Complex.exp (C x)) l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at h ⊢
  intro K hK
  obtain ⟨M₀, hM₀⟩ :=
    hK.exists_bound_of_continuousOn (Complex.continuous_exp.comp hC).continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ x ∈ K, ‖Complex.exp (C x)‖ ≤ M := fun x hx =>
    le_trans (hM₀ x hx) (le_max_left _ _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := min 1 (ε / (2 * M + 2)) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : 2 * M * δ < ε := by
    have h1 : δ ≤ ε / (2 * M + 2) := min_le_right _ _
    have h2 : 2 * M * δ ≤ 2 * M * (ε / (2 * M + 2)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : 2 * M * (ε / (2 * M + 2)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  filter_upwards [(Metric.tendstoUniformlyOn_iff).1 (h K hK) δ hδ0] with V hV x hx
  have hdist : ‖c V x - C x‖ < δ := by
    have := hV x hx
    rwa [dist_eq_norm, norm_sub_rev] at this
  have hle1 : ‖c V x - C x‖ ≤ 1 := le_trans hdist.le hδ1
  have hsplit : Complex.exp (c V x) - Complex.exp (C x) =
      Complex.exp (C x) * (Complex.exp (c V x - C x) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    ring_nf
  have hbound : ‖Complex.exp (c V x) - Complex.exp (C x)‖ ≤ M * (2 * ‖c V x - C x‖) := by
    rw [hsplit, norm_mul]
    exact mul_le_mul (hM x hx) (Complex.norm_exp_sub_one_le hle1) (norm_nonneg _) hM0
  rw [dist_eq_norm, norm_sub_rev]
  refine lt_of_le_of_lt hbound ?_
  nlinarith [norm_nonneg (c V x - C x)]

/-- A finite linear combination of convergent coefficients converges locally uniformly in the
coefficients of the combination. -/
theorem tendstoLocallyUniformly_linearCombination {ι : Type*} {l : Filter ι} {n : ℕ}
    {a : ι → Fin n → ℂ} {A : Fin n → ℂ} (h : ∀ j, Tendsto (fun V => a V j) l (𝓝 (A j))) :
    TendstoLocallyUniformly (fun V (t : Fin n → ℂ) => ∑ j, t j * a V j)
      (fun t => ∑ j, t j * A j) l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => le_trans (hR₀ x hx) (le_max_left _ _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := ε / ((n : ℝ) * R + 1) with hδdef
  have hden : (0 : ℝ) < (n : ℝ) * R + 1 := by positivity
  have hδ0 : 0 < δ := by positivity
  have hstep : ∀ j : Fin n, ∀ᶠ V in l, ‖a V j - A j‖ < δ := by
    intro j
    have hmem : Metric.ball (A j) δ ∈ 𝓝 (A j) := Metric.ball_mem_nhds _ hδ0
    filter_upwards [(h j) hmem] with V hV
    simpa [dist_eq_norm] using hV
  filter_upwards [Filter.eventually_all.2 hstep] with V hV x hx
  have hxR : ‖x‖ ≤ R := hR x hx
  have hbound : ‖(∑ j, x j * A j) - ∑ j, x j * a V j‖ ≤ (n : ℝ) * (R * δ) := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (f := fun j => ‖x j * A j - x j * a V j‖)
      (g := fun _ => R * δ) ?_) ?_
    · intro j _
      rw [← mul_sub, norm_mul]
      refine mul_le_mul (le_trans (norm_le_pi_norm x j) hxR) ?_ (norm_nonneg _) hR0
      rw [← norm_neg, neg_sub]
      exact (hV j).le
    · simp [Finset.sum_const]
  rw [dist_eq_norm]
  refine lt_of_le_of_lt hbound ?_
  have hcalc : (n : ℝ) * (R * δ) = ((n : ℝ) * R) * ε / ((n : ℝ) * R + 1) := by
    rw [hδdef]; ring
  rw [hcalc, div_lt_iff₀ hden]
  nlinarith

/-- The derivative at the origin of an exponential character is its exponent. -/
theorem deriv_exp_mul_zero (c : ℂ) : deriv (fun t : ℂ => Complex.exp (t * c)) 0 = c := by
  have h1 : HasDerivAt (fun t : ℂ => t * c) c 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul_const c
  have hd : HasDerivAt (fun t : ℂ => Complex.exp (t * c)) (Complex.exp (0 * c) * c) 0 := h1.cexp
  rw [hd.deriv]
  simp

theorem differentiable_exp_mul (c : ℂ) : Differentiable ℂ (fun t : ℂ => Complex.exp (t * c)) :=
  Complex.differentiable_exp.comp (differentiable_id.mul_const c)

/-- **Exponential characters detect their exponents.**  A family of complex numbers converges
exactly when the associated exponential characters converge locally uniformly. -/
theorem tendsto_iff_tendstoLocallyUniformly_exp {ι : Type*} {l : Filter ι} {a : ι → ℂ} {A : ℂ} :
    Tendsto a l (𝓝 A) ↔
      TendstoLocallyUniformly (fun V (t : ℂ) => Complex.exp (t * a V))
        (fun t => Complex.exp (t * A)) l := by
  constructor
  · intro h
    refine tendstoLocallyUniformly_exp (continuous_id.mul continuous_const) ?_
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn continuousOn_id
    set R : ℝ := max R₀ 0 with hRdef
    have hR0 : 0 ≤ R := le_max_right _ _
    have hR : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => le_trans (hR₀ x hx) (le_max_left _ _)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hpos : 0 < ε / (R + 1) := by positivity
    filter_upwards [h (Metric.ball_mem_nhds A hpos)] with V hV x hx
    have hd : ‖a V - A‖ < ε / (R + 1) := by simpa [dist_eq_norm] using hV
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    calc ‖x‖ * ‖A - a V‖ ≤ R * (ε / (R + 1)) := by
          refine mul_le_mul (hR x hx) ?_ (norm_nonneg _) hR0
          rw [norm_sub_rev]
          exact hd.le
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  · intro h
    have hOn : TendstoLocallyUniformlyOn (fun V (t : ℂ) => Complex.exp (t * a V))
        (fun t => Complex.exp (t * A)) l Set.univ := by
      rw [tendstoLocallyUniformlyOn_univ]
      exact h
    have hdiff : ∀ᶠ V in l, DifferentiableOn ℂ (fun t : ℂ => Complex.exp (t * a V)) Set.univ :=
      Filter.Eventually.of_forall fun V => (differentiable_exp_mul (a V)).differentiableOn
    have hat := (hOn.deriv hdiff isOpen_univ).tendsto_at (Set.mem_univ (0 : ℂ))
    simpa [Function.comp_def, deriv_exp_mul_zero] using hat

/-! ## The coherent source functor -/

variable {Φ : Type*} [AddCommGroup Φ] [Module ℂ Φ]

/-- Weak-star convergence of a family of linear functionals on the test space. -/
def TendstoWeakStar {ι : Type*} (b : ι → (Φ →ₗ[ℂ] ℂ)) (l : Filter ι) (L : Φ →ₗ[ℂ] ℂ) : Prop :=
  ∀ f : Φ, Tendsto (fun V => b V f) l (𝓝 (L f))

/-- The cocycle law for the transposed time semigroup. -/
def IsSourceCocycle (S : ℝ≥0 → (Φ →ₗ[ℂ] Φ)) (b : ℝ≥0 → (Φ →ₗ[ℂ] ℂ)) : Prop :=
  ∀ (V W : ℝ≥0) (f : Φ), b (V + W) f = b V f + b W (S V f)

/-- A primitive of the cocycle which is annihilated in the future. -/
def IsStablePrimitive (S : ℝ≥0 → (Φ →ₗ[ℂ] Φ)) (b : ℝ≥0 → (Φ →ₗ[ℂ] ℂ))
    (η : Φ →ₗ[ℂ] ℂ) : Prop :=
  (∀ (V : ℝ≥0) (f : Φ), b V f = η (S V f) - η f) ∧
    ∀ f : Φ, Tendsto (fun V => η (S V f)) atTop (𝓝 0)

/-- A coherent boundary: the coherent functionals converge locally uniformly on the span of every
finite family of test vectors. -/
def HasCoherentBoundary (b : ℝ≥0 → (Φ →ₗ[ℂ] ℂ)) (L : Φ →ₗ[ℂ] ℂ) : Prop :=
  ∀ (n : ℕ) (f : Fin n → Φ),
    TendstoLocallyUniformly (fun V (t : Fin n → ℂ) => Complex.exp (b V (∑ j, t j • f j)))
      (fun t => Complex.exp (L (∑ j, t j • f j))) atTop

theorem coherentChart_eq (β : Φ →ₗ[ℂ] ℂ) {n : ℕ} (f : Fin n → Φ) (t : Fin n → ℂ) :
    β (∑ j, t j • f j) = ∑ j, t j * β (f j) := by
  rw [map_sum]
  simp [smul_eq_mul]

/-- **Weak-star convergence produces a coherent boundary.** -/
theorem hasCoherentBoundary_of_tendstoWeakStar {b : ℝ≥0 → (Φ →ₗ[ℂ] ℂ)} {L : Φ →ₗ[ℂ] ℂ}
    (h : TendstoWeakStar b atTop L) : HasCoherentBoundary b L := by
  intro n f
  have hfam : (fun V (t : Fin n → ℂ) => Complex.exp (b V (∑ j, t j • f j))) =
      fun V (t : Fin n → ℂ) => Complex.exp (∑ j, t j * b V (f j)) := by
    funext V t
    rw [coherentChart_eq]
  have hlim : (fun t : Fin n → ℂ => Complex.exp (L (∑ j, t j • f j))) =
      fun t : Fin n → ℂ => Complex.exp (∑ j, t j * L (f j)) := by
    funext t
    rw [coherentChart_eq]
  rw [hfam, hlim]
  refine tendstoLocallyUniformly_exp ?_ (tendstoLocallyUniformly_linearCombination fun j => h (f j))
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const

/-- **A coherent boundary forces weak-star convergence.** -/
theorem tendstoWeakStar_of_hasCoherentBoundary {b : ℝ≥0 → (Φ →ₗ[ℂ] ℂ)} {L : Φ →ₗ[ℂ] ℂ}
    (h : HasCoherentBoundary b L) : TendstoWeakStar b atTop L := by
  intro f
  have hcomp := (h 1 (fun _ => f)).comp (fun s : ℂ => (fun _ : Fin 1 => s))
    (continuous_pi fun _ => continuous_id)
  have hEq : ∀ β : Φ →ₗ[ℂ] ℂ,
      ((fun t : Fin 1 → ℂ => Complex.exp (β (∑ j, t j • (fun _ : Fin 1 => f) j))) ∘
        fun s : ℂ => (fun _ : Fin 1 => s)) = fun s : ℂ => Complex.exp (s * β f) := by
    intro β
    funext s
    simp [map_smul, smul_eq_mul]
  rw [tendsto_iff_tendstoLocallyUniformly_exp]
  simpa only [hEq] using hcomp

/-! ## Stable primitives and weak-star limits -/

variable {S : ℝ≥0 → (Φ →ₗ[ℂ] Φ)} {b : ℝ≥0 → (Φ →ₗ[ℂ] ℂ)}

/-- A stable primitive produces a weak-star limit, namely its negative. -/
theorem tendstoWeakStar_of_isStablePrimitive {η : Φ →ₗ[ℂ] ℂ}
    (h : IsStablePrimitive S b η) : TendstoWeakStar b atTop (-η) := by
  intro f
  have hsub := (h.2 f).sub_const (η f)
  rw [zero_sub] at hsub
  refine hsub.congr fun V => ?_
  rw [← h.1 V f]

/-- A weak-star limit produces a stable primitive, namely its negative. -/
theorem isStablePrimitive_of_tendstoWeakStar (hcoc : IsSourceCocycle S b) {L : Φ →ₗ[ℂ] ℂ}
    (h : TendstoWeakStar b atTop L) : IsStablePrimitive S b (-L) := by
  have hshift : ∀ (W : ℝ≥0) (f : Φ), L f = b W f + L (S W f) := by
    intro W f
    have h1 : Tendsto (fun V => b (W + V) f) atTop (𝓝 (L f)) :=
      (h f).comp (tendsto_atTop_mono (fun _ => le_add_self) tendsto_id)
    have h2 : Tendsto (fun V => b W f + b V (S W f)) atTop (𝓝 (b W f + L (S W f))) :=
      (h (S W f)).const_add _
    exact tendsto_nhds_unique (h1.congr fun V => hcoc W V f) h2
  refine ⟨fun V f => ?_, fun f => ?_⟩
  · have hs := hshift V f
    simp only [LinearMap.neg_apply]
    linear_combination -hs
  · have hsub := (h f).sub_const (L f)
    rw [sub_self] at hsub
    refine hsub.congr fun V => ?_
    have hs := hshift V f
    simp only [LinearMap.neg_apply]
    linear_combination -hs

/-- **Coherent source functor.**  Existence of a stable primitive, weak-star convergence of the
cocycle, and existence of a coherent boundary are equivalent; the primitive is the negative of the
weak-star limit. -/
theorem coherent_source_tfae (hcoc : IsSourceCocycle S b) :
    [∃ η : Φ →ₗ[ℂ] ℂ, IsStablePrimitive S b η,
      ∃ L : Φ →ₗ[ℂ] ℂ, TendstoWeakStar b atTop L,
      ∃ L : Φ →ₗ[ℂ] ℂ, HasCoherentBoundary b L].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨η, hη⟩
    exact ⟨-η, tendstoWeakStar_of_isStablePrimitive hη⟩
  tfae_have 2 → 3 := by
    rintro ⟨L, hL⟩
    exact ⟨L, hasCoherentBoundary_of_tendstoWeakStar hL⟩
  tfae_have 3 → 2 := by
    rintro ⟨L, hL⟩
    exact ⟨L, tendstoWeakStar_of_hasCoherentBoundary hL⟩
  tfae_have 2 → 1 := by
    rintro ⟨L, hL⟩
    exact ⟨-L, isStablePrimitive_of_tendstoWeakStar hcoc hL⟩
  tfae_finish

/-- The stable primitive is unique. -/
theorem isStablePrimitive_unique {η η' : Φ →ₗ[ℂ] ℂ} (h : IsStablePrimitive S b η)
    (h' : IsStablePrimitive S b η') : η = η' := by
  refine LinearMap.ext fun f => ?_
  have hconst : ∀ V : ℝ≥0, η (S V f) - η' (S V f) = η f - η' f := by
    intro V
    have hs := (h.1 V f).symm.trans (h'.1 V f)
    linear_combination hs
  have hsub : Tendsto (fun V : ℝ≥0 => η (S V f) - η' (S V f)) atTop (𝓝 0) := by
    simpa using (h.2 f).sub (h'.2 f)
  have h0 : Tendsto (fun _ : ℝ≥0 => η f - η' f) atTop (𝓝 0) := hsub.congr hconst
  have huniq : (0 : ℂ) = η f - η' f := tendsto_nhds_unique h0 tendsto_const_nhds
  exact sub_eq_zero.1 huniq.symm

end GaloisForLFunctions.HTGeometry.Interfinity
