import GaloisForLFunctions.RHTower.PhysicalOrdinateExactExtractor
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Maximal collapse of the fixed physical-ordinate graph

In the Hilbert sum `ℓ²(ℕ) ⊕ ℓ²(P)`, let `R` be a closed linear relation containing the pairs
`(y_{σ_j,γ}, v_{β,γ})` for a sequence `σ_j ↓ 1` and every height `γ`.  Then `R` contains
`R_min = ℓ²(squarefree) ⊕ ℓ²(P)` **(10)**, and `R_min` is itself such a relation, hence the smallest.

* For fixed `γ`, `y_{σ,γ} ⇀ 0` as `σ ↓ 1` (unit vectors, coordinates `O(Q(σ)^{-1/2})`), and a closed
  subspace is weakly closed, so `(0, v_{β,γ}) ∈ R`.
* The seam vectors span a dense subspace of `ℓ²(P)` (Bohr uniqueness, `b_β(p) ≠ 0`), so `(0, g) ∈ R`
  for every `g`.
* At one fixed level the source vectors span a dense subspace of `ℓ²(squarefree)`, so `(f, 0) ∈ R`
  for every squarefree-supported `f`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

local notation "ℓ²ℕ" => lp (fun _ : ℕ => ℂ) 2
local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2
local notation "𝔾" => WithLp 2 (ℓ²ℕ × ℓ²P)

/-! ### The Hilbert sum -/

/-- The pair `(f, g)` in the Hilbert sum `ℓ²(ℕ) ⊕ ℓ²(P)`. -/
def graphPair (f : ℓ²ℕ) (g : ℓ²P) : 𝔾 := WithLp.toLp 2 (f, g)

theorem inner_graphPair (f f' : ℓ²ℕ) (g g' : ℓ²P) :
    inner ℂ (graphPair f g) (graphPair f' g') = inner ℂ f f' + inner ℂ g g' := by
  simp [graphPair, WithLp.prod_inner_apply]

theorem graphPair_add (f f' : ℓ²ℕ) (g g' : ℓ²P) :
    graphPair f g + graphPair f' g' = graphPair (f + f') (g + g') := by
  simp [graphPair, ← WithLp.toLp_add]

theorem graphPair_sub (f f' : ℓ²ℕ) (g g' : ℓ²P) :
    graphPair f g - graphPair f' g' = graphPair (f - f') (g - g') := by
  simp [graphPair, ← WithLp.toLp_sub]

theorem continuous_graphPair_left (g : ℓ²P) : Continuous fun f : ℓ²ℕ => graphPair f g :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ℓ²ℕ ℓ²P).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

theorem continuous_graphPair_right (f : ℓ²ℕ) : Continuous fun g : ℓ²P => graphPair f g :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ℓ²ℕ ℓ²P).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

theorem graphPair_eta (x : 𝔾) : graphPair (WithLp.ofLp x).1 (WithLp.ofLp x).2 = x := rfl

/-! ### The squarefree coordinate subspace -/

/-- `ℓ²(squarefree)`: the vectors vanishing off the squarefree integers. -/
def squarefreeSubspace : Submodule ℂ ℓ²ℕ where
  carrier := {f | ∀ n, ¬ Squarefree n → (f : ℕ → ℂ) n = 0}
  add_mem' := by
    intro f g hf hg n hn
    simp [hf n hn, hg n hn]
  zero_mem' := by intro n _; rfl
  smul_mem' := by
    intro c f hf n hn
    simp [hf n hn]

theorem coord_eq_inner_single (f : ℓ²ℕ) (n : ℕ) :
    (f : ℕ → ℂ) n = inner ℂ (lp.single 2 n (1 : ℂ)) f := by
  classical
  rw [lp.inner_single_left]; simp

theorem isClosed_squarefreeSubspace : IsClosed (squarefreeSubspace : Set ℓ²ℕ) := by
  have : (squarefreeSubspace : Set ℓ²ℕ) =
      ⋂ n ∈ {n : ℕ | ¬ Squarefree n}, {f : ℓ²ℕ | inner ℂ (lp.single 2 n (1 : ℂ)) f = 0} := by
    ext f
    simp only [SetLike.mem_coe, mem_iInter, mem_setOf_eq, ← coord_eq_inner_single]
    rfl
  rw [this]
  exact isClosed_biInter fun n _ =>
    isClosed_eq (continuous_const.inner continuous_id) continuous_const

theorem ordinateSource_mem_squarefreeSubspace (σ γ : ℝ) :
    ordinateSource σ γ ∈ squarefreeSubspace := by
  intro n hn
  by_cases hσ : 1 < σ
  · rw [ordinateSource_apply hσ, infiniteMobiusSignedWeight,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    simp
  · rw [ordinateSource_of_le (not_lt.mp hσ)]; rfl

/-- `R_min = ℓ²(squarefree) ⊕ ℓ²(P)`. -/
def minimalRelation : Submodule ℂ 𝔾 :=
  squarefreeSubspace.comap
    ((LinearMap.fst ℂ ℓ²ℕ ℓ²P).comp (WithLp.linearEquiv 2 ℂ (ℓ²ℕ × ℓ²P)).toLinearMap)

theorem mem_minimalRelation (x : 𝔾) :
    x ∈ minimalRelation ↔ (WithLp.ofLp x).1 ∈ squarefreeSubspace := Iff.rfl

theorem isClosed_minimalRelation : IsClosed (minimalRelation : Set 𝔾) :=
  isClosed_squarefreeSubspace.preimage
    (continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℂ ℓ²ℕ ℓ²P).continuous)

/-- `R_min` contains every retained pair. -/
theorem graphPair_mem_minimalRelation {β : ℝ} (hβ : β ∈ Ioo 0 1) (σ γ : ℝ) :
    graphPair (ordinateSource σ (-γ)) (seamVector β hβ γ) ∈ minimalRelation :=
  ordinateSource_mem_squarefreeSubspace σ (-γ)

/-! ### Weak nullity of the source at a fixed height -/

theorem tendsto_inv_squarefreeMobiusTotal :
    Tendsto (fun σ => (squarefreeMobiusTotal σ)⁻¹) (𝓝[>] 1) (𝓝 0) := by
  have h1 := tendsto_sub_one_mul_squarefreeMobiusTotal
  have h2 : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun σ : ℝ => σ - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have hpi : (6 / Real.pi ^ 2) ≠ 0 := by positivity
  have h3 := h2.div h1 hpi
  rw [zero_div] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hs : (1 : ℝ) < σ := hσ
  have hQ := squarefreeMobiusTotal_pos hs
  have hs1 : σ - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
  rw [Pi.div_apply]
  field_simp

theorem norm_ordinateSource_apply_le {σ : ℝ} (hσ : 1 < σ) (γ : ℝ) (n : ℕ) :
    ‖(ordinateSource σ γ : ℕ → ℂ) n‖ ≤ Real.sqrt ((squarefreeMobiusTotal σ)⁻¹) := by
  rw [ordinateSource_apply hσ, norm_mul, GaloisForLFunctions.norm_expChar, one_mul]
  have h := norm_sourceWeight_sq_le hσ n
  have hQ := squarefreeMobiusTotal_pos hσ
  have hle : (n : ℝ) ^ (-σ) / squarefreeMobiusTotal σ ≤ (squarefreeMobiusTotal σ)⁻¹ := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [Real.zero_rpow (by linarith : -σ ≠ 0)]; positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      rw [div_eq_mul_inv]
      have : (n : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
      have hinv : 0 ≤ (squarefreeMobiusTotal σ)⁻¹ := by positivity
      nlinarith
  exact Real.le_sqrt_of_sq_le (h.trans hle)

/-- **For each fixed height, `x_{σ,γ} ⇀ 0` as `σ ↓ 1`.** -/
theorem tendsto_inner_ordinateSource_zero (a : ℓ²ℕ) (γ : ℝ) :
    Tendsto (fun σ => inner ℂ a (ordinateSource σ γ)) (𝓝[>] 1) (𝓝 0) := by
  refine tendsto_inner_lp_of_coord (fun σ => ordinateSource σ γ) zero_le_one
    (fun σ => norm_ordinateSource_le σ γ) (fun n => ?_) a
  have hsq := (Real.continuous_sqrt.tendsto 0).comp tendsto_inv_squarefreeMobiusTotal
  rw [Real.sqrt_zero] at hsq
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun σ => norm_nonneg _) ?_ hsq
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact norm_ordinateSource_apply_le hσ γ n

/-! ### Density of the seam and of the source -/

theorem summable_norm_mul_of_summable_sq {ι : Type*} {u v : ι → ℂ} (hu : Summable fun i => ‖u i‖ ^ 2)
    (hv : Summable fun i => ‖v i‖ ^ 2) : Summable fun i => ‖u i * v i‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) ((hu.add hv).div_const 2)
  rw [norm_mul]
  nlinarith [sq_nonneg (‖u i‖ - ‖v i‖)]

theorem dirichletReadout_eq_tsum {c : ℕ → ℂ} (hc : WeightedAbsSummable c 0) (hc0 : c 0 = 0)
    (t : ℝ) : dirichletReadout c t = ∑' n, c n * GaloisForLFunctions.expChar (Real.log n) t := by
  rw [dirichletReadout_ofReal hc le_rfl, GaloisForLFunctions.expSeriesCarrier]
  have hs : Summable fun n => c n * GaloisForLFunctions.expChar (Real.log n) t :=
    Summable.of_norm_bounded (hc.summable_norm le_rfl) fun n => by
      rw [norm_mul, GaloisForLFunctions.norm_expChar, mul_one]
  rw [hs.tsum_eq_zero_add, hc0, zero_mul, zero_add]

theorem weightedAbsSummable_zero_of_summable_norm {c : ℕ → ℂ} (hc : Summable fun n => ‖c n‖) :
    WeightedAbsSummable c 0 := by
  unfold WeightedAbsSummable
  simpa using hc

/-- **The seam vectors span a dense subspace of `ℓ²(P)`.** -/
theorem eq_zero_of_inner_seamVector_eq_zero {β : ℝ} (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2)
    (w : ℓ²P) (hw : ∀ γ, inner ℂ w (seamVector β hβ γ) = 0) : w = 0 := by
  classical
  set d : ℕ → ℂ := fun n => if h : n.Prime then (starRingEnd ℂ) ((w : Nat.Primes → ℂ) ⟨n, h⟩) *
    (seamAmplitude β n : ℂ) else 0 with hd
  have hinjP : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  have hsupp : ∀ n ∉ Set.range (fun p : Nat.Primes => (p : ℕ)), d n = 0 := by
    intro n hn
    have : ¬ n.Prime := fun h => hn ⟨⟨n, h⟩, rfl⟩
    simp [hd, this]
  have hdP : ∀ p : Nat.Primes, d p = (starRingEnd ℂ) ((w : Nat.Primes → ℂ) p) *
      (seamAmplitude β p : ℂ) := fun p => by simp [hd, p.2]
  have hdsum : Summable fun n => ‖d n‖ := by
    refine (hinjP.summable_iff (f := fun n => ‖d n‖) fun n hn => by rw [hsupp n hn, norm_zero]).mp ?_
    refine (summable_norm_mul_of_summable_sq (u := fun p : Nat.Primes =>
      (starRingEnd ℂ) ((w : Nat.Primes → ℂ) p)) (v := fun p : Nat.Primes =>
        (seamAmplitude β p : ℂ)) ?_ ?_).congr fun p => ?_
    · simpa using summable_norm_sq_lp w
    · simpa [Complex.norm_real, sq_abs] using summable_seamAmplitude_sq_primes hβ
    · simp only [Function.comp_apply, hdP]
  have hdw := weightedAbsSummable_zero_of_summable_norm hdsum
  have hd0 : d 0 = 0 := by simp [hd, Nat.not_prime_zero]
  have hread : ∀ t : ℝ, dirichletReadout d t = 0 := by
    intro t
    rw [dirichletReadout_eq_tsum hdw hd0, ← hw t, lp.inner_eq_tsum]
    rw [← hinjP.tsum_eq (f := fun n => d n * GaloisForLFunctions.expChar (Real.log n) t)
      (fun n hn => by
        by_contra h
        exact hn (by simp only; rw [hsupp n h, zero_mul]))]
    refine tsum_congr fun p => ?_
    simp only [hdP, seamVector_apply, RCLike.inner_apply]
    ring
  ext p
  have h := coeff_eq_zero_of_dirichletReadout_eq_zero hdw le_rfl hread p.2.pos
  rw [hdP] at h
  have hb : (seamAmplitude β p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (seamAmplitude_ne_zero hβ2 p.2.two_le)
  have := (mul_eq_zero.mp h).resolve_right hb
  rw [map_eq_zero] at this
  simpa using this

/-- **At a fixed level the source spans `ℓ²(squarefree)` densely**: a vector orthogonal to every
`x_{σ,γ}` vanishes on the squarefree coordinates. -/
theorem coord_eq_zero_of_inner_ordinateSource_eq_zero {σ : ℝ} (hσ : 1 < σ) (u : ℓ²ℕ)
    (hu : ∀ γ, inner ℂ u (ordinateSource σ γ) = 0) {n : ℕ} (hn : Squarefree n) :
    (u : ℕ → ℂ) n = 0 := by
  set d : ℕ → ℂ := fun n => (starRingEnd ℂ) ((u : ℕ → ℂ) n) * sourceWeight σ n with hd
  have hwsq : Summable fun n => ‖sourceWeight σ n‖ ^ 2 := by
    refine (summable_squarefreeMobiusProbability hσ).congr fun n => ?_
    exact (norm_infiniteMobiusSignedWeight_sq hσ n).symm
  have hdsum : Summable fun n => ‖d n‖ :=
    summable_norm_mul_of_summable_sq (by simpa using summable_norm_sq_lp u) hwsq
  have hdw := weightedAbsSummable_zero_of_summable_norm hdsum
  have hd0 : d 0 = 0 := by simp [hd, sourceWeight_zero]
  have hread : ∀ t : ℝ, dirichletReadout d t = 0 := by
    intro t
    rw [dirichletReadout_eq_tsum hdw hd0, ← hu (-t), lp.inner_eq_tsum]
    refine tsum_congr fun m => ?_
    rw [ordinateSource_apply hσ, RCLike.inner_apply, hd]
    simp only [GaloisForLFunctions.expChar]
    push_cast
    ring_nf
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by subst h; exact not_squarefree_zero hn
  have h := coeff_eq_zero_of_dirichletReadout_eq_zero hdw le_rfl hread hn0
  have hwn : sourceWeight σ n ≠ 0 := by
    intro h0
    have := norm_infiniteMobiusSignedWeight_sq hσ n
    rw [show infiniteMobiusSignedWeight σ n = sourceWeight σ n from rfl, h0, norm_zero] at this
    have hprob : 0 < squarefreeMobiusProbability σ n := by
      rw [squarefreeMobiusProbability, squarefreeMobiusMass, if_pos hn]
      exact div_pos (by positivity) (squarefreeMobiusTotal_pos hσ)
    nlinarith
  have := (mul_eq_zero.mp h).resolve_right hwn
  rw [map_eq_zero] at this
  exact this

/-! ### The collapse theorem (10) -/

/-- The embedding `g ↦ (0, g)`. -/
def verticalEmbedding : ℓ²P →ₗ[ℂ] 𝔾 :=
  (WithLp.linearEquiv 2 ℂ (ℓ²ℕ × ℓ²P)).symm.toLinearMap ∘ₗ LinearMap.inr ℂ ℓ²ℕ ℓ²P

/-- The embedding `f ↦ (f, 0)`. -/
def horizontalEmbedding : ℓ²ℕ →ₗ[ℂ] 𝔾 :=
  (WithLp.linearEquiv 2 ℂ (ℓ²ℕ × ℓ²P)).symm.toLinearMap ∘ₗ LinearMap.inl ℂ ℓ²ℕ ℓ²P

theorem verticalEmbedding_apply (g : ℓ²P) : verticalEmbedding g = graphPair 0 g := rfl

theorem horizontalEmbedding_apply (f : ℓ²ℕ) : horizontalEmbedding f = graphPair f 0 := rfl

theorem closure_span_eq_top_of_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (S : Set E)
    (hS : ∀ w : E, (∀ s ∈ S, inner ℂ w s = 0) → w = 0) :
    (Submodule.span ℂ S).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro w hw
  refine hS w fun s hs => ?_
  have := (Submodule.mem_orthogonal' _ w).mp hw s (Submodule.subset_span hs)
  exact this

/-- **Graph collapse (10).**  Every closed linear relation containing the retained pairs
`(y_{σ_j,γ}, v_{β,γ})`, `σ_j ↓ 1`, contains `R_min = ℓ²(squarefree) ⊕ ℓ²(P)`. -/
theorem minimalRelation_le {β : ℝ} (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2) (σs : ℕ → ℝ)
    (hσs : Tendsto σs atTop (𝓝[>] 1)) (R : Submodule ℂ 𝔾) (hR : IsClosed (R : Set 𝔾))
    (hmem : ∀ j γ, graphPair (ordinateSource (σs j) (-γ)) (seamVector β hβ γ) ∈ R) :
    minimalRelation ≤ R := by
  have hRR : Rᗮᗮ = R := by
    rw [Submodule.orthogonal_orthogonal_eq_closure]; exact hR.submodule_topologicalClosure_eq
  -- (a) the vertical seam pairs
  have hvert : ∀ γ, graphPair 0 (seamVector β hβ γ) ∈ R := by
    intro γ
    rw [← hRR, Submodule.mem_orthogonal]
    intro u hu
    rw [← graphPair_eta u, inner_graphPair, inner_zero_right, zero_add]
    have hzero : ∀ j, inner ℂ (ordinateSource (σs j) (-γ)) (WithLp.ofLp u).1 +
        inner ℂ (seamVector β hβ γ) (WithLp.ofLp u).2 = 0 := by
      intro j
      have := (Submodule.mem_orthogonal R u).mp hu _ (hmem j γ)
      rwa [← graphPair_eta u, inner_graphPair] at this
    have hlim : Tendsto (fun j => inner ℂ (ordinateSource (σs j) (-γ)) (WithLp.ofLp u).1)
        atTop (𝓝 0) := by
      have h := ((tendsto_inner_ordinateSource_zero (WithLp.ofLp u).1 (-γ)).comp hσs).star
      simp only [star_zero] at h
      refine h.congr fun j => ?_
      simp [Function.comp_apply]
    have hconst : Tendsto (fun j => inner ℂ (ordinateSource (σs j) (-γ)) (WithLp.ofLp u).1)
        atTop (𝓝 (-inner ℂ (seamVector β hβ γ) (WithLp.ofLp u).2)) :=
      tendsto_const_nhds.congr fun j => by rw [eq_neg_of_add_eq_zero_left (hzero j)]
    have h0 := tendsto_nhds_unique hconst hlim
    rw [neg_eq_zero] at h0
    rw [← inner_conj_symm, h0, map_zero]
  -- (b) all vertical pairs
  set R₂ := R.comap verticalEmbedding with hR₂
  have hR₂c : IsClosed (R₂ : Set ℓ²P) := hR.preimage (continuous_graphPair_right 0)
  have hR₂top : R₂ = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← closure_span_eq_top_of_orthogonal (Set.range (seamVector β hβ)) (fun w hw =>
      eq_zero_of_inner_seamVector_eq_zero hβ hβ2 w fun γ => hw _ ⟨γ, rfl⟩)]
    refine Submodule.topologicalClosure_minimal _ ?_ hR₂c
    rw [Submodule.span_le]
    rintro _ ⟨γ, rfl⟩
    exact hvert γ
  -- (c) the horizontal squarefree pairs
  obtain ⟨j₀, hj₀⟩ := (hσs.eventually self_mem_nhdsWithin).exists
  have hs₀ : 1 < σs j₀ := hj₀
  set R₁ := R.comap horizontalEmbedding with hR₁
  have hR₁c : IsClosed (R₁ : Set ℓ²ℕ) := hR.preimage (continuous_graphPair_left 0)
  have hhor : ∀ γ, ordinateSource (σs j₀) γ ∈ R₁ := by
    intro γ
    change graphPair _ 0 ∈ R
    have := R.sub_mem (hmem j₀ (-γ)) (hvert (-γ))
    rwa [graphPair_sub, sub_zero, sub_self, neg_neg] at this
  have hsq : squarefreeSubspace ≤ R₁ := by
    have hle : squarefreeSubspace ≤ (Submodule.span ℂ (Set.range (ordinateSource (σs j₀))))ᗮᗮ := by
      intro f hf
      rw [Submodule.mem_orthogonal]
      intro u hu
      have hu' : ∀ γ, inner ℂ u (ordinateSource (σs j₀) γ) = 0 := fun γ =>
        (Submodule.mem_orthogonal' _ u).mp hu _ (Submodule.subset_span ⟨γ, rfl⟩)
      rw [lp.inner_eq_tsum]
      refine (tsum_congr fun n => ?_).trans tsum_zero
      by_cases hn : Squarefree n
      · rw [coord_eq_zero_of_inner_ordinateSource_eq_zero hs₀ u hu' hn, inner_zero_left]
      · rw [hf n hn, inner_zero_right]
    rw [Submodule.orthogonal_orthogonal_eq_closure] at hle
    exact hle.trans (Submodule.topologicalClosure_minimal _ (by
      rw [Submodule.span_le]; rintro _ ⟨γ, rfl⟩; exact hhor γ) hR₁c)
  -- (d) assemble
  intro x hx
  rw [← graphPair_eta x]
  have hsum : graphPair (WithLp.ofLp x).1 (WithLp.ofLp x).2 =
      graphPair (WithLp.ofLp x).1 0 + graphPair 0 (WithLp.ofLp x).2 := by
    rw [graphPair_add, add_zero, zero_add]
  rw [hsum]
  refine R.add_mem (hsq hx) ?_
  have : (WithLp.ofLp x).2 ∈ R₂ := by rw [hR₂top]; trivial
  exact this

/-- **`R_min` is the smallest closed relation containing the retained pairs.** -/
theorem isLeast_minimalRelation {β : ℝ} (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2) (σs : ℕ → ℝ)
    (hσs : Tendsto σs atTop (𝓝[>] 1)) :
    IsLeast {R : Submodule ℂ 𝔾 | IsClosed (R : Set 𝔾) ∧
      ∀ j γ, graphPair (ordinateSource (σs j) (-γ)) (seamVector β hβ γ) ∈ R} minimalRelation :=
  ⟨⟨isClosed_minimalRelation, fun j γ => graphPair_mem_minimalRelation hβ (σs j) γ⟩,
    fun R hR => minimalRelation_le hβ hβ2 σs hσs R hR.1 hR.2⟩

/-- The vertical fibre of such a relation is the whole prime space: its output is unconstrained. -/
theorem graphPair_zero_mem_of_closed {β : ℝ} (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2) (σs : ℕ → ℝ)
    (hσs : Tendsto σs atTop (𝓝[>] 1)) (R : Submodule ℂ 𝔾) (hR : IsClosed (R : Set 𝔾))
    (hmem : ∀ j γ, graphPair (ordinateSource (σs j) (-γ)) (seamVector β hβ γ) ∈ R) (g : ℓ²P) :
    graphPair 0 g ∈ R :=
  minimalRelation_le hβ hβ2 σs hσs R hR hmem (by
    change (0 : ℓ²ℕ) ∈ squarefreeSubspace
    exact squarefreeSubspace.zero_mem)

end RHTower
