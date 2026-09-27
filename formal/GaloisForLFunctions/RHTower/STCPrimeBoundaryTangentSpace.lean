import GaloisForLFunctions.RHTower.STCPrimeBoundaryHeightFibers
import GaloisForLFunctions.RHTower.STCGammaPrimeHilbertChamber

/-!
# Continuum tangent space of the critical Euler prime source

With `b_u(p) = (log p) p^{-(1+u)/2}` and `S(u) = ‖b_u‖²`:

* `S(v) = v^{-2} + O(1)` and `v² ⟪b_{bv}, b_{av}⟫ → 4/(a+b)² = ⟪f_b, f_a⟫`, `f_a(t) = e^{-at/2}` in
  `L²((0,∞), t dt)`;
* for distinct `a_j > 0`, `‖Σ c_j v b_{a_j v}‖² → ∫₀^∞ t |Σ c_j e^{-a_j t/2}|² dt`, positive unless
  `c = 0`; yet `v b_{av} ⇀ 0` weakly in `ℓ²(primes)`;
* the double-scaled source `v² Q_{κv,λv} = (P_{v b_{(κ-λ)v}} - P_{v b_{(κ+λ)v}})/2` is uniformly
  bounded and strongly null, while its moving matrix elements converge to those of the rank-two
  operator `Q^tan = (P_{f_{κ-λ}} - P_{f_{κ+λ}})/2` with kernel `e^{-κ(t+s)/2} sinh(λ(t+s)/2)`;
* at a fixed grade `g ≠ 0`, `v² Q_{|g|+v,g}` has moving limit `sign(g) P_{f_1}/2` independent of `|g|`,
  and `Q_{|g|+v,g} - sign(g) P_{b_v}/2 → -sign(g) P_{b_{2|g|}}/2` in operator norm.
-/

open Complex Filter Topology MeasureTheory Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry InnerProductSpace

namespace RHTower

noncomputable section

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

theorem ofReal_norm_sq_sum_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (c : Fin n → ℂ) (x : Fin n → E) :
    ((‖∑ i, c i • x i‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, conj (c i) * c j * inner ℂ (x i) (x j) := by
  rw [← inner_self_ofReal_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

theorem inner_half_rankOne_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y w z : E) :
    inner ℂ x (((1 / 2 : ℂ) • (rankOne ℂ y y - rankOne ℂ w w)) z) =
      (1 / 2 : ℂ) * (inner ℂ y z * inner ℂ x y - inner ℂ w z * inner ℂ x w) := by
  change inner ℂ x ((1 / 2 : ℂ) • (rankOne ℂ y y z - rankOne ℂ w w z)) = _
  rw [rankOne_apply, rankOne_apply, inner_smul_right, inner_sub_right, inner_smul_right,
    inner_smul_right]

/-! ### The prime pole and the tangent Gram -/

/-- The rescaled depth-zero vector `v b_{av}`. -/
def tangentProbe (a v : ℝ) : ℓ²P := (v : ℂ) • stcBoundaryVec (a * v)

theorem inner_tangentProbe {a b v : ℝ} (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) :
    inner ℂ (tangentProbe b v) (tangentProbe a v) =
      (v : ℂ) ^ 2 * primeLogSquareComplex (1 + (((a + b) / 2 * v : ℝ) : ℂ)) := by
  rw [tangentProbe, tangentProbe, inner_smul_left, inner_smul_right,
    inner_stcBoundaryVec (mul_pos ha hv) (mul_pos hb hv), Complex.conj_ofReal,
    show (a * v + b * v) / 2 = (a + b) / 2 * v by ring]
  ring

/-- `S(v) = ‖b_v‖² = Σ (log p)² p^{-1-v}`. -/
theorem norm_sq_stcBoundaryVec_eq_moment {v : ℝ} (hv : 0 < v) :
    ‖stcBoundaryVec v‖ ^ 2 = primeLogSquareMoment (1 + v) := by
  rw [norm_sq_stcBoundaryVec hv]
  unfold primeLogSquareMoment
  refine tsum_congr fun p => ?_
  rw [stcDepthZeroAmplitude_sq]
  congr 2
  ring

/-- **(1) Prime pole.** `S(v) - v^{-2}` converges as `v → 0⁺`; in particular `S(v) = v^{-2} + O(1)`. -/
theorem exists_tendsto_norm_sq_stcBoundaryVec_sub_pole :
    ∃ L : ℝ, Tendsto (fun v => ‖stcBoundaryVec v‖ ^ 2 - (v ^ 2)⁻¹) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_primeLogSquareMoment_sub_pole
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with v hv
  rw [norm_sq_stcBoundaryVec_eq_moment hv]

theorem exists_bound_norm_sq_stcBoundaryVec_sub_pole :
    ∃ C : ℝ, ∀ᶠ v in 𝓝[>] (0 : ℝ), |‖stcBoundaryVec v‖ ^ 2 - (v ^ 2)⁻¹| ≤ C := by
  obtain ⟨L, hL⟩ := exists_tendsto_norm_sq_stcBoundaryVec_sub_pole
  refine ⟨|L| + 1, ?_⟩
  filter_upwards [hL.eventually (Metric.ball_mem_nhds L one_pos)] with v hv
  rw [Real.dist_eq] at hv
  have := abs_sub_abs_le_abs_sub (‖stcBoundaryVec v‖ ^ 2 - (v ^ 2)⁻¹) L
  linarith

/-- **(1) Tangent Gram.** `v² ⟪b_{bv}, b_{av}⟫ → 4/(a+b)² = ⟪f_b, f_a⟫`. -/
theorem tendsto_inner_tangentProbe {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun v => inner ℂ (tangentProbe b v) (tangentProbe a v)) (𝓝[>] 0)
      (𝓝 (inner ℂ (tangentExpFeature b) (tangentExpFeature a))) := by
  rw [inner_tangentExpFeature hb ha]
  have hc : 0 < (((a + b) / 2 : ℝ) : ℂ).re := by simp; positivity
  have h := tendsto_sq_mul_primeLogSquareComplex hc (tendsto_const_nhds (x := (((a + b) / 2 : ℝ) : ℂ)))
  have hval : (((((a + b) / 2 : ℝ) : ℂ)) ^ 2)⁻¹ = ((4 / (b + a) ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp; ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  rw [inner_tangentProbe ha hb hv]
  congr 2
  push_cast
  ring

/-- **(2) Continuum limit.** `‖Σ c_j v b_{a_j v}‖² → ‖Σ c_j f_{a_j}‖²`. -/
theorem tendsto_norm_sq_sum_tangentProbe {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (c : Fin n → ℂ) :
    Tendsto (fun v => ‖∑ i, c i • tangentProbe (a i) v‖ ^ 2) (𝓝[>] 0)
      (𝓝 (‖∑ i, c i • tangentExpFeature (a i)‖ ^ 2)) := by
  have hlim : Tendsto (fun v => ∑ i, ∑ j, conj (c i) * c j *
      inner ℂ (tangentProbe (a i) v) (tangentProbe (a j) v)) (𝓝[>] 0)
      (𝓝 (∑ i, ∑ j, conj (c i) * c j *
        inner ℂ (tangentExpFeature (a i)) (tangentExpFeature (a j)))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      tendsto_const_nhds.mul (tendsto_inner_tangentProbe (ha j) (ha i))
  have hlimC : Tendsto (fun v => ((‖∑ i, c i • tangentProbe (a i) v‖ ^ 2 : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((‖∑ i, c i • tangentExpFeature (a i)‖ ^ 2 : ℝ) : ℂ)) := by
    rw [ofReal_norm_sq_sum_smul]
    exact hlim.congr fun v => (ofReal_norm_sq_sum_smul c _).symm
  have h := (Complex.continuous_re.tendsto _).comp hlimC
  rw [Complex.ofReal_re] at h
  exact h.congr fun v => by simp only [Function.comp_apply, Complex.ofReal_re]

/-- **(2)** The limit is the weighted integral and is positive unless every `c_j = 0`. -/
theorem tangent_limit_integral_pos {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    (hinj : Function.Injective a) {c : Fin n → ℂ} (hc : c ≠ 0) :
    0 < ∫ t in Ioi (0 : ℝ), t * ‖∑ i, c i * tangentExpFun (a i) t‖ ^ 2 := by
  rw [← norm_sq_sum_tangentExpFeature_integral a ha c]
  exact pow_pos (norm_sum_tangentExpFeature_pos ha hinj hc) 2

theorem tendsto_norm_sq_tangentProbe {a : ℝ} (ha : 0 < a) :
    Tendsto (fun v => ‖tangentProbe a v‖ ^ 2) (𝓝[>] 0) (𝓝 (1 / a ^ 2)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_inner_tangentProbe ha ha)
  rw [inner_tangentExpFeature ha ha, Complex.ofReal_re,
    show 4 / (a + a) ^ 2 = 1 / a ^ 2 by field_simp; ring] at h
  refine h.congr fun v => ?_
  simp only [Function.comp_apply]
  rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]

/-- Coordinatewise null and eventually bounded implies weakly null in `ℓ²`. -/
theorem tendsto_inner_lp_of_coord_eventually {α : Type*} {l : Filter α} (e : α → ℓ²P) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᶠ t in l, ‖e t‖ ≤ C)
    (hcoord : ∀ i, Tendsto (fun t => (e t : Nat.Primes → ℂ) i) l (𝓝 0)) (z : ℓ²P) :
    Tendsto (fun t => inner ℂ z (e t)) l (𝓝 0) := by
  classical
  let e' : α → ℓ²P := fun t => if ‖e t‖ ≤ C then e t else 0
  have hee' : ∀ᶠ t in l, e' t = e t := hC.mono fun t ht => by simp [e', ht]
  have hC' : ∀ t, ‖e' t‖ ≤ C := fun t => by
    by_cases h : ‖e t‖ ≤ C
    · simp [e', h]
    · simp [e', h, hC0]
  have hcoord' : ∀ i, Tendsto (fun t => (e' t : Nat.Primes → ℂ) i) l (𝓝 0) := fun i =>
    (hcoord i).congr' (hee'.mono fun t ht =>
      congrArg (fun w : ℓ²P => (w : Nat.Primes → ℂ) i) ht.symm)
  exact (tendsto_inner_lp_of_coord e' hC0 hC' hcoord' z).congr'
    (hee'.mono fun t ht => congrArg (inner ℂ z) ht)

/-- **Weak null.** `v b_{av} ⇀ 0` in `ℓ²(primes)`. -/
theorem tendsto_inner_tangentProbe_weak {a : ℝ} (ha : 0 < a) (z : ℓ²P) :
    Tendsto (fun v => inner ℂ z (tangentProbe a v)) (𝓝[>] 0) (𝓝 0) := by
  have hn := tendsto_norm_sq_tangentProbe ha
  have hC : ∀ᶠ v in 𝓝[>] (0 : ℝ), ‖tangentProbe a v‖ ≤ 1 / a ^ 2 + 2 := by
    filter_upwards [hn.eventually (eventually_le_nhds (show 1 / a ^ 2 < 1 / a ^ 2 + 1 by linarith))]
      with v hv
    by_cases h1 : ‖tangentProbe a v‖ ≤ 1
    · linarith [show 0 ≤ 1 / a ^ 2 by positivity]
    · push Not at h1
      nlinarith
  refine tendsto_inner_lp_of_coord_eventually _ (by positivity) hC (fun p => ?_) z
  have hcont : Continuous fun v : ℝ => (v : ℂ) * ((Real.log (p : ℕ) *
      Real.exp (-((1 + a * v) / 2) * Real.log (p : ℕ)) : ℝ) : ℂ) := by fun_prop
  have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [Complex.ofReal_zero, zero_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv' : (0 : ℝ) < v := hv
  rw [tangentProbe, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    stcBoundaryVec_apply (mul_pos ha hv'), stcDepthZeroAmplitude_eq_exp]

/-! ### The double-scaled source -/

/-- The chamber operator `Q_{u,g} = (P_{b_{u-g}} - P_{b_{u+g}})/2`. -/
def stcGammaChamberOp (u g : ℝ) : ℓ²P →L[ℂ] ℓ²P :=
  (1 / 2 : ℂ) • (rankOne ℂ (stcBoundaryVec (u - g)) (stcBoundaryVec (u - g)) -
    rankOne ℂ (stcBoundaryVec (u + g)) (stcBoundaryVec (u + g)))

/-- In the chamber `|g| < u` it is the operator with matrix `Q_{u,g}`. -/
theorem hasLpMatrix_stcGammaChamberOp {u g : ℝ} (hu : |g| < u) :
    HasLpMatrix (stcGammaChamberOp u g) (stcGammaKernel u g) := by
  have h := hasLpMatrix_stcGammaKernel_chamber hu
  have h1 : 0 < u - g := by linarith [le_abs_self g]
  have h2 : 0 < u + g := by linarith [neg_abs_le g]
  have e1 : stcBoundaryVec (u - g) = lpOfReal (stcDepthZeroAmplitude (u - g))
      ((stcGammaChannels_summable_iff u g).mpr hu).1 := by rw [stcBoundaryVec, dif_pos h1]
  have e2 : stcBoundaryVec (u + g) = lpOfReal (stcDepthZeroAmplitude (u + g))
      ((stcGammaChannels_summable_iff u g).mpr hu).2 := by rw [stcBoundaryVec, dif_pos h2]
  rw [stcGammaChamberOp, e1, e2]
  exact h

theorem rankOne_smul_self (x : ℓ²P) (v : ℝ) :
    rankOne ℂ ((v : ℂ) • x) ((v : ℂ) • x) = ((v ^ 2 : ℝ) : ℂ) • rankOne ℂ x x := by
  refine ContinuousLinearMap.ext fun y => ?_
  change rankOne ℂ ((v : ℂ) • x) ((v : ℂ) • x) y = ((v ^ 2 : ℝ) : ℂ) • rankOne ℂ x x y
  rw [rankOne_apply, rankOne_apply, inner_smul_left, Complex.conj_ofReal, smul_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- **(5)** `v² Q_{κv,λv} = (P_{v b_{(κ-λ)v}} - P_{v b_{(κ+λ)v}})/2`. -/
theorem sq_smul_stcGammaChamberOp (κ l v : ℝ) :
    ((v ^ 2 : ℝ) : ℂ) • stcGammaChamberOp (κ * v) (l * v) =
      (1 / 2 : ℂ) • (rankOne ℂ (tangentProbe (κ - l) v) (tangentProbe (κ - l) v) -
        rankOne ℂ (tangentProbe (κ + l) v) (tangentProbe (κ + l) v)) := by
  rw [tangentProbe, tangentProbe, rankOne_smul_self, rankOne_smul_self, stcGammaChamberOp,
    show κ * v - l * v = (κ - l) * v by ring, show κ * v + l * v = (κ + l) * v by ring,
    smul_comm, ← smul_sub]

/-- **(5)** The double-scaled source is eventually uniformly bounded. -/
theorem eventually_norm_sq_smul_stcGammaChamberOp_le {κ l : ℝ} (hκ : |l| < κ) :
    ∀ᶠ v in 𝓝[>] (0 : ℝ), ‖((v ^ 2 : ℝ) : ℂ) • stcGammaChamberOp (κ * v) (l * v)‖ ≤
      (1 / (κ - l) ^ 2 + 1 / (κ + l) ^ 2 + 2) / 2 := by
  have h1 : 0 < κ - l := by linarith [le_abs_self l]
  have h2 : 0 < κ + l := by linarith [neg_abs_le l]
  filter_upwards [(tendsto_norm_sq_tangentProbe h1).eventually
      (eventually_le_nhds (show 1 / (κ - l) ^ 2 < 1 / (κ - l) ^ 2 + 1 by linarith)),
    (tendsto_norm_sq_tangentProbe h2).eventually
      (eventually_le_nhds (show 1 / (κ + l) ^ 2 < 1 / (κ + l) ^ 2 + 1 by linarith))] with v hv1 hv2
  rw [sq_smul_stcGammaChamberOp, norm_smul]
  have hn := norm_sub_le (rankOne ℂ (tangentProbe (κ - l) v) (tangentProbe (κ - l) v))
    (rankOne ℂ (tangentProbe (κ + l) v) (tangentProbe (κ + l) v))
  simp only [norm_rankOne] at hn
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf]
  nlinarith

/-- **(5)** It tends strongly to zero on the fixed prime Hilbert space. -/
theorem tendsto_sq_smul_stcGammaChamberOp_apply {κ l : ℝ} (hκ : |l| < κ) (y : ℓ²P) :
    Tendsto (fun v => (((v ^ 2 : ℝ) : ℂ) • stcGammaChamberOp (κ * v) (l * v)) y) (𝓝[>] 0)
      (𝓝 0) := by
  have h1 : 0 < κ - l := by linarith [le_abs_self l]
  have h2 : 0 < κ + l := by linarith [neg_abs_le l]
  have hP : ∀ {a : ℝ}, 0 < a →
      Tendsto (fun v => rankOne ℂ (tangentProbe a v) (tangentProbe a v) y) (𝓝[>] 0) (𝓝 0) := by
    intro a ha
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hw := tendsto_inner_tangentProbe_weak ha y
    have hbd := (tendsto_norm_sq_tangentProbe ha).sqrt
    have hprod := (tendsto_norm.comp hw).mul hbd
    simp only [norm_zero, zero_mul, Function.comp_apply] at hprod
    refine hprod.congr fun v => ?_
    rw [rankOne_apply, norm_smul, Real.sqrt_sq (norm_nonneg _), ← inner_conj_symm, RCLike.norm_conj]
  have h := ((hP h1).sub (hP h2)).const_smul (1 / 2 : ℂ)
  simp only [sub_zero, smul_zero] at h
  refine h.congr fun v => ?_
  rw [sq_smul_stcGammaChamberOp]
  rfl

/-- **(6)** The tangent operator `Q^tan = (P_{f_{κ-λ}} - P_{f_{κ+λ}})/2`. -/
def tangentGradeOp (κ l : ℝ) : ExpTangentSpace →L[ℂ] ExpTangentSpace :=
  (1 / 2 : ℂ) • (rankOne ℂ (tangentExpFeature (κ - l)) (tangentExpFeature (κ - l)) -
    rankOne ℂ (tangentExpFeature (κ + l)) (tangentExpFeature (κ + l)))

/-- **(6)** Moving matrix elements converge to those of `Q^tan`. -/
theorem tendsto_matrixElement_sq_smul_stcGammaChamberOp {κ l α β : ℝ} (hκ : |l| < κ)
    (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun v => inner ℂ (tangentProbe α v)
        ((((v ^ 2 : ℝ) : ℂ) • stcGammaChamberOp (κ * v) (l * v)) (tangentProbe β v))) (𝓝[>] 0)
      (𝓝 (inner ℂ (tangentExpFeature α) (tangentGradeOp κ l (tangentExpFeature β)))) := by
  have h1 : 0 < κ - l := by linarith [le_abs_self l]
  have h2 : 0 < κ + l := by linarith [neg_abs_le l]
  simp_rw [sq_smul_stcGammaChamberOp, inner_half_rankOne_sub]
  rw [tangentGradeOp, inner_half_rankOne_sub]
  exact tendsto_const_nhds.mul (((tendsto_inner_tangentProbe hβ h1).mul
    (tendsto_inner_tangentProbe h1 hα)).sub ((tendsto_inner_tangentProbe hβ h2).mul
      (tendsto_inner_tangentProbe h2 hα)))

/-- **(6)** `Q^tan` is compact. -/
theorem isCompactOperator_tangentGradeOp (κ l : ℝ) : IsCompactOperator (tangentGradeOp κ l) := by
  rw [tangentGradeOp, FunLike.coe_smul, FunLike.coe_sub]
  exact ((isCompactOperator_innerRankOne _ _).sub (isCompactOperator_innerRankOne _ _)).smul _

/-- **(6)** For `λ ≠ 0` the operator `Q^tan` has rank exactly two. -/
theorem finrank_range_tangentGradeOp {κ l : ℝ} (hκ : |l| < κ) (hl : l ≠ 0) :
    Module.finrank ℂ (LinearMap.range (tangentGradeOp κ l : ExpTangentSpace →ₗ[ℂ] ExpTangentSpace))
      = 2 := by
  have h1 : 0 < κ - l := by linarith [le_abs_self l]
  have h2 : 0 < κ + l := by linarith [neg_abs_le l]
  set f₁ := tangentExpFeature (κ - l)
  set f₂ := tangentExpFeature (κ + l)
  have hrange : LinearMap.range (tangentGradeOp κ l : ExpTangentSpace →ₗ[ℂ] ExpTangentSpace) ≤
      Submodule.span ℂ {f₁, f₂} := by
    rintro _ ⟨h, rfl⟩
    simp only [ContinuousLinearMap.coe_coe, tangentGradeOp, _root_.smul_apply,
      _root_.sub_apply, rankOne_apply]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [f₁]))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [f₂]))
  have hle : Module.finrank ℂ (LinearMap.range
      (tangentGradeOp κ l : ExpTangentSpace →ₗ[ℂ] ExpTangentSpace)) ≤ 2 :=
    finrank_range_le_two hrange
  haveI : FiniteDimensional ℂ (Submodule.span ℂ ({f₁, f₂} : Set ExpTangentSpace)) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  haveI : FiniteDimensional ℂ (LinearMap.range
      (tangentGradeOp κ l : ExpTangentSpace →ₗ[ℂ] ExpTangentSpace)) :=
    Submodule.finiteDimensional_of_le hrange
  have hk0 : κ ≠ 0 := by linarith [abs_nonneg l]
  -- the images of `f₁`, `f₂` are independent
  set G₁₁ : ℂ := ((1 / (κ - l) ^ 2 : ℝ) : ℂ)
  set G₂₂ : ℂ := ((1 / (κ + l) ^ 2 : ℝ) : ℂ)
  set G₁₂ : ℂ := ((1 / κ ^ 2 : ℝ) : ℂ)
  have i11 : inner ℂ f₁ f₁ = G₁₁ := by
    rw [inner_tangentExpFeature h1 h1]; congr 1; field_simp; ring
  have i22 : inner ℂ f₂ f₂ = G₂₂ := by
    rw [inner_tangentExpFeature h2 h2]; congr 1; field_simp; ring
  have i12 : inner ℂ f₁ f₂ = G₁₂ := by
    rw [inner_tangentExpFeature h1 h2]; congr 1; field_simp; ring
  have i21 : inner ℂ f₂ f₁ = G₁₂ := by
    rw [inner_tangentExpFeature h2 h1]; congr 1; field_simp; ring
  have hind : LinearIndependent ℂ ![f₁, f₂] := by
    have := linearIndependent_tangentExpFeature (a := ![κ - l, κ + l])
      (fun i => by fin_cases i <;> simp [h1, h2])
      (fun i j hij => by
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> exact hl (by linarith))
    convert this using 1
    funext i; fin_cases i <;> rfl
  have himg : ∀ h, tangentGradeOp κ l h =
      (1 / 2 : ℂ) • (inner ℂ f₁ h • f₁ - inner ℂ f₂ h • f₂) := fun h => by
    simp only [tangentGradeOp, _root_.smul_apply, _root_.sub_apply,
      rankOne_apply, f₁, f₂]
  have hdet : G₁₁ * G₂₂ - G₁₂ * G₁₂ ≠ 0 := by
    simp only [G₁₁, G₂₂, G₁₂]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    refine Complex.ofReal_ne_zero.mpr ?_
    have hk : 0 < κ := by linarith [abs_nonneg l]
    have hsq : (κ - l) ^ 2 * (κ + l) ^ 2 < κ ^ 4 := by
      have : (κ - l) * (κ + l) = κ ^ 2 - l ^ 2 := by ring
      have hl2 : 0 < l ^ 2 := by positivity
      have hpos : 0 < κ ^ 2 - l ^ 2 := by nlinarith [sq_abs l, abs_nonneg l]
      nlinarith
    have e : 1 / (κ - l) ^ 2 * (1 / (κ + l) ^ 2) - 1 / κ ^ 2 * (1 / κ ^ 2) =
        (κ ^ 4 - (κ - l) ^ 2 * (κ + l) ^ 2) / ((κ - l) ^ 2 * (κ + l) ^ 2 * κ ^ 4) := by
      field_simp
    rw [e]
    exact div_ne_zero (by linarith) (by positivity)
  have hind2 : LinearIndependent ℂ ![tangentGradeOp κ l f₁, tangentGradeOp κ l f₂] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_two, himg, himg, i11, i12, i21, i22] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
    have hc' : ((1 / 2 : ℂ) * (c 0 * G₁₁ + c 1 * G₁₂)) • f₁ +
        (-(1 / 2 : ℂ) * (c 0 * G₁₂ + c 1 * G₂₂)) • f₂ = 0 := by
      rw [← hc]; module
    have hco := Fintype.linearIndependent_iff.mp hind ![(1 / 2 : ℂ) * (c 0 * G₁₁ + c 1 * G₁₂),
      -(1 / 2 : ℂ) * (c 0 * G₁₂ + c 1 * G₂₂)] (by
        rw [Fin.sum_univ_two]; simpa using hc')
    have e0 := hco 0
    have e1 := hco 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_eq_zero,
      one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or, neg_eq_zero] at e0 e1
    have hc0 : c 0 = 0 := by
      have : c 0 * (G₁₁ * G₂₂ - G₁₂ * G₁₂) = 0 := by linear_combination G₂₂ * e0 - G₁₂ * e1
      exact (mul_eq_zero.mp this).resolve_right hdet
    have hc1 : c 1 = 0 := by
      have : c 1 * (G₁₁ * G₂₂ - G₁₂ * G₁₂) = 0 := by linear_combination G₁₁ * e1 - G₁₂ * e0
      exact (mul_eq_zero.mp this).resolve_right hdet
    intro i; fin_cases i
    · exact hc0
    · exact hc1
  have hge : 2 ≤ Module.finrank ℂ (LinearMap.range
      (tangentGradeOp κ l : ExpTangentSpace →ₗ[ℂ] ExpTangentSpace)) := by
    have hsub : Submodule.span ℂ (Set.range ![tangentGradeOp κ l f₁, tangentGradeOp κ l f₂]) ≤
        LinearMap.range (tangentGradeOp κ l : ExpTangentSpace →ₗ[ℂ] ExpTangentSpace) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact ⟨f₁, rfl⟩
      · exact ⟨f₂, rfl⟩
    have := Submodule.finrank_mono hsub
    rwa [finrank_span_eq_card hind2, Fintype.card_fin] at this
  omega

/-- **(7)** The integral kernel of `Q^tan` relative to `s ds` is `e^{-κ(t+s)/2} sinh(λ(t+s)/2)`. -/
theorem tangentGradeOp_kernel {κ l : ℝ} (hκ : |l| < κ) (h : ExpTangentSpace) :
    (tangentGradeOp κ l h : ℝ → ℂ) =ᵐ[tangentMeasure] fun t =>
      ∫ s in Ioi (0 : ℝ), s • (((Real.exp (-(κ * (t + s)) / 2) *
        Real.sinh (l * (t + s) / 2) : ℝ) : ℂ) * (h : ℝ → ℂ) s) := by
  have h1 : 0 < κ - l := by linarith [le_abs_self l]
  have h2 : 0 < κ + l := by linarith [neg_abs_le l]
  have hinner : ∀ {a : ℝ}, 0 < a → inner ℂ (tangentExpFeature a) h =
      ∫ s in Ioi (0 : ℝ), s • ((tangentExpFun a s) * (h : ℝ → ℂ) s) := by
    intro a ha
    rw [L2.inner_def, ← integral_tangentMeasure]
    refine integral_congr_ae ?_
    filter_upwards [tangentExpFeature_ae ha] with s hs
    rw [hs, RCLike.inner_apply, tangentExpFun, Complex.conj_ofReal, mul_comm]
  have hint : ∀ {a : ℝ}, 0 < a → IntegrableOn (fun s => s • ((tangentExpFun a s) * (h : ℝ → ℂ) s))
      (Ioi 0) := by
    intro a ha
    rw [← integrable_tangentMeasure_iff]
    have := L2.integrable_inner (𝕜 := ℂ) (tangentExpFeature a) h
    refine this.congr ?_
    filter_upwards [tangentExpFeature_ae ha] with s hs
    rw [hs, RCLike.inner_apply, tangentExpFun, Complex.conj_ofReal, mul_comm]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (rankOne ℂ (tangentExpFeature (κ - l))
      (tangentExpFeature (κ - l)) h - rankOne ℂ (tangentExpFeature (κ + l))
        (tangentExpFeature (κ + l)) h),
    Lp.coeFn_sub (rankOne ℂ (tangentExpFeature (κ - l)) (tangentExpFeature (κ - l)) h)
      (rankOne ℂ (tangentExpFeature (κ + l)) (tangentExpFeature (κ + l)) h),
    Lp.coeFn_smul (inner ℂ (tangentExpFeature (κ - l)) h) (tangentExpFeature (κ - l)),
    Lp.coeFn_smul (inner ℂ (tangentExpFeature (κ + l)) h) (tangentExpFeature (κ + l)),
    tangentExpFeature_ae h1, tangentExpFeature_ae h2] with t e1 e2 e3 e4 e5 e6
  rw [tangentGradeOp, _root_.smul_apply, _root_.sub_apply, e1, Pi.smul_apply, e2, Pi.sub_apply, rankOne_apply, rankOne_apply, e3, e4, Pi.smul_apply,
    Pi.smul_apply, e5, e6, hinner h1, hinner h2, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    ← integral_mul_const, ← integral_mul_const, ← integral_sub ((hint h1).mul_const _)
      ((hint h2).mul_const _), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [tangentExpFun, Complex.real_smul, Real.sinh_eq]
  push_cast
  have k1 : Complex.exp (-(((κ : ℂ) - l) * s) / 2) * Complex.exp (-(((κ : ℂ) - l) * t) / 2) =
      Complex.exp (-((κ : ℂ) * (t + s)) / 2) * Complex.exp ((l : ℂ) * (t + s) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have k2 : Complex.exp (-(((κ : ℂ) + l) * s) / 2) * Complex.exp (-(((κ : ℂ) + l) * t) / 2) =
      Complex.exp (-((κ : ℂ) * (t + s)) / 2) * Complex.exp (-((l : ℂ) * (t + s) / 2)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  linear_combination (1 / 2 * (s : ℂ) * (h : ℝ → ℂ) s) * k1 -
    (1 / 2 * (s : ℂ) * (h : ℝ → ℂ) s) * k2

/-! ### Fixed grade -/

theorem inner_smul_rankOne_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℂ) (x y w z : E) :
    inner ℂ x ((c • (rankOne ℂ y y - rankOne ℂ w w)) z) =
      c * (inner ℂ y z * inner ℂ x y - inner ℂ w z * inner ℂ x w) := by
  rw [_root_.smul_apply, _root_.sub_apply, rankOne_apply, rankOne_apply, inner_smul_right,
    inner_sub_right, inner_smul_right, inner_smul_right]

/-- `v² Q_{|g|+v,g} = sign(g)(P_{v b_v} - P_{v b_{v+2|g|}})/2`. -/
theorem sq_smul_stcGammaWallOp (g v : ℝ) :
    ((v ^ 2 : ℝ) : ℂ) • stcGammaWallOp g v =
      ((Real.sign g / 2 : ℝ) : ℂ) • (rankOne ℂ (tangentProbe 1 v) (tangentProbe 1 v) -
        rankOne ℂ ((v : ℂ) • stcBoundaryVec (v + 2 * |g|)) ((v : ℂ) • stcBoundaryVec (v + 2 * |g|))) := by
  rw [stcGammaWallOp, tangentProbe, one_mul, rankOne_smul_self, rankOne_smul_self, smul_comm,
    ← smul_sub]

/-- The second channel of the fixed-grade wall escapes to zero in norm. -/
theorem tendsto_norm_smul_stcBoundaryVec_shift {g : ℝ} (hg : g ≠ 0) :
    Tendsto (fun v : ℝ => ‖(v : ℂ) • stcBoundaryVec (v + 2 * |g|)‖) (𝓝[>] 0) (𝓝 0) := by
  have ha : 0 < |g| := abs_pos.mpr hg
  have hv0 : Tendsto (fun v : ℝ => |v|) (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hb := hv0.mul_const ‖stcBoundaryVec (2 * |g|)‖
  rw [zero_mul] at hb
  refine squeeze_zero' (Eventually.of_forall fun v => norm_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv' : (0 : ℝ) < v := hv
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_stcBoundaryVec_shift_le ha hv'.le) (abs_nonneg v)

/-- **Fixed grade.** The moving matrix elements of `v² Q_{|g|+v,g}` converge to those of
`sign(g) P_{f_1}/2`, independent of `|g|`. -/
theorem tendsto_matrixElement_fixedGrade {g α β : ℝ} (hg : g ≠ 0) (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun v => inner ℂ (tangentProbe α v)
        ((((v ^ 2 : ℝ) : ℂ) • stcGammaWallOp g v) (tangentProbe β v))) (𝓝[>] 0)
      (𝓝 (((Real.sign g / 2 : ℝ) : ℂ) * inner ℂ (tangentExpFeature α)
        (rankOne ℂ (tangentExpFeature 1) (tangentExpFeature 1) (tangentExpFeature β)))) := by
  set w : ℝ → ℓ²P := fun v : ℝ => ((v : ℝ) : ℂ) • stcBoundaryVec (v + 2 * |g|)
  have hw := tendsto_norm_smul_stcBoundaryVec_shift hg
  have hnα := (tendsto_norm_sq_tangentProbe hα).sqrt
  have hnβ := (tendsto_norm_sq_tangentProbe hβ).sqrt
  have hsecond : Tendsto (fun v => inner ℂ (w v) (tangentProbe β v) * inner ℂ (tangentProbe α v) (w v))
      (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd := (((hw.mul hnβ).mul hnα).mul hw)
    simp only [zero_mul, mul_zero] at hbd
    refine squeeze_zero (fun v => norm_nonneg _) (fun v => ?_) hbd
    rw [norm_mul, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have h1 := norm_inner_le_norm (𝕜 := ℂ) (w v) (tangentProbe β v)
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (tangentProbe α v) (w v)
    calc ‖inner ℂ (w v) (tangentProbe β v)‖ * ‖inner ℂ (tangentProbe α v) (w v)‖
        ≤ (‖w v‖ * ‖tangentProbe β v‖) * (‖tangentProbe α v‖ * ‖w v‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hfirst := (tendsto_inner_tangentProbe hβ one_pos).mul (tendsto_inner_tangentProbe one_pos hα)
  have h := (hfirst.sub hsecond).const_mul (((Real.sign g / 2 : ℝ) : ℂ))
  rw [sub_zero] at h
  rw [rankOne_apply, inner_smul_right]
  refine h.congr fun v => ?_
  rw [sq_smul_stcGammaWallOp, inner_smul_rankOne_sub]

/-- `b_w → b_c` in `ℓ²(primes)` as `w → c > 0`. -/
theorem tendsto_stcBoundaryVec {c : ℝ} (hc : 0 < c) :
    Tendsto stcBoundaryVec (𝓝 c) (𝓝 (stcBoundaryVec c)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hF := continuousOn_primeLogSquareComplex (half_pos hc)
  have hmem : ∀ w, c / 2 < w → (1 + ((w : ℝ) : ℂ)) ∈ {s : ℂ | 1 + c / 2 ≤ s.re} := fun w hw => by
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith
  have hnear : ∀ᶠ w in 𝓝 c, c / 2 < w := eventually_gt_nhds (by linarith)
  have hcont : ∀ φ : ℝ → ℝ, Continuous φ → φ c = c → Tendsto (fun w =>
      primeLogSquareComplex (1 + ((φ w : ℝ) : ℂ))) (𝓝 c) (𝓝 (primeLogSquareComplex (1 + c))) := by
    intro φ hφ hφc
    have hlim : Tendsto (fun w => (1 : ℂ) + ((φ w : ℝ) : ℂ)) (𝓝 c) (𝓝 (1 + ((φ c : ℝ) : ℂ))) :=
      tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto _).comp (hφ.tendsto c))
    rw [hφc] at hlim
    exact (hF.continuousWithinAt (hmem c (by linarith))).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hlim, (hφ.tendsto c).eventually (eventually_gt_nhds (by
        rw [hφc]; linarith)) |>.mono fun w hw => hmem _ hw⟩)
  have h1 := hcont id continuous_id rfl
  have h2 := hcont (fun w => (w + c) / 2) (by fun_prop) (by ring)
  have hsq : Tendsto (fun w => ‖stcBoundaryVec w - stcBoundaryVec c‖ ^ 2) (𝓝 c) (𝓝 0) := by
    have hre := (Complex.continuous_re.tendsto _).comp ((h1.add
      (tendsto_const_nhds (x := primeLogSquareComplex (1 + ((c : ℝ) : ℂ))))).sub (h2.const_mul 2))
    have e : (primeLogSquareComplex (1 + c) + primeLogSquareComplex (1 + c) -
        2 * primeLogSquareComplex (1 + c)).re = 0 := by ring_nf; simp
    rw [e] at hre
    refine hre.congr' ?_
    filter_upwards [hnear] with w hw
    have hw0 : 0 < w := by linarith
    simp only [Function.comp_apply, id]
    rw [@norm_sub_sq ℂ, ← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      inner_stcBoundaryVec hw0 hw0, inner_stcBoundaryVec hc hc, inner_stcBoundaryVec hc hw0,
      RCLike.re_to_complex, RCLike.re_to_complex, RCLike.re_to_complex,
      show (w + w) / 2 = w by ring, show (c + c) / 2 = c by ring, show (c + w) / 2 = (w + c) / 2 by ring]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero]
    ring
  have h3 := hsq.sqrt
  simp only [Real.sqrt_zero] at h3
  exact h3.congr fun w => Real.sqrt_sq (norm_nonneg _)

/-- `x ↦ |x⟩⟨x|` is continuous in operator norm. -/
theorem continuous_rankOne_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    Continuous fun x : E => rankOne ℂ x x := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ x : E, ‖rankOne ℂ x x - rankOne ℂ y y‖ ≤ ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ := by
    intro x
    have e : rankOne ℂ x x - rankOne ℂ y y = rankOne ℂ (x - y) x + rankOne ℂ y (x - y) := by
      rw [map_sub, map_sub, _root_.sub_apply]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_rankOne, norm_rankOne]
  have h1 : Tendsto (fun x : E => ‖x - y‖) (𝓝 y) (𝓝 0) := by
    rw [← tendsto_iff_norm_sub_tendsto_zero]; exact tendsto_id
  have h2 : Tendsto (fun x : E => ‖x‖) (𝓝 y) (𝓝 ‖y‖) := continuous_norm.tendsto y
  have hb := (h1.mul h2).add (tendsto_const_nhds (x := ‖y‖) |>.mul h1)
  simp only [zero_mul, mul_zero, add_zero] at hb
  exact squeeze_zero (fun x => norm_nonneg _) key hb

/-- **Finite part.** `Q_{|g|+v,g} - sign(g) P_{b_v}/2 → -sign(g) P_{b_{2|g|}}/2` in operator norm. -/
theorem tendsto_stcGammaWallOp_sub_leading {g : ℝ} (hg : g ≠ 0) :
    Tendsto (fun v => stcGammaWallOp g v -
        ((Real.sign g / 2 : ℝ) : ℂ) • rankOne ℂ (stcBoundaryVec v) (stcBoundaryVec v)) (𝓝[>] 0)
      (𝓝 (-(((Real.sign g / 2 : ℝ) : ℂ) • rankOne ℂ (stcBoundaryVec (2 * |g|))
        (stcBoundaryVec (2 * |g|))))) := by
  have ha : 0 < |g| := abs_pos.mpr hg
  have hshift : Tendsto (fun v : ℝ => v + 2 * |g|) (𝓝[>] 0) (𝓝 (2 * |g|)) := by
    have h0 : Tendsto (fun v : ℝ => v + 2 * |g|) (𝓝 0) (𝓝 (0 + 2 * |g|)) :=
      tendsto_id.add tendsto_const_nhds
    rw [zero_add] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hb := (tendsto_stcBoundaryVec (by positivity : 0 < 2 * |g|)).comp hshift
  have hrank : Continuous fun x : ℓ²P => rankOne ℂ x x := continuous_rankOne_self
  have h := ((hrank.tendsto _).comp hb).const_smul (((Real.sign g / 2 : ℝ) : ℂ))
  refine h.neg.congr fun v => ?_
  simp only [Function.comp_apply]
  rw [stcGammaWallOp, smul_sub, sub_sub_cancel_left]

end

end RHTower
