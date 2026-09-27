import GaloisForLFunctions.RHTower.STCPrimeLogSquarePoleScaling
import GaloisForLFunctions.HTGeometry.ExponentialFeatureTangentSpace

/-!
# Spectral height fibres of the critical Euler prime boundary

On `H = ℓ²(primes)` the depth-zero source at regulator `a v` and height `t` is

`x_{a,t,v}(p) = v (log p) p^{-(1+av)/2} e^{it log p}`.

Its Gram is `⟪x_{b,s,v}, x_{a,t,v}⟫ = v² F(cv - i(t-s))`, `F(z) = Σ_p (log p)² p^{-1-z}`,
`c = (a+b)/2`.  As `v → 0⁺`:

* at equal heights the Gram tends to `4/(a+b)²`, at distinct fixed heights to `0`;
* if `(t - s)/v → κ` it tends to `(c - iκ)^{-2}`;
* for each `v` the source depends continuously on `t`, so boundary and coalescence limits do not
  commute.

The limiting Gram is realized in `⊕_{t ∈ ℝ} L²((0,∞), r dr)` by `e^{-ar/2}` in the `t` summand,
whose span is dense; this space is not separable, and no separable Hilbert space carries nonzero
strong limits with the limiting Gram at every height.  The endpoint reader
`Λ_τ y = Σ (log p) p^{-1/2} e^{-iτ log p} y(p)` is not closable.
-/

open Complex Filter Topology MeasureTheory Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-! ### The source and its exact Gram -/

/-- The depth-zero source `x_{a,t,v} = v p^{it} b_{av}`. -/
def primeHeightSource (a t v : ℝ) : ℓ²P := (v : ℂ) • stcVerticalPhaseTwist t (stcBoundaryVec (a * v))

theorem primeHeightSource_apply {a v : ℝ} (ha : 0 < a) (hv : 0 < v) (t : ℝ) (p : Nat.Primes) :
    (primeHeightSource a t v : Nat.Primes → ℂ) p =
      ((v * Real.log (p : ℕ) * Real.exp (-((1 + a * v) / 2) * Real.log (p : ℕ)) : ℝ) : ℂ) *
        Complex.exp ((t : ℂ) * Complex.I * (Real.log (p : ℕ) : ℂ)) := by
  change (v : ℂ) * (((p : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) *
    (stcBoundaryVec (a * v) : Nat.Primes → ℂ) p) = _
  rw [stcBoundaryVec_apply (mul_pos ha hv), stcDepthZeroAmplitude_eq_exp, natCast_prime_cpow]
  push_cast
  ring

/-- The prime log-square series at `1 + cv - iω`. -/
theorem primeLogSquareComplex_height_series (c v ω : ℝ) :
    primeLogSquareComplex (1 + ((c * v : ℝ) : ℂ) - (ω : ℂ) * Complex.I) =
      ∑' p : Nat.Primes, (Real.log (p : ℕ) : ℂ) ^ 2 *
        (((p : ℕ) : ℝ) ^ (-1 - c * v) : ℝ) * Complex.exp (Complex.I * ω * Real.log (p : ℕ)) := by
  rw [primeLogSquareComplex_eq_tsum_exp]
  refine tsum_congr fun p => ?_
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  rw [Real.rpow_def_of_pos hp, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **(1) Exact Gram.** `⟪x_{b,s,v}, x_{a,t,v}⟫ = v² F(cv - i(t-s))`, `c = (a+b)/2`. -/
theorem inner_primeHeightSource {a b v : ℝ} (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (s t : ℝ) :
    inner ℂ (primeHeightSource b s v) (primeHeightSource a t v) =
      (v : ℂ) ^ 2 * primeLogSquareComplex
        (1 + (((a + b) / 2 * v : ℝ) : ℂ) - ((t - s : ℝ) : ℂ) * Complex.I) := by
  rw [primeHeightSource, primeHeightSource, inner_smul_left, inner_smul_right,
    inner_stcVerticalPhaseTwist_stcBoundaryVec (mul_pos ha hv) (mul_pos hb hv), Complex.conj_ofReal]
  rw [show (a * v + b * v) / 2 = (a + b) / 2 * v by ring]
  ring

/-- **(5) The Euler identity.** On `Re s > 1`, `F(s) = (log ζ)''(s) - E(s)` with
`E = -H'`, `H(s) = Σ_p Σ_{m ≥ 2} (log p) p^{-ms}` holomorphic on `Re s > 1/2`. -/
theorem primeLogSquareComplex_eq_logDeriv_deriv {s : ℂ} (hs : 1 < s.re) :
    primeLogSquareComplex s =
      deriv (fun z => deriv riemannZeta z / riemannZeta z) s + deriv xiPrimeLogHigherValuation s := by
  rw [primeLogSquareComplex_eq_neg_deriv_continuation hs]
  have hfun : xiPrimeLogDirichletContinuation =
      fun z => (-deriv riemannZeta z / riemannZeta z) - xiPrimeLogHigherValuation z := by
    funext z
    simp [xiPrimeLogDirichletContinuation, infinitePrimeFlux, logDeriv_apply, neg_div]
  have h1 := differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re hs
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : DifferentiableAt ℂ xiPrimeLogHigherValuation s :=
    (differentiableOn_xiPrimeLogHigherValuation_halfPlane s (by simp only [Set.mem_setOf_eq]; linarith)
      ).differentiableAt (hopen.mem_nhds (by simp only [Set.mem_setOf_eq]; linarith))
  rw [hfun, deriv_fun_sub h1 h2]
  have hneg : (fun z => -deriv riemannZeta z / riemannZeta z) =
      fun z => -(deriv riemannZeta z / riemannZeta z) := by funext z; ring
  rw [hneg, deriv.fun_neg]
  ring

/-! ### Boundary limits -/

/-- **(2), equal heights.** `⟪x_{b,t,v}, x_{a,t,v}⟫ → 4/(a+b)²`. -/
theorem tendsto_inner_primeHeightSource_same {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    Tendsto (fun v => inner ℂ (primeHeightSource b t v) (primeHeightSource a t v)) (𝓝[>] 0)
      (𝓝 ((4 / (a + b) ^ 2 : ℝ) : ℂ)) := by
  have hc : 0 < (((a + b) / 2 : ℝ) : ℂ).re := by simp; positivity
  have h := tendsto_sq_mul_primeLogSquareComplex hc (tendsto_const_nhds (x := (((a + b) / 2 : ℝ) : ℂ)))
  have hval : (((((a + b) / 2 : ℝ) : ℂ)) ^ 2)⁻¹ = ((4 / (a + b) ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp; ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  rw [inner_primeHeightSource ha hb hv]
  congr 2
  push_cast
  ring

/-- **(2), distinct heights.** `⟪x_{b,s,v}, x_{a,t,v}⟫ → 0` for `s ≠ t`. -/
theorem tendsto_inner_primeHeightSource_ne {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s t : ℝ}
    (hst : s ≠ t) :
    Tendsto (fun v => inner ℂ (primeHeightSource b s v) (primeHeightSource a t v)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_primeLogSquareComplex_fixed_nonzero_height (c := (a + b) / 2) (τ := s - t)
    (by positivity) (sub_ne_zero.mpr hst)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  rw [inner_primeHeightSource ha hb hv]
  congr 2
  push_cast
  ring

/-- **(3) Coherent moving heights.** If `(t(v) - s(v))/v → κ`, the Gram tends to `(c - iκ)^{-2}`. -/
theorem tendsto_inner_primeHeightSource_moving {a b κ : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s t : ℝ → ℝ} (h : Tendsto (fun v => (t v - s v) / v) (𝓝[>] 0) (𝓝 κ)) :
    Tendsto (fun v => inner ℂ (primeHeightSource b (s v) v) (primeHeightSource a (t v) v)) (𝓝[>] 0)
      (𝓝 (((((a + b) / 2 : ℝ) : ℂ) - (κ : ℂ) * Complex.I) ^ 2)⁻¹) := by
  have hc : 0 < ((((a + b) / 2 : ℝ) : ℂ) - (κ : ℂ) * Complex.I).re := by simp; positivity
  have hw : Tendsto (fun v => (((a + b) / 2 : ℝ) : ℂ) - (((t v - s v) / v : ℝ) : ℂ) * Complex.I)
      (𝓝[>] 0) (𝓝 ((((a + b) / 2 : ℝ) : ℂ) - (κ : ℂ) * Complex.I)) :=
    tendsto_const_nhds.sub ((Complex.continuous_ofReal.tendsto κ).comp h |>.mul tendsto_const_nhds)
  refine (tendsto_sq_mul_primeLogSquareComplex hc hw).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv0 : (v : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hv)
  rw [inner_primeHeightSource ha hb hv]
  congr 2
  push_cast
  field_simp
  ring

/-! ### Continuity in the height -/

/-- `F` is continuous on every closed half-plane `Re s ≥ 1 + δ`, `δ > 0`. -/
theorem continuousOn_primeLogSquareComplex {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn primeLogSquareComplex {s : ℂ | 1 + δ ≤ s.re} := by
  refine continuousOn_tsum (u := fun p : Nat.Primes => stcDepthZeroAmplitude δ p ^ 2)
    (fun p => ?_) ((summable_stcDepthZeroAmplitude_sq_iff δ).mpr hδ) fun p s hs => ?_
  · have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
    exact (continuous_const.mul (continuous_const.cpow continuous_neg
      fun _ => Or.inl (by exact_mod_cast p.property.pos))).continuousOn
  · have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.one_lt.le
    have hp0 : (0 : ℝ) < (p : ℕ) := by linarith
    rw [stcDepthZeroAmplitude_sq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast p.property.pos)]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 ?_) (sq_nonneg _)
    simp only [Set.mem_setOf_eq] at hs
    simp only [Complex.neg_re]
    linarith

/-- For each `v > 0` the source depends continuously on the height. -/
theorem continuous_primeHeightSource {a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    Continuous fun t => primeHeightSource a t v := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hav : 0 < a * v := mul_pos ha hv
  have hF : ContinuousOn primeLogSquareComplex {s : ℂ | 1 + a * v ≤ s.re} :=
    continuousOn_primeLogSquareComplex hav
  have hg : Continuous fun t : ℝ => (1 + (((a + a) / 2 * v : ℝ) : ℂ) - ((t₀ - t : ℝ) : ℂ) * Complex.I) :=
    by fun_prop
  have hmem : ∀ t, (1 + (((a + a) / 2 * v : ℝ) : ℂ) - ((t₀ - t : ℝ) : ℂ) * Complex.I) ∈
      {s : ℂ | 1 + a * v ≤ s.re} := fun t => by
    simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    linarith
  have hcomp : Continuous fun t : ℝ => primeLogSquareComplex
      (1 + (((a + a) / 2 * v : ℝ) : ℂ) - ((t₀ - t : ℝ) : ℂ) * Complex.I) :=
    hF.comp_continuous hg hmem
  have hsq : ∀ t, ‖primeHeightSource a t v - primeHeightSource a t₀ v‖ ^ 2 =
      2 * ((v : ℂ) ^ 2 * primeLogSquareComplex (1 + (((a + a) / 2 * v : ℝ) : ℂ))).re -
        2 * ((v : ℂ) ^ 2 * primeLogSquareComplex
          (1 + (((a + a) / 2 * v : ℝ) : ℂ) - ((t₀ - t : ℝ) : ℂ) * Complex.I)).re := by
    intro t
    rw [@norm_sub_sq ℂ, ← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      inner_primeHeightSource ha ha hv, inner_primeHeightSource ha ha hv, inner_primeHeightSource ha ha hv]
    simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero, RCLike.re_to_complex]
    ring
  have hlim : Tendsto (fun t => ‖primeHeightSource a t v - primeHeightSource a t₀ v‖ ^ 2) (𝓝 t₀) (𝓝 0) := by
    simp_rw [hsq]
    have hG : Continuous fun t : ℝ => ((v : ℂ) ^ 2 * primeLogSquareComplex
        (1 + (((a + a) / 2 * v : ℝ) : ℂ) - ((t₀ - t : ℝ) : ℂ) * Complex.I)).re :=
      Complex.continuous_re.comp (continuous_const.mul hcomp)
    have h := hG.tendsto t₀
    simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero] at h
    have h3 := (tendsto_const_nhds (x := 2 * ((v : ℂ) ^ 2 *
      primeLogSquareComplex (1 + (((a + a) / 2 * v : ℝ) : ℂ))).re)).sub (h.const_mul 2)
    rwa [sub_self] at h3
  have h2 := hlim.sqrt
  simp only [Real.sqrt_zero] at h2
  refine h2.congr fun t => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-- **Non-commuting limits.** At each `v > 0` the Gram is continuous in the height, while the
boundary Gram is `1/a²` on the diagonal and `0` off it. -/
theorem primeHeightSource_limits_noncommuting {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (∀ v, 0 < v → Continuous fun s => inner ℂ (primeHeightSource a s v) (primeHeightSource a t v)) ∧
      Tendsto (fun v => inner ℂ (primeHeightSource a t v) (primeHeightSource a t v)) (𝓝[>] 0)
        (𝓝 ((1 / a ^ 2 : ℝ) : ℂ)) ∧
      ∀ s, s ≠ t →
        Tendsto (fun v => inner ℂ (primeHeightSource a s v) (primeHeightSource a t v)) (𝓝[>] 0) (𝓝 0) := by
  refine ⟨fun v hv => (continuous_primeHeightSource ha hv).inner continuous_const, ?_,
    fun s hs => tendsto_inner_primeHeightSource_ne ha ha hs⟩
  have h := tendsto_inner_primeHeightSource_same ha ha t
  have e : ((4 / (a + a) ^ 2 : ℝ) : ℂ) = ((1 / a ^ 2 : ℝ) : ℂ) := by
    congr 1; field_simp; ring
  rwa [e] at h

theorem inner_self_ofReal_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x : E) : inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

theorem norm_eq_of_inner_self_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {x : E} {r : ℝ} (hr : 0 ≤ r) (h : inner ℂ x x = ((r ^ 2 : ℝ) : ℂ)) : ‖x‖ = r := by
  rw [inner_self_ofReal_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) hr two_ne_zero).mp (Complex.ofReal_injective h)

/-! ### The boundary Hilbert space -/

/-- The boundary space `⊕_{t ∈ ℝ} L²((0,∞), r dr)`. -/
abbrev HeightBoundarySpace := lp (fun _ : ℝ => ExpTangentSpace) 2

/-- The boundary vector of `(a, t)`: `e^{-ar/2}` in the `t` summand. -/
def heightBoundaryVector (a t : ℝ) : HeightBoundarySpace := lp.single 2 t (tangentExpFeature a)

/-- **(4)** The boundary vectors realize the limiting Gram (2). -/
theorem inner_heightBoundaryVector {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s t : ℝ) :
    inner ℂ (heightBoundaryVector b s) (heightBoundaryVector a t) =
      if s = t then ((4 / (a + b) ^ 2 : ℝ) : ℂ) else 0 := by
  rw [heightBoundaryVector, heightBoundaryVector, lp.inner_single_left, lp.single_apply]
  split_ifs with h
  · subst h
    rw [Pi.single_eq_same, inner_tangentExpFeature hb ha, add_comm]
  · rw [Pi.single_eq_of_ne h, inner_zero_right]

/-- **(4)** The boundary vectors span a dense subspace: the completion of the limiting Gram is
`⊕_t L²((0,∞), r dr)`. -/
theorem dense_span_heightBoundaryVector :
    (Submodule.span ℂ (Set.range fun q : Ioi (0 : ℝ) × ℝ => heightBoundaryVector q.1 q.2)
      ).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro z hz
  have hcoord : ∀ t, (z : ℝ → ExpTangentSpace) t = 0 := by
    intro t
    have hperp : (z : ℝ → ExpTangentSpace) t ∈
        (Submodule.span ℂ (Set.range fun a : Ioi (0 : ℝ) => tangentExpFeature a))ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      refine Submodule.span_induction (p := fun u _ => inner ℂ u ((z : ℝ → ExpTangentSpace) t) = 0)
        ?_ (by simp) (fun x y _ _ hx hy => by rw [inner_add_left, hx, hy, add_zero])
        (fun c x _ hx => by rw [inner_smul_left, hx, mul_zero]) hu
      rintro _ ⟨a, rfl⟩
      have := (Submodule.mem_orthogonal _ z).mp hz (heightBoundaryVector a t)
        (Submodule.subset_span ⟨(a, t), rfl⟩)
      rwa [heightBoundaryVector, lp.inner_single_left] at this
    have hbot := Submodule.topologicalClosure_eq_top_iff.mp dense_span_tangentExpFeature
    rw [hbot] at hperp
    exact (Submodule.mem_bot ℂ).mp hperp
  exact lp.ext (funext hcoord)

/-- In a separable inner product space there is no uncountable family of pairwise orthogonal
vectors of one common positive norm. -/
theorem not_separable_of_orthogonal_family {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [TopologicalSpace.SeparableSpace E] {r : ℝ} (hr : 0 < r)
    (Y : ℝ → E) (horth : ∀ s t, s ≠ t → inner ℂ (Y s) (Y t) = 0) (hnorm : ∀ t, ‖Y t‖ = r) :
    False := by
  have hdist : ∀ s t, s ≠ t → r ≤ dist (Y s) (Y t) := by
    intro s t hst
    rw [dist_eq_norm]
    have h := @norm_sub_sq ℂ E _ _ _ (Y s) (Y t)
    rw [horth s t hst, map_zero, mul_zero, sub_zero, hnorm, hnorm] at h
    nlinarith [norm_nonneg (Y s - Y t)]
  have hdisj : (Set.univ : Set ℝ).PairwiseDisjoint fun t => Metric.ball (Y t) (r / 2) := by
    intro s _ t _ hst
    refine Set.disjoint_left.mpr fun x hxs hxt => ?_
    rw [Metric.mem_ball, dist_comm] at hxs hxt
    have := dist_triangle_right (Y s) (Y t) x
    linarith [hdist s t hst]
  have hcount := hdisj.countable_of_isOpen (fun t _ => Metric.isOpen_ball)
    (fun t _ => ⟨Y t, Metric.mem_ball_self (by linarith)⟩)
  exact Cardinal.not_countable_real hcount

/-- **(4) Nonseparability.** The boundary space is not separable. -/
theorem not_separableSpace_heightBoundarySpace :
    ¬ TopologicalSpace.SeparableSpace HeightBoundarySpace := by
  intro hsep
  refine not_separable_of_orthogonal_family (r := 1 / 2) (by norm_num)
    (fun t => heightBoundaryVector 2 t) (fun s t hst => ?_) (fun t => ?_)
  · rw [inner_heightBoundaryVector two_pos two_pos, if_neg hst]
  · have h := inner_heightBoundaryVector two_pos two_pos t t
    rw [if_pos rfl, show (4 / (2 + 2) ^ 2 : ℝ) = (1 / 2) ^ 2 by norm_num] at h
    exact norm_eq_of_inner_self_eq (by norm_num) h

/-- **(4) No separable strong realization.** No separable Hilbert space carries, at every real
height, a family converging strongly as `v → 0⁺` whose Gram tends to the limiting Gram (2). -/
theorem no_separable_strong_realization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [TopologicalSpace.SeparableSpace E] {a : ℝ} (ha : 0 < a) (y : ℝ → ℝ → E) (Y : ℝ → E)
    (hY : ∀ t, Tendsto (y t) (𝓝[>] 0) (𝓝 (Y t)))
    (hG : ∀ s t, Tendsto (fun v => inner ℂ (y s v) (y t v)) (𝓝[>] 0)
      (𝓝 (if s = t then ((1 / a ^ 2 : ℝ) : ℂ) else 0))) : False := by
  have hlim : ∀ s t, inner ℂ (Y s) (Y t) = if s = t then ((1 / a ^ 2 : ℝ) : ℂ) else 0 :=
    fun s t => tendsto_nhds_unique (((hY s).inner (hY t))) (hG s t)
  refine not_separable_of_orthogonal_family (r := 1 / a) (by positivity) Y
    (fun s t hst => by rw [hlim, if_neg hst]) (fun t => ?_)
  have h := hlim t t
  rw [if_pos rfl, show (1 / a ^ 2 : ℝ) = (1 / a) ^ 2 by ring] at h
  exact norm_eq_of_inner_self_eq (by positivity) h

/-- The same obstruction for asymptotically Gram-preserving maps applied to the literal sources. -/
theorem no_separable_gram_preserving_realization {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [TopologicalSpace.SeparableSpace E] {a : ℝ} (ha : 0 < a)
    (T : ℝ → ℓ²P → E) (Y : ℝ → E)
    (hY : ∀ t, Tendsto (fun v => T v (primeHeightSource a t v)) (𝓝[>] 0) (𝓝 (Y t)))
    (hT : ∀ s t, Tendsto (fun v => inner ℂ (T v (primeHeightSource a s v)) (T v (primeHeightSource a t v)) -
      inner ℂ (primeHeightSource a s v) (primeHeightSource a t v)) (𝓝[>] 0) (𝓝 0)) : False := by
  refine no_separable_strong_realization ha (fun t v => T v (primeHeightSource a t v)) Y hY
    fun s t => ?_
  have hsrc : Tendsto (fun v => inner ℂ (primeHeightSource a s v) (primeHeightSource a t v)) (𝓝[>] 0)
      (𝓝 (if s = t then ((1 / a ^ 2 : ℝ) : ℂ) else 0)) := by
    split_ifs with h
    · subst h; exact (primeHeightSource_limits_noncommuting ha s).2.1
    · exact tendsto_inner_primeHeightSource_ne ha ha h
  simpa using (hT s t).add hsrc

/-! ### The singular endpoint reader -/

/-- The endpoint reader `Λ_τ y = Σ (log p) p^{-1/2} e^{-iτ log p} y(p)`. -/
def boundaryReader (τ : ℝ) (y : ℓ²P) : ℂ :=
  ∑' p : Nat.Primes, ((Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    Complex.exp (-((τ : ℂ) * Complex.I * (Real.log (p : ℕ) : ℂ))) * (y : Nat.Primes → ℂ) p

/-- Its natural domain: absolute convergence. -/
def boundaryReaderDomain : Set ℓ²P :=
  {y | Summable fun p : Nat.Primes =>
    Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ‖(y : Nat.Primes → ℂ) p‖}

/-- The probes `z_{a,t,v} = v x_{a,t,v}`. -/
def readerProbe (a t v : ℝ) : ℓ²P := (v : ℂ) • primeHeightSource a t v

theorem norm_sq_readerProbe {a v : ℝ} (ha : 0 < a) (hv : 0 < v) (t : ℝ) :
    ((‖readerProbe a t v‖ ^ 2 : ℝ) : ℂ) =
      (v : ℂ) ^ 4 * primeLogSquareComplex (1 + ((a * v : ℝ) : ℂ)) := by
  rw [← inner_self_ofReal_norm_sq, readerProbe, inner_smul_left,
    inner_smul_right, inner_primeHeightSource ha ha hv, Complex.conj_ofReal]
  simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero]
  rw [show (a + a) / 2 * v = a * v by ring]
  ring

/-- `‖z_{a,t,v}‖ → 0`. -/
theorem tendsto_readerProbe {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Tendsto (fun v => readerProbe a t v) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnsq : Tendsto (fun v => ‖primeHeightSource a t v‖ ^ 2) (𝓝[>] 0) (𝓝 (1 / a ^ 2)) := by
    have h := (Complex.continuous_re.tendsto _).comp (primeHeightSource_limits_noncommuting ha t).2.1
    rw [Complex.ofReal_re] at h
    refine h.congr fun v => ?_
    simp only [Function.comp_apply]
    rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
  have hn := hnsq.sqrt
  have hv0 : Tendsto (fun v : ℝ => |v|) (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hprod := hv0.mul hn
  rw [zero_mul] at hprod
  refine hprod.congr fun v => ?_
  rw [readerProbe, norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_sq (norm_nonneg _)]

theorem readerProbe_mem_domain {a v : ℝ} (ha : 0 < a) (hv : 0 < v) (t : ℝ) :
    readerProbe a t v ∈ boundaryReaderDomain := by
  have hs := (summable_stcDepthZeroAmplitude_sq_iff (a * v / 2)).mpr (by positivity)
  refine (hs.mul_left (v ^ 2)).congr fun p => ?_
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  change v ^ 2 * stcDepthZeroAmplitude (a * v / 2) p ^ 2 = Real.log (p : ℕ) *
    ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ‖(v : ℂ) * (primeHeightSource a t v : Nat.Primes → ℂ) p‖
  rw [primeHeightSource_apply ha hv, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_exp, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hv,
    stcDepthZeroAmplitude_eq_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, mul_one, sub_self, zero_mul, Real.exp_zero, mul_one]
  have hlog : 0 ≤ Real.log (p : ℕ) := Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
  rw [abs_of_nonneg (by positivity), Real.rpow_def_of_pos hp, mul_pow, ← Real.exp_nat_mul]
  have e : Real.exp (Real.log (p : ℕ) * -(1 / 2)) * Real.exp (-((1 + a * v) / 2) * Real.log (p : ℕ))
      = Real.exp (((2 : ℕ) : ℝ) * (-((1 + a * v / 2) / 2) * Real.log (p : ℕ))) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  calc v ^ 2 * (Real.log (p : ℕ) ^ 2 *
        Real.exp (((2 : ℕ) : ℝ) * (-((1 + a * v / 2) / 2) * Real.log (p : ℕ))))
      = v ^ 2 * (Real.log (p : ℕ) ^ 2 * (Real.exp (Real.log (p : ℕ) * -(1 / 2)) *
          Real.exp (-((1 + a * v) / 2) * Real.log (p : ℕ)))) := by rw [e]
    _ = _ := by ring

/-- **(7)** `Λ_τ(z_{a,t,v}) = v² F(av/2 - i(t-τ))`. -/
theorem boundaryReader_readerProbe {a v : ℝ} (ha : 0 < a) (hv : 0 < v) (t τ : ℝ) :
    boundaryReader τ (readerProbe a t v) =
      (v : ℂ) ^ 2 * primeLogSquareComplex
        (1 + ((a * v / 2 : ℝ) : ℂ) - ((t - τ : ℝ) : ℂ) * Complex.I) := by
  rw [boundaryReader, primeLogSquareComplex_eq_tsum_exp, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  change _ * _ * ((v : ℂ) * (primeHeightSource a t v : Nat.Primes → ℂ) p) = _
  rw [primeHeightSource_apply ha hv, Real.rpow_def_of_pos hp]
  push_cast
  have e : ∀ L w x y z u : ℂ, L * Complex.exp x * Complex.exp y *
      (w * (w * L * Complex.exp z * Complex.exp u)) = w ^ 2 * (L ^ 2 * Complex.exp (x + y + z + u)) := by
    intro L w x y z u; simp only [Complex.exp_add]; ring
  rw [e]
  congr 3
  ring

/-- **(7)** The phase-matched reader gives the universal charge `4/a²` at every height. -/
theorem tendsto_boundaryReader_readerProbe_same {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    Tendsto (fun v => boundaryReader τ (readerProbe a τ v)) (𝓝[>] 0)
      (𝓝 ((4 / a ^ 2 : ℝ) : ℂ)) := by
  have hc : 0 < (((a / 2 : ℝ)) : ℂ).re := by simp; positivity
  have h := tendsto_sq_mul_primeLogSquareComplex hc (tendsto_const_nhds (x := ((a / 2 : ℝ) : ℂ)))
  have hval : ((((a / 2 : ℝ)) : ℂ) ^ 2)⁻¹ = ((4 / a ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp; ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  rw [boundaryReader_readerProbe ha hv]
  congr 2
  push_cast
  ring

/-- **(7)** A fixed reader misses every distinct fixed height. -/
theorem tendsto_boundaryReader_readerProbe_ne {a : ℝ} (ha : 0 < a) {t τ : ℝ} (htτ : t ≠ τ) :
    Tendsto (fun v => boundaryReader τ (readerProbe a t v)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_primeLogSquareComplex_fixed_nonzero_height (c := a / 2) (τ := τ - t)
    (by positivity) (sub_ne_zero.mpr htτ.symm)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  rw [boundaryReader_readerProbe ha hv]
  congr 2
  push_cast
  ring

/-- **(7) Nonclosability.** Every linear functional on a subspace containing the probes and agreeing
with `Λ_τ` on them has domain vectors tending to `0` on which it tends to `4/a² ≠ 0`. -/
theorem boundaryReader_not_closable {a : ℝ} (ha : 0 < a) (τ : ℝ) (D : Submodule ℂ ℓ²P)
    (ℓ : D →ₗ[ℂ] ℂ) (hD : ∀ v, 0 < v → readerProbe a τ v ∈ D)
    (hℓ : ∀ v (hv : 0 < v), ℓ ⟨_, hD v hv⟩ = boundaryReader τ (readerProbe a τ v)) :
    ∃ z : ℕ → D, Tendsto (fun n => (z n : ℓ²P)) atTop (𝓝 0) ∧
      Tendsto (fun n => ℓ (z n)) atTop (𝓝 ((4 / a ^ 2 : ℝ) : ℂ)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hpos⟩
  refine ⟨fun n => ⟨_, hD _ (hpos n)⟩, (tendsto_readerProbe ha τ).comp hseq, ?_⟩
  have h := (tendsto_boundaryReader_readerProbe_same ha τ).comp hseq
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [hℓ _ (hpos n)]

/-- The charge is nonzero. -/
theorem boundaryReader_charge_ne_zero {a : ℝ} (ha : 0 < a) : ((4 / a ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (by positivity : (4 / a ^ 2 : ℝ) ≠ 0)

/-- **Fixed grade.** At fixed `g ≠ 0` the normalized compact channel `v² P_{b_{v+2|g|}}` vanishes in
operator norm. -/
theorem tendsto_norm_fixedGrade_channel {g : ℝ} (hg : g ≠ 0) :
    Tendsto (fun v : ℝ => ‖((v ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ
      (stcBoundaryVec (v + 2 * |g|)) (stcBoundaryVec (v + 2 * |g|))‖) (𝓝[>] 0) (𝓝 0) := by
  have ha : 0 < |g| := abs_pos.mpr hg
  have hv2 : Tendsto (fun v : ℝ => v ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hbound := hv2.mul_const (‖stcBoundaryVec (2 * |g|)‖ ^ 2)
  rw [zero_mul] at hbound
  refine squeeze_zero' (Eventually.of_forall fun v => norm_nonneg _) ?_ hbound
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv' : (0 : ℝ) < v := hv
  rw [norm_smul, InnerProductSpace.norm_rankOne, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg v)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg v)
  have h := norm_stcBoundaryVec_shift_le ha hv'.le
  rw [← sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end

end RHTower
