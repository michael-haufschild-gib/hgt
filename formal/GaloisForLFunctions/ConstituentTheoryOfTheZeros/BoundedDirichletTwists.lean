import GaloisForLFunctions.ConstituentTheoryOfTheZeros.ABoundedConstituentLivesInTheBohrStrip
import GaloisForLFunctions.HTGeometry.MontelOpenSetSubsequence
import GaloisForLFunctions.PrimeTorusTheory.TheHullOverTheTorus
import GaloisForLFunctions.RHTower.ZetaTwistedDirichletHeadsNearAZeroHaveVanishingHaarMass

/-!
# Unitary twists of bounded Dirichlet series

Every prime twist of a bounded holomorphic Dirichlet series has a bounded
holomorphic continuation to the same half-plane. Kronecker approximation gives
vertical translates with the required coefficients; Montel gives a limit, and
absolute convergence identifies that limit far to the right. Three-lines carries
continuity in the prime phases throughout the half-plane. Nonzero vertical
limits preserve a single-line restriction on zeros, so the whole prime-torus
family of a pure series is pure.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry _root_.RHTower

noncomputable section
namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

/-- Twisting a coefficient multiplies its Dirichlet term by the same phase. -/
theorem term_primePhaseTwist (a : ℕ → ℂ) (ω : Nat.Primes → Circle) (s : ℂ) (n : ℕ) :
    LSeries.term (fun m => a m * primePhaseTwist ω m) s n =
      primePhaseTwist ω n * LSeries.term a s n := by
  by_cases hn : n = 0
  · simp only [hn, LSeries.term_zero, mul_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    ring

/-- Absolute convergence is unchanged by a unitary prime twist. -/
theorem lSeriesSummable_primePhaseTwist {a : ℕ → ℂ} {s : ℂ}
    (hs : LSeriesSummable a s) (ω : Nat.Primes → Circle) :
    LSeriesSummable (fun m => a m * primePhaseTwist ω m) s := by
  apply hs.norm.of_norm_bounded
  intro n
  rw [term_primePhaseTwist, norm_mul, norm_primePhaseTwist, one_mul]

/-- Vertical translation realizes the corresponding unitary prime twist. -/
theorem term_verticalTranslate_eq_primePhaseTwist (a : ℕ → ℂ) (s : ℂ) (t : ℝ) (n : ℕ) :
    LSeries.term a (s + (t : ℂ) * I) n =
      primePhaseTwist (circlePhaseFlow primeFrequency t) n * LSeries.term a s n := by
  by_cases hn : n = 0
  · simp only [hn, LSeries.term_zero, mul_zero]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hphase : primePhaseTwist (circlePhaseFlow primeFrequency t) n =
      (n : ℂ) ^ (-((t : ℂ) * I)) := by
    simpa only [Complex.ofReal_natCast] using primePhaseTwist_circlePhaseFlow t hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, hphase,
    Complex.cpow_add _ _ hnC, Complex.cpow_neg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Every prime-torus point is approached by vertical prime phases. -/
theorem exists_primePhaseFlow_sequence (ω : Nat.Primes → Circle) :
    ∃ t : ℕ → ℝ, Tendsto (fun n => circlePhaseFlow primeFrequency (t n)) atTop (𝓝 ω) := by
  classical
  have hdense := dense_forwardOrbit_circlePhaseFlow rationallyIndependentSequence_primeFrequency 0
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense ω)
  choose t ht htv using hv
  refine ⟨t, ?_⟩
  simpa only [htv] using hlim

/-- The unitary twist inherits a bounded holomorphic continuation from the
original Dirichlet series. -/
theorem exists_bounded_holomorphic_primePhaseTwist
    {a : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ M : ℝ}
    (hx : x < u₀) (hsum : LSeriesSummable a (u₀ : ℂ))
    (hF : DifferentiableOn ℂ F {s : ℂ | x < s.re})
    (hM : ∀ s, x < s.re → ‖F s‖ ≤ M)
    (hFL : ∀ s, u₀ < s.re → F s = LSeries a s)
    (ω : Nat.Primes → Circle) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | x < s.re} ∧
      (∀ s, x < s.re → ‖G s‖ ≤ M) ∧
      (∀ s, u₀ < s.re → G s = LSeries (fun m => a m * primePhaseTwist ω m) s) ∧
      ∃ τ : ℕ → ℝ,
        Tendsto (fun n => circlePhaseFlow primeFrequency (τ n)) atTop (𝓝 ω) ∧
        TendstoLocallyUniformlyOn (fun n s => F (s + (τ n : ℂ) * I)) G atTop
          {s : ℂ | x < s.re} := by
  obtain ⟨t, ht⟩ := exists_primePhaseFlow_sequence ω
  have hU : IsOpen {s : ℂ | x < s.re} := isOpen_lt continuous_const continuous_re
  have hshift (s : ℂ) (n : ℕ) : (s + (t n : ℂ) * I).re = s.re := by simp
  have htr (n : ℕ) : DifferentiableOn ℂ (fun s => F (s + (t n : ℂ) * I))
      {s : ℂ | x < s.re} := by
    intro s hs
    have hs' : x < (s + (t n : ℂ) * I).re := by rw [hshift]; exact hs
    exact ((hF.differentiableAt (hU.mem_nhds hs')).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hbd (n : ℕ) (s : ℂ) (hs : x < s.re) : ‖F (s + (t n : ℂ) * I)‖ ≤ M :=
    hM _ (by rw [hshift]; exact hs)
  obtain ⟨φ, hφ, G, hconv⟩ := exists_tendstoLocallyUniformlyOn_subseq_of_bounded hU htr hbd
  refine ⟨G, hconv.differentiableOn (Eventually.of_forall fun n => htr (φ n)) hU,
    ?_, ?_, fun n => t (φ n), ht.comp hφ.tendsto_atTop, hconv⟩
  · intro s hs
    exact le_of_tendsto (hconv.tendsto_at hs).norm
      (Eventually.of_forall fun n => hbd (φ n) s hs)
  · intro s hs
    have hssum : LSeriesSummable a s := hsum.of_re_le_re (by simpa using hs.le)
    have hphase : Tendsto (fun n => circlePhaseFlow primeFrequency (t (φ n)))
        atTop (𝓝 ω) := ht.comp hφ.tendsto_atTop
    have hterms (m : ℕ) :
        Tendsto (fun n => LSeries.term a (s + (t (φ n) : ℂ) * I) m) atTop
          (𝓝 (LSeries.term (fun k => a k * primePhaseTwist ω k) s m)) := by
      have h := ((continuous_primePhaseTwist m).tendsto ω).comp hphase
      simpa only [Function.comp_apply, term_verticalTranslate_eq_primePhaseTwist, term_primePhaseTwist]
        using h.mul_const (LSeries.term a s m)
    have hdom : ∀ᶠ n in atTop, ∀ m,
        ‖LSeries.term a (s + (t (φ n) : ℂ) * I) m‖ ≤ ‖LSeries.term a s m‖ := by
      filter_upwards with n m
      rw [term_verticalTranslate_eq_primePhaseTwist, norm_mul, norm_primePhaseTwist, one_mul]
    have hseries := tendsto_tsum_of_dominated_convergence hssum.norm hterms hdom
    have hpoint := hconv.tendsto_at (lt_trans hx hs)
    have heq : (fun n => F (s + (t (φ n) : ℂ) * I)) =
        fun n => LSeries a (s + (t (φ n) : ℂ) * I) := by
      funext n
      exact hFL _ (by rw [hshift]; exact hs)
    rw [heq] at hpoint
    exact tendsto_nhds_unique hpoint hseries

/-- A surviving Dirichlet coefficient prevents a twisted continuation from
vanishing identically on its half-plane. -/
theorem exists_ne_zero_of_primePhaseTwist_coefficient
    {a : ℕ → ℂ} {G : ℂ → ℂ} {x u₀ : ℝ} {n : ℕ}
    (hsum : LSeriesSummable a (u₀ : ℂ)) (ω : Nat.Primes → Circle)
    (hG : DifferentiableOn ℂ G {s : ℂ | x < s.re})
    (hGL : ∀ s, u₀ < s.re → G s = LSeries (fun m => a m * primePhaseTwist ω m) s)
    (hn : a (n + 1) ≠ 0) : ∃ s : ℂ, x < s.re ∧ G s ≠ 0 := by
  by_contra h
  push Not at h
  have hbound (s : ℂ) (hs : x < s.re) : ‖G s‖ ≤ 0 := by
    rw [h s hs, norm_zero]
  have hcoeff := norm_coeff_le_of_bounded (lSeriesSummable_primePhaseTwist hsum ω)
    hG hbound hGL (σ := x + 1) (by linarith) n
  have hpos : 0 < ‖a (n + 1) * primePhaseTwist ω (n + 1)‖ *
      ((n : ℝ) + 1) ^ (-(x + 1)) := by
    rw [norm_mul, norm_primePhaseTwist, mul_one]
    exact mul_pos (norm_pos_iff.mpr hn) (Real.rpow_pos_of_pos (by positivity) _)
  exact (not_le_of_gt hpos) hcoeff

/-- A nonzero vertical limit preserves a single-line restriction on zeros. -/
theorem pure_of_vertical_limit
    {F G : ℂ → ℂ} {x c : ℝ} {t : ℕ → ℝ}
    (hF : DifferentiableOn ℂ F {s : ℂ | x < s.re})
    (hG : DifferentiableOn ℂ G {s : ℂ | x < s.re})
    (hconv : TendstoLocallyUniformlyOn (fun n s => F (s + (t n : ℂ) * I)) G atTop
      {s : ℂ | x < s.re})
    (hpure : ∀ s, x < s.re → F s = 0 → s.re = c)
    (hne : ∃ s : ℂ, x < s.re ∧ G s ≠ 0)
    {s : ℂ} (hs : x < s.re) (hz : G s = 0) : s.re = c := by
  by_contra hsc
  have hU : IsOpen {z : ℂ | x < z.re} := isOpen_lt continuous_const continuous_re
  have hV : IsOpen {z : ℂ | x < z.re ∧ z.re ≠ c} :=
    hU.inter (isOpen_compl_singleton.preimage continuous_re)
  have hshift (z : ℂ) (n : ℕ) : (z + (t n : ℂ) * I).re = z.re := by simp
  have htr (n : ℕ) : DifferentiableOn ℂ (fun z => F (z + (t n : ℂ) * I))
      {z : ℂ | x < z.re ∧ z.re ≠ c} := by
    intro z hz
    have hz' : x < (z + (t n : ℂ) * I).re := by rw [hshift]; exact hz.1
    exact ((hF.differentiableAt (hU.mem_nhds hz')).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hno (n : ℕ) (z : ℂ) (hz : x < z.re ∧ z.re ≠ c) :
      F (z + (t n : ℂ) * I) ≠ 0 := by
    intro hzero
    have h := hpure _ (by rw [hshift]; exact hz.1) hzero
    rw [hshift] at h
    exact hz.2 h
  have he := PrimeTorusTheory.eventually_eq_zero_of_limit hV
    (hconv.mono (fun z hz => hz.1)) htr (hG.mono (fun z hz => hz.1)) hno ⟨hs, hsc⟩ hz
  have hpre : IsPreconnected {z : ℂ | x < z.re} :=
    (convex_halfSpace_gt
      (show IsLinearMap ℝ Complex.re from ⟨Complex.reLm.map_add, Complex.reLm.map_smul⟩) x).isPreconnected
  have hall := (hG.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hs he
  obtain ⟨a, ha, hGa⟩ := hne
  exact hGa (hall ha)

/-- Every unitary twist of a nonzero bounded pure Dirichlet series remains pure
on the same half-plane. -/
theorem exists_bounded_pure_primePhaseTwist
    {a : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ M c : ℝ} {n : ℕ}
    (hx : x < u₀) (hsum : LSeriesSummable a (u₀ : ℂ))
    (hF : DifferentiableOn ℂ F {s : ℂ | x < s.re})
    (hM : ∀ s, x < s.re → ‖F s‖ ≤ M)
    (hFL : ∀ s, u₀ < s.re → F s = LSeries a s)
    (hn : a (n + 1) ≠ 0)
    (hpure : ∀ s, x < s.re → F s = 0 → s.re = c)
    (ω : Nat.Primes → Circle) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | x < s.re} ∧
      (∀ s, x < s.re → ‖G s‖ ≤ M) ∧
      (∀ s, u₀ < s.re → G s = LSeries (fun m => a m * primePhaseTwist ω m) s) ∧
      (∀ s, x < s.re → G s = 0 → s.re = c) := by
  obtain ⟨G, hG, hGM, hGL, t, _, hconv⟩ :=
    exists_bounded_holomorphic_primePhaseTwist hx hsum hF hM hFL ω
  refine ⟨G, hG, hGM, hGL, fun s hs hz => ?_⟩
  exact pure_of_vertical_limit hF hG hconv hpure
    (exists_ne_zero_of_primePhaseTwist_coefficient hsum ω hG hGL hn) hs hz

/-- Converging prime phases give uniform convergence of the twisted series
on every closed half-plane of absolute convergence. -/
theorem tendstoUniformlyOn_LSeries_primePhaseTwist
    {ι : Type*} {p : Filter ι} {a : ℕ → ℂ} {u : ℝ}
    (hsum : LSeriesSummable a (u : ℂ))
    {ω : ι → Nat.Primes → Circle} {ω₀ : Nat.Primes → Circle}
    (hω : Tendsto ω p (𝓝 ω₀)) :
    TendstoUniformlyOn (fun i => LSeries (fun n => a n * primePhaseTwist (ω i) n))
      (LSeries (fun n => a n * primePhaseTwist ω₀ n)) p {s : ℂ | u ≤ s.re} := by
  let e : ι → ℕ → ℝ := fun i n =>
    ‖primePhaseTwist (ω i) n - primePhaseTwist ω₀ n‖ * ‖LSeries.term a (u : ℂ) n‖
  have hphase (i : ι) (n : ℕ) :
      ‖primePhaseTwist (ω i) n - primePhaseTwist ω₀ n‖ ≤ 2 := by
    have h := norm_sub_le (primePhaseTwist (ω i) n) (primePhaseTwist ω₀ n)
    simpa only [norm_primePhaseTwist, one_add_one_eq_two] using h
  have he0 (i : ι) (n : ℕ) : 0 ≤ e i n := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have heBound (i : ι) (n : ℕ) : e i n ≤ 2 * ‖LSeries.term a (u : ℂ) n‖ :=
    mul_le_mul_of_nonneg_right (hphase i n) (norm_nonneg _)
  have heSum (i : ι) : Summable (e i) :=
    Summable.of_nonneg_of_le (he0 i) (heBound i) (hsum.norm.mul_left 2)
  have hePoint (n : ℕ) : Tendsto (fun i => e i n) p (𝓝 0) := by
    have h := ((continuous_primePhaseTwist n).tendsto ω₀).comp hω
    have hd := h.sub (tendsto_const_nhds (x := primePhaseTwist ω₀ n))
    simpa only [e, Function.comp_apply, sub_self, norm_zero, zero_mul] using
      hd.norm.mul_const ‖LSeries.term a (u : ℂ) n‖
  have heLim : Tendsto (fun i => ∑' n, e i n) p (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (hsum.norm.mul_left 2) hePoint
      (Eventually.of_forall fun i n => by
        rw [Real.norm_eq_abs, abs_of_nonneg (he0 i n)]
        exact heBound i n)
    simpa only [tsum_zero] using h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [heLim.eventually (gt_mem_nhds hε)] with i hi s hs
  have hssum : LSeriesSummable a s := hsum.of_re_le_re (by simpa using hs)
  have hsi := lSeriesSummable_primePhaseTwist hssum (ω i)
  have hs0 := lSeriesSummable_primePhaseTwist hssum ω₀
  let d : ℕ → ℂ := fun n =>
    (primePhaseTwist (ω i) n - primePhaseTwist ω₀ n) * LSeries.term a s n
  have hdEq (n : ℕ) : LSeries.term (fun k => a k * primePhaseTwist (ω i) k) s n -
      LSeries.term (fun k => a k * primePhaseTwist ω₀ k) s n = d n := by
    rw [term_primePhaseTwist, term_primePhaseTwist]
    dsimp only [d]
    ring
  have hdSum : Summable d := (Summable.sub hsi hs0).congr hdEq
  have hEq : LSeries (fun n => a n * primePhaseTwist (ω i) n) s -
      LSeries (fun n => a n * primePhaseTwist ω₀ n) s = ∑' n, d n := by
    change (∑' n, LSeries.term (fun k => a k * primePhaseTwist (ω i) k) s n) -
      (∑' n, LSeries.term (fun k => a k * primePhaseTwist ω₀ k) s n) = _
    rw [← Summable.tsum_sub hsi hs0]
    exact tsum_congr hdEq
  have hdBound (n : ℕ) : ‖d n‖ ≤ e i n := by
    dsimp only [d]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (LSeries.norm_term_le_of_re_le_re a (by simpa using hs) n) (norm_nonneg _)
  rw [dist_eq_norm, norm_sub_rev, hEq]
  exact ((norm_tsum_le_tsum_norm hdSum.norm).trans
    (hdSum.norm.tsum_le_tsum hdBound (heSum i))).trans_lt hi

/-- A small bound on one vertical line controls a bounded holomorphic function
uniformly on every closed strip lying strictly inside its half-plane. -/
theorem exists_line_bound_for_strip_bound {x v u M ε : ℝ}
    (hxv : x < v) (hvu : v ≤ u) (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : ℂ → ℂ,
      DifferentiableOn ℂ f {s : ℂ | x < s.re} →
      (∀ s, x < s.re → ‖f s‖ ≤ M) →
      (∀ s, s.re = u → ‖f s‖ ≤ δ) →
      ∀ s, v ≤ s.re → s.re ≤ u → ‖f s‖ ≤ ε := by
  let l : ℝ := (x + v) / 2
  have hxl : x < l := by dsimp only [l]; linarith
  have hlv : l < v := by dsimp only [l]; linarith
  have hlu : l < u := lt_of_lt_of_le hlv hvu
  let θ₀ : ℝ := (v - l) / (u - l)
  have hθ₀ : 0 < θ₀ := div_pos (sub_pos.mpr hlv) (sub_pos.mpr hlu)
  let A : ℝ := max M 1
  have hA1 : 1 ≤ A := le_max_right _ _
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hεA : 0 < ε / A := div_pos hε hA0
  let δ : ℝ := min 1 ((ε / A) ^ (1 / θ₀))
  have hδ : 0 < δ := lt_min one_pos (Real.rpow_pos_of_pos hεA _)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδθ : δ ^ θ₀ ≤ ε / A := by
    calc
      δ ^ θ₀ ≤ ((ε / A) ^ (1 / θ₀)) ^ θ₀ :=
        Real.rpow_le_rpow hδ.le (min_le_right _ _) hθ₀.le
      _ = ε / A := by
        rw [← Real.rpow_mul hεA.le, one_div_mul_cancel hθ₀.ne', Real.rpow_one]
  refine ⟨δ, hδ, fun f hf hM hline s hsv hsu => ?_⟩
  have hbound (z : ℂ) (hz : x < z.re) : ‖f z‖ ≤ A :=
    (hM z hz).trans (le_max_left _ _)
  have hcl : closure (HadamardThreeLines.verticalStrip l u) ⊆ {z : ℂ | x < z.re} := by
    have hc : IsClosed {z : ℂ | l ≤ z.re} := isClosed_le continuous_const continuous_re
    refine (closure_minimal (fun z hz => ?_) hc).trans fun z hz => lt_of_lt_of_le hxl hz
    exact (show l < z.re ∧ z.re < u from hz).1.le
  have hdc : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip l u) :=
    (hf.mono hcl).diffContOnCl
  have hbdd : BddAbove (norm ∘ f '' HadamardThreeLines.verticalClosedStrip l u) := by
    refine ⟨A, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hbound z (lt_of_lt_of_le hxl (show l ≤ z.re ∧ z.re ≤ u from hz).1)
  have h3 := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (a := A) (b := δ) hlu (show s ∈ HadamardThreeLines.verticalClosedStrip l u from
      ⟨le_trans hlv.le hsv, hsu⟩) hdc hbdd
    (fun z hz => hbound z (by change z.re = l at hz; rw [hz]; exact hxl)) hline
  let θ : ℝ := (s.re - l) / (u - l)
  have hθlo : θ₀ ≤ θ :=
    div_le_div_of_nonneg_right (sub_le_sub_right hsv l) (sub_nonneg.mpr hlu.le)
  have hAθ : A ^ (1 - θ) ≤ A := by
    calc
      A ^ (1 - θ) ≤ A ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hA1 (by linarith [hθ₀])
      _ = A := Real.rpow_one A
  have hδθ' : δ ^ θ ≤ ε / A :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hθlo).trans hδθ
  calc
    ‖f s‖ ≤ A ^ (1 - θ) * δ ^ θ := h3
    _ ≤ A * (ε / A) := mul_le_mul hAθ hδθ' (by positivity) hA0.le
    _ = ε := by field_simp

/-- Uniform convergence on a right-hand vertical line propagates left through
a common half-plane of boundedness. -/
theorem tendstoUniformlyOn_strip_of_bounded_of_line
    {ι : Type*} {p : Filter ι} {Fn : ι → ℂ → ℂ} {F : ℂ → ℂ} {x v u M : ℝ}
    (hxv : x < v) (hvu : v ≤ u)
    (hFn : ∀ n, DifferentiableOn ℂ (Fn n) {s : ℂ | x < s.re})
    (hF : DifferentiableOn ℂ F {s : ℂ | x < s.re})
    (hMn : ∀ n s, x < s.re → ‖Fn n s‖ ≤ M)
    (hM : ∀ s, x < s.re → ‖F s‖ ≤ M)
    (hline : TendstoUniformlyOn Fn F p {s : ℂ | s.re = u}) :
    TendstoUniformlyOn Fn F p {s : ℂ | v ≤ s.re ∧ s.re ≤ u} := by
  rw [Metric.tendstoUniformlyOn_iff] at hline ⊢
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := exists_line_bound_for_strip_bound
    (M := 2 * M) hxv hvu (half_pos hε)
  filter_upwards [hline δ hδ] with n hn s hs
  have hbound (z : ℂ) (hz : x < z.re) : ‖Fn n z - F z‖ ≤ 2 * M := by
    exact (norm_sub_le _ _).trans (by linarith [hMn n z hz, hM z hz])
  have hright (z : ℂ) (hz : z.re = u) : ‖Fn n z - F z‖ ≤ δ := by
    have h := (hn z hz).le
    simpa only [dist_eq_norm, norm_sub_rev] using h
  have h := hsmall (fun z => Fn n z - F z) ((hFn n).sub hF) hbound hright s hs.1 hs.2
  rw [dist_eq_norm, norm_sub_rev]
  exact h.trans_lt (half_lt_self hε)

/-- Bounded holomorphic continuations vary locally uniformly with their prime
phases. Absolute convergence controls a right-hand line; three-lines controls
each compact subset of the full half-plane. -/
theorem tendstoLocallyUniformlyOn_bounded_primePhaseTwists
    {ι : Type*} {p : Filter ι} {a : ℕ → ℂ} {x u₀ M : ℝ}
    {ω : ι → Nat.Primes → Circle} {ω₀ : Nat.Primes → Circle}
    {G : ι → ℂ → ℂ} {G₀ : ℂ → ℂ}
    (hsum : LSeriesSummable a (u₀ : ℂ)) (hω : Tendsto ω p (𝓝 ω₀))
    (hG : ∀ i, DifferentiableOn ℂ (G i) {s : ℂ | x < s.re})
    (hG₀ : DifferentiableOn ℂ G₀ {s : ℂ | x < s.re})
    (hM : ∀ i s, x < s.re → ‖G i s‖ ≤ M)
    (hM₀ : ∀ s, x < s.re → ‖G₀ s‖ ≤ M)
    (hGL : ∀ i s, u₀ < s.re → G i s = LSeries (fun n => a n * primePhaseTwist (ω i) n) s)
    (hG₀L : ∀ s, u₀ < s.re → G₀ s = LSeries (fun n => a n * primePhaseTwist ω₀ n) s) :
    TendstoLocallyUniformlyOn G G₀ p {s : ℂ | x < s.re} := by
  have hU : IsOpen {s : ℂ | x < s.re} := isOpen_lt continuous_const continuous_re
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with rfl | hne
  · intro V hV
    exact Eventually.of_forall fun i z hz => False.elim hz
  obtain ⟨b, hb, hmin⟩ := hK.exists_isMinOn hne continuous_re.continuousOn
  obtain ⟨d, hd, hmax⟩ := hK.exists_isMaxOn hne continuous_re.continuousOn
  let u : ℝ := max u₀ d.re + 1
  have hu₀ : u₀ < u := by dsimp only [u]; linarith [le_max_left u₀ d.re]
  have hdu : d.re ≤ u := by dsimp only [u]; linarith [le_max_right u₀ d.re]
  have hbu : b.re ≤ u := (hmax hb).trans hdu
  have hfar := tendstoUniformlyOn_LSeries_primePhaseTwist hsum hω
  have hline : TendstoUniformlyOn G G₀ p {s : ℂ | s.re = u} := by
    rw [Metric.tendstoUniformlyOn_iff] at hfar ⊢
    intro ε hε
    filter_upwards [hfar ε hε] with i hi z hz
    have hz₀ : u₀ < z.re := by rw [hz]; exact hu₀
    rw [hGL i z hz₀, hG₀L z hz₀]
    exact hi z hz₀.le
  exact (tendstoUniformlyOn_strip_of_bounded_of_line (hKU hb) hbu
    hG hG₀ hM hM₀ hline).mono
      (fun z hz => ⟨hmin hz, (hmax hz).trans hdu⟩)

/-- The bounded prime-torus lift is jointly continuous on its half-plane. -/
theorem continuousOn_bounded_primePhaseTwists
    {a : ℕ → ℂ} {x u₀ M : ℝ} {G : (Nat.Primes → Circle) → ℂ → ℂ}
    (hsum : LSeriesSummable a (u₀ : ℂ))
    (hG : ∀ ω, DifferentiableOn ℂ (G ω) {s : ℂ | x < s.re})
    (hM : ∀ ω s, x < s.re → ‖G ω s‖ ≤ M)
    (hGL : ∀ ω s, u₀ < s.re → G ω s = LSeries (fun n => a n * primePhaseTwist ω n) s) :
    ContinuousOn (fun q : (Nat.Primes → Circle) × ℂ => G q.1 q.2)
      (univ ×ˢ {s : ℂ | x < s.re}) := by
  intro q hq
  let p : Filter ((Nat.Primes → Circle) × ℂ) :=
    𝓝[univ ×ˢ {s : ℂ | x < s.re}] q
  have hω : Tendsto (fun v : (Nat.Primes → Circle) × ℂ => v.1) p (𝓝 q.1) :=
    continuous_fst.continuousWithinAt
  have hz : Tendsto (fun v : (Nat.Primes → Circle) × ℂ => v.2) p
      (𝓝[{s : ℂ | x < s.re}] q.2) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨continuous_snd.continuousWithinAt, ?_⟩
    have hm : ∀ᶠ v in p, v ∈ (univ ×ˢ {s : ℂ | x < s.re}) := self_mem_nhdsWithin
    exact hm.mono fun v hv => hv.2
  have hbase : Tendsto (fun v : (Nat.Primes → Circle) × ℂ => G q.1 v.2) p
      (𝓝 (G q.1 q.2)) :=
    Filter.Tendsto.comp ((hG q.1).continuousOn q.2 hq.2) hz
  have hlu := tendstoLocallyUniformlyOn_bounded_primePhaseTwists
    (G := fun v => G v.1) (G₀ := G q.1) hsum hω
    (fun v => hG v.1) (hG q.1) (fun v => hM v.1) (hM q.1)
    (fun v => hGL v.1) (hGL q.1)
  change Tendsto (fun v : (Nat.Primes → Circle) × ℂ => G v.1 v.2) p (𝓝 (G q.1 q.2))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨V, hV, hclose⟩ := hlu _ (dist_mem_uniformity (half_pos hε)) q.2 hq.2
  filter_upwards [hclose, hz.eventually hV,
    (Metric.tendsto_nhds.mp hbase) (ε / 2) (half_pos hε)] with v hv hvV hvbase
  have hnear : dist (G q.1 v.2) (G v.1 v.2) < ε / 2 := hv v.2 hvV
  have htri := dist_triangle (G v.1 v.2) (G q.1 v.2) (G q.1 q.2)
  rw [dist_comm (G v.1 v.2) (G q.1 v.2)] at htri
  linarith

/-- Holomorphic continuations of the same far-right function agree throughout
their common half-plane. -/
theorem eqOn_halfPlane_of_eq_far_right {F G : ℂ → ℂ} {x u : ℝ}
    (hF : DifferentiableOn ℂ F {s : ℂ | x < s.re})
    (hG : DifferentiableOn ℂ G {s : ℂ | x < s.re})
    (hfar : ∀ s, u < s.re → F s = G s) : EqOn F G {s : ℂ | x < s.re} := by
  have hU : IsOpen {s : ℂ | x < s.re} := isOpen_lt continuous_const continuous_re
  let z : ℂ := ((max x u + 1 : ℝ) : ℂ)
  have hz : x < z.re := by dsimp only [z]; simp only [Complex.ofReal_re]; linarith [le_max_left x u]
  have hzu : u < z.re := by dsimp only [z]; simp only [Complex.ofReal_re]; linarith [le_max_right x u]
  have he : (fun s => F s - G s) =ᶠ[𝓝 z] 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hzu] with s hs
    exact sub_eq_zero.mpr (hfar s hs)
  have hpre : IsPreconnected {s : ℂ | x < s.re} :=
    (convex_halfSpace_gt
      (show IsLinearMap ℝ Complex.re from ⟨Complex.reLm.map_add, Complex.reLm.map_smul⟩) x).isPreconnected
  have hall := ((hF.sub hG).analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hpre hz he
  intro s hs
  exact sub_eq_zero.mp (hall hs)

/-- The identity prime phase leaves every coefficient unchanged. -/
theorem primePhaseTwist_one (n : ℕ) : primePhaseTwist (1 : Nat.Primes → Circle) n = 1 := by
  unfold primePhaseTwist
  apply Finset.prod_eq_one
  intro p hp
  rw [dif_pos (Nat.prime_of_mem_primeFactors hp)]
  change (1 : ℂ) ^ n.factorization p = 1
  exact one_pow _

/-- A bounded pure Dirichlet series extends to a jointly continuous family over
the prime torus. Every fibre is bounded, holomorphic, nonzero and pure; the
identity fibre is the original function. -/
theorem exists_bounded_pure_primeTorus_lift
    {a : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ M c : ℝ} {n : ℕ}
    (hx : x < u₀) (hsum : LSeriesSummable a (u₀ : ℂ))
    (hF : DifferentiableOn ℂ F {s : ℂ | x < s.re})
    (hM : ∀ s, x < s.re → ‖F s‖ ≤ M)
    (hFL : ∀ s, u₀ < s.re → F s = LSeries a s)
    (hn : a (n + 1) ≠ 0)
    (hpure : ∀ s, x < s.re → F s = 0 → s.re = c) :
    ∃ G : (Nat.Primes → Circle) → ℂ → ℂ,
      (∀ ω, DifferentiableOn ℂ (G ω) {s : ℂ | x < s.re}) ∧
      (∀ ω s, x < s.re → ‖G ω s‖ ≤ M) ∧
      (∀ ω s, u₀ < s.re → G ω s = LSeries (fun m => a m * primePhaseTwist ω m) s) ∧
      (∀ ω s, x < s.re → G ω s = 0 → s.re = c) ∧
      ContinuousOn (fun q : (Nat.Primes → Circle) × ℂ => G q.1 q.2)
        (univ ×ˢ {s : ℂ | x < s.re}) ∧
      EqOn (G 1) F {s : ℂ | x < s.re} := by
  choose G hG hGM hGL hGp using
    fun ω => exists_bounded_pure_primePhaseTwist hx hsum hF hM hFL hn hpure ω
  refine ⟨G, hG, hGM, hGL, hGp, continuousOn_bounded_primePhaseTwists hsum hG hGM hGL, ?_⟩
  apply eqOn_halfPlane_of_eq_far_right (hG 1) hF (u := u₀)
  intro s hs
  rw [hGL 1 s hs, hFL s hs]
  congr 1
  funext m
  rw [primePhaseTwist_one, mul_one]

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
