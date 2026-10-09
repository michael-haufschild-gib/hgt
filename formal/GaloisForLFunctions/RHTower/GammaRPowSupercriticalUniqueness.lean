import GaloisForLFunctions.RHTower.GammaRPowOddTwins
import GaloisForLFunctions.RHTower.GammaRPowFunctionalEquationAbundance

/-!
# Supercritical Voronoi charts: uniqueness modulo finitely many values

For `d ≥ 3` the integer nodes `X_n = n^{1/d}` are supercritical for the Voronoi involution of
`ζ(s)^d` in the chart `x = X^d`: away from `0` their gaps satisfy `X_n(X_{n+2} − X_n) → 0`, while
chart functions obey `‖F'‖ ≤ K‖XF‖`. With finitely many auxiliary points `p₀ < ⋯ < p_m` near `0`
the sampling inequality `(1 − c K²)∫X²|F|² ≤ C Σ_j p_{j+1}(|F(p_j)|² + |F(p_{j+1})|²) + 2p₀³|F(p₀)|²`
holds, so a chart function vanishing at every integer node `n ≥ 2` and at the auxiliary points
vanishes on `(0,∞)`:

* `exists_sym_uniqueness_mod_finite` (fixed points, `F = HF`);
* `exists_anti_uniqueness_mod_finite` (anti-fixed points, `F = −HF`);
* `exists_card_le_of_sym_vanishing`: fixed points vanishing on the integer nodes `n ≥ 2` form a
  space of dimension at most `m + 1` on `(0,∞)`.

Read through the divisor transfer of exact-null tests, this is the supercritical half of the
order/degree dictionary: tests `ĝ = Ξ^k R`, `k ≥ 3`, blind at `log ℕ_{≥2}` correspond to a
finite-dimensional space, in contrast with the subcritical order `k = 1`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.GammaRPowTwins

/-- A continuous function on `(0,∞)` with `∫_{(0,∞)} x²|F|² = 0` vanishes there. -/
theorem eq_zero_of_integral_sq_mul_norm_sq_eq_zero {F : ℝ → ℂ} (hc : ContinuousOn F (Ioi 0))
    (hint : IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0))
    (h0 : ∫ x in Ioi (0 : ℝ), x ^ 2 * ‖F x‖ ^ 2 = 0) {x : ℝ} (hx : 0 < x) : F x = 0 := by
  by_contra hFx
  set g : ℝ → ℝ := fun y => y ^ 2 * ‖F y‖ ^ 2 with hg
  have hgc : ContinuousOn g (Ioi 0) := by
    refine ((continuousOn_id.pow 2).mul ((continuous_norm.comp_continuousOn hc).pow 2))
  have hgx : 0 < g x := by
    have : 0 < ‖F x‖ := norm_pos_iff.mpr hFx
    simp only [hg]; positivity
  -- `g > g x / 2` on a neighbourhood of `x` inside `(0,∞)`
  have hev : ∀ᶠ y in 𝓝 x, g x / 2 < g y := by
    have hcx : ContinuousAt g x := hgc.continuousAt (Ioi_mem_nhds hx)
    exact hcx.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set δ' := min δ x / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hsub : Icc (x - δ') (x + δ') ⊆ Ioi 0 := by
    intro y hy; simp only [mem_Ioi]
    have : δ' < x := by rw [hδ']; have := min_le_right δ x; linarith
    linarith [hy.1]
  have hlow : ∀ y ∈ Icc (x - δ') (x + δ'), g x / 2 ≤ g y := by
    intro y hy
    have hd : dist y x < δ := by
      rw [Real.dist_eq, abs_lt]
      have : δ' < δ := by rw [hδ']; have := min_le_left δ x; linarith
      constructor <;> linarith [hy.1, hy.2]
    exact (hball hd).le
  have hpos : 0 < ∫ y in Icc (x - δ') (x + δ'), g y := by
    have h1 : ∫ y in Icc (x - δ') (x + δ'), g x / 2 ≤ ∫ y in Icc (x - δ') (x + δ'), g y :=
      setIntegral_mono_on (integrableOn_const (by simp))
        (hint.mono_set hsub) measurableSet_Icc hlow
    have h2 : ∫ y in Icc (x - δ') (x + δ'), g x / 2 = (2 * δ') * (g x / 2) := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
      simp only [smul_eq_mul]; ring
    rw [h2] at h1
    have : 0 < (2 * δ') * (g x / 2) := by positivity
    linarith
  have hle : ∫ y in Icc (x - δ') (x + δ'), g y ≤ ∫ y in Ioi 0, g y :=
    setIntegral_mono_set hint (Eventually.of_forall fun y => by simp only [hg]; positivity)
      (Eventually.of_forall hsub)
  rw [h0] at hle
  linarith

/-- **Uniqueness from the sampling inequality.** If `F` has the analytic package of the chart
spaces (derivative bound `‖F'‖ ≤ K‖XF‖`) and vanishes at every node of a supercritical sequence
`p`, then `F` vanishes on `(0,∞)`. -/
theorem eq_zero_of_nodeSeq_vanishing {d : ℕ} (hd : 3 ≤ d) {K a : ℝ} {N₀ m : ℕ} (hN₀ : 1 ≤ N₀)
    (hgap : ∀ j, max |nodeSeq d N₀ m j| |nodeSeq d N₀ m (j + 1)| *
      (nodeSeq d N₀ m (j + 1) - nodeSeq d N₀ m j) ≤ a / 2)
    (hbr : 0 < 1 - ((1 + 1) ^ 2 * (a / (2 * Real.pi)) ^ 2 + 2 * nodeSeq d N₀ m 0 ^ 4) * K ^ 2)
    {F F' : ℝ → ℂ} (hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x) (hF'c : ContinuousOn F' (Ioi 0))
    (hXF : IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0))
    (hF'2 : IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0))
    (hKb : ∫ x in Ioi 0, ‖F' x‖ ^ 2 ≤ K ^ 2 * ∫ x in Ioi 0, x ^ 2 * ‖F x‖ ^ 2)
    (hzero : ∀ j, F (nodeSeq d N₀ m j) = 0) {x : ℝ} (hx : 0 < x) : F x = 0 := by
  have hsum : Summable fun j => max |nodeSeq d N₀ m j| |nodeSeq d N₀ m (j + 1)| *
      (‖F (nodeSeq d N₀ m j)‖ ^ 2 + ‖F (nodeSeq d N₀ m (j + 1))‖ ^ 2) := by
    simp only [hzero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero, mul_zero]
    exact summable_zero
  have hsl := GaloisForLFunctions.HTGeometry.sampling_lower_bound hderiv hF'c hXF hF'2 hKb
    (nodeSeq_strictMono (by omega) hN₀ m) (nodeSeq_pos (by omega) hN₀ m 0)
    (tendsto_nodeSeq (by omega) N₀ m) one_pos hgap hsum
  simp only [hzero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, mul_zero, tsum_zero] at hsl
  have hI0 : 0 ≤ ∫ x in Ioi (0 : ℝ), x ^ 2 * ‖F x‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun y _ => by positivity
  have hI : ∫ x in Ioi (0 : ℝ), x ^ 2 * ‖F x‖ ^ 2 = 0 := by
    rcases mul_nonpos_iff.mp hsl with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact le_antisymm h2 hI0
    · exact absurd h1 (not_le.mpr hbr)
  have hc : ContinuousOn F (Ioi 0) := fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
  exact eq_zero_of_integral_sq_mul_norm_sq_eq_zero hc hXF hI hx

/-- **Supercritical uniqueness modulo finitely many values (symmetric charts).** For `d ≥ 3`
there are points `0 < p₀ < ⋯ < p_m` such that a symmetric degree-`d` chart function (a fixed
point of the Voronoi involution of `ζ(s)^d` in the chart) vanishing at every integer node
`X_n = n^{1/d}`, `n ≥ 2`, and at `p₀, …, p_m`, vanishes on `(0,∞)`. -/
theorem exists_sym_uniqueness_mod_finite {d : ℕ} (hd : 3 ≤ d) :
    ∃ m : ℕ, ∃ p : ℕ → ℝ, (∀ j, 0 < p j) ∧ ∀ F ∈ symChartSpace d,
      (∀ n : ℕ, 2 ≤ n → F (nodeX d n) = 0) → (∀ j, j ≤ m → F (p j) = 0) →
        ∀ x : ℝ, 0 < x → F x = 0 := by
  obtain ⟨K, a, N₀, m, hN₀, hNN₀, -, hK, hgap, hbr⟩ := exists_chart_sampling_parameters hd 2
  refine ⟨m, nodeSeq d N₀ m, nodeSeq_pos (by omega) hN₀ m, fun F hF hint hpts x hx => ?_⟩
  obtain ⟨F', hderiv, hF'c, hXF, hF'2, hKb⟩ := hF.1.analytic hK
  refine eq_zero_of_nodeSeq_vanishing hd hN₀ hgap hbr hderiv hF'c hXF hF'2 hKb (fun j => ?_) hx
  by_cases hj : j ≤ m
  · exact hpts j hj
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + m := ⟨j - m, by omega⟩
    rw [nodeSeq_add]
    exact hint _ (by omega)

/-- **Supercritical uniqueness modulo finitely many values (antisymmetric charts).** The same
for antisymmetric degree-`d` chart functions (`F = −HF` in the chart), `d ≥ 3`. -/
theorem exists_anti_uniqueness_mod_finite {d : ℕ} (hd : 3 ≤ d) :
    ∃ m : ℕ, ∃ p : ℕ → ℝ, (∀ j, 0 < p j) ∧ ∀ F ∈ antiChartSpace d,
      (∀ n : ℕ, 2 ≤ n → F (nodeX d n) = 0) → (∀ j, j ≤ m → F (p j) = 0) →
        ∀ x : ℝ, 0 < x → F x = 0 := by
  obtain ⟨K, a, N₀, m, hN₀, hNN₀, -, hK, hgap, hbr⟩ := exists_chart_sampling_parameters hd 2
  refine ⟨m, nodeSeq d N₀ m, nodeSeq_pos (by omega) hN₀ m, fun F hF hint hpts x hx => ?_⟩
  obtain ⟨F', hderiv, hF'c, hXF, hF'2, hKb⟩ := hF.1.analytic hK
  refine eq_zero_of_nodeSeq_vanishing hd hN₀ hgap hbr hderiv hF'c hXF hF'2 hKb (fun j => ?_) hx
  by_cases hj : j ≤ m
  · exact hpts j hj
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + m := ⟨j - m, by omega⟩
    rw [nodeSeq_add]
    exact hint _ (by omega)

/-- **Finite dimension (symmetric charts).** For `d ≥ 3` the symmetric degree-`d` chart functions
vanishing at every integer node `n^{1/d}`, `n ≥ 2`, span a space of dimension at most `m + 1` on
`(0,∞)`: any family of them that is linearly independent on `(0,∞)` has at most `m + 1` members. -/
theorem exists_card_le_of_sym_vanishing {d : ℕ} (hd : 3 ≤ d) :
    ∃ m : ℕ, ∀ (r : ℕ) (F : Fin r → ℝ → ℂ), (∀ i, F i ∈ symChartSpace d) →
      (∀ i n, 2 ≤ n → F i (nodeX d n) = 0) →
      (∀ c : Fin r → ℂ, (∀ x : ℝ, 0 < x → ∑ i, c i * F i x = 0) → c = 0) → r ≤ m + 1 := by
  obtain ⟨m, p, -, huniq⟩ := exists_sym_uniqueness_mod_finite hd
  refine ⟨m, fun r F hF hnode hind => ?_⟩
  by_contra hr
  push Not at hr
  let L : (Fin r → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    { toFun := fun c j => ∑ i, c i * F i (p j)
      map_add' := fun c c' => by funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by funext j; simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hr)
  obtain ⟨c, hcL, hc0⟩ := (Submodule.ne_bot_iff _).mp hker
  apply hc0
  apply hind c
  set G : ℝ → ℂ := ∑ i, c i • F i with hG
  have hGmem : G ∈ symChartSpace d :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hF i)
  have hGapp : ∀ x, G x = ∑ i, c i * F i x := by
    intro x; simp [hG, Finset.sum_apply]
  have hGnode : ∀ n : ℕ, 2 ≤ n → G (nodeX d n) = 0 := by
    intro n hn; rw [hGapp]; simp [hnode _ n hn]
  have hGp : ∀ j, j ≤ m → G (p j) = 0 := by
    intro j hj
    have := congrFun (LinearMap.mem_ker.mp hcL) ⟨j, Nat.lt_succ_of_le hj⟩
    rw [hGapp]; simpa [L] using this
  intro x hx
  rw [← hGapp]
  exact huniq G hGmem hGnode hGp x hx

end RHTower.GammaRPowTwins
