import GaloisForLFunctions.RHTower.XiGaussianHeatWindowWeilMargin

/-!
# The heat Hankel window from a Weil margin: the asymptotic regime

**Per-term bounds** (`heatTest_tail_bounds`).  For `0 < a < 1`, `deg P ≤ n`, `L > 0` and a moment
order `k`, put `β = 1/(2a)` and `t = (2n + 1 + k)/((β − ½) L²)`.  If `t^k ≤ ½`, then with
`V = ∫ g²`, `E = 4eπ e^{L²}` and `Y = 4β(2n + 1)`:

* `∫_{|x| ≥ L} g² ≤ t^k V`;
* `(∫_{|x| ≥ L} |g| e^{|x|/2})² ≤ E t^k V` and `(∫_{|x| ≥ L} |g'| e^{|x|/2})² ≤ E t^k Y V`;
* `(∫ |g'| e^{|x|/2})² ≤ E Y V`.

**Moment order** (`exists_heatMomentOrder`).  If `4K < L²`, there is `m ≥ 1` such that with
`j = ⌊n/m⌋ + 1` and `k = 2j`, uniformly in `0 < a ≤ K/n`, both `t^j` and `t^j Y` tend to `0`.  The
ratio `t` is at most `2K(2n + 2n/m + 3)/((n − K) L²) → 4K(1 + 1/m)/L² < 1`, while `Y ≍ n/a` costs
only a polynomial factor against `t^j ≤ θ^{⌊n/m⌋}`.  The order `k ≍ n/m`, with `m` large, is what
makes the window constant `L²/4` sharp: a polynomial–Gaussian of degree `2n` at width `√a` has its
turning point at `x² = 4an`.
-/

open scoped Real
open Complex MeasureTheory Set Polynomial Filter Topology
open GaloisForLFunctions (gaussPolyFun gaussPolyDerivPoly setIntegral_tail_gaussPolyFun_sq_le
  sq_setIntegral_tail_abs_gaussPolyFun_mul_exp_half_le sq_integral_abs_gaussPolyFun_mul_exp_half_le
  integral_gaussPolyFun_derivPoly_sq_le)

namespace RHTower

noncomputable section

theorem natDegree_gaussPolyDerivPoly_le (Q : ℝ[X]) (β : ℝ) :
    (gaussPolyDerivPoly Q β).natDegree ≤ Q.natDegree + 1 := by
  unfold gaussPolyDerivPoly
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_derivative_le _).trans (by omega)) ?_)
  refine natDegree_mul_le.trans ?_
  have := (natDegree_C_mul_le (2 * β) (X : ℝ[X])).trans natDegree_X_le
  omega

/-- The moment ratio `t = (2n + 1 + k)/((β − ½) L²)`, `β = 1/(2a)`. -/
def heatMomentRatio (n k : ℕ) (a L : ℝ) : ℝ :=
  (2 * n + 1 + k) / ((1 / (2 * a) - 1 / 2) * L ^ 2)

/-- The strip constant `E = 4eπ e^{L²}`. -/
def heatStripConstant (L : ℝ) : ℝ := 4 * Real.exp 1 * π * Real.exp (L ^ 2)

theorem half_lt_inv_two_mul {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : 1 / 2 < 1 / (2 * a) := by
  rw [lt_div_iff₀ (by positivity)]; nlinarith

theorem heatMomentRatio_pos {n k : ℕ} {a L : ℝ} (ha : 0 < a) (ha1 : a < 1) (hL : 0 < L) :
    0 < heatMomentRatio n k a L := by
  have := half_lt_inv_two_mul ha ha1
  unfold heatMomentRatio
  apply div_pos (by positivity)
  have : 0 < 1 / (2 * a) - 1 / 2 := by linarith
  positivity

theorem ratio_le_heatMomentRatio {n k d : ℕ} (hd : d ≤ 2 * n + 1) {a L : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (hL : 0 < L) :
    ((d : ℝ) + k) / ((1 / (2 * a) - 1 / 2) * L ^ 2) ≤ heatMomentRatio n k a L := by
  have := half_lt_inv_two_mul ha ha1
  have hpos : 0 < (1 / (2 * a) - 1 / 2) * L ^ 2 := by
    have : 0 < 1 / (2 * a) - 1 / 2 := by linarith
    positivity
  unfold heatMomentRatio
  gcongr
  exact_mod_cast hd

theorem ratio_le_heatMomentRatio' {n k d : ℕ} (hd : d ≤ 2 * n + 1) {a L : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (hL : 0 < L) :
    ((d : ℝ) + k) / (1 / (2 * a) * L ^ 2) ≤ heatMomentRatio n k a L := by
  have h := half_lt_inv_two_mul ha ha1
  refine le_trans ?_ (ratio_le_heatMomentRatio hd ha ha1 hL)
  have hpos : 0 < (1 / (2 * a) - 1 / 2) * L ^ 2 := by
    have : 0 < 1 / (2 * a) - 1 / 2 := by linarith
    positivity
  apply div_le_div_of_nonneg_left (by positivity) hpos
  nlinarith [sq_nonneg L]

theorem sq_le_of_one_sub_mul_le {τ r t c V : ℝ} (h : (1 - r) * τ ^ 2 ≤ c * r * V)
    (hr : r ≤ t) (ht : t ≤ 1 / 2) (hc : 0 ≤ c) (hV : 0 ≤ V) : τ ^ 2 ≤ 2 * c * t * V := by
  have hτ := sq_nonneg τ
  have h1 : τ ^ 2 * (1 / 2) ≤ (1 - r) * τ ^ 2 := by nlinarith
  have h2 : c * r * V ≤ c * t * V := by
    have := mul_le_mul_of_nonneg_left hr hc
    exact mul_le_mul_of_nonneg_right this hV
  linarith

theorem sq_le_of_one_sub_mul_le' {M r c W : ℝ} (h : (1 - r) * M ^ 2 ≤ c * W) (hr : r ≤ 1 / 2) :
    M ^ 2 ≤ 2 * c * W := by
  have hM := sq_nonneg M
  have h1 : M ^ 2 * (1 / 2) ≤ (1 - r) * M ^ 2 := by nlinarith
  linarith

/-- **Per-term bounds for the heat test.** -/
theorem heatTest_tail_bounds {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {n : ℕ} {P : ℝ[X]}
    (hdeg : P.natDegree ≤ n) {L : ℝ} (hL : 0 < L) (k : ℕ)
    (hk : heatMomentRatio n k a L ^ k ≤ 1 / 2) :
    (∫ x in heatTailSet L, heatTest a P x ^ 2) ≤
        heatMomentRatio n k a L ^ k * ∫ x, heatTest a P x ^ 2 ∧
      stripMassOn (heatTest a P) (heatTailSet L) ^ 2 ≤
        heatStripConstant L * heatMomentRatio n k a L ^ k * ∫ x, heatTest a P x ^ 2 ∧
      stripMassOn (heatTestDeriv a P) (heatTailSet L) ^ 2 ≤
        heatStripConstant L * heatMomentRatio n k a L ^ k * (4 * (1 / (2 * a)) * (2 * n + 1)) *
          ∫ x, heatTest a P x ^ 2 ∧
      (∫ x, |heatTestDeriv a P x| * Real.exp (|x| / 2)) ^ 2 ≤
        heatStripConstant L * (4 * (1 / (2 * a)) * (2 * n + 1)) * ∫ x, heatTest a P x ^ 2 := by
  have hβ : 1 / 2 < 1 / (2 * a) := half_lt_inv_two_mul ha ha1
  have hβ0 : 0 < 1 / (2 * a) := lt_trans (by norm_num) hβ
  have hβ1 : 0 < 1 / (2 * a) - 1 / 2 := sub_pos.2 hβ
  have ht0 : 0 ≤ heatMomentRatio n k a L := (heatMomentRatio_pos ha ha1 hL).le
  have hdP : (heatPolyR a P).natDegree ≤ 2 * P.natDegree := natDegree_heatPolyR_le a P
  have hd1 : (gaussPolyDerivPoly (heatPolyR a P) (1 / (2 * a))).natDegree ≤
      (heatPolyR a P).natDegree + 1 := natDegree_gaussPolyDerivPoly_le _ _
  have hdQ : (heatPolyR a P).natDegree ≤ 2 * n + 1 := by omega
  have hdQ₁ : (gaussPolyDerivPoly (heatPolyR a P) (1 / (2 * a))).natDegree ≤ 2 * n + 1 := by
    omega
  have hdQ' : ((heatPolyR a P).natDegree : ℝ) + 1 ≤ 2 * n + 1 := by
    have : (heatPolyR a P).natDegree ≤ 2 * n := by omega
    have : ((heatPolyR a P).natDegree : ℝ) ≤ 2 * n := by exact_mod_cast this
    linarith
  have hV : 0 ≤ ∫ x, heatTest a P x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hV₁0 : 0 ≤ ∫ x, heatTestDeriv a P x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hV₁ : ∫ x, heatTestDeriv a P x ^ 2 ≤
      4 * (1 / (2 * a)) * (2 * n + 1) * ∫ x, heatTest a P x ^ 2 := by
    have h : ∫ x, heatTestDeriv a P x ^ 2 ≤
        4 * (1 / (2 * a)) * ((heatPolyR a P).natDegree + 1) * ∫ x, heatTest a P x ^ 2 :=
      integral_gaussPolyFun_derivPoly_sq_le (heatPolyR a P) hβ0
    refine h.trans ?_
    gcongr
  have hc : 0 ≤ 2 * Real.exp 1 * π * Real.exp (L ^ 2) := by positivity
  have hE : heatStripConstant L = 2 * (2 * Real.exp 1 * π * Real.exp (L ^ 2)) := by
    unfold heatStripConstant; ring
  have hr : (((heatPolyR a P).natDegree + k) / ((1 / (2 * a) - 1 / 2) * L ^ 2) : ℝ) ^ k ≤
      heatMomentRatio n k a L ^ k :=
    pow_le_pow_left₀ (by positivity) (ratio_le_heatMomentRatio hdQ ha ha1 hL) k
  have hr₁ : (((gaussPolyDerivPoly (heatPolyR a P) (1 / (2 * a))).natDegree + k) /
      ((1 / (2 * a) - 1 / 2) * L ^ 2) : ℝ) ^ k ≤ heatMomentRatio n k a L ^ k :=
    pow_le_pow_left₀ (by positivity) (ratio_le_heatMomentRatio hdQ₁ ha ha1 hL) k
  rw [hE]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : (∫ x in heatTailSet L, heatTest a P x ^ 2) ≤
        (((heatPolyR a P).natDegree + k) / (1 / (2 * a) * L ^ 2) : ℝ) ^ k *
          ∫ x, heatTest a P x ^ 2 :=
      setIntegral_tail_gaussPolyFun_sq_le (heatPolyR a P) hβ0 hL k
    have hrr : (((heatPolyR a P).natDegree + k) / (1 / (2 * a) * L ^ 2) : ℝ) ^ k ≤
        heatMomentRatio n k a L ^ k :=
      pow_le_pow_left₀ (by positivity) (ratio_le_heatMomentRatio' hdQ ha ha1 hL) k
    exact h.trans (mul_le_mul_of_nonneg_right hrr hV)
  · have h : (1 - (((heatPolyR a P).natDegree + k) / ((1 / (2 * a) - 1 / 2) * L ^ 2) : ℝ) ^ k) *
        stripMassOn (heatTest a P) (heatTailSet L) ^ 2 ≤
        2 * Real.exp 1 * π * (((heatPolyR a P).natDegree + k) /
          ((1 / (2 * a) - 1 / 2) * L ^ 2) : ℝ) ^ k * Real.exp (L ^ 2) *
          ∫ x, heatTest a P x ^ 2 :=
      (sq_setIntegral_tail_abs_gaussPolyFun_mul_exp_half_le (heatPolyR a P) hβ hL k
        ((hr.trans hk).trans_lt (by norm_num))).2
    exact sq_le_of_one_sub_mul_le (c := 2 * Real.exp 1 * π * Real.exp (L ^ 2))
      (h.trans_eq (by ring)) hr hk hc hV
  · have h : (1 - (((gaussPolyDerivPoly (heatPolyR a P) (1 / (2 * a))).natDegree + k) /
          ((1 / (2 * a) - 1 / 2) * L ^ 2) : ℝ) ^ k) *
        stripMassOn (heatTestDeriv a P) (heatTailSet L) ^ 2 ≤
        2 * Real.exp 1 * π * (((gaussPolyDerivPoly (heatPolyR a P) (1 / (2 * a))).natDegree + k) /
          ((1 / (2 * a) - 1 / 2) * L ^ 2) : ℝ) ^ k * Real.exp (L ^ 2) *
          ∫ x, heatTestDeriv a P x ^ 2 :=
      (sq_setIntegral_tail_abs_gaussPolyFun_mul_exp_half_le
        (gaussPolyDerivPoly (heatPolyR a P) (1 / (2 * a))) hβ hL k
        ((hr₁.trans hk).trans_lt (by norm_num))).2
    have h' := sq_le_of_one_sub_mul_le (c := 2 * Real.exp 1 * π * Real.exp (L ^ 2))
      (h.trans_eq (by ring)) hr₁ hk hc hV₁0
    have h3 := mul_le_mul_of_nonneg_left hV₁
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc) (pow_nonneg ht0 k))
    exact h'.trans (h3.trans_eq (by ring))
  · have h : (1 - (((gaussPolyDerivPoly (heatPolyR a P) (1 / (2 * a))).natDegree + k) /
          ((1 / (2 * a) - 1 / 2) * L ^ 2) : ℝ) ^ k) *
        (∫ x, |heatTestDeriv a P x| * Real.exp (|x| / 2)) ^ 2 ≤
        2 * Real.exp 1 * π * Real.exp (L ^ 2) * ∫ x, heatTestDeriv a P x ^ 2 :=
      (sq_integral_abs_gaussPolyFun_mul_exp_half_le
        (gaussPolyDerivPoly (heatPolyR a P) (1 / (2 * a))) hβ hL k).2
    have h' := sq_le_of_one_sub_mul_le' h (hr₁.trans hk)
    have h3 := mul_le_mul_of_nonneg_left hV₁ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc)
    exact h'.trans ((le_of_eq (by ring)).trans (h3.trans_eq (by ring)))

/-! ## The margin algebra -/

/-- **Collecting the bounds.**  The comparison inequality together with the per-term bounds
leaves `V (μ/2 − σ²(μ/2 + 2μB₀E/c₀²) − SEσ(7Y + 6(C² + N²/c₀²))) ≤ H`. -/
theorem le_of_margin_bounds {μ V T κ M ρ τ₀ τ₁ N c₀ C B₀ E S σ Y H : ℝ} (hμ : 0 ≤ μ)
    (hS : 0 ≤ S) (hc₀ : 0 < c₀) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hB₀ : 0 ≤ B₀) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hY : 0 ≤ Y) (hτ₀ : 0 ≤ τ₀) (hτ₁ : 0 ≤ τ₁)
    (hmain : μ * ((V - T) / 2 - 2 * B₀ * κ ^ 2) ≤ H + (2 * M * ρ + ρ ^ 2) * S)
    (hρ : ρ = τ₁ + C * τ₀ + |κ| * N) (hT : T ≤ σ ^ 2 * V) (hτ₀b : τ₀ ^ 2 ≤ E * σ ^ 2 * V)
    (hτ₁b : τ₁ ^ 2 ≤ E * σ ^ 2 * Y * V) (hMb : M ^ 2 ≤ E * Y * V) (hκ : |κ| * c₀ ≤ τ₀) :
    V * (μ / 2 - σ ^ 2 * (μ / 2 + 2 * μ * B₀ * E / c₀ ^ 2) -
      S * E * σ * (7 * Y + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2))) ≤ H := by
  have hκ0 := abs_nonneg κ
  have hκ2 : κ ^ 2 * c₀ ^ 2 ≤ E * σ ^ 2 * V := by
    have h1 : (|κ| * c₀) ^ 2 ≤ τ₀ ^ 2 := pow_le_pow_left₀ (by positivity) hκ 2
    rw [mul_pow, sq_abs] at h1
    linarith
  have hκ2' : κ ^ 2 ≤ E * σ ^ 2 * V / c₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact hκ2
  set W := Y + C ^ 2 + N ^ 2 / c₀ ^ 2 with hW
  have hW0 : 0 ≤ W := by positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ2 : ρ ^ 2 ≤ 3 * E * σ ^ 2 * V * W := by
    have h3 : ρ ^ 2 ≤ 3 * (τ₁ ^ 2 + C ^ 2 * τ₀ ^ 2 + κ ^ 2 * N ^ 2) := by
      rw [hρ]
      nlinarith [sq_nonneg (τ₁ - C * τ₀), sq_nonneg (τ₁ - |κ| * N), sq_nonneg (C * τ₀ - |κ| * N),
        sq_abs κ]
    have h4 : C ^ 2 * τ₀ ^ 2 ≤ C ^ 2 * (E * σ ^ 2 * V) :=
      mul_le_mul_of_nonneg_left hτ₀b (sq_nonneg C)
    have h5 : κ ^ 2 * N ^ 2 ≤ E * σ ^ 2 * V / c₀ ^ 2 * N ^ 2 :=
      mul_le_mul_of_nonneg_right hκ2' (sq_nonneg N)
    have h6 : 3 * E * σ ^ 2 * V * W =
        3 * (E * σ ^ 2 * Y * V + C ^ 2 * (E * σ ^ 2 * V) + E * σ ^ 2 * V / c₀ ^ 2 * N ^ 2) := by
      rw [hW]; ring
    rw [h6]
    linarith
  have hMρ : σ * (2 * M * ρ) ≤ σ ^ 2 * M ^ 2 + ρ ^ 2 := by nlinarith [sq_nonneg (σ * M - ρ)]
  have hsum : 2 * M * ρ + ρ ^ 2 ≤ σ * E * V * (Y + 6 * W) := by
    have a2 : σ ^ 2 * M ^ 2 ≤ σ ^ 2 * (E * Y * V) := mul_le_mul_of_nonneg_left hMb (sq_nonneg σ)
    have a3 : σ * ρ ^ 2 ≤ ρ ^ 2 := mul_le_of_le_one_left (sq_nonneg ρ) hσ1
    have a1 : σ * (2 * M * ρ + ρ ^ 2) = σ * (2 * M * ρ) + σ * ρ ^ 2 := by ring
    have a4 : σ * (σ * E * V * (Y + 6 * W)) = σ ^ 2 * (E * Y * V) + 2 * (3 * E * σ ^ 2 * V * W) := by
      ring
    have h3 : σ * (2 * M * ρ + ρ ^ 2) ≤ σ * (σ * E * V * (Y + 6 * W)) := by
      rw [a1, a4]; linarith
    exact le_of_mul_le_mul_left h3 hσ0
  have hsumS : (2 * M * ρ + ρ ^ 2) * S ≤ σ * E * V * (Y + 6 * W) * S :=
    mul_le_mul_of_nonneg_right hsum hS
  have hlow : μ * ((V - σ ^ 2 * V) / 2 - 2 * B₀ * (E * σ ^ 2 * V / c₀ ^ 2)) ≤
      μ * ((V - T) / 2 - 2 * B₀ * κ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hμ
    have := mul_le_mul_of_nonneg_left hκ2' hB₀
    linarith
  have hfin : V * (μ / 2 - σ ^ 2 * (μ / 2 + 2 * μ * B₀ * E / c₀ ^ 2) -
      S * E * σ * (7 * Y + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2))) =
      μ * ((V - σ ^ 2 * V) / 2 - 2 * B₀ * (E * σ ^ 2 * V / c₀ ^ 2)) -
        σ * E * V * (Y + 6 * W) * S := by
    rw [hW]; ring
  rw [hfin]
  linarith

/-! ## Choice of the moment order -/

theorem tendsto_sq_mul_pow_div {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * θ ^ (n / m)) atTop (𝓝 0) := by
  have habs : |θ| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hq : Tendsto (fun q : ℕ => (m : ℝ) ^ 2 * (((q : ℝ) + 1) ^ 2 * θ ^ q)) atTop (𝓝 0) := by
    have e : (fun q : ℕ => (m : ℝ) ^ 2 * (((q : ℝ) + 1) ^ 2 * θ ^ q)) = fun q : ℕ =>
        (m : ℝ) ^ 2 * ((q : ℝ) ^ 2 * θ ^ q + 2 * ((q : ℝ) ^ 1 * θ ^ q) + (q : ℝ) ^ 0 * θ ^ q) := by
      funext q; ring
    rw [e]
    have h2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 habs
    have h1' := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 habs
    have h0' := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 habs
    simpa using ((h2.add (h1'.const_mul 2)).add h0').const_mul ((m : ℝ) ^ 2)
  have hcomp := hq.comp (Nat.tendsto_div_const_atTop hm.ne')
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcomp
    (fun n => by positivity) fun n => ?_
  simp only [Function.comp_apply]
  have hlt := Nat.lt_mul_div_succ n hm
  have hle : (n : ℝ) + 1 ≤ m * ((n / m : ℕ) + 1 : ℝ) := by exact_mod_cast hlt
  have hpow : ((n : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ 2 * (((n / m : ℕ) : ℝ) + 1) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hle 2
  have := mul_le_mul_of_nonneg_right hpow (pow_nonneg h0 (n / m))
  linarith

theorem heatMomentRatio_le_of_large {n m j : ℕ} {K L a θ : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hm : 0 < m) (ha : 0 < a) (haK : a ≤ K / n) (hnK : K + 1 ≤ n) (hj : j = n / m + 1)
    (hθbig : 2 * K * (2 * n + 2 * n / m + 3) ≤ θ * ((n - K) * L ^ 2)) :
    heatMomentRatio n (2 * j) a L ≤ θ := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hnK' : (0 : ℝ) < n - K := by linarith
  have hβlow : (n - K) / (2 * K) ≤ 1 / (2 * a) - 1 / 2 := by
    have h1 : n / (2 * K) ≤ 1 / (2 * a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := (le_div_iff₀ hnpos).1 haK
      nlinarith
    have : (n - K) / (2 * K) = n / (2 * K) - 1 / 2 := by field_simp
    linarith
  have hnum : (2 * n + 1 + ((2 * j : ℕ) : ℝ)) ≤ 2 * n + 2 * n / m + 3 := by
    have hdiv : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / m := Nat.cast_div_le
    have hcast : ((2 * j : ℕ) : ℝ) = 2 * ((n / m : ℕ) : ℝ) + 2 := by
      rw [hj]; push_cast; ring
    have h2 : (2 : ℝ) * n / m = 2 * ((n : ℝ) / m) := by ring
    rw [hcast, h2]
    linarith
  have hden : 0 < (n - K) / (2 * K) * L ^ 2 := by positivity
  unfold heatMomentRatio
  calc (2 * n + 1 + ((2 * j : ℕ) : ℝ)) / ((1 / (2 * a) - 1 / 2) * L ^ 2)
      ≤ (2 * n + 2 * n / m + 3) / ((n - K) / (2 * K) * L ^ 2) :=
        div_le_div₀ (by positivity) hnum hden (mul_le_mul_of_nonneg_right hβlow (sq_nonneg L))
    _ = 2 * K * (2 * n + 2 * n / m + 3) / ((n - K) * L ^ 2) := by
        field_simp
    _ ≤ θ := by
        rw [div_le_iff₀ (by positivity)]
        exact hθbig

theorem heatMomentRatio_pow_mul_le {n m j : ℕ} {a L θ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hL : 0 < L) (hj : j = n / m + 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (htθ : heatMomentRatio n (2 * j) a L ≤ θ) :
    heatMomentRatio n (2 * j) a L ^ j * (4 * (1 / (2 * a)) * (2 * n + 1)) ≤
      8 * (1 / 2 + 4 / L ^ 2) * (((n : ℝ) + 1) ^ 2 * θ ^ (n / m)) := by
  have htpos : 0 < heatMomentRatio n (2 * j) a L := heatMomentRatio_pos ha ha1 hL
  obtain ⟨t, ht⟩ : ∃ t, t = heatMomentRatio n (2 * j) a L := ⟨_, rfl⟩
  rw [← ht] at htpos htθ ⊢
  have hβ : 1 / (2 * a) = 1 / 2 + (2 * n + 1 + ((2 * j : ℕ) : ℝ)) / (t * L ^ 2) := by
    rw [ht, heatMomentRatio]
    have h1 : 0 < 1 / (2 * a) - 1 / 2 := by linarith [half_lt_inv_two_mul ha ha1]
    have h2 : (0 : ℝ) < 2 * n + 1 + ((2 * j : ℕ) : ℝ) := by positivity
    field_simp
    ring
  have hjn : ((2 * j : ℕ) : ℝ) ≤ 2 * n + 2 := by
    have : 2 * j ≤ 2 * n + 2 := by
      have := Nat.div_le_self n m
      omega
    exact_mod_cast this
  have htj1 : t ^ (n / m) ≤ θ ^ (n / m) := pow_le_pow_left₀ htpos.le htθ _
  have hjsplit : t ^ j = t ^ (n / m) * t := by rw [hj, pow_succ]
  have hL2 : 0 < L ^ 2 := by positivity
  have hθp := pow_nonneg hθ0 (n / m)
  have htn := pow_nonneg htpos.le (n / m)
  -- `t^j β = t^j/2 + t^{n/m}(2n + 1 + 2j)/L²`
  have hkey : t ^ j * (1 / (2 * a)) =
      t ^ j * (1 / 2) + t ^ (n / m) * ((2 * n + 1 + ((2 * j : ℕ) : ℝ)) / L ^ 2) := by
    rw [hβ, mul_add, hjsplit]
    field_simp
  have hfirst : t ^ j ≤ θ ^ (n / m) * θ := by rw [hjsplit]; exact mul_le_mul htj1 htθ htpos.le hθp
  have hsecond : t ^ (n / m) * ((2 * n + 1 + ((2 * j : ℕ) : ℝ)) / L ^ 2) ≤
      θ ^ (n / m) * ((4 * n + 3) / L ^ 2) := by
    apply mul_le_mul htj1 _ (by positivity) hθp
    exact div_le_div_of_nonneg_right (by linarith) hL2.le
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hthird : t ^ j * (1 / (2 * a)) ≤ θ ^ (n / m) * (θ / 2 + (4 * n + 3) / L ^ 2) := by
    rw [hkey]
    have := mul_le_mul_of_nonneg_right hfirst (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith
  have hfourth : θ ^ (n / m) * (θ / 2 + (4 * n + 3) / L ^ 2) ≤
      θ ^ (n / m) * ((n + 1) * (1 / 2 + 4 / L ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hθp
    have h4 : (4 * n + 3) / L ^ 2 ≤ (n + 1) * (4 / L ^ 2) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hL2]; linarith
    have h5 : θ / 2 ≤ (n + 1) * (1 / 2) := by nlinarith
    nlinarith
  have e : t ^ j * (4 * (1 / (2 * a)) * (2 * n + 1)) = 4 * (2 * n + 1) * (t ^ j * (1 / (2 * a))) := by
    ring
  rw [e]
  have h6 := mul_le_mul_of_nonneg_left (hthird.trans hfourth)
    (by positivity : (0 : ℝ) ≤ 4 * (2 * n + 1))
  refine h6.trans ?_
  have h7 : (0 : ℝ) ≤ θ ^ (n / m) * (1 / 2 + 4 / L ^ 2) := by positivity
  have e2 : 4 * (2 * (n : ℝ) + 1) * (θ ^ (n / m) * ((n + 1) * (1 / 2 + 4 / L ^ 2))) =
      (2 * n + 1) * (n + 1) * (4 * (θ ^ (n / m) * (1 / 2 + 4 / L ^ 2))) := by ring
  have e3 : 8 * (1 / 2 + 4 / L ^ 2) * (((n : ℝ) + 1) ^ 2 * θ ^ (n / m)) =
      2 * (n + 1) * (n + 1) * (4 * (θ ^ (n / m) * (1 / 2 + 4 / L ^ 2))) := by ring
  rw [e2, e3]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith

/-- **Choice of the moment order.**  If `4K < L²`, some `m ≥ 1` makes the moment ratio at order
`2(⌊n/m⌋ + 1)` geometrically small, uniformly in `0 < a ≤ K/n`, even after multiplication by
`4β(2n + 1)`. -/
theorem exists_heatMomentOrder {K L : ℝ} (hK : 0 < K) (hL : 0 < L) (hKL : 4 * K < L ^ 2) :
    ∃ m : ℕ, 0 < m ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ K / n →
      a < 1 ∧ heatMomentRatio n (2 * (n / m + 1)) a L ^ (n / m + 1) ≤ δ ∧
        heatMomentRatio n (2 * (n / m + 1)) a L ^ (n / m + 1) *
          (4 * (1 / (2 * a)) * (2 * n + 1)) ≤ δ := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈4 * K / (L ^ 2 - 4 * K)⌉₊ + 1 := ⟨_, rfl⟩
  have hgap : 0 < L ^ 2 - 4 * K := by linarith
  have hm0 : 0 < m := by rw [hm]; exact Nat.succ_pos _
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmR : 4 * K / (L ^ 2 - 4 * K) < m := by
    have := Nat.le_ceil (4 * K / (L ^ 2 - 4 * K))
    rw [hm]; push_cast; linarith
  have hmK : 4 * K < m * (L ^ 2 - 4 * K) := by rwa [div_lt_iff₀ hgap] at hmR
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ℝ, θ₀ = 4 * K * (1 + 1 / (m : ℝ)) / L ^ 2 := ⟨_, rfl⟩
  have hθ₀1 : θ₀ < 1 := by
    rw [hθ₀, div_lt_one (by positivity)]
    have e : 4 * K * (1 + 1 / (m : ℝ)) = 4 * K + 4 * K / m := by ring
    have : 4 * K / m < L ^ 2 - 4 * K := by rw [div_lt_iff₀ hmpos]; linarith
    linarith
  have hθ₀0 : 0 ≤ θ₀ := by rw [hθ₀]; positivity
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 + θ₀) / 2 := ⟨_, rfl⟩
  have hθ1 : θ < 1 := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have hθθ₀ : 0 < θ - θ₀ := by linarith
  have hθ₀L : 4 * K * (1 + 1 / (m : ℝ)) = θ₀ * L ^ 2 := by
    rw [hθ₀]; field_simp
  refine ⟨m, hm0, fun δ hδ => ?_⟩
  have hD0 : 0 < 8 * (1 / 2 + 4 / L ^ 2) := by positivity
  have hlim := tendsto_sq_mul_pow_div hθ0 hθ1 hm0
  have hev1 : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ 2 * θ ^ (n / m) ≤ δ / (8 * (1 / 2 + 4 / L ^ 2)) :=
    hlim.eventually (ge_mem_nhds (by positivity))
  have hev2 : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ 2 * θ ^ (n / m) ≤ δ :=
    hlim.eventually (ge_mem_nhds hδ)
  have hev3 : ∀ᶠ n : ℕ in atTop,
      (6 * K + K * L ^ 2) / ((θ - θ₀) * L ^ 2) + K + 1 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hev1, hev2, hev3] with n hn1 hn2 hn3 a ha haK
  have hfrac0 : 0 ≤ (6 * K + K * L ^ 2) / ((θ - θ₀) * L ^ 2) := by positivity
  have hnK : K + 1 ≤ (n : ℝ) := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have ha1 : a < 1 := by
    have : K / n < 1 := by rw [div_lt_one hnpos]; linarith
    linarith
  have hbig : 2 * K * (2 * n + 2 * n / m + 3) ≤ θ * ((n - K) * L ^ 2) := by
    have h3 : (6 * K + K * L ^ 2) / ((θ - θ₀) * L ^ 2) ≤ n := by linarith
    rw [div_le_iff₀ (by positivity)] at h3
    have e1 : 2 * K * (2 * n + 2 * n / m + 3) = 4 * K * (1 + 1 / (m : ℝ)) * n + 6 * K := by
      field_simp; ring
    rw [e1, hθ₀L]
    have hθK : θ * (K * L ^ 2) ≤ 1 * (K * L ^ 2) :=
      mul_le_mul_of_nonneg_right hθ1.le (by positivity)
    have e2 : θ * ((n - K) * L ^ 2) = θ * L ^ 2 * n - θ * (K * L ^ 2) := by ring
    have e3 : (n : ℝ) * ((θ - θ₀) * L ^ 2) = θ * L ^ 2 * n - θ₀ * L ^ 2 * n := by ring
    rw [e2]
    rw [e3] at h3
    linarith
  have htθ := heatMomentRatio_le_of_large hK hL hm0 ha haK hnK rfl hbig
  have hprod := heatMomentRatio_pow_mul_le ha ha1 hL rfl hθ0 hθ1.le htθ
  have htpos := heatMomentRatio_pos (n := n) (k := 2 * (n / m + 1)) ha ha1 hL
  refine ⟨ha1, ?_, ?_⟩
  · have h1 : heatMomentRatio n (2 * (n / m + 1)) a L ^ (n / m + 1) ≤ θ ^ (n / m + 1) :=
      pow_le_pow_left₀ htpos.le htθ _
    have h2 : θ ^ (n / m + 1) ≤ θ ^ (n / m) := pow_le_pow_of_le_one hθ0 hθ1.le (by omega)
    have h3 : θ ^ (n / m) ≤ ((n : ℝ) + 1) ^ 2 * θ ^ (n / m) := by
      have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      nlinarith [pow_nonneg hθ0 (n / m)]
    linarith
  · calc heatMomentRatio n (2 * (n / m + 1)) a L ^ (n / m + 1) * (4 * (1 / (2 * a)) * (2 * n + 1))
        ≤ 8 * (1 / 2 + 4 / L ^ 2) * (((n : ℝ) + 1) ^ 2 * θ ^ (n / m)) := hprod
      _ ≤ 8 * (1 / 2 + 4 / L ^ 2) * (δ / (8 * (1 / 2 + 4 / L ^ 2))) :=
          mul_le_mul_of_nonneg_left hn1 hD0.le
      _ = δ := by field_simp

end

end RHTower
