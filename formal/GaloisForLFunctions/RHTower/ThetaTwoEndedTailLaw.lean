import GaloisForLFunctions.RHTower.ThetaSeedTransferQuartet
import GaloisForLFunctions.RHTower.ThetaTailScalingAsymptotics

/-!
# The sharp two-ended moment–tail law of zero-division deformations

Let `k` be the full theta source, `h` its logarithmic seed and `F = XiC`.  For a finite selection of
off-line quartets with divisor `P(w) = ∏ (1 − w/β²)`, `D = deg P`, and a real polynomial `N` with
`deg N ≤ D`, the partial-fraction source `u_N` has transform `F · N(z²)/P(z²)` and the seed `v_N`
satisfies `u_N = Σ n^{-1/2} v_N(· + log n)` on `x ≥ 0`.

* **Sharp tail law (4).**  With `d = D − deg N` and `c = N_top ∏(−β²)`,
  `e^{4dx} u_N/k` and `e^{4dx} v_N/h` both tend to `(−1)^d c/(2π)^{2d} ≠ 0`.
* **Two-ended filtration (5).**  The first `J` even moments of `u_N` vanish iff `X^J ∣ N`, and
  `u_N = O(e^{-4dx} k)` iff `N = 0` or `deg N + d ≤ D`; the space `W_{J,d}` of such directions has
  dimension `max(D + 1 − J − d, 0)`.  With finitely many off-line quartets this is the dimension of
  the full space of bounded divisor-keeping source differences; with infinitely many, every
  `W_{J,d}` is infinite-dimensional.
* **Seed transfer.**  Every direction of `W_{J,d}` has a seed bounded by `C h`, of tail order
  `e^{-4dx}`, and small positive perturbations keep both the source and the seed positive, the
  Euler identity, the real-zero divisor and the first `J` moments.
* **Faithful germ.**  `u_N` is flat to all orders in `e^{-2x}` only for `N = 0`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## The sharp two-ended tail coefficient (4) -/

section Selection

variable {l : List ℂ}

theorem tendsto_re_of_tendsto {g : ℝ → ℂ} {w : ℝ → ℝ} {lim₀ : ℝ}
    (h : Tendsto (fun x => ((w x : ℝ) : ℂ) * g x) atTop (𝓝 (lim₀ : ℂ))) :
    Tendsto (fun x => w x * (g x).re) atTop (𝓝 lim₀) := by
  have := (Complex.continuous_re.tendsto _).comp h
  rw [Complex.ofReal_re] at this
  exact this.congr fun x => by simp only [Function.comp]; rw [Complex.re_ofReal_mul]

/-- **The sharp tail law (4)** for the source: for `N ≠ 0` of degree `≤ D = |L|`, with
`d = D − deg N` and `c = N_top · ∏(−β²)`, `e^{4dx} u_N(x)/k(x) → (−1)^d c/(2π)^{2d}`. -/
theorem tendsto_rationalSource {N : Polynomial ℝ} (hN0 : N ≠ 0) (hN : N.natDegree ≤ (quadrantListOf l).length) {r : ℝ}
    (hr : ((quadrantListOf l).map fun β : ℂ => -β ^ 2).prod = (r : ℂ)) :
    Tendsto (fun x => Real.exp (4 * (((quadrantListOf l).length - N.natDegree : ℕ) : ℝ) * x) *
      rationalSource l N x / thetaCuspFullSource x) atTop
      (𝓝 ((-1) ^ ((quadrantListOf l).length - N.natDegree) * N.leadingCoeff * r /
        (2 * Real.pi) ^ (2 * ((quadrantListOf l).length - N.natDegree)))) := by
  have hinj : Function.Injective (algebraMap ℝ ℂ) := (algebraMap ℝ ℂ).injective
  have h := thetaTypeTail_source.tendsto_listComb (quadrantListOf l) (N.map (algebraMap ℝ ℂ))
    (Polynomial.map_ne_zero hN0) (by rw [Polynomial.natDegree_map_eq_of_injective hinj]; exact hN)
  rw [Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.leadingCoeff_map_of_injective hinj,
    hr] at h
  have hval : (-1 : ℂ) ^ ((quadrantListOf l).length - N.natDegree) *
      (algebraMap ℝ ℂ) N.leadingCoeff * (r : ℂ) /
        (2 * (Real.pi : ℂ)) ^ (2 * ((quadrantListOf l).length - N.natDegree)) =
      (((-1) ^ ((quadrantListOf l).length - N.natDegree) * N.leadingCoeff * r /
        (2 * Real.pi) ^ (2 * ((quadrantListOf l).length - N.natDegree)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hval] at h
  have h2 := tendsto_re_of_tendsto (w := fun x =>
    Real.exp (4 * (((quadrantListOf l).length - N.natDegree : ℕ) : ℝ) * x) / thetaCuspFullSource x)
    (g := listComb (fun L' => halfListDivision L' fun y => (thetaCuspFullSource y : ℂ))
      (quadrantListOf l) (N.map (algebraMap ℝ ℂ))) (h.congr fun x => by push_cast; ring)
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [rationalSource, listComb_congr (fun L y hy => thetaListDivision_eq_halfListDivision L y hy)
    _ _ hx]
  have e : (fun y => ((thetaCuspFullSource y : ℝ) : ℂ)) = thetaSourceC := rfl
  rw [e]
  ring

/-- **The sharp tail law (4)** for the seed: `e^{4dx} v_N(x)/h(x)` has the same limit. -/
theorem tendsto_rationalSeed {N : Polynomial ℝ} (hN0 : N ≠ 0)
    (hN : N.natDegree ≤ (quadrantListOf l).length) {r : ℝ}
    (hr : ((quadrantListOf l).map fun β : ℂ => -β ^ 2).prod = (r : ℂ)) :
    Tendsto (fun x => Real.exp (4 * (((quadrantListOf l).length - N.natDegree : ℕ) : ℝ) * x) *
      rationalSeed l N x / thetaCuspLogSeed x) atTop
      (𝓝 ((-1) ^ ((quadrantListOf l).length - N.natDegree) * N.leadingCoeff * r /
        (2 * Real.pi) ^ (2 * ((quadrantListOf l).length - N.natDegree)))) := by
  have hinj : Function.Injective (algebraMap ℝ ℂ) := (algebraMap ℝ ℂ).injective
  have h := thetaTypeTail_seed.tendsto_listComb (quadrantListOf l) (N.map (algebraMap ℝ ℂ))
    (Polynomial.map_ne_zero hN0) (by rw [Polynomial.natDegree_map_eq_of_injective hinj]; exact hN)
  rw [Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.leadingCoeff_map_of_injective hinj,
    hr] at h
  have hval : (-1 : ℂ) ^ ((quadrantListOf l).length - N.natDegree) *
      (algebraMap ℝ ℂ) N.leadingCoeff * (r : ℂ) /
        (2 * (Real.pi : ℂ)) ^ (2 * ((quadrantListOf l).length - N.natDegree)) =
      (((-1) ^ ((quadrantListOf l).length - N.natDegree) * N.leadingCoeff * r /
        (2 * Real.pi) ^ (2 * ((quadrantListOf l).length - N.natDegree)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hval] at h
  have h2 := tendsto_re_of_tendsto (w := fun x =>
    Real.exp (4 * (((quadrantListOf l).length - N.natDegree : ℕ) : ℝ) * x) / thetaCuspLogSeed x)
    (g := listComb (fun L' => halfListDivision L' fun y => (thetaCuspLogSeed y : ℂ))
      (quadrantListOf l) (N.map (algebraMap ℝ ℂ))) (h.congr fun x => by push_cast; ring)
  refine h2.congr fun x => ?_
  have e : (fun L' => halfListDivision L' fun y => ((thetaCuspLogSeed y : ℝ) : ℂ)) =
    seedListDivision := rfl
  rw [e, rationalSeed]
  ring

theorem tail_limit_ne_zero {N : Polynomial ℝ} (hN0 : N ≠ 0) {r : ℝ} (hr : 0 < r) (d : ℕ) :
    (-1) ^ d * N.leadingCoeff * r / (2 * Real.pi) ^ (2 * d) ≠ 0 := by
  have : N.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hN0
  have hπ : (2 * Real.pi) ^ (2 * d) ≠ 0 := pow_ne_zero _ (by positivity)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) this) hr.ne') hπ

/-! ## Tail orders -/

/-- `u = O(e^{-4dx} k)` at `+∞`. -/
def tailOrderSubmodule (d : ℕ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {u | ∃ C, ∀ᶠ x in atTop, |u x| ≤ C * Real.exp (-(4 * d * x)) * thetaCuspFullSource x}
  add_mem' := by
    rintro u v ⟨Cu, hu⟩ ⟨Cv, hv⟩
    refine ⟨Cu + Cv, ?_⟩
    filter_upwards [hu, hv] with x h1 h2
    simp only [Pi.add_apply]
    calc |u x + v x| ≤ |u x| + |v x| := abs_add_le _ _
      _ ≤ _ := by linarith
  zero_mem' := ⟨0, Eventually.of_forall fun x => by simp⟩
  smul_mem' := by
    rintro c u ⟨C, hu⟩
    refine ⟨|c| * C, ?_⟩
    filter_upwards [hu] with x hx
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    calc |c| * |u x| ≤ |c| * (C * Real.exp (-(4 * d * x)) * thetaCuspFullSource x) :=
          mul_le_mul_of_nonneg_left hx (abs_nonneg c)
      _ = _ := by ring

theorem mem_tailOrderSubmodule {d : ℕ} {u : ℝ → ℝ} : u ∈ tailOrderSubmodule d ↔
    ∃ C, ∀ᶠ x in atTop, |u x| ≤ C * Real.exp (-(4 * d * x)) * thetaCuspFullSource x := Iff.rfl

/-- A finite limit of `e^{4jx} u/w` gives `|u| ≤ C e^{-4dx} w` at `+∞` for every `d ≤ j`. -/
theorem exists_exp_bound_of_tendsto {u w : ℝ → ℝ} {j d : ℕ} {a : ℝ} (hd : d ≤ j)
    (hw : ∀ᶠ x in atTop, 0 < w x)
    (h : Tendsto (fun x => Real.exp (4 * j * x) * u x / w x) atTop (𝓝 a)) :
    ∃ C, ∀ᶠ x in atTop, |u x| ≤ C * Real.exp (-(4 * d * x)) * w x := by
  refine ⟨|a| + 1, ?_⟩
  filter_upwards [h.eventually (Metric.ball_mem_nhds a one_pos), hw, eventually_ge_atTop (0 : ℝ)]
    with x hx hk hx0
  rw [Real.dist_eq] at hx
  have he := Real.exp_pos (4 * j * x)
  have h1 : |Real.exp (4 * j * x) * u x / w x| ≤ |a| + 1 := by
    have := abs_sub_abs_le_abs_sub (Real.exp (4 * j * x) * u x / w x) a
    linarith
  rw [abs_div, abs_mul, abs_of_pos he, abs_of_pos hk, div_le_iff₀ hk] at h1
  have heq : Real.exp (-(4 * j * x)) * Real.exp (4 * j * x) = 1 := by rw [← Real.exp_add]; simp
  have hdj : (d : ℝ) ≤ j := by exact_mod_cast hd
  have hexp : Real.exp (-(4 * j * x)) ≤ Real.exp (-(4 * d * x)) := Real.exp_le_exp.2 (by nlinarith)
  calc |u x| = Real.exp (-(4 * j * x)) * (Real.exp (4 * j * x) * |u x|) := by
        rw [← mul_assoc, heq, one_mul]
    _ ≤ Real.exp (-(4 * j * x)) * ((|a| + 1) * w x) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ ≤ Real.exp (-(4 * d * x)) * ((|a| + 1) * w x) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = _ := by ring

theorem mem_tailOrderSubmodule_of_tendsto {u : ℝ → ℝ} {j : ℕ} {a : ℝ}
    (h : Tendsto (fun x => Real.exp (4 * j * x) * u x / thetaCuspFullSource x) atTop (𝓝 a)) :
    u ∈ tailOrderSubmodule j :=
  exists_exp_bound_of_tendsto le_rfl (Eventually.of_forall thetaCuspFullSource_pos) h

theorem tailOrderSubmodule_antitone {d d' : ℕ} (h : d ≤ d') :
    tailOrderSubmodule d' ≤ tailOrderSubmodule d := by
  rintro u ⟨C, hu⟩
  refine ⟨max C 0, ?_⟩
  filter_upwards [hu, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  refine hx.trans ?_
  have hdd : (d : ℝ) ≤ d' := by exact_mod_cast h
  have he : Real.exp (-(4 * d' * x)) ≤ Real.exp (-(4 * d * x)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hk := (thetaCuspFullSource_pos x).le
  calc C * Real.exp (-(4 * d' * x)) * thetaCuspFullSource x ≤
        max C 0 * Real.exp (-(4 * d' * x)) * thetaCuspFullSource x := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * Real.exp (-(4 * d * x)) * thetaCuspFullSource x := by
        have := le_max_right C 0
        gcongr

theorem tendsto_zero_of_mem_tailOrderSubmodule {u : ℝ → ℝ} {d d' : ℕ}
    (hu : u ∈ tailOrderSubmodule d) (hd : d' < d) :
    Tendsto (fun x => Real.exp (4 * d' * x) * u x / thetaCuspFullSource x) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hu
  have hpos : (0 : ℝ) < 4 * ((d : ℝ) - d') := by
    have : (d' : ℝ) < d := by exact_mod_cast hd
    linarith
  have hlim : Tendsto (fun x : ℝ => |C| * Real.exp (-(4 * ((d : ℝ) - d') * x))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hpos)).const_mul
      |C|
    rw [mul_zero] at this
    exact this.congr fun x => by simp only [Function.comp, id]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hC] with x hx
  have hk := thetaCuspFullSource_pos x
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hk,
    div_le_iff₀ hk]
  have heq : Real.exp (4 * d' * x) * Real.exp (-(4 * d * x)) =
      Real.exp (-(4 * ((d : ℝ) - d') * x)) := by rw [← Real.exp_add]; ring_nf
  calc Real.exp (4 * d' * x) * |u x| ≤ Real.exp (4 * d' * x) *
        (|C| * Real.exp (-(4 * d * x)) * thetaCuspFullSource x) :=
        mul_le_mul_of_nonneg_left (hx.trans (by gcongr; exact le_abs_self C)) (Real.exp_pos _).le
    _ = |C| * Real.exp (-(4 * ((d : ℝ) - d') * x)) * thetaCuspFullSource x := by
        rw [← heq]; ring

/-! ## The monomial basis `s_j = u_{X^j}` -/

/-- The basis `s_j = u_{X^j}`, `0 ≤ j ≤ |L|`, of the partial-fraction sources of a selection. -/
def rationalBasis (l : List ℂ) (j : Fin ((quadrantListOf l).length + 1)) : ℝ → ℝ :=
  rationalSource l (Polynomial.X ^ (j : ℕ))

theorem rationalBasis_spec (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) (hnd : l.Nodup) {r : ℝ}
    (hr : ((quadrantListOf l).map fun β : ℂ => -β ^ 2).prod = (r : ℂ)) :
    (∀ j, Continuous (rationalBasis l j)) ∧ (∀ j x, rationalBasis l j (-x) = rationalBasis l j x) ∧
      (∃ C, ∀ j x, |rationalBasis l j x| ≤ C * thetaCuspFullSource x) ∧
      (∀ j z, sourceTransform (fun x => (rationalBasis l j x : ℂ)) z *
        listDivisor (quadrantListOf l) z = XiC z * z ^ (2 * (j : ℕ))) ∧
      ∀ j, Tendsto (fun x => |rationalBasis l j x - (if (j : ℕ) = (quadrantListOf l).length then r
        else 0) * thetaCuspFullSource x| / thetaCuspFullSource x) (cocompact ℝ) (𝓝 0) := by
  have h : ∀ j : Fin ((quadrantListOf l).length + 1), _ := fun j =>
    rationalSource_spec hl hnd (Polynomial.X ^ (j : ℕ))
      (by rw [Polynomial.natDegree_X_pow]; exact Nat.lt_succ_iff.1 j.isLt) hr
  choose hc he hC hT ht hm using h
  choose C hC using hC
  refine ⟨fun j => (hc j).continuous, he, ⟨∑ j, max (C j) 0, fun j x => ?_⟩, fun j z => ?_,
    fun j => ?_⟩
  · calc |rationalBasis l j x| ≤ C j * thetaCuspFullSource x := hC j x
      _ ≤ max (C j) 0 * thetaCuspFullSource x :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (thetaCuspFullSource_pos x).le
      _ ≤ (∑ i, max (C i) 0) * thetaCuspFullSource x :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => le_max_right (C i) 0)
            (Finset.mem_univ j)) (thetaCuspFullSource_pos x).le
  · rw [rationalBasis, hT j z, Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_pow,
      Polynomial.eval_X, ← pow_mul]
  · have := ht j
    rw [Polynomial.coeff_X_pow] at this
    refine this.congr fun x => ?_
    rw [rationalBasis]
    congr 3
    split_ifs with h1 h2 h2
    · rw [one_mul]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp

/-- Exact tail order of the basis: `e^{4(|L| − j)x} s_j/k → (−1)^{|L|−j} r/(2π)^{2(|L|−j)} ≠ 0`. -/
theorem tendsto_rationalBasis {r : ℝ}
    (hr : ((quadrantListOf l).map fun β : ℂ => -β ^ 2).prod = (r : ℂ))
    (j : Fin ((quadrantListOf l).length + 1)) :
    Tendsto (fun x => Real.exp (4 * (((quadrantListOf l).length - j : ℕ) : ℝ) * x) *
      rationalBasis l j x / thetaCuspFullSource x) atTop
      (𝓝 ((-1) ^ ((quadrantListOf l).length - j) * r /
        (2 * Real.pi) ^ (2 * ((quadrantListOf l).length - j)))) := by
  have h := tendsto_rationalSource (l := l) (N := Polynomial.X ^ (j : ℕ))
    (pow_ne_zero _ Polynomial.X_ne_zero)
    (by rw [Polynomial.natDegree_X_pow]; exact Nat.lt_succ_iff.1 j.isLt) hr
  rw [Polynomial.natDegree_X_pow, Polynomial.leadingCoeff_X_pow, mul_one] at h
  exact h

end Selection

/-! ## Coordinates of the tail order -/

section Coords

variable {l : List ℂ} {r : ℝ} (hr0 : 0 < r)
  (hr : ((quadrantListOf l).map fun β : ℂ => -β ^ 2).prod = (r : ℂ))

include hr in
theorem divisorBasis_rationalBasis_mem_tailOrder {j d : ℕ}
    (hj : j < (quadrantListOf l).length + 1) (hjd : j + d ≤ (quadrantListOf l).length) :
    divisorBasis (rationalBasis l) j ∈ tailOrderSubmodule d := by
  have h := mem_tailOrderSubmodule_of_tendsto (tendsto_rationalBasis hr ⟨j, hj⟩)
  refine tailOrderSubmodule_antitone (show d ≤ (quadrantListOf l).length - j by omega) ?_
  rwa [divisorBasis, dif_pos hj]

include hr0 hr in
/-- **Tail order in coordinates.**  `Σ c_j s_j = O(e^{-4dx} k)` iff `c_j = 0` whenever
`|L| < j + d`. -/
theorem divisorBasisComb_mem_tailOrder_iff (c : ℕ → ℝ) (d : ℕ) :
    divisorBasisComb (rationalBasis l) c ∈ tailOrderSubmodule d ↔
      ∀ j < (quadrantListOf l).length + 1, (quadrantListOf l).length < j + d → c j = 0 := by
  constructor
  · intro hu
    by_contra hne
    push Not at hne
    obtain ⟨j₀, hj₀, hj₀d, hc₀⟩ := hne
    set T := (Finset.range ((quadrantListOf l).length + 1)).filter fun j => c j ≠ 0
    have hT : T.Nonempty := ⟨j₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj₀, hc₀⟩⟩
    set js := T.max' hT
    have hjsT := Finset.max'_mem T hT
    obtain ⟨hjs_lt, hcjs⟩ := Finset.mem_filter.1 hjsT
    rw [Finset.mem_range] at hjs_lt
    have hj₀js : j₀ ≤ js := T.le_max' j₀ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj₀, hc₀⟩)
    set ds := (quadrantListOf l).length - js
    have hds : ds < d := by omega
    set lam := (-1) ^ ((quadrantListOf l).length - js) * r /
      (2 * Real.pi) ^ (2 * ((quadrantListOf l).length - js))
    have hlam : lam ≠ 0 := by
      have := tail_limit_ne_zero (N := (Polynomial.X : Polynomial ℝ) ^ js)
        (pow_ne_zero _ Polynomial.X_ne_zero) hr0 ((quadrantListOf l).length - js)
      rwa [Polynomial.leadingCoeff_X_pow, mul_one] at this
    have hterm : ∀ j ∈ Finset.range ((quadrantListOf l).length + 1),
        Tendsto (fun x => c j * (Real.exp (4 * (ds : ℝ) * x) *
          divisorBasis (rationalBasis l) j x / thetaCuspFullSource x)) atTop
          (𝓝 (if j = js then c js * lam else 0)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      by_cases hjj : j = js
      · rw [if_pos hjj, hjj]
        refine (tendsto_rationalBasis hr ⟨js, hjs_lt⟩).const_mul (c js) |>.congr fun x => ?_
        rw [divisorBasis, dif_pos hjs_lt]
      · rw [if_neg hjj]
        by_cases hcj : c j = 0
        · rw [hcj]; simp only [zero_mul]; exact tendsto_const_nhds
        · have hjle : j ≤ js := T.le_max' j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hcj⟩)
          have hmem := divisorBasis_rationalBasis_mem_tailOrder hr hj
            (d := (quadrantListOf l).length - j) (by omega)
          have := (tendsto_zero_of_mem_tailOrderSubmodule hmem (d' := ds) (by omega)).const_mul
            (c j)
          rwa [mul_zero] at this
    have hsum := tendsto_finsetSum _ hterm
    rw [Finset.sum_ite_eq' (Finset.range _) js, if_pos (Finset.mem_range.2 hjs_lt)] at hsum
    have hzero := tendsto_zero_of_mem_tailOrderSubmodule hu hds
    have heq : ∀ x, Real.exp (4 * (ds : ℝ) * x) * divisorBasisComb (rationalBasis l) c x /
        thetaCuspFullSource x = ∑ j ∈ Finset.range ((quadrantListOf l).length + 1),
          c j * (Real.exp (4 * (ds : ℝ) * x) * divisorBasis (rationalBasis l) j x /
            thetaCuspFullSource x) := fun x => by
      rw [divisorBasisComb, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hlim := hzero.congr heq
    exact mul_ne_zero hcjs hlam (tendsto_nhds_unique hsum hlim)
  · intro h
    have heq : divisorBasisComb (rationalBasis l) c =
        ∑ j ∈ Finset.range ((quadrantListOf l).length + 1),
          c j • divisorBasis (rationalBasis l) j := by
      funext x
      simp only [divisorBasisComb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    by_cases hcj : c j = 0
    · rw [hcj, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (divisorBasis_rationalBasis_mem_tailOrder hr hj
        (by by_contra h'; exact hcj (h j hj (by omega))))

end Coords

/-! ## The two-ended filtration (5) -/

/-- `W_{J,d}`: divisor-keeping sources whose even moments of orders `0, 2, …, 2J − 2` vanish and with
`u = O(e^{-4dx} k)` at `+∞`. -/
def twoEndedSources (J d : ℕ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {u | u ∈ thetaKeepingSources ∧ (∀ i < J, ∫ x, x ^ (2 * i) * u x = 0) ∧
    u ∈ tailOrderSubmodule d}
  add_mem' := by
    rintro u v ⟨hu, hum, hut⟩ ⟨hv, hvm, hvt⟩
    refine ⟨thetaKeepingSources.add_mem hu hv, fun i hi => ?_,
      (tailOrderSubmodule d).add_mem hut hvt⟩
    obtain ⟨huc, -, ⟨Cu, hCu⟩, -⟩ := hu
    obtain ⟨hvc, -, ⟨Cv, hCv⟩, -⟩ := hv
    simp only [Pi.add_apply, mul_add]
    rw [integral_add (integrable_pow_mul_of_le huc hCu _) (integrable_pow_mul_of_le hvc hCv _),
      hum i hi, hvm i hi, add_zero]
  zero_mem' := ⟨thetaKeepingSources.zero_mem, fun i _ => by simp, (tailOrderSubmodule d).zero_mem⟩
  smul_mem' := by
    rintro c u ⟨hu, hum, hut⟩
    refine ⟨thetaKeepingSources.smul_mem c hu, fun i hi => ?_, (tailOrderSubmodule d).smul_mem c hut⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (fun x => x ^ (2 * i) * (c * u x)) = fun x => c * (x ^ (2 * i) * u x) from
      funext fun x => by ring, integral_const_mul, hum i hi, mul_zero]

theorem mem_twoEndedSources {J d : ℕ} {u : ℝ → ℝ} : u ∈ twoEndedSources J d ↔
    u ∈ thetaKeepingSources ∧ (∀ i < J, ∫ x, x ^ (2 * i) * u x = 0) ∧
      u ∈ tailOrderSubmodule d := Iff.rfl

/-- The linear map `c ↦ Σ c_j s_j`. -/
def divisorBasisCombMap (l : List ℂ) : (ℕ → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun c := divisorBasisComb (rationalBasis l) c
  map_add' c c' := funext fun x => by
    simp only [divisorBasisComb, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := funext fun x => by
    simp only [divisorBasisComb, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- The space of partial-fraction sources `u_N`, `deg N ≤ |L|`, of a selection of quartets. -/
def rationalSelection (l : List ℂ) : Submodule ℝ (ℝ → ℝ) := LinearMap.range (divisorBasisCombMap l)

section Basis

variable {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) (hnd : l.Nodup) {r : ℝ} (hr0 : 0 < r)
  (hr : ((quadrantListOf l).map fun β : ℂ => -β ^ 2).prod = (r : ℂ))

include hl hnd hr0 hr in
/-- **Membership in coordinates.**  `Σ c_j s_j ∈ W_{J,d}` iff `c_j = 0` for `j < J` and for
`|L| < j + d`. -/
theorem divisorBasisComb_mem_twoEndedSources_iff (c : ℕ → ℝ) (J d : ℕ) :
    divisorBasisComb (rationalBasis l) c ∈ twoEndedSources J d ↔
      (∀ j < (quadrantListOf l).length + 1, j < J → c j = 0) ∧
        ∀ j < (quadrantListOf l).length + 1, (quadrantListOf l).length < j + d → c j = 0 := by
  obtain ⟨hsc, hse, ⟨C, hsC⟩, hsT, hst⟩ := rationalBasis_spec hl hnd hr
  rw [mem_twoEndedSources, divisorBasisComb_mem_tailOrder_iff hr0 hr]
  have hW := divisorBasisComb_mem_thetaKeepingSources hl hsc hse hsC hsT c
  have hmom : (∀ i < J, ∫ x, x ^ (2 * i) * divisorBasisComb (rationalBasis l) c x = 0) ↔
      ∀ j < (quadrantListOf l).length + 1, j < J → c j = 0 := by
    rcases J with _ | J
    · simp
    · have := moments_sum_divisorBasis_iff hsc hse hsC hsT c J
      constructor
      · intro h j hj hjJ
        exact this.1 (fun i hi => h i (by omega)) j hj (by omega)
      · intro h i hi
        exact this.2 (fun j hj hjJ => h j hj (by omega)) i (by omega)
  rw [hmom]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hW, h.1, h.2⟩⟩

include hl hnd hr in
/-- `u_N = Σ_j N_j s_j`. -/
theorem rationalSource_eq_divisorBasisComb (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) :
    rationalSource l N = divisorBasisComb (rationalBasis l) fun j => N.coeff j := by
  obtain ⟨hsc, hse, ⟨C, hsC⟩, hsT, hst⟩ := rationalBasis_spec hl hnd hr
  obtain ⟨huc, -, ⟨Cu, huC⟩, huT, -, -⟩ := rationalSource_spec hl hnd N hN hr
  exact eq_sum_divisorBasis_of_mul_eq hl hsc hsC hsT huc.continuous huC hN huT

include hl hnd hr0 hr in
/-- **The two-ended law for `u_N`.**  The first `J` even moments of `u_N` vanish iff `X^J ∣ N`, and
`u_N = O(e^{-4dx} k)` iff `N = 0` or `deg N + d ≤ |L|`. -/
theorem rationalSource_mem_twoEndedSources_iff (N : Polynomial ℝ)
    (hN : N.natDegree ≤ (quadrantListOf l).length) (J d : ℕ) :
    rationalSource l N ∈ twoEndedSources J d ↔
      Polynomial.X ^ J ∣ N ∧ (N = 0 ∨ N.natDegree + d ≤ (quadrantListOf l).length) := by
  rw [rationalSource_eq_divisorBasisComb hl hnd hr N hN,
    divisorBasisComb_mem_twoEndedSources_iff hl hnd hr0 hr, Polynomial.X_pow_dvd_iff]
  refine and_congr ⟨fun h j hj => ?_, fun h j _ hj => h j hj⟩ ⟨fun h => ?_, fun h j hj hjd => ?_⟩
  · by_cases hjn : j < (quadrantListOf l).length + 1
    · exact h j hjn hj
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · by_cases hN0 : N = 0
    · exact Or.inl hN0
    · refine Or.inr (not_lt.1 fun hlt => ?_)
      exact Polynomial.leadingCoeff_ne_zero.2 hN0 (h _ (by omega) hlt)
  · rcases h with rfl | h
    · simp
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

include hl hnd hr0 hr in
/-- **The full tail germ is faithful**: `u_N` is flat to all orders in `e^{-2x}` iff `N = 0`. -/
theorem rationalSource_flat_iff (N : Polynomial ℝ) (hN : N.natDegree ≤ (quadrantListOf l).length) :
    (∀ d, rationalSource l N ∈ tailOrderSubmodule d) ↔ N = 0 := by
  constructor
  · intro h
    have := ((rationalSource_mem_twoEndedSources_iff hl hnd hr0 hr N hN 0
      ((quadrantListOf l).length + 1)).1 ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _), h _⟩).2
    · rcases this with h0 | h0
      · exact h0
      · omega
    · rw [rationalSource_eq_divisorBasisComb hl hnd hr N hN]
      obtain ⟨hsc, hse, ⟨C, hsC⟩, hsT, -⟩ := rationalBasis_spec hl hnd hr
      exact divisorBasisComb_mem_thetaKeepingSources hl hsc hse hsC hsT _
  · rintro rfl d
    rw [rationalSource_eq_divisorBasisComb hl hnd hr 0 (by simp)]
    have : divisorBasisComb (rationalBasis l) (fun j => (0 : Polynomial ℝ).coeff j) = 0 := by
      funext x; simp [divisorBasisComb]
    rw [this]
    exact (tailOrderSubmodule d).zero_mem

include hl hnd hr0 hr in
/-- **The full tail germ determines the rational defect.** -/
theorem rationalSource_germ_injective {N N' : Polynomial ℝ}
    (hN : N.natDegree ≤ (quadrantListOf l).length) (hN' : N'.natDegree ≤ (quadrantListOf l).length)
    (h : ∀ d, (fun x => rationalSource l N x - rationalSource l N' x) ∈ tailOrderSubmodule d) :
    N = N' := by
  have hsub : (N - N').natDegree ≤ (quadrantListOf l).length :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hN hN')
  have heq : rationalSource l (N - N') = fun x => rationalSource l N x - rationalSource l N' x := by
    rw [rationalSource_eq_divisorBasisComb hl hnd hr _ hsub,
      rationalSource_eq_divisorBasisComb hl hnd hr _ hN,
      rationalSource_eq_divisorBasisComb hl hnd hr _ hN']
    funext x
    simp only [divisorBasisComb, Polynomial.coeff_sub, sub_mul, Finset.sum_sub_distrib]
  exact sub_eq_zero.1 ((rationalSource_flat_iff hl hnd hr0 hr _ hsub).1 (fun d => heq ▸ h d))

include hl hnd hr0 hr in
/-- **Exact dimension (5) for a selection.**  The partial-fraction directions of the selection
with vanishing first `J` even moments and tail `O(e^{-4dx} k)` form a space of dimension
`max(D + 1 − J − d, 0)`, `D = |L|`. -/
theorem finrank_rationalSelection_inf_twoEndedSources (J d : ℕ) :
    Module.finrank ℝ (rationalSelection l ⊓ twoEndedSources J d : Submodule ℝ (ℝ → ℝ)) =
      (quadrantListOf l).length + 1 - J - d := by
  obtain ⟨hsc, hse, ⟨C, hsC⟩, hsT, hst⟩ := rationalBasis_spec hl hnd hr
  by_cases hJd : J + d ≤ (quadrantListOf l).length + 1
  · have hW : rationalSelection l ⊓ twoEndedSources J d = LinearMap.range
        (Fintype.linearCombination ℝ fun i : Fin ((quadrantListOf l).length + 1 - J - d) =>
          divisorBasis (rationalBasis l) (J + i)) := by
      refine le_antisymm (fun u hu => ?_) ?_
      · obtain ⟨⟨c, rfl⟩, hu2⟩ := hu
        obtain ⟨h1, h2⟩ := (divisorBasisComb_mem_twoEndedSources_iff hl hnd hr0 hr c J d).1 hu2
        exact ⟨fun i => c (J + i), (divisorBasisComb_eq_linearCombination (by omega) c
          fun j hj hj' => by rcases hj' with hj' | hj'; exact h1 j hj hj'; exact h2 j hj (by omega)).symm⟩
      · rw [Fintype.range_linearCombination, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        have hi := i.isLt
        have hsingle := divisorBasisComb_single (s := rationalBasis l)
          (show J + (i : ℕ) < (quadrantListOf l).length + 1 by omega)
        refine ⟨⟨fun k => if k = J + i then 1 else 0, hsingle⟩, ?_⟩
        show divisorBasis (rationalBasis l) (J + i) ∈ twoEndedSources J d
        rw [← hsingle, divisorBasisComb_mem_twoEndedSources_iff hl hnd hr0 hr]
        exact ⟨fun j _ hj => if_neg (by omega), fun j _ hj => if_neg (by omega)⟩
    rw [hW, LinearMap.finrank_range_of_inj (injective_linearCombination_divisorBasis hsc hsC hsT
      (by omega)), Module.finrank_fin_fun]
  · have hW : rationalSelection l ⊓ twoEndedSources J d = ⊥ := by
      refine eq_bot_iff.2 fun u hu => ?_
      obtain ⟨⟨c, rfl⟩, hu2⟩ := hu
      obtain ⟨h1, h2⟩ := (divisorBasisComb_mem_twoEndedSources_iff hl hnd hr0 hr c J d).1 hu2
      rw [Submodule.mem_bot]
      funext x
      show divisorBasisComb (rationalBasis l) c x = 0
      refine Finset.sum_eq_zero fun j hj => ?_
      have := Finset.mem_range.1 hj
      by_cases hjJ : j < J
      · simp [h1 j this hjJ]
      · simp [h2 j this (by omega)]
    rw [hW, finrank_bot]
    omega

include hl hnd hr in
/-- Every direction of the selection is a partial-fraction source `u_N`, `deg N ≤ |L|`. -/
theorem exists_rationalSource_of_mem_rationalSelection {u : ℝ → ℝ} (hu : u ∈ rationalSelection l) :
    ∃ N : Polynomial ℝ, N.natDegree ≤ (quadrantListOf l).length ∧ u = rationalSource l N := by
  obtain ⟨c, rfl⟩ := hu
  have hdeg : (∑ j ∈ Finset.range ((quadrantListOf l).length + 1),
      Polynomial.C (c j) * Polynomial.X ^ j).natDegree ≤ (quadrantListOf l).length :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.1 hj; omega)
  refine ⟨_, hdeg, ?_⟩
  rw [rationalSource_eq_divisorBasisComb hl hnd hr _ hdeg]
  funext x
  show divisorBasisComb _ c x = _
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  show c j = (∑ i ∈ Finset.range ((quadrantListOf l).length + 1),
    Polynomial.C (c i) * Polynomial.X ^ i).coeff j
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j (fun i _ hij => by
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hij)]) (fun h => absurd hj h),
    Polynomial.coeff_C_mul_X_pow, if_pos rfl]

include hl hnd hr0 hr in
/-- **Seed transfer of every two-ended direction.**  Every `u ∈ W_{J,d}` of the selection has a seed
`v` with `|v| ≤ C h` on `x ≥ 0`, `v = O(e^{-4dx} h)` at `+∞` and `u = Σ n^{-1/2} v(· + log n)` on
`x ≥ 0`.  For small `ε > 0`: `k + εu > 0`, `h + εv > 0` on `x ≥ 0`, the pair satisfies the Euler
identity, the perturbed source keeps the real-zero divisor of `F` and the first `J` even moments of
`k`, and differs from `k` by `O(e^{-4dx} k)`. -/
theorem twoEnded_seed_transfer {J d : ℕ} {u : ℝ → ℝ}
    (hu : u ∈ rationalSelection l ⊓ twoEndedSources J d) :
    ∃ v : ℝ → ℝ, (∃ C, ∀ x, 0 ≤ x → |v x| ≤ C * thetaCuspLogSeed x) ∧
      (∃ C, ∀ᶠ x in atTop, |v x| ≤ C * Real.exp (-(4 * d * x)) * thetaCuspLogSeed x) ∧
      (∀ x, 0 ≤ x → u x = ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ)) * v (x + Real.log n)) ∧
      ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (∀ x, 0 < thetaCuspFullSource x + ε * u x) ∧
        (∀ x, 0 ≤ x → 0 < thetaCuspLogSeed x + ε * v x) ∧
        (∀ x, 0 ≤ x → thetaCuspFullSource x + ε * u x = ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (thetaCuspLogSeed (x + Real.log n) + ε * v (x + Real.log n))) ∧
        (∀ γ : ℝ, analyticOrderAt (sourceTransform fun x =>
          ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) γ = analyticOrderAt XiC γ) ∧
        (∀ i < J, ∫ x, x ^ (2 * i) * (thetaCuspFullSource x + ε * u x) =
          ∫ x, x ^ (2 * i) * thetaCuspFullSource x) ∧
        (fun x => thetaCuspFullSource x + ε * u x - thetaCuspFullSource x) ∈
          tailOrderSubmodule d := by
  obtain ⟨hsel, hW⟩ := hu
  obtain ⟨N, hN, rfl⟩ := exists_rationalSource_of_mem_rationalSelection hl hnd hr hsel
  have hmem := (rationalSource_mem_twoEndedSources_iff hl hnd hr0 hr N hN J d).1 hW
  obtain ⟨hvC, -, hE⟩ := rationalSeed_spec (l := l) N hN hr
  obtain ⟨-, hmom, hut⟩ := hW
  refine ⟨rationalSeed l N, hvC, ?_, hE, ?_⟩
  · by_cases hN0 : N = 0
    · subst hN0
      refine ⟨0, Eventually.of_forall fun x => ?_⟩
      have h0 : rationalSeed l 0 x = 0 := by simp [rationalSeed, listComb_zero]
      simp [h0]
    · exact exists_exp_bound_of_tendsto (by have := hmem.2.resolve_left hN0; omega)
        (eventually_ge_atTop (0 : ℝ) |>.mono fun x hx => thetaCuspLogSeed_pos hx)
        (tendsto_rationalSeed hN0 hN hr)
  · obtain ⟨ε₀, hε₀, hgen⟩ := rational_seed_transfer hl hnd N hN
    refine ⟨ε₀, hε₀, fun ε hε hεlt => ?_⟩
    obtain ⟨hpos, hseed, hEε, hord, -, hmomε⟩ := hgen ε hε hεlt
    refine ⟨hpos, hseed, hEε, hord, fun i hi => hmomε i (hmom i hi), ?_⟩
    have := (tailOrderSubmodule d).smul_mem ε hut
    refine (congrArg (· ∈ tailOrderSubmodule d) (funext fun x => ?_)).mp this
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end Basis

/-- **Exact dimension (5) for the full bounded source-difference space.**  With finitely many
off-line quartets of first-quadrant multiplicity `M`, `dim W_{J,d} = max(2M + 1 − J − d, 0)`. -/
theorem finrank_twoEndedSources (hfin : xiQuadrantZeros.Finite) (J d : ℕ) :
    Module.finrank ℝ (twoEndedSources J d) = 2 * xiQuadrantMult hfin + 1 - J - d := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  have hnd := nodup_xiOffLine_toList hfin
  obtain ⟨r, hr0, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨hsc, hse, ⟨C, hsC⟩, hsT, -⟩ := rationalBasis_spec hl hnd hr
  have hn : (quadrantListOf hfin.toFinset.toList).length = 2 * xiQuadrantMult hfin :=
    length_xiOffLineList hfin
  have hle : twoEndedSources J d ≤ rationalSelection hfin.toFinset.toList := fun u hu => by
    obtain ⟨c, rfl⟩ := exists_divisorBasisComb_of_mem hfin hsc hsC hsT (mem_twoEndedSources.1 hu).1
    exact ⟨c, rfl⟩
  rw [← inf_eq_right.2 hle, finrank_rationalSelection_inf_twoEndedSources hl hnd hr0 hr, hn]

/-- **Seed transfer on the full space.**  With finitely many off-line quartets, every
`u ∈ W_{J,d}` has the seed-transfer properties of `twoEnded_seed_transfer`. -/
theorem twoEnded_seed_transfer_of_finite (hfin : xiQuadrantZeros.Finite) {J d : ℕ} {u : ℝ → ℝ}
    (hu : u ∈ twoEndedSources J d) :
    ∃ v : ℝ → ℝ, (∃ C, ∀ x, 0 ≤ x → |v x| ≤ C * thetaCuspLogSeed x) ∧
      (∃ C, ∀ᶠ x in atTop, |v x| ≤ C * Real.exp (-(4 * d * x)) * thetaCuspLogSeed x) ∧
      (∀ x, 0 ≤ x → u x = ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ)) * v (x + Real.log n)) ∧
      ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (∀ x, 0 < thetaCuspFullSource x + ε * u x) ∧
        (∀ x, 0 ≤ x → 0 < thetaCuspLogSeed x + ε * v x) ∧
        (∀ x, 0 ≤ x → thetaCuspFullSource x + ε * u x = ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (thetaCuspLogSeed (x + Real.log n) + ε * v (x + Real.log n))) ∧
        (∀ γ : ℝ, analyticOrderAt (sourceTransform fun x =>
          ((thetaCuspFullSource x + ε * u x : ℝ) : ℂ)) γ = analyticOrderAt XiC γ) ∧
        (∀ i < J, ∫ x, x ^ (2 * i) * (thetaCuspFullSource x + ε * u x) =
          ∫ x, x ^ (2 * i) * thetaCuspFullSource x) ∧
        (fun x => thetaCuspFullSource x + ε * u x - thetaCuspFullSource x) ∈
          tailOrderSubmodule d := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  have hnd := nodup_xiOffLine_toList hfin
  obtain ⟨r, hr0, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨hsc, hse, ⟨C, hsC⟩, hsT, -⟩ := rationalBasis_spec hl hnd hr
  obtain ⟨c, rfl⟩ := exists_divisorBasisComb_of_mem hfin hsc hsC hsT (mem_twoEndedSources.1 hu).1
  exact twoEnded_seed_transfer hl hnd hr0 hr ⟨⟨c, rfl⟩, hu⟩

/-- **Infinitely many off-line quartets.**  Every `W_{J,d}` is infinite-dimensional. -/
theorem not_finiteDimensional_twoEndedSources (hinf : xiQuadrantZeros.Infinite) (J d : ℕ) :
    ¬ FiniteDimensional ℝ (twoEndedSources J d) := by
  intro hfd
  obtain ⟨t, ht, htc⟩ := hinf.exists_subset_card_eq
    (Module.finrank ℝ (twoEndedSources J d) + J + d)
  have hl : ∀ α ∈ t.toList, α ∈ xiQuadrantZeros := fun α hα => ht (Finset.mem_toList.1 hα)
  obtain ⟨r, hr0, hr⟩ := prod_neg_sq_quadrantListOf hl
  have hlen : t.card ≤ (quadrantListOf t.toList).length := by
    rw [length_quadrantListOf, Finset.sum_map_toList, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun α hα => by have := one_le_xiZeroMult (ht hα).2.2; omega
  have h := Submodule.finrank_mono (inf_le_right :
    rationalSelection t.toList ⊓ twoEndedSources J d ≤ twoEndedSources J d)
  rw [finrank_rationalSelection_inf_twoEndedSources hl (Finset.nodup_toList t) hr0 hr] at h
  omega

end

end RHTower
