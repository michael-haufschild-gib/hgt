import GaloisForLFunctions.FiniteFreeProbability.AlmostAllJensenRootsAreReal
import GaloisForLFunctions.HTGeometry.BallLogarithm

/-!
# The real roots of `R_d(Ξ)` follow the Cauchy law, unconditionally

Rescale the roots of `R_d(ξ(σ + i·))` by `ℓ_d = ½ log d`, and let `y` run over the rescaled roots.

**Theorem.** For every `w` with `Im w > 0`, with no hypothesis on the zeros:

`(1/d) Σ_{y real} 1/(w − y) → 1/(w + i)`   at `σ = 1/2`.

Since `1/(w + i)` is the Cauchy transform of `dλ/(π(1 + λ²))`, the real roots of `R_d(Ξ)`, which are almost
all the roots, follow the standard Cauchy law at scale `½ log d`. For `σ ≥ 1/2` the same limit holds for
the rescaled roots outside a disc around `iθ` (the discs exhaust the upper half-plane).

Mechanism. On a disc `|z − iθ| < R`, `R < θ`, reflect the roots inside the disc in its boundary and divide by
`(z + i)^d`. The quotient `Q_d` has no zero in the disc, `|Q_d| ≤ e^{o(d)}` by the maximum principle, and
`|Q_d(iθ)| ≥ e^{−o(d)}` by the first-order law. By Borel–Carathéodory, `(1/d) log Q_d → 0` locally uniformly,
so its derivative `(1/d) Σ_y (log-derivative of the reflected factors) − 1/(z + i)` tends to `0`. The reflected
factors are bounded and `o(d)` in number, and so are the non-real roots outside the disc (R38).
-/

open Polynomial Filter Topology Complex Metric
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-! ## The reflected factors -/

theorem blaschkeFactor_ne_zero {c : ℂ} {R : ℝ} (hR : 0 < R) (y : ℂ) {z : ℂ} (hz : z ∈ ball c R) :
    blaschkeFactor c R y z ≠ 0 := by
  rw [mem_ball, dist_eq_norm] at hz
  unfold blaschkeFactor
  split_ifs with h
  · refine div_ne_zero (fun h0 => ?_) (ofReal_ne_zero.2 hR.ne')
    have heq := congrArg norm (sub_eq_zero.1 h0)
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_mul, Complex.norm_conj] at heq
    nlinarith [norm_nonneg (y - c), norm_nonneg (z - c)]
  · intro h0
    rw [sub_eq_zero.1 h0] at hz
    exact h hz

/-- The logarithmic derivative of `blaschkeFactor`. -/
def blaschkeLogDeriv (c : ℂ) (R : ℝ) (y z : ℂ) : ℂ :=
  if ‖y - c‖ < R then -conj (y - c) / ((R : ℂ) ^ 2 - conj (y - c) * (z - c)) else 1 / (z - y)

theorem hasDerivAt_blaschkeFactor {c : ℂ} {R : ℝ} (hR : 0 < R) (y : ℂ) {z : ℂ} (hz : z ∈ ball c R) :
    HasDerivAt (blaschkeFactor c R y) (blaschkeFactor c R y z * blaschkeLogDeriv c R y z) z := by
  have hne := blaschkeFactor_ne_zero hR y hz
  have hR' : (R : ℂ) ≠ 0 := ofReal_ne_zero.2 hR.ne'
  by_cases h : ‖y - c‖ < R
  · have hfun : blaschkeFactor c R y = fun z => ((R : ℂ) ^ 2 - conj (y - c) * (z - c)) / R :=
      funext fun z => if_pos h
    have hval : blaschkeFactor c R y z * blaschkeLogDeriv c R y z = -conj (y - c) / R := by
      have hden : (R : ℂ) ^ 2 - conj (y - c) * (z - c) ≠ 0 := fun h0 => hne (by
        rw [hfun]
        show ((R : ℂ) ^ 2 - conj (y - c) * (z - c)) / R = 0
        rw [h0, zero_div])
      simp only [blaschkeFactor, blaschkeLogDeriv, if_pos h]
      field_simp
    rw [hfun] at hval ⊢
    simp only [blaschkeLogDeriv, if_pos h] at hval
    have hd : HasDerivAt (fun z : ℂ => ((R : ℂ) ^ 2 - conj (y - c) * (z - c)) / R)
        (-conj (y - c) / R) z := by
      have h1 : HasDerivAt (fun z : ℂ => (R : ℂ) ^ 2 - conj (y - c) * (z - c)) (-conj (y - c)) z := by
        simpa using (((hasDerivAt_id z).sub_const c).const_mul (conj (y - c))).const_sub ((R : ℂ) ^ 2)
      exact h1.div_const _
    simp only [blaschkeLogDeriv, if_pos h]
    rw [hval]
    exact hd
  · have hfun : blaschkeFactor c R y = fun z => z - y := funext fun z => if_neg h
    have hzy : z - y ≠ 0 := fun h0 => hne (by rw [hfun]; exact h0)
    rw [hfun]
    simp only [blaschkeLogDeriv, if_neg h]
    rw [mul_one_div_cancel hzy]
    exact (hasDerivAt_id z).sub_const y

/-- `|L_y(w)| ≤ 1/(R − |w − c|)` for all `y`. -/
theorem norm_blaschkeLogDeriv_le {c w : ℂ} {R : ℝ} (hw : ‖w - c‖ < R) (y : ℂ) :
    ‖blaschkeLogDeriv c R y w‖ ≤ 1 / (R - ‖w - c‖) := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hw
  have hδ : 0 < R - ‖w - c‖ := by linarith
  unfold blaschkeLogDeriv
  split_ifs with h
  · set a := ‖y - c‖
    have ha0 : 0 ≤ a := norm_nonneg _
    set ρ := ‖w - c‖
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    have hlow : R ^ 2 - a * ρ ≤ ‖(R : ℂ) ^ 2 - conj (y - c) * (w - c)‖ := by
      have h1 := norm_sub_norm_le ((R : ℂ) ^ 2) (conj (y - c) * (w - c))
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_mul, Complex.norm_conj] at h1
      exact h1
    have hpos : 0 < R ^ 2 - a * ρ := by nlinarith
    rw [norm_div, norm_neg, Complex.norm_conj, div_le_div_iff₀ (lt_of_lt_of_le hpos hlow) hδ, one_mul]
    nlinarith
  · push Not at h
    rw [norm_div, norm_one]
    refine one_div_le_one_div_of_le hδ ?_
    have h1 := norm_sub_norm_le (y - c) (w - c)
    rw [show y - c - (w - c) = y - w by ring, norm_sub_rev y w] at h1
    linarith

theorem hasDerivAt_multiset_prod_blaschke {c : ℂ} {R : ℝ} (hR : 0 < R) (M : Multiset ℂ) {z : ℂ}
    (hz : z ∈ ball c R) :
    HasDerivAt (fun z => (M.map fun y => blaschkeFactor c R y z).prod)
      ((M.map fun y => blaschkeFactor c R y z).prod * (M.map fun y => blaschkeLogDeriv c R y z).sum)
      z := by
  induction M using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const z (1 : ℂ)
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    have h : HasDerivAt (fun z => blaschkeFactor c R a z *
        (M.map fun y => blaschkeFactor c R y z).prod) _ z :=
      (hasDerivAt_blaschkeFactor hR a hz).mul ih
    refine h.congr_deriv ?_
    ring

/-- The reflected product divided by `(z + i)^n`. -/
def blaschkeQuotient (c : ℂ) (R : ℝ) (M : Multiset ℂ) (z : ℂ) : ℂ :=
  (M.map fun y => blaschkeFactor c R y z).prod / (z + I) ^ Multiset.card M

theorem blaschkeQuotient_center_norm {c : ℂ} {R : ℝ} (hR : 0 < R) (M : Multiset ℂ) :
    ‖blaschkeQuotient c R M c‖ =
      (M.map fun y => max R ‖c - y‖).prod / ‖c + I‖ ^ Multiset.card M := by
  rw [blaschkeQuotient, norm_div, norm_pow, norm_multiset_prod_map]
  congr 1
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun y _ => norm_blaschkeFactor_center hR y)

/-- The maximum principle for the reflected quotient. -/
theorem norm_blaschkeQuotient_le {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hne : ∀ z ∈ closedBall c R, z + I ≠ 0) (M : Multiset ℂ)
    (hB : ∀ z ∈ sphere c R, ‖(M.map fun y => z - y).prod‖ ≤ B * ‖z + I‖ ^ Multiset.card M)
    {z : ℂ} (hz : z ∈ closedBall c R) : ‖blaschkeQuotient c R M z‖ ≤ B := by
  have hQd : DiffContOnCl ℂ (blaschkeQuotient c R M) (ball c R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hR.ne']
    refine DifferentiableOn.div (differentiable_multiset_prod_blaschke c R M).differentiableOn
      (by fun_prop) fun z hz => pow_ne_zero _ (hne z hz)
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hQd (fun u hu => ?_)
    (by rwa [closure_ball c hR.ne'])
  rw [frontier_ball c hR.ne'] at hu
  have hpos : 0 < ‖u + I‖ ^ Multiset.card M :=
    pow_pos (norm_pos_iff.2 (hne u (sphere_subset_closedBall hu))) _
  rw [blaschkeQuotient, norm_div, norm_pow, div_le_iff₀ hpos, norm_multiset_prod_map]
  have heq : (M.map fun y => ‖blaschkeFactor c R y u‖) = M.map fun y => ‖u - y‖ :=
    Multiset.map_congr rfl fun y _ => norm_blaschkeFactor_sphere hR y hu
  rw [heq, ← norm_multiset_prod_map]
  exact hB u hu

/-- **The logarithmic derivative is small.** If `|Q| ≤ B` on the disc and `|Q(c)| ≥ m`, then at `w` the
sum of the reflected logarithmic derivatives differs from `|M|/(w + i)` by `O(log(B/m) + 1)`. -/
theorem norm_sum_blaschkeLogDeriv_sub_le {c w : ℂ} {R B m : ℝ} (hR : 0 < R)
    (hne : ∀ z ∈ closedBall c R, z + I ≠ 0) (M : Multiset ℂ)
    (hB : ∀ z ∈ sphere c R, ‖(M.map fun y => z - y).prod‖ ≤ B * ‖z + I‖ ^ Multiset.card M)
    (hm0 : 0 < m) (hm : m ≤ ‖blaschkeQuotient c R M c‖) (hw : ‖w - c‖ < R) (hcard : M ≠ 0) :
    ‖(M.map fun y => blaschkeLogDeriv c R y w).sum - (Multiset.card M : ℂ) / (w + I)‖ ≤
      (2 * (Real.log (B / m) + 1) * ((‖w - c‖ + R) / 2) / (R - (‖w - c‖ + R) / 2)) /
        ((R - ‖w - c‖) / 2) := by
  set n := Multiset.card M
  have hn : 1 ≤ n := Multiset.card_pos.2 hcard
  set ρ := ‖w - c‖
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  set r₁ := (ρ + R) / 2
  have hr₁ : r₁ < R := by simp only [r₁]; linarith
  have hr₁0 : 0 ≤ r₁ := by simp only [r₁]; linarith
  set δ := (R - ρ) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hρr : ρ + δ = r₁ := by simp only [δ, r₁]; ring
  have hsubball : ball c R ⊆ closedBall c R := ball_subset_closedBall
  have hdiff : DifferentiableOn ℂ (blaschkeQuotient c R M) (ball c R) := by
    refine DifferentiableOn.div (differentiable_multiset_prod_blaschke c R M).differentiableOn
      (by fun_prop) fun z hz => pow_ne_zero _ (hne z (hsubball hz))
  have hfne : ∀ z ∈ ball c R, blaschkeQuotient c R M z ≠ 0 := fun z hz => by
    refine div_ne_zero ?_ (pow_ne_zero _ (hne z (hsubball hz)))
    rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
    rintro ⟨y, _, hy⟩
    exact blaschkeFactor_ne_zero hR y hz hy
  have hM : ∀ z ∈ ball c R, ‖blaschkeQuotient c R M z‖ ≤ B := fun z hz =>
    norm_blaschkeQuotient_le hR hne M hB (hsubball hz)
  obtain ⟨g, hgd, _, hgeq, hgb⟩ := exists_bound_log_on_ball hr₁0 hr₁ hdiff hfne hM hm0 hm
  set C := 2 * (Real.log (B / m) + 1) * r₁ / (R - r₁)
  have hwball : w ∈ ball c R := by rwa [mem_ball, dist_eq_norm]
  -- Cauchy's estimate for `g'` at `w`
  have hclosed : closedBall w δ ⊆ ball c R := fun z hz => by
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    have : ‖z - c‖ ≤ ‖z - w‖ + ‖w - c‖ := by
      calc ‖z - c‖ = ‖(z - w) + (w - c)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  have hgcont : DiffContOnCl ℂ g (ball w δ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball w hδ.ne']
    exact hgd.mono hclosed
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hgcont (C := C)
    (fun z hz => hgb z (by
      rw [mem_sphere, dist_eq_norm] at hz
      have : ‖z - c‖ ≤ ‖z - w‖ + ‖w - c‖ := by
        calc ‖z - c‖ = ‖(z - w) + (w - c)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith))
  -- the identification of `g'`
  have hg' : HasDerivAt g (deriv g w) w :=
    (hgd.differentiableAt (isOpen_ball.mem_nhds hwball)).hasDerivAt
  have hexp : HasDerivAt (blaschkeQuotient c R M)
      (blaschkeQuotient c R M c * (Complex.exp (g w) * deriv g w)) w := by
    have h1 := (hg'.cexp).const_mul (blaschkeQuotient c R M c)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hwball] with z hz
    exact hgeq z hz
  have hwI : w + I ≠ 0 := hne w (hsubball hwball)
  set P := (M.map fun y => blaschkeFactor c R y w).prod
  set Λ := (M.map fun y => blaschkeLogDeriv c R y w).sum
  have hexplicit : HasDerivAt (blaschkeQuotient c R M)
      (blaschkeQuotient c R M w * (Λ - (n : ℂ) / (w + I))) w := by
    have hP := hasDerivAt_multiset_prod_blaschke hR M hwball
    have hA : HasDerivAt (fun z : ℂ => (z + I) ^ n) ((n : ℂ) * (w + I) ^ (n - 1) * 1) w :=
      ((hasDerivAt_id w).add_const I).pow n
    have hd : HasDerivAt (fun z => (M.map fun y => blaschkeFactor c R y z).prod / (z + I) ^ n) _ w :=
      hP.div hA (pow_ne_zero _ hwI)
    have hpow : (w + I) ^ n = (w + I) ^ (n - 1) * (w + I) := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    have hA0 : (w + I) ^ (n - 1) ≠ 0 := pow_ne_zero _ hwI
    have hQw' : blaschkeQuotient c R M w = P / (w + I) ^ n := rfl
    refine HasDerivAt.congr_deriv (f := blaschkeQuotient c R M) hd ?_
    rw [hQw', hpow]
    first
      | (field_simp; done)
      | (field_simp; ring)
  have huniq := hexp.unique hexplicit
  have hgw := hgeq w hwball
  have hQw : blaschkeQuotient c R M w ≠ 0 := hfne w hwball
  have hderiv : deriv g w = Λ - (n : ℂ) / (w + I) := by
    rw [← mul_assoc, ← hgw] at huniq
    exact mul_left_cancel₀ hQw huniq
  rw [← hderiv]
  exact hcauchy

/-! ## The exterior transform -/

theorem multiset_sum_filter_split (M : Multiset ℂ) (p : ℂ → Prop) [DecidablePred p] (f : ℂ → ℂ) :
    (M.map f).sum = ((M.filter p).map f).sum + ((M.filter fun y => ¬ p y).map f).sum := by
  conv_lhs => rw [← Multiset.filter_add_not p M]
  rw [Multiset.map_add, Multiset.sum_add]

/-- The rescaled roots outside a disc around `iθ₀` have the limiting Cauchy transform `1/(w + i)` in the
disc. -/
theorem tendsto_exterior_transform {σ : ℝ} (hσ : 1 / 2 ≤ σ) {θ₀ R R₂ : ℝ} (hR : 0 < R) (hRR₂ : R < R₂)
    (hR₂ : R₂ < θ₀) {w : ℂ} (hw : ‖w - I * (θ₀ : ℂ)‖ < R) :
    Tendsto (fun d : ℕ => (1 / (d : ℂ)) *
      (((scaledRoots σ d).filter fun y => R ≤ ‖I * (θ₀ : ℂ) - y‖).map fun y => 1 / (w - y)).sum)
      atTop (𝓝 (1 / (w + I))) := by
  set c := I * (θ₀ : ℂ)
  have hθ₀ : 0 < θ₀ := by linarith
  have hRθ : R < θ₀ := by linarith
  have hC₀ := xiC0_nonneg σ
  have h2C : 0 < 2 + xiC0 σ := by linarith
  have hξ : 0 < ‖xi (σ : ℂ)‖ := norm_pos_iff.2 (xi_ne_zero_of_real σ)
  have h1θ : 0 < 1 + θ₀ := by linarith
  have hne : ∀ z ∈ closedBall c R, z + I ≠ 0 := fun z hz h0 => by
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : z = -I := by linear_combination h0
    rw [h1, show -I - c = -(I * ((1 + θ₀ : ℝ) : ℂ)) by simp only [c]; push_cast; ring, norm_neg,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg h1θ.le] at hz
    linarith
  set ρ := ‖w - c‖
  have hδ : 0 < R - ρ := by linarith
  set r₁ := (ρ + R) / 2
  -- the error `err(d)/d → 0`
  have hlaw := tendsto_log_jensenMass hσ hθ₀
  have hu : Tendsto (fun d : ℕ => (Real.log (2 + xiC0 σ) + jensenError σ d) / d +
      (Real.log (1 + θ₀) - (Real.log (jensenMass (xiMoment σ) d (θ₀ * cauchyScale d)) / d -
        Real.log (cauchyScale d)))) atTop (𝓝 0) := by
    have := (tendsto_jensenError_div σ (Real.log (2 + xiC0 σ))).add
      (hlaw.const_sub (Real.log (1 + θ₀)))
    simpa using this
  have hinv : Tendsto (fun d : ℕ => (1 : ℝ) / d) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  set K : ℝ := 2 * ((ρ + R) / 2) / (R - (ρ + R) / 2) / ((R - ρ) / 2)
  have hKpos : 0 ≤ K := by
    have h1 : 0 < R - (ρ + R) / 2 := by linarith
    have h2 : 0 < (R - ρ) / 2 := by linarith
    have h3 : 0 ≤ ρ := norm_nonneg _
    positivity
  have hbound1 : Tendsto (fun d : ℕ => K * (((Real.log (2 + xiC0 σ) + jensenError σ d) / d +
      (Real.log (1 + θ₀) - (Real.log (jensenMass (xiMoment σ) d (θ₀ * cauchyScale d)) / d -
        Real.log (cauchyScale d)))) + 1 / d)) atTop (𝓝 0) := by
    have := (hu.add hinv).const_mul K
    simpa using this
  have hnear := tendsto_card_near_div hσ (θ₀ := θ₀) hR hRR₂ hR₂
  have hbound2 : Tendsto (fun d : ℕ => (Multiset.card ((scaledRoots σ d).filter
      fun y => ‖c - y‖ ≤ R) : ℝ) / d * (1 / (R - ρ))) atTop (𝓝 0) := by
    simpa using hnear.mul_const (1 / (R - ρ))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (by
    simpa using hbound1.add hbound2)
  filter_upwards [eventually_sphere_bound hσ hR hRθ, eventually_jensenError_nonneg σ hσ,
    tendsto_cauchyScale.eventually_ge_atTop (1 / θ₀), tendsto_cauchyScale.eventually_gt_atTop 0,
    eventually_gt_atTop 0] with d hB hE hℓθ hℓ hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have ht : 1 ≤ θ₀ * cauchyScale d := by
    rw [div_le_iff₀ hθ₀] at hℓθ
    linarith
  have hm := jensenMass_pos hσ d ht
  have hcenter := prod_norm_center (σ := σ) (θ₀ := θ₀) hℓ hm.le
  set M := scaledRoots σ d
  have hcardM : Multiset.card M = d := card_scaledRoots σ d
  have hM0 : M ≠ 0 := fun h => by
    rw [h] at hcardM
    simp at hcardM
    omega
  set m := jensenMass (xiMoment σ) d (θ₀ * cauchyScale d)
  set ℓ := cauchyScale d
  set E := jensenError σ d
  have hℓd : 0 < ℓ ^ d := pow_pos hℓ d
  set B := (2 * Real.exp E + xiC0 σ) / ‖xi (σ : ℂ)‖
  have hBpos : 0 < B := by positivity
  set mlow := m / (‖xi (σ : ℂ)‖ * ℓ ^ d * (1 + θ₀) ^ d)
  have hmlow : 0 < mlow := by positivity
  have hnormc : ‖c + I‖ = 1 + θ₀ := by
    rw [show c + I = I * ((1 + θ₀ : ℝ) : ℂ) by simp only [c]; push_cast; ring, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg h1θ.le]
  have hle : mlow ≤ ‖blaschkeQuotient c R M c‖ := by
    rw [blaschkeQuotient_center_norm hR, hcardM, hnormc]
    have h1 := pow_mul_prod_norm_le M c (r := R) (R := R) hR le_rfl
    rw [div_self hR.ne', one_pow, one_mul] at h1
    have h2 : m / (‖xi (σ : ℂ)‖ * ℓ ^ d) ≤ (M.map fun y => max R ‖c - y‖).prod := by
      rw [← hcenter, mul_div_cancel_left₀ _ (by positivity)]
      exact h1
    simp only [mlow]
    rw [← div_div]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hBq : ∀ z ∈ sphere c R, ‖(M.map fun y => z - y).prod‖ ≤ B * ‖z + I‖ ^ Multiset.card M :=
    fun z hz => by
      rw [hcardM]
      exact hB z hz
  have hmain := norm_sum_blaschkeLogDeriv_sub_le hR hne M hBq hmlow hle hw hM0
  rw [hcardM] at hmain
  -- `log (B / mlow)` is controlled by the error
  have hlogB : Real.log (B / mlow) ≤ Real.log (2 + xiC0 σ) + E + d * Real.log (1 + θ₀) +
      d * Real.log ℓ - Real.log m := by
    have hratio : B / mlow = (2 * Real.exp E + xiC0 σ) * (ℓ ^ d * (1 + θ₀) ^ d) / m := by
      simp only [B, mlow]
      field_simp
    have hle2 : (2 * Real.exp E + xiC0 σ) * (ℓ ^ d * (1 + θ₀) ^ d) / m ≤
        (2 + xiC0 σ) * Real.exp E * (ℓ ^ d * (1 + θ₀) ^ d) / m := by
      gcongr
      exact two_mul_exp_add_le hE hC₀
    rw [hratio]
    refine (Real.log_le_log (by positivity) hle2).trans_eq ?_
    rw [Real.log_div (by positivity) hm.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul h2C.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  -- the splitting
  set p : ℂ → Prop := fun y => R ≤ ‖c - y‖
  have hext : ∀ y ∈ M.filter p, blaschkeLogDeriv c R y w = 1 / (w - y) := fun y hy => by
    have hyR : R ≤ ‖c - y‖ := (Multiset.mem_filter.1 hy).2
    unfold blaschkeLogDeriv
    rw [if_neg (by rw [norm_sub_rev]; exact not_lt.2 hyR)]
  have hsplit := multiset_sum_filter_split M p (fun y => blaschkeLogDeriv c R y w)
  rw [Multiset.map_congr rfl hext] at hsplit
  set Sₑ := ((M.filter p).map fun y => 1 / (w - y)).sum
  set Sᵢ := ((M.filter fun y => ¬ p y).map fun y => blaschkeLogDeriv c R y w).sum
  have hSi : ‖Sᵢ‖ ≤ (Multiset.card (M.filter fun y => ‖c - y‖ ≤ R) : ℝ) * (1 / (R - ρ)) := by
    have h1 := norm_multiset_sum_map_le (M.filter fun y => ¬ p y)
      (fun y => blaschkeLogDeriv c R y w) (B := 1 / (R - ρ))
      (fun y _ => norm_blaschkeLogDeriv_le hw y)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hmono : (M.filter fun y => ¬ p y) ≤ M.filter fun y => ‖c - y‖ ≤ R :=
      Multiset.monotone_filter_right M fun y hy => (not_le.1 hy).le
    exact_mod_cast Multiset.card_le_card hmono
  -- assembling
  have hid : (1 / (d : ℂ)) * Sₑ - 1 / (w + I) =
      (1 / (d : ℂ)) * (((M.map fun y => blaschkeLogDeriv c R y w).sum - (d : ℂ) / (w + I)) - Sᵢ) := by
    rw [hsplit]
    have hwI : w + I ≠ 0 := hne w (ball_subset_closedBall (by rwa [mem_ball, dist_eq_norm]))
    field_simp
    ring
  rw [hid, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hmain' : ‖(M.map fun y => blaschkeLogDeriv c R y w).sum - (d : ℂ) / (w + I)‖ ≤
      K * ((Real.log (2 + xiC0 σ) + E + d * Real.log (1 + θ₀) + d * Real.log ℓ - Real.log m) + 1) := by
    refine hmain.trans ?_
    have hK : 2 * (Real.log (B / mlow) + 1) * ((ρ + R) / 2) / (R - (ρ + R) / 2) / ((R - ρ) / 2) =
        K * (Real.log (B / mlow) + 1) := by
      simp only [K]
      ring
    rw [hK]
    exact mul_le_mul_of_nonneg_left (by linarith) hKpos
  have hnorm := (norm_sub_le _ _).trans (add_le_add hmain' hSi)
  have hdiv := mul_le_mul_of_nonneg_left hnorm (by positivity : (0 : ℝ) ≤ 1 / (d : ℝ))
  refine hdiv.trans_eq ?_
  have hexpand : (1 / (d : ℝ)) * (K * ((Real.log (2 + xiC0 σ) + E + d * Real.log (1 + θ₀) +
      d * Real.log ℓ - Real.log m) + 1)) = K * ((Real.log (2 + xiC0 σ) + E) / d +
        (Real.log (1 + θ₀) - (Real.log m / d - Real.log ℓ)) + 1 / d) := by
    field_simp
    ring
  rw [mul_add, hexpand]
  ring

/-! ## The real roots at `σ = 1/2` -/

/-- **The Cauchy law of the real roots, unconditional.** For `Im w > 0`,
`(1/d) Σ_{y real} 1/(w − y) → 1/(w + i)`, over the real rescaled roots `y` of `R_d(Ξ)`. -/
theorem tendsto_real_jensenCauchy {w : ℂ} (hw : 0 < w.im) :
    Tendsto (fun d : ℕ => (1 / (d : ℂ)) *
      (((scaledRoots (1 / 2) d).filter fun y => y.im = 0).map fun y => 1 / (w - y)).sum)
      atTop (𝓝 (1 / (w + I))) := by
  -- a disc around `iθ₀` containing `w`
  set θ₀ := ‖w‖ ^ 2 / w.im + w.im + 1
  have hq : 0 ≤ ‖w‖ ^ 2 / w.im := by positivity
  have hθw : w.im < θ₀ := by simp only [θ₀]; linarith
  have hθ₀ : 0 < θ₀ := by linarith
  have hθA : ‖w‖ ^ 2 ≤ θ₀ * w.im := by
    have e : θ₀ * w.im = ‖w‖ ^ 2 + w.im ^ 2 + w.im := by
      simp only [θ₀]
      field_simp
    rw [e]
    nlinarith
  have hrad : 0 < θ₀ ^ 2 - w.im * θ₀ := by nlinarith
  set ρ₀ := Real.sqrt (θ₀ ^ 2 - w.im * θ₀)
  have hρ₀ : 0 < ρ₀ := Real.sqrt_pos.2 hrad
  have hρθ : ρ₀ < θ₀ := (Real.sqrt_lt' hθ₀).2 (by nlinarith)
  set R := (ρ₀ + θ₀) / 2
  have hρR : ρ₀ < R := by simp only [R]; linarith
  have hRθ : R < θ₀ := by simp only [R]; linarith
  set R₂ := (R + θ₀) / 2
  have hRR₂ : R < R₂ := by simp only [R₂]; linarith
  have hR₂θ : R₂ < θ₀ := by simp only [R₂]; linarith
  have hR : 0 < R := by linarith
  have hwc : ‖w - I * (θ₀ : ℂ)‖ < R := by
    have hsq1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hsq2 : ‖w - I * (θ₀ : ℂ)‖ ^ 2 = w.re ^ 2 + (w.im - θ₀) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [sub_re, sub_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul,
        zero_add, sub_zero, mul_zero]
      ring
    have hle : ‖w - I * (θ₀ : ℂ)‖ ^ 2 ≤ θ₀ ^ 2 - w.im * θ₀ := by
      rw [hsq2]
      nlinarith
    exact lt_of_le_of_lt ((le_abs_self _).trans (Real.abs_le_sqrt hle)) hρR
  have hext := tendsto_exterior_transform (σ := 1 / 2) le_rfl hR hRR₂ hR₂θ hwc
  -- the non-real roots
  have hnon := tendsto_card_nonreal_roots_div
  have hδ : 0 < R - ‖w - I * (θ₀ : ℂ)‖ := by linarith
  have hsmall := hnon.mul_const (1 / (R - ‖w - I * (θ₀ : ℂ)‖))
  rw [zero_mul] at hsmall
  have hlim := (tendsto_iff_norm_sub_tendsto_zero.1 hext).add hsmall
  rw [add_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [tendsto_cauchyScale.eventually_gt_atTop 0, eventually_gt_atTop 0] with d hℓ hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  set c := I * (θ₀ : ℂ)
  set M := scaledRoots (1 / 2) d
  set p : ℂ → Prop := fun y => R ≤ ‖c - y‖
  have hrealext : (M.filter fun y => y.im = 0) = ((M.filter p).filter fun y => y.im = 0) := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr fun y _ => ?_
    constructor
    · intro hy
      refine ⟨hy, ?_⟩
      have him : (c - y).im = θ₀ := by
        simp [c, hy]
      have h1 := Complex.abs_im_le_norm (c - y)
      rw [him, abs_of_pos hθ₀] at h1
      show R ≤ ‖c - y‖
      linarith
    · exact fun h => h.1
  have hsplit := multiset_sum_filter_split (M.filter p) (fun y => y.im = 0) (fun y => 1 / (w - y))
  rw [← hrealext] at hsplit
  set Sᵣ := ((M.filter fun y => y.im = 0).map fun y => 1 / (w - y)).sum
  set Sₙ := (((M.filter p).filter fun y => ¬ y.im = 0).map fun y => 1 / (w - y)).sum
  set Sₑ := ((M.filter p).map fun y => 1 / (w - y)).sum
  have hkernel : ∀ y ∈ (M.filter p).filter (fun y => ¬ y.im = 0),
      ‖1 / (w - y)‖ ≤ 1 / (R - ‖w - c‖) := fun y hy => by
    have hyR : R ≤ ‖c - y‖ := (Multiset.mem_filter.1 (Multiset.mem_filter.1 hy).1).2
    rw [norm_div, norm_one]
    refine one_div_le_one_div_of_le hδ ?_
    have h1 := norm_sub_norm_le (c - y) (c - w)
    rw [show c - y - (c - w) = w - y by ring, norm_sub_rev c w] at h1
    linarith
  have hSn := norm_multiset_sum_map_le _ _ hkernel
  -- non-real rescaled roots are non-real roots
  have hcardn : (Multiset.card ((M.filter p).filter fun y => ¬ y.im = 0) : ℝ) ≤
      (Multiset.card ((jensenRev d xiSeries).roots.filter fun x => x.im ≠ 0) : ℝ) := by
    have h1 : (M.filter p).filter (fun y => ¬ y.im = 0) ≤ M.filter fun y => ¬ y.im = 0 :=
      Multiset.monotone_filter_left _ (Multiset.filter_le _ _)
    have h2 : Multiset.card (M.filter fun y => ¬ y.im = 0) =
        Multiset.card ((jensenRev d xiSeries).roots.filter fun x => x.im ≠ 0) := by
      simp only [M, scaledRoots, xiJensen, mk_xiShiftCoeff_half]
      rw [Multiset.filter_map, Multiset.card_map]
      congr 1
      refine Multiset.filter_congr fun x _ => ?_
      simp only [Function.comp_apply, Complex.div_ofReal_im, div_eq_zero_iff, hℓ.ne', or_false]
    exact_mod_cast h2 ▸ Multiset.card_le_card h1
  have hid : (1 / (d : ℂ)) * Sᵣ - 1 / (w + I) = ((1 / (d : ℂ)) * Sₑ - 1 / (w + I)) -
      (1 / (d : ℂ)) * Sₙ := by
    rw [hsplit]
    ring
  rw [hid]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  have hbound : ‖Sₙ‖ ≤ (Multiset.card ((jensenRev d xiSeries).roots.filter fun x => x.im ≠ 0) : ℝ) *
      (1 / (R - ‖w - c‖)) :=
    hSn.trans (mul_le_mul_of_nonneg_right hcardn (by positivity))
  have hn : ‖(1 / (d : ℂ)) * Sₙ‖ = ‖Sₙ‖ / d := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    ring
  rw [hn]
  calc ‖Sₙ‖ / d ≤ _ := div_le_div_of_nonneg_right hbound hdR.le
    _ = _ := by ring

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.tendsto_exterior_transform
#print axioms FiniteFreeProbability.tendsto_real_jensenCauchy
