import GaloisForLFunctions.RHTower.ThetaEndpointDefectIndex

/-!
# Sharp moment and tail filtrations of divisor-keeping theta sources

Let `k` be the theta cusp source and `F = XiC` its transform.  `W` is the real space of even
continuous sources `u` with `|u| ≤ C_u k` whose transforms keep every real zero of `F` with its
multiplicity; `W_N ⊆ W` imposes vanishing of the even moments of orders `0, 2, …, 2N`, and the tail
space inside `W_N` imposes `u / k → 0` at infinity.

* Even moments are the even Taylor coefficients of the transform at the origin, so vanishing of the
  first `N + 1` even moments is a zero of order `2N + 2` there.
* For a finite off-line configuration of first-quadrant multiplicity `M`, the partial-fraction
  sources `s_j` with `ŝ_j P = F z^{2j}`, `0 ≤ j ≤ 2M`, form a basis of `W`; hence
  `dim W = 2M + 1`, `dim W_N = max(2M − N, 0)` and the tail space has dimension
  `max(2M − N − 1, 0)`, the top coordinate being `lim u/k` divided by `∏(−β²)`.
* For infinitely many off-line quartets every `W_N` and every tail space is infinite-dimensional.
-/
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Even moments as Taylor coefficients -/

theorem thetaCosJet_zero_two_mul (i : ℕ) (x : ℝ) :
    thetaCosJet 0 (2 * i) x = (-1) ^ i * x ^ (2 * i) := by
  unfold thetaCosJet
  rw [pow_mul, show (-(I * (x : ℂ))) ^ 2 = -((x : ℂ) ^ 2) by ring_nf; rw [Complex.I_sq]; ring]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
  rw [neg_pow, show ((x : ℂ) ^ 2) ^ i = ((x ^ (2 * i) : ℝ) : ℂ) by push_cast; ring]
  rw [show ((-1 : ℂ)) ^ i = (((-1 : ℝ) ^ i : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- The even moments of a real even source are, up to sign, the even derivatives of its transform
at the origin. -/
theorem iteratedDeriv_two_mul_zero_ofReal {v : ℝ → ℝ} (hv : AEStronglyMeasurable v) {C : ℝ}
    (hC : ∀ x, |v x| ≤ C * thetaCuspFullSource x) (heven : ∀ x, v (-x) = v x) (i : ℕ) :
    iteratedDeriv (2 * i) (sourceTransform fun x => (v x : ℂ)) 0 =
      (((-1) ^ i * ∫ x, x ^ (2 * i) * v x : ℝ) : ℂ) := by
  have h := iteratedDeriv_sourceTransform_ofReal hv hC heven 0 (2 * i)
  rw [Complex.ofReal_zero] at h
  rw [h]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [thetaCosJet_zero_two_mul]
  ring

theorem iteratedDeriv_odd_zero_of_even {H : ℂ → ℂ} (heven : ∀ z, H (-z) = H z) (i : ℕ) :
    iteratedDeriv (2 * i + 1) H 0 = 0 := by
  have hfun : H = fun w => H (-w) := funext fun w => (heven w).symm
  have key := congrArg (fun f => iteratedDeriv (2 * i + 1) f 0) hfun
  rw [iteratedDeriv_comp_neg, neg_zero, smul_eq_mul, pow_succ, pow_mul, neg_one_sq, one_pow,
    one_mul] at key
  have : (2 : ℂ) * iteratedDeriv (2 * i + 1) H 0 = 0 := by linear_combination key
  simpa using this

/-- **Vanishing even moments are a zero of the transform at the origin.** -/
theorem moments_eq_zero_iff_order {v : ℝ → ℝ} (hv : AEStronglyMeasurable v) {C : ℝ}
    (hC : ∀ x, |v x| ≤ C * thetaCuspFullSource x) (heven : ∀ x, v (-x) = v x) (N : ℕ) :
    (∀ i ≤ N, ∫ x, x ^ (2 * i) * v x = 0) ↔
      ((2 * N + 2 : ℕ) : ℕ∞) ≤ analyticOrderAt (sourceTransform fun x => (v x : ℂ)) 0 := by
  have hms : MeasurableMomentSource fun x => (v x : ℂ) :=
    measurableMomentSource_of_le (Complex.continuous_ofReal.comp_aestronglyMeasurable hv)
      fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC x
  have hHeven : ∀ z, sourceTransform (fun x => (v x : ℂ)) (-z) =
      sourceTransform (fun x => (v x : ℂ)) z :=
    sourceTransform_neg_eq_of_even fun x => by simp only [heven]
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hms.differentiable_sourceTransform.analyticAt 0)]
  constructor
  · intro h i hi
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [iteratedDeriv_two_mul_zero_ofReal hv hC heven, h k (by omega)]
      simp
    · exact iteratedDeriv_odd_zero_of_even hHeven k
  · intro h i hi
    have := h (2 * i) (by omega)
    rw [iteratedDeriv_two_mul_zero_ofReal hv hC heven] at this
    have h2 : (-1 : ℝ) ^ i * ∫ x, x ^ (2 * i) * v x = 0 := by exact_mod_cast this
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ (by norm_num))

/-- Orders of even polynomials at the origin. -/
theorem natCast_le_analyticOrderAt_evenPoly_iff (c : ℕ → ℂ) (n m : ℕ) :
    (m : ℕ∞) ≤ analyticOrderAt (fun z => ∑ j ∈ Finset.range n, c j * z ^ (2 * j)) 0 ↔
      ∀ j < n, 2 * j < m → c j = 0 := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (by fun_prop)]
  have hder : ∀ i, iteratedDeriv i (fun z => ∑ j ∈ Finset.range n, c j * z ^ (2 * j)) 0 =
      ∑ j ∈ Finset.range n, c j * ((if i = 2 * j then (2 * j).factorial else 0 : ℕ) : ℂ) := by
    intro i
    rw [iteratedDeriv_fun_sum fun j _ => by fun_prop]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  simp only [hder]
  constructor
  · intro h j hj hjm
    have := h (2 * j) hjm
    rw [Finset.sum_eq_single j (fun b _ hb => by rw [if_neg (by omega)]; simp)
      (fun h' => absurd (Finset.mem_range.2 hj) h'), if_pos rfl] at this
    exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast (Nat.factorial_pos _).ne')
  · intro h i hi
    refine Finset.sum_eq_zero fun j hj => ?_
    split_ifs with h'
    · rw [h j (Finset.mem_range.1 hj) (by omega), zero_mul]
    · simp

/-! ## Basis sources -/

/-- The tail constant `∏_{β ∈ L} (-β²)` of a quadrant list is a positive real number. -/
theorem prod_neg_sq_quadrantListOf {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) :
    ∃ r : ℝ, 0 < r ∧ ((quadrantListOf l).map fun β : ℂ => -β ^ 2).prod = (r : ℂ) := by
  induction l with
  | nil => exact ⟨1, one_pos, by simp [quadrantListOf]⟩
  | cons α l ih =>
    obtain ⟨r, hr, hrl⟩ := ih fun a ha => hl a (List.mem_cons_of_mem _ ha)
    have hα := hl α List.mem_cons_self
    have hα0 : α ≠ 0 := fun h => by rw [h] at hα; simp [xiQuadrantZeros] at hα
    refine ⟨((Complex.normSq α ^ 2) ^ xiZeroMult α * r : ℝ),
      mul_pos (pow_pos (pow_pos (Complex.normSq_pos.2 hα0) 2) _) hr, ?_⟩
    rw [quadrantListOf, List.map_append, List.map_append, List.prod_append, List.prod_append, hrl,
      List.map_replicate, List.map_replicate, List.prod_replicate, List.prod_replicate, ← mul_pow]
    have : (-α ^ 2) * (-(starRingEnd ℂ) α ^ 2) = ((Complex.normSq α : ℝ) : ℂ) ^ 2 := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    rw [this]
    push_cast
    ring


/-- **Basis sources.**  For a duplicate-free list `l` of first-quadrant zeros there are real even
continuous `k`-dominated sources `s_j`, `j ≤ |L|`, with `ŝ_j P_L = F z^{2j}`, `s_j = o(k)` for
`j < |L|` and `s_{|L|} - Π k = o(k)`, where `Π = ∏_{β ∈ L} (-β²) > 0`. -/
theorem exists_basis_sources {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) (hnd : l.Nodup)
    {r : ℝ} (hr : ((quadrantListOf l).map fun β : ℂ => -β ^ 2).prod = (r : ℂ)) :
    ∃ s : Fin ((quadrantListOf l).length + 1) → ℝ → ℝ, (∀ j, Continuous (s j)) ∧
      (∀ j x, s j (-x) = s j x) ∧ (∃ C, ∀ j x, |s j x| ≤ C * thetaCuspFullSource x) ∧
      (∀ j z, sourceTransform (fun x => (s j x : ℂ)) z * listDivisor (quadrantListOf l) z =
        XiC z * z ^ (2 * (j : ℕ))) ∧
      ∀ j, Tendsto (fun x => |s j x - (if (j : ℕ) = (quadrantListOf l).length then r else 0) *
        thetaCuspFullSource x| / thetaCuspFullSource x) (cocompact ℝ) (𝓝 0) := by
  have hL := thetaDivisionList_quadrantListOf hl hnd
  have h : ∀ j : Fin ((quadrantListOf l).length + 1), ∃ u : ℝ → ℂ, ExpMomentSource u ∧
      (∀ x, u (-x) = u x) ∧ (∃ C, ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x) ∧
      (∀ z, sourceTransform u z * listDivisor (quadrantListOf l) z =
        XiC z * (Polynomial.X ^ (j : ℕ) : Polynomial ℂ).eval (z ^ 2)) ∧
      Tendsto (fun x => ‖u x - (Polynomial.X ^ (j : ℕ) : Polynomial ℂ).coeff
        (quadrantListOf l).length * ((quadrantListOf l).map fun β => -β ^ 2).prod *
          thetaSourceC x‖ / thetaCuspFullSource x) (cocompact ℝ) (𝓝 0) := fun j =>
    exists_source_mul_listDivisor hL _ (by rw [Polynomial.natDegree_X_pow]; omega)
  choose u hum hue huC huT hut using h
  choose Cu hCu using huC
  refine ⟨fun j x => (u j x).re, fun j => Complex.continuous_re.comp (hum j).continuous,
    fun j x => by simp only [hue], ⟨∑ j, max (Cu j) 0, fun j x => ?_⟩, fun j z => ?_,
    fun j => ?_⟩
  · calc |(u j x).re| ≤ ‖u j x‖ := Complex.abs_re_le_norm _
      _ ≤ Cu j * thetaCuspFullSource x := hCu j x
      _ ≤ max (Cu j) 0 * thetaCuspFullSource x :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (thetaCuspFullSource_pos x).le
      _ ≤ (∑ i, max (Cu i) 0) * thetaCuspFullSource x :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => le_max_right (Cu i) 0)
            (Finset.mem_univ j)) (thetaCuspFullSource_pos x).le
  · rw [sourceTransform_ofReal_re (hum j) (hue j)]
    have h1 := huT j z
    have h2 := congrArg (starRingEnd ℂ) (huT j ((starRingEnd ℂ) z))
    simp only [Polynomial.eval_pow, Polynomial.eval_X, map_mul, map_pow, XiC_conj,
      Complex.conj_conj, listDivisor_quadrantListOf_conj] at h1 h2
    rw [div_mul_eq_mul_div, add_mul, h1, h2, ← pow_mul, mul_comm 2]
    ring
  · refine squeeze_zero (fun x => div_nonneg (abs_nonneg _) (thetaCuspFullSource_pos x).le)
      (fun x => ?_) (hut j)
    refine div_le_div_of_nonneg_right ?_ (thetaCuspFullSource_pos x).le
    rw [Polynomial.coeff_X_pow, hr]
    have hre : (u j x).re - (if (j : ℕ) = (quadrantListOf l).length then r else 0) *
        thetaCuspFullSource x = (u j x - (if (quadrantListOf l).length = (j : ℕ) then (1 : ℂ)
          else 0) * (r : ℂ) * thetaSourceC x).re := by
      split_ifs with h1 h2 h2
      · simp [thetaSourceC]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp [thetaSourceC]
    rw [hre]
    exact Complex.abs_re_le_norm _

/-- Independence of sources with distinct monomial transforms. -/
theorem sources_independent_of_pow {l : List ℂ} {n : ℕ} {v : Fin n → ℝ → ℝ}
    (hvc : ∀ i, Continuous (v i)) {C : ℝ} (hvC : ∀ i x, |v i x| ≤ C * thetaCuspFullSource x)
    (d : Fin n → ℕ) (hd : Function.Injective d)
    (hvT : ∀ i z, sourceTransform (fun x => (v i x : ℂ)) z * listDivisor (quadrantListOf l) z =
      XiC z * z ^ d i)
    (c : Fin n → ℝ) (h : ∀ x, ∑ i, c i * v i x = 0) : c = 0 := by
  have hT : ∀ z, ∑ i, (c i : ℂ) * sourceTransform (fun x => (v i x : ℂ)) z = 0 := by
    intro z
    rw [← sourceTransform_finset_sum_ofReal Finset.univ (fun i _ => (hvc i).aestronglyMeasurable)
      (fun i _ => hvC i) c z]
    simp only [h, Complex.ofReal_zero]
    unfold sourceTransform
    simp
  set q : Polynomial ℂ := ∑ i : Fin n, Polynomial.C (c i : ℂ) * Polynomial.X ^ d i
  have hq : q = 0 := by
    refine Polynomial.eq_of_infinite_eval_eq q 0 ?_
    refine ((Set.Icc_infinite (zero_lt_one' ℝ)).image Complex.ofReal_injective.injOn).mono ?_
    rintro _ ⟨t, ht, rfl⟩
    have hz : ‖(t : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg ht.1]; exact ht.2
    simp only [mem_setOf_eq, Polynomial.eval_zero, q, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have h2 : (∑ i, (c i : ℂ) * sourceTransform (fun x => (v i x : ℂ)) t) *
        listDivisor (quadrantListOf l) t = XiC t * ∑ i, (c i : ℂ) * (t : ℂ) ^ d i := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, hvT i t]; ring
    rw [hT t, zero_mul] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (XiC_ne_zero_of_norm_le_one hz)
  funext i
  have := congrArg (fun p : Polynomial ℂ => p.coeff (d i)) hq
  simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i (fun b _ hb => if_neg (fun h' => hb (hd h'.symm)))
    (fun h' => absurd (Finset.mem_univ i) h'), if_pos rfl] at this
  exact_mod_cast this

/-- A continuous `k`-dominated real source whose transform vanishes on the closed unit disc is zero. -/
theorem eq_zero_of_sourceTransform_eq_zero_on_disc {D : ℝ → ℝ} (hDc : Continuous D) {C : ℝ}
    (hDC : ∀ x, |D x| ≤ C * thetaCuspFullSource x)
    (h : ∀ z : ℂ, ‖z‖ ≤ 1 → sourceTransform (fun x => (D x : ℂ)) z = 0) : ∀ x, D x = 0 := by
  have hDms : MeasurableMomentSource fun x => (D x : ℂ) :=
    measurableMomentSource_of_le (Complex.continuous_ofReal.comp hDc).aestronglyMeasurable
      fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hDC x
  have hall : ∀ z, sourceTransform (fun x => (D x : ℂ)) z = 0 := by
    have hA : AnalyticOnNhd ℂ (sourceTransform fun x => (D x : ℂ)) univ :=
      fun z _ => hDms.differentiable_sourceTransform.analyticAt z
    have hev : (sourceTransform fun x => (D x : ℂ)) =ᶠ[𝓝 0] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
      exact h z (by rw [Metric.mem_ball, dist_zero_right] at hz; exact hz.le)
    intro z
    exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 0) hev
      (mem_univ z)
  have hD0 := ae_eq_zero_of_sourceTransform_eq_zero ((hDms.moment 0).mono'
    hDms.aestronglyMeasurable (Eventually.of_forall fun x => by simp)) hall
  have hc : (fun x => (D x : ℂ)) = 0 :=
    ((Complex.continuous_ofReal.comp hDc).ae_eq_iff_eq volume continuous_const).1 hD0
  intro x
  have := congrFun hc x
  simpa using this

/-! ## The space of divisor-keeping sources and its moment filtration -/

theorem expMomentSource_ofReal_of_le {u : ℝ → ℝ} (hu : Continuous u) {C : ℝ}
    (hC : ∀ x, |u x| ≤ C * thetaCuspFullSource x) : ExpMomentSource fun x => (u x : ℂ) := by
  refine ⟨Complex.continuous_ofReal.comp hu, fun c => ?_⟩
  refine ((expMomentSource_thetaSourceC.moment c).const_mul C).mono'
    ((by fun_prop : Continuous fun x : ℝ => Real.exp (c * |x|)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp hu).aestronglyMeasurable.norm)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), Complex.norm_real, Real.norm_eq_abs, thetaSourceC,
    Complex.norm_real, Real.norm_of_nonneg (thetaCuspFullSource_pos x).le]
  calc Real.exp (c * |x|) * |u x| ≤ Real.exp (c * |x|) * (C * thetaCuspFullSource x) :=
        mul_le_mul_of_nonneg_left (hC x) (Real.exp_pos _).le
    _ = C * (Real.exp (c * |x|) * thetaCuspFullSource x) := by ring

theorem integrable_pow_mul_of_le {u : ℝ → ℝ} (hu : Continuous u) {C : ℝ}
    (hC : ∀ x, |u x| ≤ C * thetaCuspFullSource x) (n : ℕ) : Integrable fun x => x ^ n * u x := by
  have hm := expMomentSource_ofReal_of_le hu hC
  refine ((hm.moment 1).const_mul (n.factorial : ℝ)).mono' (by fun_prop)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, Complex.norm_real, Real.norm_eq_abs, one_mul]
  calc |x| ^ n * |u x| ≤ (n.factorial * Real.exp |x|) * |u x| :=
        mul_le_mul_of_nonneg_right (abs_pow_le_factorial_mul_exp x n) (abs_nonneg _)
    _ = n.factorial * (Real.exp |x| * |u x|) := by ring

/-- The real even continuous `k`-dominated sources whose transforms keep every real zero of `F`. -/
def thetaKeepingSources : Submodule ℝ (ℝ → ℝ) where
  carrier := {u | Continuous u ∧ (∀ x, u (-x) = u x) ∧
    (∃ C, ∀ x, |u x| ≤ C * thetaCuspFullSource x) ∧
    KeepsRealZeros (sourceTransform fun x => (u x : ℂ))}
  add_mem' := by
    rintro u v ⟨huc, hue, ⟨Cu, hCu⟩, huk⟩ ⟨hvc, hve, ⟨Cv, hCv⟩, hvk⟩
    refine ⟨huc.add hvc, fun x => by simp only [Pi.add_apply, hue, hve],
      ⟨Cu + Cv, fun x => ?_⟩, fun γ => ?_⟩
    · simp only [Pi.add_apply]
      calc |u x + v x| ≤ |u x| + |v x| := abs_add_le _ _
        _ ≤ Cu * thetaCuspFullSource x + Cv * thetaCuspFullSource x := add_le_add (hCu x) (hCv x)
        _ = (Cu + Cv) * thetaCuspFullSource x := by ring
    · have hsum : (sourceTransform fun x => ((u + v) x : ℂ)) =
          (sourceTransform fun x => (u x : ℂ)) + sourceTransform fun x => (v x : ℂ) :=
        funext fun z => by
          have := sourceTransform_add (expMomentSource_ofReal_of_le huc hCu)
            (expMomentSource_ofReal_of_le hvc hCv) z
          simpa [Pi.add_apply, Complex.ofReal_add] using this
      rw [hsum]
      exact (le_min (huk γ) (hvk γ)).trans le_analyticOrderAt_add
  zero_mem' := by
    refine ⟨continuous_const, fun x => rfl, ⟨0, fun x => by simp⟩, fun γ => ?_⟩
    have h0 : (sourceTransform fun x => ((0 : ℝ → ℝ) x : ℂ)) = fun _ => 0 := funext fun z => by
      simp [sourceTransform]
    rw [h0, analyticOrderAt_eq_top.2 (Eventually.of_forall fun _ => rfl)]
    exact le_top
  smul_mem' := by
    rintro c u ⟨huc, hue, ⟨Cu, hCu⟩, huk⟩
    refine ⟨continuous_const.mul huc, fun x => by simp only [Pi.smul_apply, smul_eq_mul, hue],
      ⟨|c| * Cu, fun x => ?_⟩, fun γ => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hCu x) (abs_nonneg _)
    · have hsm : (sourceTransform fun x => ((c • u) x : ℂ)) =
          (fun _ => (c : ℂ)) * sourceTransform fun x => (u x : ℂ) := funext fun z => by
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Pi.mul_apply]
        exact sourceTransform_const_mul _ _ z
      rw [hsm]
      rcases eq_or_ne c 0 with rfl | hc
      · have h0 : ((fun _ => ((0 : ℝ) : ℂ)) * sourceTransform fun x => (u x : ℂ)) = fun _ => 0 :=
          funext fun z => by simp
        rw [h0, analyticOrderAt_eq_top.2 (Eventually.of_forall fun _ => rfl)]
        exact le_top
      · rw [analyticOrderAt_mul analyticAt_const
          ((expMomentSource_ofReal_of_le huc hCu).differentiable_sourceTransform.analyticAt _),
          analyticAt_const.analyticOrderAt_eq_zero.2 (by exact_mod_cast hc), zero_add]
        exact huk γ

theorem mem_thetaKeepingSources {u : ℝ → ℝ} : u ∈ thetaKeepingSources ↔
    Continuous u ∧ (∀ x, u (-x) = u x) ∧ (∃ C, ∀ x, |u x| ≤ C * thetaCuspFullSource x) ∧
      KeepsRealZeros (sourceTransform fun x => (u x : ℂ)) := Iff.rfl

/-- `W_N`: divisor-keeping sources whose even moments of orders `0, 2, …, 2N` vanish. -/
def thetaKeepingMomentSources (N : ℕ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {u | u ∈ thetaKeepingSources ∧ ∀ i ≤ N, ∫ x, x ^ (2 * i) * u x = 0}
  add_mem' := by
    rintro u v ⟨hu, hum⟩ ⟨hv, hvm⟩
    refine ⟨thetaKeepingSources.add_mem hu hv, fun i hi => ?_⟩
    obtain ⟨huc, -, ⟨Cu, hCu⟩, -⟩ := hu
    obtain ⟨hvc, -, ⟨Cv, hCv⟩, -⟩ := hv
    simp only [Pi.add_apply, mul_add]
    rw [integral_add (integrable_pow_mul_of_le huc hCu _) (integrable_pow_mul_of_le hvc hCv _),
      hum i hi, hvm i hi, add_zero]
  zero_mem' := ⟨thetaKeepingSources.zero_mem, fun i _ => by simp⟩
  smul_mem' := by
    rintro c u ⟨hu, hum⟩
    refine ⟨thetaKeepingSources.smul_mem c hu, fun i hi => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    rw [integral_const_mul, hum i hi, mul_zero]

/-- The tail-normalized subspace: sources in `W_N` with `u/k → 0` at both ends. -/
def thetaKeepingTailSources (N : ℕ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {u | u ∈ thetaKeepingMomentSources N ∧
    Tendsto (fun x => u x / thetaCuspFullSource x) (cocompact ℝ) (𝓝 0)}
  add_mem' := by
    rintro u v ⟨hu, hut⟩ ⟨hv, hvt⟩
    refine ⟨(thetaKeepingMomentSources N).add_mem hu hv, ?_⟩
    simpa [Pi.add_apply, add_div] using hut.add hvt
  zero_mem' := ⟨(thetaKeepingMomentSources N).zero_mem, by
    simp only [Pi.zero_apply, zero_div]; exact tendsto_const_nhds⟩
  smul_mem' := by
    rintro c u ⟨hu, hut⟩
    refine ⟨(thetaKeepingMomentSources N).smul_mem c hu, ?_⟩
    simpa [Pi.smul_apply, smul_eq_mul, mul_div_assoc] using hut.const_mul c

theorem mem_thetaKeepingMomentSources {N : ℕ} {u : ℝ → ℝ} : u ∈ thetaKeepingMomentSources N ↔
    u ∈ thetaKeepingSources ∧ ∀ i ≤ N, ∫ x, x ^ (2 * i) * u x = 0 := Iff.rfl

theorem mem_thetaKeepingTailSources {N : ℕ} {u : ℝ → ℝ} : u ∈ thetaKeepingTailSources N ↔
    u ∈ thetaKeepingMomentSources N ∧
      Tendsto (fun x => u x / thetaCuspFullSource x) (cocompact ℝ) (𝓝 0) := Iff.rfl

/-! ## Coordinates of divisor-keeping sources -/

section Coordinates

variable {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) {r : ℝ}
  {s : Fin ((quadrantListOf l).length + 1) → ℝ → ℝ} (hsc : ∀ j, Continuous (s j))
  (hse : ∀ j x, s j (-x) = s j x) {C : ℝ} (hsC : ∀ j x, |s j x| ≤ C * thetaCuspFullSource x)
  (hsT : ∀ j z, sourceTransform (fun x => (s j x : ℂ)) z * listDivisor (quadrantListOf l) z =
    XiC z * z ^ (2 * (j : ℕ)))

/-- The basis extended by zero to all indices. -/
def divisorBasis (s : Fin ((quadrantListOf l).length + 1) → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  if h : j < (quadrantListOf l).length + 1 then s ⟨j, h⟩ else 0

include hsc in
theorem continuous_divisorBasis (j : ℕ) : Continuous (divisorBasis s j) := by
  unfold divisorBasis; split_ifs
  · exact hsc _
  · exact continuous_const

include hsC in
theorem abs_divisorBasis_le (j : ℕ) (x : ℝ) : |divisorBasis s j x| ≤ max C 0 * thetaCuspFullSource x := by
  unfold divisorBasis; split_ifs
  · exact (hsC _ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (thetaCuspFullSource_pos x).le)
  · simp only [Pi.zero_apply, abs_zero]
    exact mul_nonneg (le_max_right _ _) (thetaCuspFullSource_pos x).le

include hsT in
theorem sourceTransform_divisorBasis_mul {j : ℕ} (hj : j < (quadrantListOf l).length + 1) (z : ℂ) :
    sourceTransform (fun x => (divisorBasis s j x : ℂ)) z * listDivisor (quadrantListOf l) z =
      XiC z * z ^ (2 * j) := by
  unfold divisorBasis
  rw [dif_pos hj]
  exact hsT ⟨j, hj⟩ z

include hsc hsC hsT in
/-- Transform of a basis combination: `(Σ c_j s_j)^ P = F Σ c_j z^{2j}`. -/
theorem sourceTransform_sum_divisorBasis_mul (c : ℕ → ℝ) (z : ℂ) :
    sourceTransform (fun x => ((∑ j ∈ Finset.range ((quadrantListOf l).length + 1),
      c j * divisorBasis s j x : ℝ) : ℂ)) z * listDivisor (quadrantListOf l) z =
      XiC z * ∑ j ∈ Finset.range ((quadrantListOf l).length + 1), (c j : ℂ) * z ^ (2 * j) := by
  rw [sourceTransform_finset_sum_ofReal _ (fun j _ => (continuous_divisorBasis hsc j).aestronglyMeasurable)
    (fun j _ => abs_divisorBasis_le hsC j) c z, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mul_assoc, sourceTransform_divisorBasis_mul hsT (Finset.mem_range.1 hj)]
  ring

include hsc hsC hsT hl in
/-- **Coordinates.**  Every divisor-keeping source over the list `L` is a basis combination whose
coefficients are those of `e`. -/
theorem eq_sum_divisorBasis_of_mul_eq {u : ℝ → ℝ} (huc : Continuous u) {Cu : ℝ}
    (huC : ∀ x, |u x| ≤ Cu * thetaCuspFullSource x) {e : Polynomial ℝ}
    (he : e.natDegree ≤ (quadrantListOf l).length)
    (heT : ∀ z, sourceTransform (fun x => (u x : ℂ)) z * listDivisor (quadrantListOf l) z =
      XiC z * (e.map (algebraMap ℝ ℂ)).eval (z ^ 2)) :
    u = fun x => ∑ j ∈ Finset.range ((quadrantListOf l).length + 1), e.coeff j * divisorBasis s j x := by
  set B : ℝ → ℝ := fun x => ∑ j ∈ Finset.range ((quadrantListOf l).length + 1), e.coeff j * divisorBasis s j x
  have hBc : Continuous B := continuous_finsetSum _ fun j _ =>
    (continuous_const.mul (continuous_divisorBasis hsc j) : Continuous fun x => e.coeff j * divisorBasis s j x)
  set CB := ∑ j ∈ Finset.range ((quadrantListOf l).length + 1), |e.coeff j| * max C 0
  have hBC : ∀ x, |B x| ≤ CB * thetaCuspFullSource x := fun x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_divisorBasis_le hsC j x) (abs_nonneg _)
  have hD := eq_zero_of_sourceTransform_eq_zero_on_disc (D := fun x => u x - B x)
    (huc.sub hBc) (C := Cu + CB) (fun x => by
      refine (abs_sub _ _).trans ?_
      have h1 := huC x; have h2 := hBC x; nlinarith) (fun z hz => ?_)
  · funext x
    exact sub_eq_zero.1 (hD x)
  · have hP := listDivisor_quadrantListOf_ne_zero_of_norm_le_one hl hz
    refine (mul_eq_zero.1 ?_).resolve_right hP
    rw [sourceTransform_ofReal_sub huc.aestronglyMeasurable huC hBc.aestronglyMeasurable hBC,
      sub_mul, heT, sourceTransform_sum_divisorBasis_mul hsc hsC hsT,
      Polynomial.eval_eq_sum_range' (Polynomial.natDegree_map_le.trans_lt (Nat.lt_succ_of_le he))]
    simp only [Polynomial.coeff_map, Complex.coe_algebraMap, ← pow_mul]
    ring

include hsc hsC hsT in
/-- The order at the origin of a basis combination is that of `Σ c_j z^{2j}`. -/
theorem analyticOrderAt_sum_divisorBasis (c : ℕ → ℝ) :
    analyticOrderAt (sourceTransform fun x => ((∑ j ∈ Finset.range ((quadrantListOf l).length + 1),
      c j * divisorBasis s j x : ℝ) : ℂ)) 0 = analyticOrderAt (fun z =>
        ∑ j ∈ Finset.range ((quadrantListOf l).length + 1), (c j : ℂ) * z ^ (2 * j)) 0 := by
  set U := sourceTransform fun x => ((∑ j ∈ Finset.range ((quadrantListOf l).length + 1), c j * divisorBasis s j x : ℝ) : ℂ)
  have hUc : Continuous fun x => ∑ j ∈ Finset.range ((quadrantListOf l).length + 1), c j * divisorBasis s j x :=
    continuous_finsetSum _ fun j _ => (continuous_const.mul (continuous_divisorBasis hsc j) :
      Continuous fun x => c j * divisorBasis s j x)
  have hUC : ∀ x, |∑ j ∈ Finset.range ((quadrantListOf l).length + 1), c j * divisorBasis s j x| ≤
      (∑ j ∈ Finset.range ((quadrantListOf l).length + 1), |c j| * max C 0) * thetaCuspFullSource x := fun x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_divisorBasis_le hsC j x) (abs_nonneg _)
  have hUd := (expMomentSource_ofReal_of_le hUc hUC).differentiable_sourceTransform
  have hPd := differentiable_listDivisor (quadrantListOf l)
  have h := congrArg (fun f => analyticOrderAt f 0) (show U * listDivisor (quadrantListOf l) =
    XiC * fun z => ∑ j ∈ Finset.range ((quadrantListOf l).length + 1), (c j : ℂ) * z ^ (2 * j) from
      funext (sourceTransform_sum_divisorBasis_mul hsc hsC hsT c))
  rw [analyticOrderAt_mul (hUd.analyticAt 0) (hPd.analyticAt 0),
    analyticOrderAt_mul (XiC_differentiable.analyticAt 0) (by fun_prop),
    (hPd.analyticAt 0).analyticOrderAt_eq_zero.2 (by rw [listDivisor_zero]; exact one_ne_zero),
    (XiC_differentiable.analyticAt 0).analyticOrderAt_eq_zero.2
      (XiC_ne_zero_of_norm_le_one (by simp)), add_zero, zero_add] at h
  exact h

include hsc hse hsC hsT in
/-- **Moments in coordinates.**  The even moments of orders `≤ 2N` of `Σ c_j s_j` vanish iff
`c_j = 0` for `j ≤ N`. -/
theorem moments_sum_divisorBasis_iff (c : ℕ → ℝ) (N : ℕ) :
    (∀ i ≤ N, ∫ x, x ^ (2 * i) * ∑ j ∈ Finset.range ((quadrantListOf l).length + 1),
      c j * divisorBasis s j x = 0) ↔
      ∀ j < (quadrantListOf l).length + 1, j ≤ N → c j = 0 := by
  have hUc : Continuous fun x => ∑ j ∈ Finset.range ((quadrantListOf l).length + 1), c j * divisorBasis s j x :=
    continuous_finsetSum _ fun j _ => (continuous_const.mul (continuous_divisorBasis hsc j) :
      Continuous fun x => c j * divisorBasis s j x)
  have hUC : ∀ x, |∑ j ∈ Finset.range ((quadrantListOf l).length + 1), c j * divisorBasis s j x| ≤
      (∑ j ∈ Finset.range ((quadrantListOf l).length + 1), |c j| * max C 0) * thetaCuspFullSource x := fun x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_divisorBasis_le hsC j x) (abs_nonneg _)
  have hUe : ∀ x, (∑ j ∈ Finset.range ((quadrantListOf l).length + 1), c j * divisorBasis s j (-x)) =
      ∑ j ∈ Finset.range ((quadrantListOf l).length + 1), c j * divisorBasis s j x := fun x =>
    Finset.sum_congr rfl fun j _ => by
      unfold divisorBasis; split_ifs
      · rw [hse]
      · rfl
  rw [moments_eq_zero_iff_order hUc.aestronglyMeasurable hUC hUe N,
    analyticOrderAt_sum_divisorBasis hsc hsC hsT, natCast_le_analyticOrderAt_evenPoly_iff]
  constructor
  · intro h j hj hjN
    exact_mod_cast h j hj (by omega)
  · intro h j hj hj2
    exact_mod_cast h j hj (by omega)

/-- A basis combination `Σ_{j ≤ |L|} c_j s_j`. -/
def divisorBasisComb (s : Fin ((quadrantListOf l).length + 1) → ℝ → ℝ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range ((quadrantListOf l).length + 1), c j * divisorBasis s j x

include hsc in
theorem continuous_divisorBasisComb (c : ℕ → ℝ) : Continuous (divisorBasisComb s c) :=
  continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_divisorBasis hsc j)

include hsC in
theorem abs_divisorBasisComb_le (c : ℕ → ℝ) (x : ℝ) : |divisorBasisComb s c x| ≤
    (∑ j ∈ Finset.range ((quadrantListOf l).length + 1), |c j| * max C 0) *
      thetaCuspFullSource x := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_divisorBasis_le hsC j x) (abs_nonneg _)

include hse in
theorem divisorBasisComb_neg (c : ℕ → ℝ) (x : ℝ) : divisorBasisComb s c (-x) = divisorBasisComb s c x :=
  Finset.sum_congr rfl fun j _ => by
    unfold divisorBasis; split_ifs
    · rw [hse]
    · rfl

include hl hsc hse hsC hsT in
theorem divisorBasisComb_mem_thetaKeepingSources (c : ℕ → ℝ) : divisorBasisComb s c ∈ thetaKeepingSources :=
  ⟨continuous_divisorBasisComb hsc c, divisorBasisComb_neg hse c, ⟨_, abs_divisorBasisComb_le hsC c⟩,
    keepsRealZeros_of_mul_eq
      (expMomentSource_ofReal_of_le (continuous_divisorBasisComb hsc c)
        (abs_divisorBasisComb_le hsC c)).differentiable_sourceTransform (by fun_prop) hl
      (sourceTransform_sum_divisorBasis_mul hsc hsC hsT c)⟩

include hl hsc hse hsC hsT in
theorem divisorBasisComb_mem_moment_iff (c : ℕ → ℝ) (N : ℕ) :
    divisorBasisComb s c ∈ thetaKeepingMomentSources N ↔
      ∀ j < (quadrantListOf l).length + 1, j ≤ N → c j = 0 := by
  rw [← moments_sum_divisorBasis_iff hsc hse hsC hsT c N, mem_thetaKeepingMomentSources]
  exact ⟨fun h => h.2, fun h => ⟨divisorBasisComb_mem_thetaKeepingSources hl hsc hse hsC hsT c, h⟩⟩

theorem divisorBasisComb_single {j : ℕ} (hj : j < (quadrantListOf l).length + 1) :
    divisorBasisComb s (fun k => if k = j then 1 else 0) = divisorBasis s j := by
  funext x
  simp only [divisorBasisComb, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, hj,
    if_true]

theorem divisorBasisComb_eq_linearCombination {a m : ℕ} (ham : a + m ≤ (quadrantListOf l).length + 1)
    (c : ℕ → ℝ) (h0 : ∀ j < (quadrantListOf l).length + 1, (j < a ∨ a + m ≤ j) → c j = 0) :
    divisorBasisComb s c =
      Fintype.linearCombination ℝ (fun i : Fin m => divisorBasis s (a + i)) fun i => c (a + i) := by
  funext x
  obtain ⟨t, ht⟩ : ∃ t, (quadrantListOf l).length + 1 = a + m + t :=
    ⟨_, (Nat.add_sub_cancel' ham).symm⟩
  have hA : ∑ j ∈ Finset.range a, c j * divisorBasis s j x = 0 := Finset.sum_eq_zero fun j hj => by
    have := Finset.mem_range.1 hj
    rw [h0 j (by omega) (Or.inl this), zero_mul]
  have hT : ∑ j ∈ Finset.range t, c (a + m + j) * divisorBasis s (a + m + j) x = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have := Finset.mem_range.1 hj
      rw [h0 (a + m + j) (by omega) (Or.inr (by omega)), zero_mul]
  rw [Fintype.linearCombination_apply, Finset.sum_apply, divisorBasisComb, ht, Finset.sum_range_add,
    Finset.sum_range_add, hA, hT, zero_add, add_zero]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (Fin.sum_univ_eq_sum_range (fun i => c (a + i) * divisorBasis s (a + i) x) m).symm

include hsc hsC hsT in
theorem injective_linearCombination_divisorBasis {a m : ℕ}
    (ham : a + m ≤ (quadrantListOf l).length + 1) :
    Function.Injective (Fintype.linearCombination ℝ fun i : Fin m => divisorBasis s (a + i)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  refine sources_independent_of_pow (l := l) (v := fun i : Fin m => divisorBasis s (a + i))
    (fun i => continuous_divisorBasis hsc _) (C := max C 0) (fun i x => abs_divisorBasis_le hsC _ x)
    (fun i => 2 * (a + i)) (fun i i' (h : 2 * (a + (i : ℕ)) = 2 * (a + i')) => Fin.ext (by omega))
    (fun i z => sourceTransform_divisorBasis_mul hsT (by have := i.isLt; omega) z) c fun x => ?_
  have := congrFun hc x
  simpa only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] using this

include hl hsc hse hsC hsT in
theorem range_linearCombination_divisorBasis_le {a m : ℕ}
    (ham : a + m ≤ (quadrantListOf l).length + 1) :
    LinearMap.range (Fintype.linearCombination ℝ fun i : Fin m => divisorBasis s (a + i)) ≤
      thetaKeepingSources := by
  rw [Fintype.range_linearCombination, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hi := i.isLt
  show divisorBasis s (a + i) ∈ thetaKeepingSources
  rw [← divisorBasisComb_single (s := s) (show a + (i : ℕ) < _ by omega)]
  exact divisorBasisComb_mem_thetaKeepingSources hl hsc hse hsC hsT _

include hl hsc hse hsC hsT in
theorem range_linearCombination_divisorBasis_le_moment {a m N : ℕ}
    (ham : a + m ≤ (quadrantListOf l).length + 1) (haN : N < a) :
    LinearMap.range (Fintype.linearCombination ℝ fun i : Fin m => divisorBasis s (a + i)) ≤
      thetaKeepingMomentSources N := by
  rw [Fintype.range_linearCombination, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hi := i.isLt
  show divisorBasis s (a + i) ∈ thetaKeepingMomentSources N
  rw [← divisorBasisComb_single (s := s) (show a + (i : ℕ) < _ by omega),
    divisorBasisComb_mem_moment_iff hl hsc hse hsC hsT]
  exact fun j _ hj => if_neg (by omega)

variable (hst : ∀ j, Tendsto (fun x => |s j x - (if (j : ℕ) = (quadrantListOf l).length then r
  else 0) * thetaCuspFullSource x| / thetaCuspFullSource x) (cocompact ℝ) (𝓝 0))

include hst in
theorem tendsto_divisorBasis_div (j : ℕ) : Tendsto (fun x => divisorBasis s j x / thetaCuspFullSource x)
    (cocompact ℝ) (𝓝 (if j = (quadrantListOf l).length then r else 0)) := by
  by_cases h : j < (quadrantListOf l).length + 1
  · refine tendsto_iff_norm_sub_tendsto_zero.2 ((hst ⟨j, h⟩).congr fun x => ?_)
    have hk := thetaCuspFullSource_pos x
    rw [Real.norm_eq_abs, divisorBasis, dif_pos h, div_sub' hk.ne', abs_div, abs_of_pos hk, mul_comm]
  · have hj : j ≠ (quadrantListOf l).length := by omega
    simp only [divisorBasis, dif_neg h, Pi.zero_apply, zero_div, if_neg hj]
    exact tendsto_const_nhds

include hst in
/-- The first-atom tail coefficient of a basis combination is its top coordinate times `r`. -/
theorem tendsto_divisorBasisComb_div (c : ℕ → ℝ) :
    Tendsto (fun x => divisorBasisComb s c x / thetaCuspFullSource x) (cocompact ℝ)
      (𝓝 (c (quadrantListOf l).length * r)) := by
  have h := tendsto_finsetSum (Finset.range ((quadrantListOf l).length + 1))
    fun j _ => (tendsto_divisorBasis_div hst j).const_mul (c j)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self,
    if_true] at h
  refine h.congr fun x => ?_
  rw [divisorBasisComb, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

include hl hsc hse hsC hsT hst in
theorem divisorBasisComb_mem_tail_iff (hr : r ≠ 0) (c : ℕ → ℝ) (N : ℕ) :
    divisorBasisComb s c ∈ thetaKeepingTailSources N ↔
      (∀ j < (quadrantListOf l).length + 1, j ≤ N → c j = 0) ∧
        c (quadrantListOf l).length = 0 := by
  rw [mem_thetaKeepingTailSources, divisorBasisComb_mem_moment_iff hl hsc hse hsC hsT]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · exact (mul_eq_zero.1 (tendsto_nhds_unique (tendsto_divisorBasisComb_div hst c) h)).resolve_right hr
  · have := tendsto_divisorBasisComb_div hst c
    rwa [h, zero_mul] at this

include hl hsc hse hsC hsT hst in
theorem range_linearCombination_divisorBasis_le_tail (hr : r ≠ 0) {a m N : ℕ}
    (ham : a + m ≤ (quadrantListOf l).length) (haN : N < a) :
    LinearMap.range (Fintype.linearCombination ℝ fun i : Fin m => divisorBasis s (a + i)) ≤
      thetaKeepingTailSources N := by
  rw [Fintype.range_linearCombination, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hi := i.isLt
  show divisorBasis s (a + i) ∈ thetaKeepingTailSources N
  rw [← divisorBasisComb_single (s := s) (show a + (i : ℕ) < _ by omega),
    divisorBasisComb_mem_tail_iff hl hsc hse hsC hsT hst hr]
  exact ⟨fun j _ hj => if_neg (by omega), if_neg (by omega)⟩

end Coordinates

/-! ## Exact dimensions of the moment and tail filtrations -/

section FiniteDefect

variable (hfin : xiQuadrantZeros.Finite)

theorem exists_divisorBasisComb_of_mem {s : Fin ((quadrantListOf hfin.toFinset.toList).length + 1) → ℝ → ℝ}
    (hsc : ∀ j, Continuous (s j)) {C : ℝ} (hsC : ∀ j x, |s j x| ≤ C * thetaCuspFullSource x)
    (hsT : ∀ j z, sourceTransform (fun x => (s j x : ℂ)) z *
      listDivisor (quadrantListOf hfin.toFinset.toList) z = XiC z * z ^ (2 * (j : ℕ)))
    {u : ℝ → ℝ} (hu : u ∈ thetaKeepingSources) : ∃ c : ℕ → ℝ, u = divisorBasisComb s c := by
  obtain ⟨huc, hue, ⟨Cu, huC⟩, huk⟩ := hu
  obtain ⟨e, he, heT⟩ :=
    exists_realPolynomial_of_keepsRealZeros hfin huc.aestronglyMeasurable huC hue huk
  exact ⟨fun j => e.coeff j, eq_sum_divisorBasis_of_mul_eq
    (fun α hα => mem_xiOffLineList_toList hfin hα) hsc hsC hsT huc huC he heT⟩

/-- **The divisor-keeping space.**  If the off-line quartets are finite with total first-quadrant
multiplicity `M`, the real even `k`-dominated sources keeping every real zero of `F` form a space of
dimension `2M + 1`. -/
theorem finrank_thetaKeepingSources :
    Module.finrank ℝ thetaKeepingSources = 2 * xiQuadrantMult hfin + 1 := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  obtain ⟨r, -, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨s, hsc, hse, ⟨C, hsC⟩, hsT, -⟩ := exists_basis_sources hl (nodup_xiOffLine_toList hfin) hr
  have hn : (quadrantListOf hfin.toFinset.toList).length = 2 * xiQuadrantMult hfin :=
    length_xiOffLineList hfin
  have hW : thetaKeepingSources = LinearMap.range (Fintype.linearCombination ℝ
      fun i : Fin ((quadrantListOf hfin.toFinset.toList).length + 1) => divisorBasis s (0 + i)) := by
    refine le_antisymm (fun u hu => ?_) (range_linearCombination_divisorBasis_le hl hsc hse hsC hsT (by omega))
    obtain ⟨c, rfl⟩ := exists_divisorBasisComb_of_mem hfin hsc hsC hsT hu
    exact ⟨fun i => c (0 + i),
      (divisorBasisComb_eq_linearCombination (by omega) c fun j hj h => by omega).symm⟩
  rw [hW, LinearMap.finrank_range_of_inj
      (injective_linearCombination_divisorBasis (a := 0) hsc hsC hsT (by omega)),
    Module.finrank_fin_fun, hn]

/-- **Sharp moment filtration.**  `dim W_N = max(2M − N, 0)`: vanishing of the even moments of
orders `0, 2, …, 2N` removes exactly the coordinates `0, …, N`. -/
theorem finrank_thetaKeepingMomentSources (N : ℕ) :
    Module.finrank ℝ (thetaKeepingMomentSources N) = 2 * xiQuadrantMult hfin - N := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  obtain ⟨r, -, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨s, hsc, hse, ⟨C, hsC⟩, hsT, -⟩ := exists_basis_sources hl (nodup_xiOffLine_toList hfin) hr
  have hn : (quadrantListOf hfin.toFinset.toList).length = 2 * xiQuadrantMult hfin :=
    length_xiOffLineList hfin
  rcases le_or_gt N (quadrantListOf hfin.toFinset.toList).length with hN | hN
  · have hW : thetaKeepingMomentSources N = LinearMap.range (Fintype.linearCombination ℝ
        fun i : Fin ((quadrantListOf hfin.toFinset.toList).length - N) => divisorBasis s (N + 1 + i)) := by
      refine le_antisymm (fun u hu => ?_)
        (range_linearCombination_divisorBasis_le_moment hl hsc hse hsC hsT (by omega) (by omega))
      obtain ⟨c, rfl⟩ := exists_divisorBasisComb_of_mem hfin hsc hsC hsT
        (mem_thetaKeepingMomentSources.1 hu).1
      have hc := (divisorBasisComb_mem_moment_iff hl hsc hse hsC hsT c N).1 hu
      exact ⟨fun i => c (N + 1 + i),
        (divisorBasisComb_eq_linearCombination (by omega) c fun j hj h => hc j hj (by omega)).symm⟩
    rw [hW, LinearMap.finrank_range_of_inj
      (injective_linearCombination_divisorBasis hsc hsC hsT (by omega)), Module.finrank_fin_fun, hn]
  · have hW : thetaKeepingMomentSources N = ⊥ := by
      refine eq_bot_iff.2 fun u hu => ?_
      obtain ⟨c, rfl⟩ := exists_divisorBasisComb_of_mem hfin hsc hsC hsT
        (mem_thetaKeepingMomentSources.1 hu).1
      have hc := (divisorBasisComb_mem_moment_iff hl hsc hse hsC hsT c N).1 hu
      rw [Submodule.mem_bot]
      funext x
      refine Finset.sum_eq_zero fun j hj => ?_
      have := Finset.mem_range.1 hj
      rw [hc j this (by omega), zero_mul]
    rw [hW, finrank_bot]
    omega

/-- **Tail filtration.**  Inside `W_N`, vanishing of the first-atom tail coefficient
`lim u/k` removes exactly the top coordinate: `dim = max(2M − N − 1, 0)`. -/
theorem finrank_thetaKeepingTailSources (N : ℕ) :
    Module.finrank ℝ (thetaKeepingTailSources N) = 2 * xiQuadrantMult hfin - N - 1 := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  obtain ⟨r, hr0, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨s, hsc, hse, ⟨C, hsC⟩, hsT, hst⟩ :=
    exists_basis_sources hl (nodup_xiOffLine_toList hfin) hr
  have hn : (quadrantListOf hfin.toFinset.toList).length = 2 * xiQuadrantMult hfin :=
    length_xiOffLineList hfin
  rcases lt_or_ge N (quadrantListOf hfin.toFinset.toList).length with hN | hN
  · have hW : thetaKeepingTailSources N = LinearMap.range (Fintype.linearCombination ℝ
        fun i : Fin ((quadrantListOf hfin.toFinset.toList).length - N - 1) =>
          divisorBasis s (N + 1 + i)) := by
      refine le_antisymm (fun u hu => ?_)
        (range_linearCombination_divisorBasis_le_tail hl hsc hse hsC hsT hst hr0.ne' (by omega)
          (by omega))
      obtain ⟨c, rfl⟩ := exists_divisorBasisComb_of_mem hfin hsc hsC hsT
        (mem_thetaKeepingMomentSources.1 (mem_thetaKeepingTailSources.1 hu).1).1
      obtain ⟨hc, hcn⟩ := (divisorBasisComb_mem_tail_iff hl hsc hse hsC hsT hst hr0.ne' c N).1 hu
      refine ⟨fun i => c (N + 1 + i),
        (divisorBasisComb_eq_linearCombination (by omega) c fun j hj h => ?_).symm⟩
      rcases h with h | h
      · exact hc j hj (by omega)
      · obtain rfl : j = (quadrantListOf hfin.toFinset.toList).length := by omega
        exact hcn
    rw [hW, LinearMap.finrank_range_of_inj
      (injective_linearCombination_divisorBasis hsc hsC hsT (by omega)), Module.finrank_fin_fun, hn]
  · have hW : thetaKeepingTailSources N = ⊥ := by
      refine eq_bot_iff.2 fun u hu => ?_
      obtain ⟨c, rfl⟩ := exists_divisorBasisComb_of_mem hfin hsc hsC hsT
        (mem_thetaKeepingMomentSources.1 (mem_thetaKeepingTailSources.1 hu).1).1
      have hc := (divisorBasisComb_mem_moment_iff hl hsc hse hsC hsT c N).1
        (mem_thetaKeepingTailSources.1 hu).1
      rw [Submodule.mem_bot]
      funext x
      refine Finset.sum_eq_zero fun j hj => ?_
      have := Finset.mem_range.1 hj
      rw [hc j this (by omega), zero_mul]
    rw [hW, finrank_bot]
    omega

end FiniteDefect

/-- **Infinitely many off-line quartets.**  Every moment filtration step `W_N` is then
infinite-dimensional. -/
theorem not_finiteDimensional_thetaKeepingMomentSources (hinf : xiQuadrantZeros.Infinite)
    (N : ℕ) : ¬ FiniteDimensional ℝ (thetaKeepingMomentSources N) := by
  intro hfd
  obtain ⟨t, ht, htc⟩ := hinf.exists_subset_card_eq
    (Module.finrank ℝ (thetaKeepingMomentSources N) + N + 1)
  have hl : ∀ α ∈ t.toList, α ∈ xiQuadrantZeros := fun α hα => ht (Finset.mem_toList.1 hα)
  obtain ⟨r, -, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨s, hsc, hse, ⟨C, hsC⟩, hsT, -⟩ := exists_basis_sources hl (Finset.nodup_toList t) hr
  have hlen : t.card ≤ (quadrantListOf t.toList).length := by
    rw [length_quadrantListOf, Finset.sum_map_toList, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun α hα => by have := one_le_xiZeroMult (ht hα).2.2; omega
  have h := Submodule.finrank_mono (range_linearCombination_divisorBasis_le_moment hl hsc hse hsC hsT
    (m := (quadrantListOf t.toList).length - N) (a := N + 1) (N := N) (by omega) (by omega))
  rw [LinearMap.finrank_range_of_inj (injective_linearCombination_divisorBasis hsc hsC hsT (by omega)),
    Module.finrank_fin_fun] at h
  omega

/-- The tail filtration is infinite-dimensional as well when the off-line quartets are
infinite. -/
theorem not_finiteDimensional_thetaKeepingTailSources (hinf : xiQuadrantZeros.Infinite)
    (N : ℕ) : ¬ FiniteDimensional ℝ (thetaKeepingTailSources N) := by
  intro hfd
  obtain ⟨t, ht, htc⟩ := hinf.exists_subset_card_eq
    (Module.finrank ℝ (thetaKeepingTailSources N) + N + 2)
  have hl : ∀ α ∈ t.toList, α ∈ xiQuadrantZeros := fun α hα => ht (Finset.mem_toList.1 hα)
  obtain ⟨r, hr0, hr⟩ := prod_neg_sq_quadrantListOf hl
  obtain ⟨s, hsc, hse, ⟨C, hsC⟩, hsT, hst⟩ := exists_basis_sources hl (Finset.nodup_toList t) hr
  have hlen : t.card ≤ (quadrantListOf t.toList).length := by
    rw [length_quadrantListOf, Finset.sum_map_toList, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun α hα => by have := one_le_xiZeroMult (ht hα).2.2; omega
  have h := Submodule.finrank_mono (range_linearCombination_divisorBasis_le_tail hl hsc hse hsC hsT hst
    hr0.ne' (m := (quadrantListOf t.toList).length - N - 1) (a := N + 1) (N := N) (by omega) (by omega))
  rw [LinearMap.finrank_range_of_inj (injective_linearCombination_divisorBasis hsc hsC hsT (by omega)),
    Module.finrank_fin_fun] at h
  omega

end

end RHTower
