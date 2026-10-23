import GaloisForLFunctions.HTGeometry.CosineProductSquaredMajorization
import GaloisForLFunctions.HTGeometry.PolynomialRootSumSemicontinuity
import GaloisForLFunctions.HTGeometry.CosineDepthCountRigidity

/-!
# Squared-height majorization for the heat flow

For a nonzero real polynomial `p`, `τ ≥ 0` and every threshold `s ≥ 0`, the roots `w` of the heat
flow `e^{−τD²}p` (`polyHeat`) satisfy

`Σ_w ((Im w)⁺² − s)_+ ≤ Σ_{u ∈ U(p)} ((Im u)² − 2τ − s)_+`
(`sum_roots_polyHeat_sq_sub_le`),

with `U(p)` the roots of `p` in the open upper half-plane.  So the squared heights of the upper
roots lose at least `2τ` in the sense of weak majorization; `s = 0` is the energy law
`Σ (Im w)⁺² ≤ Σ ((Im u)² − 2τ)_+`.  The heat flow has no depth-resolved count of nonreal roots
(`not_heat_depthCountLaw`), but it does have this energy law.

**Proof.**  `n` cosine steps of depth `√(2τ/n)` lose exactly `2τ` of squared height
(`sum_roots_cosProd_sq_sub_le`).  They converge to the heat flow: on polynomials of degree `≤ N`,
`n` steps act as `Σ_{m ≤ N} c_{n,m} (−D²)^m` with `c_{n,m}` the `m`-th coefficient of
`(Σ_k h^{2k}/(2k)! Y^k)^n` (`cosProd_replicate_eq_sum`), and with `s = h² = 2τ/n`

`C(n,m)(τ/n)^m ≤ c_{n,m} ≤ τ^m/m!`

coefficientwise, from `1 + (s/2)Y ≤ cos-series ≤ e^{(s/2)Y}` (`2^k k! ≤ (2k)!`).  The lower bound
tends to `τ^m/m!`.  The root sums pass to the limit by lower semicontinuity
(`sum_roots_le_of_tendstoLocallyUniformly`).
-/

open Polynomial Complex Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The operator calculus in `Y = −D²` -/

/-- `Q(−D²)` applied to a polynomial of degree `≤ N`. -/
theorem aeval_neg_derivSq_apply (Q : ℝ[X]) {p : ℝ[X]} {N : ℕ} (hN : p.natDegree ≤ N) :
    (aeval (-derivSq) Q) p =
      ∑ m ∈ range (N + 1), C (Q.coeff m * (-1) ^ m) * derivative^[2 * m] p := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply]
  have hterm : ∀ i, (Q.coeff i • (-derivSq : Module.End ℝ ℝ[X]) ^ i) p =
      C (Q.coeff i * (-1) ^ i) * derivative^[2 * i] p := by
    intro i
    rw [show (-derivSq : Module.End ℝ ℝ[X]) = (-1 : ℝ) • derivSq from (neg_one_smul ℝ _).symm,
      _root_.smul_pow, smul_smul, LinearMap.smul_apply, derivSq_pow_apply, smul_eq_C_mul]
  simp_rw [hterm]
  set M := max Q.natDegree N + 1
  have h1 : range (Q.natDegree + 1) ⊆ range M := range_subset_range.mpr (by omega)
  have h2 : range (N + 1) ⊆ range M := range_subset_range.mpr (by omega)
  rw [Finset.sum_subset h1 (fun k hk hk' => ?_), Finset.sum_subset h2 (fun k hk hk' => ?_)]
  · simp only [mem_range, not_lt] at hk'
    rw [iterate_derivative_eq_zero (by omega), mul_zero]
  · simp only [mem_range, not_lt] at hk'
    rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, C_0, zero_mul]

/-- The cosine series `Σ_k h^{2k}/(2k)! Y^k`. -/
private def cosSeries (h : ℝ) : PowerSeries ℝ := PowerSeries.mk (cosCoeff h)

theorem natDegree_evenOp_le (a : ℕ → ℝ) (q : ℝ[X]) : (evenOp a q).natDegree ≤ q.natDegree := by
  unfold evenOp
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => (natDegree_C_mul_le _ _).trans ?_
  have := natDegree_iterate_derivative q (2 * k)
  omega

theorem natDegree_shiftAvg_le (h : ℝ) (q : ℝ[X]) : (shiftAvg h q).natDegree ≤ q.natDegree := by
  rw [shiftAvg_eq_evenOp_cosCoeff]; exact natDegree_evenOp_le _ _

/-- One cosine step as `trunc(cos-series)(−D²)`. -/
theorem shiftAvg_eq_aeval (h : ℝ) {q : ℝ[X]} {N : ℕ} (hN : q.natDegree ≤ N) :
    shiftAvg h q = (aeval (-derivSq) (PowerSeries.trunc (N + 1) (cosSeries h))) q := by
  rw [aeval_neg_derivSq_apply _ hN, shiftAvg_eq_evenOp_cosCoeff, evenOp_eq_sum_of_le _ hN]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [PowerSeries.coeff_trunc, if_pos (by simpa using hm), cosSeries, PowerSeries.coeff_mk]
  ring_nf

theorem natDegree_cosProd_replicate_le (h : ℝ) (p : ℝ[X]) :
    ∀ n, (cosProd (List.replicate n h) p).natDegree ≤ p.natDegree
  | 0 => le_rfl
  | n + 1 => (natDegree_shiftAvg_le h _).trans (natDegree_cosProd_replicate_le h p n)

/-- `n` cosine steps as one polynomial in `−D²`. -/
theorem cosProd_replicate_eq_aeval (h : ℝ) (p : ℝ[X]) :
    ∀ n, cosProd (List.replicate n h) p =
      (aeval (-derivSq) (PowerSeries.trunc (p.natDegree + 1) (cosSeries h) ^ n)) p
  | 0 => by simp [cosProd]
  | n + 1 => by
    have hstep : cosProd (List.replicate (n + 1) h) p =
        shiftAvg h (cosProd (List.replicate n h) p) := rfl
    rw [hstep, shiftAvg_eq_aeval h (natDegree_cosProd_replicate_le h p n),
      cosProd_replicate_eq_aeval h p n, pow_succ', map_mul, Module.End.mul_apply]

/-- **`n` cosine steps with explicit coefficients.** -/
theorem cosProd_replicate_eq_sum (h : ℝ) (p : ℝ[X]) (n : ℕ) :
    cosProd (List.replicate n h) p =
      ∑ m ∈ range (p.natDegree + 1),
        C (PowerSeries.coeff m (cosSeries h ^ n) * (-1) ^ m) * derivative^[2 * m] p := by
  rw [cosProd_replicate_eq_aeval, aeval_neg_derivSq_apply _ le_rfl]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 3
  have hm' : m < p.natDegree + 1 := by simpa using hm
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow]
  have := congrArg (fun P : ℝ[X] => P.coeff m)
    (PowerSeries.trunc_trunc_pow (cosSeries h) (p.natDegree + 1) n)
  simp only [PowerSeries.coeff_trunc, if_pos hm'] at this
  exact this

/-! ## Coefficient bounds -/

theorem coeff_mul_nonneg {A B : PowerSeries ℝ} (hA : ∀ k, 0 ≤ PowerSeries.coeff k A)
    (hB : ∀ k, 0 ≤ PowerSeries.coeff k B) (k : ℕ) : 0 ≤ PowerSeries.coeff k (A * B) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hA _) (hB _)

theorem coeff_mul_le_mul {A B A' B' : PowerSeries ℝ} (hA : ∀ k, 0 ≤ PowerSeries.coeff k A)
    (hA' : ∀ k, 0 ≤ PowerSeries.coeff k A')
    (hAB : ∀ k, PowerSeries.coeff k A ≤ PowerSeries.coeff k B)
    (hAB' : ∀ k, PowerSeries.coeff k A' ≤ PowerSeries.coeff k B') (k : ℕ) :
    PowerSeries.coeff k (A * A') ≤ PowerSeries.coeff k (B * B') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  exact Finset.sum_le_sum fun x _ =>
    mul_le_mul (hAB _) (hAB' _) (hA' _) ((hA _).trans (hAB _))

theorem coeff_pow_nonneg {A : PowerSeries ℝ} (hA : ∀ k, 0 ≤ PowerSeries.coeff k A) :
    ∀ n k, 0 ≤ PowerSeries.coeff k (A ^ n)
  | 0, k => by
    rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> norm_num
  | n + 1, k => by
    rw [pow_succ]; exact coeff_mul_nonneg (coeff_pow_nonneg hA n) hA k

theorem coeff_pow_le_pow {A B : PowerSeries ℝ} (hA : ∀ k, 0 ≤ PowerSeries.coeff k A)
    (hAB : ∀ k, PowerSeries.coeff k A ≤ PowerSeries.coeff k B) :
    ∀ n k, PowerSeries.coeff k (A ^ n) ≤ PowerSeries.coeff k (B ^ n)
  | 0, k => le_rfl
  | n + 1, k => by
    rw [pow_succ, pow_succ]
    exact coeff_mul_le_mul (coeff_pow_nonneg hA n) hA (coeff_pow_le_pow hA hAB n) hAB k

theorem two_pow_mul_factorial_le (k : ℕ) : 2 ^ k * k.factorial ≤ (2 * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      pow_succ, Nat.factorial_succ]
    have h1 : 2 * (k + 1) ≤ (2 * k + 1 + 1) * (2 * k + 1) := by nlinarith
    calc 2 ^ k * 2 * ((k + 1) * k.factorial) = (2 * (k + 1)) * (2 ^ k * k.factorial) := by ring
      _ ≤ ((2 * k + 1 + 1) * (2 * k + 1)) * (2 * k).factorial := Nat.mul_le_mul h1 ih
      _ = (2 * k + 1 + 1) * ((2 * k + 1) * (2 * k).factorial) := by ring

theorem coeff_cosSeries (h : ℝ) (k : ℕ) :
    PowerSeries.coeff k (cosSeries h) = (h ^ 2) ^ k / ((2 * k).factorial : ℝ) := by
  rw [cosSeries, PowerSeries.coeff_mk, cosCoeff, pow_mul]

theorem coeff_rescale_exp (a : ℝ) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.rescale a (PowerSeries.exp ℝ)) = a ^ k / (k.factorial : ℝ) := by
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

/-- **Upper bound.** `c_{n,m} ≤ (n h²/2)^m / m!`. -/
theorem coeff_cosSeries_pow_le (h : ℝ) (n m : ℕ) :
    PowerSeries.coeff m (cosSeries h ^ n) ≤ ((n : ℝ) * (h ^ 2 / 2)) ^ m / (m.factorial : ℝ) := by
  have hs : 0 ≤ h ^ 2 := sq_nonneg h
  have hA : ∀ k, 0 ≤ PowerSeries.coeff k (cosSeries h) := fun k => by
    rw [coeff_cosSeries]; positivity
  have hAB : ∀ k, PowerSeries.coeff k (cosSeries h) ≤
      PowerSeries.coeff k (PowerSeries.rescale (h ^ 2 / 2) (PowerSeries.exp ℝ)) := by
    intro k
    rw [coeff_cosSeries, coeff_rescale_exp, div_pow,
      div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : ((2 ^ k * k.factorial : ℕ) : ℝ) ≤ ((2 * k).factorial : ℝ) := by
      exact_mod_cast two_pow_mul_factorial_le k
    push_cast at h2
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have h1 := coeff_pow_le_pow hA hAB n m
  refine h1.trans (le_of_eq ?_)
  rw [← map_pow, PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale,
    coeff_rescale_exp, mul_comm]

/-- **Lower bound.** `C(n,m)(h²/2)^m ≤ c_{n,m}`. -/
theorem choose_mul_le_coeff_cosSeries_pow (h : ℝ) (n m : ℕ) :
    (n.choose m : ℝ) * (h ^ 2 / 2) ^ m ≤ PowerSeries.coeff m (cosSeries h ^ n) := by
  set L : PowerSeries ℝ := PowerSeries.rescale (h ^ 2 / 2) ((((X + 1) : ℝ[X])) : PowerSeries ℝ)
  have hL : ∀ k, PowerSeries.coeff k L = (h ^ 2 / 2) ^ k * ((X + 1 : ℝ[X]).coeff k) := by
    intro k; rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe]
  have hL0 : ∀ k, 0 ≤ PowerSeries.coeff k L := by
    intro k; rw [hL]
    refine mul_nonneg (by positivity) ?_
    rw [coeff_add, coeff_X, coeff_one]; split_ifs <;> norm_num
  have hLA : ∀ k, PowerSeries.coeff k L ≤ PowerSeries.coeff k (cosSeries h) := by
    intro k
    rw [hL, coeff_cosSeries, coeff_add, coeff_X, coeff_one]
    rcases k with _ | _ | k
    · simp
    · simp
    · simp only [show (1 : ℕ) ≠ k + 2 by omega, show k + 2 ≠ 0 by omega, if_false, add_zero,
        mul_zero]
      positivity
  have h1 := coeff_pow_le_pow hL0 hLA n m
  refine le_of_eq_of_le ?_ h1
  rw [← map_pow, ← Polynomial.coe_pow, PowerSeries.coeff_rescale, Polynomial.coeff_coe,
    coeff_X_add_one_pow, mul_comm]

/-- **The coefficients converge to the heat coefficients.** -/
theorem tendsto_coeff_cosSeries_pow {τ : ℝ} (hτ : 0 ≤ τ) (m : ℕ) :
    Tendsto (fun n : ℕ => PowerSeries.coeff m (cosSeries (Real.sqrt (2 * τ / n)) ^ n)) atTop
      (𝓝 (τ ^ m / (m.factorial : ℝ))) := by
  have hsq : ∀ n : ℕ, Real.sqrt (2 * τ / n) ^ 2 / 2 = τ / n := by
    intro n; rw [Real.sq_sqrt (by positivity)]; ring
  have hlow : Tendsto (fun n : ℕ => (n.choose m : ℝ) * (τ / n) ^ m) atTop
      (𝓝 (τ ^ m / (m.factorial : ℝ))) := by
    have := tendsto_choose_mul_pow (-τ) m
    simp only [neg_div, neg_neg] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    (Eventually.of_forall fun n => ?_) ?_
  · have := choose_mul_le_coeff_cosSeries_pow (Real.sqrt (2 * τ / n)) n m
    rwa [hsq] at this
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have := coeff_cosSeries_pow_le (Real.sqrt (2 * τ / n)) n m
    rw [hsq, mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)] at this
    exact this

/-- **Cosine steps converge to the heat flow**, locally uniformly on `ℂ`. -/
theorem tendstoLocallyUniformly_eval_cosProd_replicate {τ : ℝ} (hτ : 0 ≤ τ) (p : ℝ[X]) :
    TendstoLocallyUniformly
      (fun (n : ℕ) (z : ℂ) =>
        ((cosProd (List.replicate n (Real.sqrt (2 * τ / n))) p).map Complex.ofRealHom).eval z)
      (fun z => ((polyHeat τ p).map Complex.ofRealHom).eval z) atTop := by
  set N := p.natDegree + 1
  set q : ℕ → ℝ[X] := fun k => derivative^[2 * k] p
  set c : ℕ → ℕ → ℝ := fun n k =>
    PowerSeries.coeff k (cosSeries (Real.sqrt (2 * τ / n)) ^ n) * (-1) ^ k
  have hheat : polyHeat τ p = ∑ k ∈ range N, C ((-τ) ^ k / (k.factorial : ℝ)) * q k := rfl
  have hcos : ∀ n, cosProd (List.replicate n (Real.sqrt (2 * τ / n))) p =
      ∑ k ∈ range N, C (c n k) * q k := fun n => cosProd_replicate_eq_sum _ p n
  have hlim : ∀ k, Tendsto (fun n => c n k) atTop (𝓝 ((-τ) ^ k / (k.factorial : ℝ))) := by
    intro k
    have := (tendsto_coeff_cosSeries_pow hτ k).mul_const ((-1 : ℝ) ^ k)
    rw [neg_pow, show (-1 : ℝ) ^ k * τ ^ k / (k.factorial : ℝ) =
      τ ^ k / (k.factorial : ℝ) * (-1) ^ k by ring]
    exact this
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hbound : ∀ k, ∃ B, 0 ≤ B ∧ ∀ z ∈ K, ‖((q k).map Complex.ofRealHom).eval z‖ ≤ B := by
    intro k
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      ((q k).map Complex.ofRealHom).continuous.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun z hz => (hB z hz).trans (le_max_left _ _)⟩
  choose B hB0 hB using hbound
  set Bs := ∑ k ∈ range N, B k + 1
  have hBs : 0 < Bs := by have := Finset.sum_nonneg (fun k (_ : k ∈ range N) => hB0 k); linarith
  have hev : ∀ k ∈ range N, ∀ᶠ n : ℕ in atTop,
      |c n k - (-τ) ^ k / (k.factorial : ℝ)| < ε / Bs := by
    intro k _
    have h := hlim k
    rw [Metric.tendsto_nhds] at h
    filter_upwards [h (ε / Bs) (by positivity)] with n hn
    rwa [Real.dist_eq] at hn
  filter_upwards [(Filter.eventually_all_finset (range N)).mpr hev] with n hn z hz
  rw [hcos n, hheat, dist_eq_norm, eval_map_sum_C_mul, eval_map_sum_C_mul, ← Finset.sum_sub_distrib]
  calc ‖∑ k ∈ range N, (((-τ) ^ k / (k.factorial : ℝ) : ℝ) * ((q k).map Complex.ofRealHom).eval z -
        ((c n k : ℝ) : ℂ) * ((q k).map Complex.ofRealHom).eval z)‖
      ≤ ∑ k ∈ range N, ε / Bs * B k := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_sub_comm]
        exact mul_le_mul (hn k hk).le (hB k z hz) (norm_nonneg _) (by positivity)
    _ = ε / Bs * ∑ k ∈ range N, B k := by rw [Finset.mul_sum]
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hBs]
        nlinarith

/-! ## The heat law -/

theorem sum_replicate_sq (n : ℕ) (b : ℝ) :
    ((List.replicate n b).map fun a => a ^ 2).sum = n * b ^ 2 := by
  simp [List.map_replicate, List.sum_replicate, nsmul_eq_mul]

/-- **Squared-height majorization for the heat flow.** -/
theorem sum_roots_polyHeat_sq_sub_le {p : ℝ[X]} (hp : p ≠ 0) {τ s : ℝ} (hτ : 0 ≤ τ)
    (hs : 0 ≤ s) :
    ((((polyHeat τ p).map ofRealHom).roots).map fun w => max ((max w.im 0) ^ 2 - s) 0).sum ≤
      ((upperRoots p).map fun u => max (u.im ^ 2 - 2 * τ - s) 0).sum := by
  have hf : (polyHeat τ p).map ofRealHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr (natDegree_polyHeat τ hp).2
  refine sum_roots_le_of_tendstoLocallyUniformly hf
    (tendstoLocallyUniformly_eval_cosProd_replicate hτ p) (by fun_prop)
    (fun w => le_max_right _ _) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hstep := sum_roots_cosProd_sq_sub_le hp (List.replicate n (Real.sqrt (2 * τ / n)))
    (fun a ha => by rw [List.eq_of_mem_replicate ha]; exact Real.sqrt_nonneg _) hs
  rw [sum_replicate_sq, Real.sq_sqrt (by positivity),
    mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)] at hstep
  exact hstep

end

end GaloisForLFunctions.HTGeometry
