import GaloisForLFunctions.RHTower.CompletionOrderOneEnvelopeAnyLine
import GaloisForLFunctions.RHTower.HerglotzWeilBridgeAnyLine
import GaloisForLFunctions.RHTower.CompletionLogDerivZeroPairs
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional

/-!
# Twin rigidity: a degree-`d` twin of `ζ^d` with all zeros critical is `ζ^d`

Let `T(s) = Σ a(n) n^{−s}` have real coefficients with `a(1) = 1`, absolutely convergent on
`Re s > σ₀`, and let `Λ = (s(s − 1)Γ_ℝ(s))^d T(s)` extend to an entire function of finite order with
`Λ(1 − s) = Λ(s)` (`TwinDatum`).  If every zero of `Λ` lies on `Re s = ½`, then the Riemann
hypothesis holds and `T = ζ^d` on `Re s > max σ₀ 1` (`twin_rigidity`).

**Proof.**
* The weights `λ_T` are the coefficients of `−T'/T`: `λ_T = (a · log) ⋆ a^{−1}` with the Dirichlet
  inverse `a^{−1}`, whose series converges absolutely once `Σ_{n≥2} |a(n)| n^{−σ} < 1`
  (`summable_dinv`, partial sums `P_N ≤ 1 + S P_N`).
* `Λ` has the order-one envelope (`CompletionGrowth.orderOneEnvelope_of_finiteOrder_abscissa`), so
  `Λ'/Λ = ½ Σ_ρ (1/(s − ρ) + 1/(s − (1 − ρ)))` over its zeros; with every zero on the critical line
  each term has nonnegative real part on `Re s > ½`.  Hence `Φ = Λ'/(dΛ)` is a Herglotz function on
  `Re s > ½` equal to the Weil function of `λ_T/d` far to the right.
* By the Herglotz–Weil bridge for any abscissa, `λ_T/d` is full-cone Weil-positive; the unconditional
  uniqueness of the Weil cone gives RH and `λ_T = dΛ`.  Then `(T/ζ^d)' = 0` and `T(σ) → a(1) = 1`.
-/

open Complex Filter Topology Set LSeries
open GaloisForLFunctions.EntireZeroDivisor

noncomputable section

namespace RHTower.TwinRigidity

/-! ### The Dirichlet inverse and the weights `λ_T` -/

/-- A real sequence as an arithmetic function. -/
def arith (a : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else a n, by simp⟩

theorem arith_apply {a : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) : arith a n = a n := by
  simp [arith, hn]

/-- The Dirichlet inverse of a sequence with `a(1) = 1`. -/
def dinv (a : ℕ → ℝ) (ha : a 1 = 1) : ArithmeticFunction ℝ :=
  ArithmeticFunction.dirichletInverse (arith a) (invertibleOfNonzero (by
    rw [arith_apply one_ne_zero, ha]; exact one_ne_zero))

theorem arith_mul_dinv (a : ℕ → ℝ) (ha : a 1 = 1) : arith a * dinv a ha = 1 :=
  ArithmeticFunction.self_mul_dirichletInverse _ _

/-- The weights `λ_T = (a · log) ⋆ a^{−1}`, the coefficients of `−T'/T`. -/
def lamT (a : ℕ → ℝ) (ha : a 1 = 1) : ℕ → ℝ :=
  ⇑((arith a).pmul ArithmeticFunction.log * dinv a ha)

theorem dinv_one (a : ℕ → ℝ) (ha : a 1 = 1) : dinv a ha 1 = 1 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f 1) (arith_mul_dinv a ha)
  simp only [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton,
    ArithmeticFunction.one_one] at h
  rwa [arith_apply one_ne_zero, ha, one_mul] at h

/-- For `n ≥ 2`, `a^{−1}(n) = −Σ_{de = n, d ≥ 2} a(d) a^{−1}(e)`. -/
theorem dinv_eq_neg_sum (a : ℕ → ℝ) (ha : a 1 = 1) {n : ℕ} (hn : 2 ≤ n) :
    dinv a ha n = -∑ p ∈ n.divisorsAntidiagonal.filter (fun p => p.1 ≠ 1),
      arith a p.1 * dinv a ha p.2 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (arith_mul_dinv a ha)
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  rw [if_neg (by omega)] at h
  rw [← Finset.sum_filter_add_sum_filter_not n.divisorsAntidiagonal (fun p => p.1 ≠ 1)] at h
  have hone : (n.divisorsAntidiagonal.filter fun p => ¬ p.1 ≠ 1) = {(1, n)} := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, not_not, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      rw [h2, one_mul] at h1
      exact Prod.ext h2 h1
    · rintro rfl
      exact ⟨⟨one_mul n, by omega⟩, rfl⟩
  rw [hone, Finset.sum_singleton, arith_apply one_ne_zero, ha, one_mul] at h
  linarith

/-- **Absolute convergence of the Dirichlet inverse.**  If `Σ_{n≥2} |a(n)| n^{−σ} ≤ S < 1`, then
`Σ |a^{−1}(n)| n^{−σ} ≤ 1/(1 − S)`. -/
theorem sum_dinv_le (a : ℕ → ℝ) (ha : a 1 = 1) {σ S : ℝ} (hS1 : S < 1)
    (hS : ∀ N : ℕ, ∑ d ∈ Finset.Icc 2 N, |a d| * (d : ℝ) ^ (-σ) ≤ S) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, |dinv a ha n| * (n : ℝ) ^ (-σ) ≤ 1 / (1 - S) := by
  set G : ℕ → ℝ := fun n => |dinv a ha n| * (n : ℝ) ^ (-σ) with hG
  set F : ℕ → ℝ := fun d => |a d| * (d : ℝ) ^ (-σ) with hF
  have hG0 : ∀ n, 0 ≤ G n := fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hF0 : ∀ n, 0 ≤ F n := fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun d _ => hF0 d).trans (hS 0)
  -- termwise bound for `n ≥ 2`
  have hterm : ∀ n, 2 ≤ n → G n ≤ ∑ p ∈ n.divisorsAntidiagonal.filter (fun p => p.1 ≠ 1),
      F p.1 * G p.2 := by
    intro n hn
    simp only [hG, hF]
    rw [dinv_eq_neg_sum a ha hn, abs_neg]
    refine (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans (le_of_eq ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := (Finset.mem_filter.mp hp).1
    rw [Nat.mem_divisorsAntidiagonal] at hp'
    have h1 : p.1 ≠ 0 := fun h => by rw [h, zero_mul] at hp'; omega
    have h2 : p.2 ≠ 0 := fun h => by rw [h, mul_zero] at hp'; omega
    rw [abs_mul, arith_apply h1, ← hp'.1, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  -- summing the termwise bound
  have hpairs : ∑ n ∈ Finset.Icc 2 N, ∑ p ∈ n.divisorsAntidiagonal.filter (fun p => p.1 ≠ 1),
      F p.1 * G p.2 ≤ (∑ d ∈ Finset.Icc 2 N, F d) * ∑ e ∈ Finset.Icc 1 N, G e := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    rw [← Finset.sum_biUnion]
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => mul_nonneg (hF0 _) (hG0 _)
      intro p hp
      simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter,
        Nat.mem_divisorsAntidiagonal] at hp
      obtain ⟨n, ⟨hn2, hnN⟩, ⟨hpn, -⟩, hp1⟩ := hp
      have h1 : p.1 ≠ 0 := fun h => by rw [h, zero_mul] at hpn; omega
      have h2 : p.2 ≠ 0 := fun h => by rw [h, mul_zero] at hpn; omega
      have hle1 : p.1 ≤ n := Nat.le_of_dvd (by omega) ⟨p.2, hpn.symm⟩
      have hle2 : p.2 ≤ n := Nat.le_of_dvd (by omega) ⟨p.1, by rw [mul_comm]; exact hpn.symm⟩
      simp only [Finset.mem_product, Finset.mem_Icc]
      omega
    · intro n _ m _ hnm
      refine Finset.disjoint_left.mpr fun p hp hq => hnm ?_
      have h1 := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp hp).1).1
      have h2 := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp hq).1).1
      rw [← h1, ← h2]
  have hP : ∑ n ∈ Finset.Icc 1 N, G n ≤ 1 + S * ∑ n ∈ Finset.Icc 1 N, G n := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Finset.Icc_eq_empty_of_lt (show 1 > 0 by norm_num), Finset.sum_empty, mul_zero,
        add_zero]
      norm_num
    have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext n; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hG1 : G 1 = 1 := by simp [hG, dinv_one a ha]
    have hexp : ∑ n ∈ Finset.Icc 1 N, G n = 1 + ∑ n ∈ Finset.Icc 2 N, G n := by
      rw [hsplit, Finset.sum_insert (by simp), hG1]
    have h2 : ∑ n ∈ Finset.Icc 2 N, G n ≤ S * ∑ e ∈ Finset.Icc 1 N, G e :=
      (Finset.sum_le_sum fun n hn => hterm n (Finset.mem_Icc.mp hn).1).trans
        (hpairs.trans (mul_le_mul_of_nonneg_right (hS N) (Finset.sum_nonneg fun e _ => hG0 e)))
    linarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith [Finset.sum_nonneg fun n (_ : n ∈ Finset.Icc 1 N) => hG0 n]

/-- The complex sequence of a real one. -/
def cplx (f : ℕ → ℝ) : ℕ → ℂ := fun n => (f n : ℂ)

theorem lseriesSummable_of_partial {f : ℕ → ℝ} (hf0 : f 0 = 0) {σ C : ℝ}
    (hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, |f n| * (n : ℝ) ^ (-σ) ≤ C) :
    LSeriesSummable (cplx f) σ := by
  have hsum : Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-σ) := by
    refine summable_of_sum_range_le (c := C) (fun n => mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) fun N => ?_
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using (Finset.sum_nonneg fun n (_ : n ∈ Finset.Icc 1 0) =>
        mul_nonneg (abs_nonneg (f n)) (Real.rpow_nonneg (Nat.cast_nonneg n) (-σ))).trans (hC 0)
    have hr : Finset.range N = insert 0 (Finset.Icc 1 (N - 1)) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hr, Finset.sum_insert (by simp), hf0, abs_zero, zero_mul, zero_add]
    exact hC (N - 1)
  refine Summable.of_norm_bounded hsum fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, hf0]
  · rw [LSeries.norm_term_eq, if_neg hn, cplx, Complex.norm_real, Real.norm_eq_abs,
      Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- The Dirichlet inverse is absolutely summable wherever `Σ_{n≥2} |a(n)| n^{−σ} ≤ S < 1`. -/
theorem summable_dinv (a : ℕ → ℝ) (ha : a 1 = 1) {σ S : ℝ} (hS1 : S < 1)
    (hS : ∀ N : ℕ, ∑ d ∈ Finset.Icc 2 N, |a d| * (d : ℝ) ^ (-σ) ≤ S) :
    LSeriesSummable (cplx (dinv a ha)) σ :=
  lseriesSummable_of_partial (by simp) (sum_dinv_le a ha hS1 hS)

theorem norm_term_cplx {f : ℕ → ℝ} {σ : ℝ} {n : ℕ} (hn : n ≠ 0) :
    ‖LSeries.term (cplx f) σ n‖ = |f n| * (n : ℝ) ^ (-σ) := by
  rw [LSeries.norm_term_eq, if_neg hn, cplx, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- Far to the right, `Σ_{n≥2} |a(n)| n^{−σ} ≤ ½`. -/
theorem exists_tail_le_half {a : ℕ → ℝ} {σ₁ : ℝ} (h : LSeriesSummable (cplx a) σ₁) :
    ∃ σ₂, σ₁ ≤ σ₂ ∧ ∀ σ, σ₂ ≤ σ → ∀ N : ℕ,
      ∑ d ∈ Finset.Icc 2 N, |a d| * (d : ℝ) ^ (-σ) ≤ 1 / 2 := by
  set T₁ : ℝ := ∑' n, ‖LSeries.term (cplx a) σ₁ n‖ with hT₁
  have hT0 : 0 ≤ T₁ := tsum_nonneg fun n => norm_nonneg _
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨σ₁ + (2 * T₁ + 2) / Real.log 2, by have := div_nonneg (by positivity : (0 : ℝ) ≤ 2 * T₁ + 2) hl2.le; linarith,
    fun σ hσ N => ?_⟩
  have hx : (2 * T₁ + 2) / Real.log 2 ≤ σ - σ₁ := by linarith
  have hxpos : 0 ≤ σ - σ₁ := le_trans (div_nonneg (by positivity) hl2.le) hx
  have hy : 2 * T₁ + 2 ≤ Real.log 2 * (σ - σ₁) := by
    rw [div_le_iff₀ hl2] at hx; linarith
  -- `2^{−(σ − σ₁)} ≤ 1/(2T₁ + 2)`
  have hfac : (2 : ℝ) ^ (-(σ - σ₁)) ≤ 1 / (2 * T₁ + 2) := by
    rw [Real.rpow_def_of_pos two_pos, show Real.log 2 * -(σ - σ₁) = -(Real.log 2 * (σ - σ₁)) by ring,
      Real.exp_neg, ← one_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    linarith [Real.add_one_le_exp (Real.log 2 * (σ - σ₁))]
  have hterm : ∀ d ∈ Finset.Icc 2 N, |a d| * (d : ℝ) ^ (-σ) ≤
      ‖LSeries.term (cplx a) σ₁ d‖ * (1 / (2 * T₁ + 2)) := by
    intro d hd
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
    rw [norm_term_cplx hd0, show -σ = -σ₁ + -(σ - σ₁) by ring,
      Real.rpow_add (by linarith), ← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by linarith) _))
    exact (Real.rpow_le_rpow_of_nonpos two_pos hd2 (by linarith [hxpos])).trans hfac
  calc ∑ d ∈ Finset.Icc 2 N, |a d| * (d : ℝ) ^ (-σ)
      ≤ ∑ d ∈ Finset.Icc 2 N, ‖LSeries.term (cplx a) σ₁ d‖ * (1 / (2 * T₁ + 2)) :=
        Finset.sum_le_sum hterm
    _ = (∑ d ∈ Finset.Icc 2 N, ‖LSeries.term (cplx a) σ₁ d‖) * (1 / (2 * T₁ + 2)) := by
        rw [Finset.sum_mul]
    _ ≤ T₁ * (1 / (2 * T₁ + 2)) := by
        gcongr
        exact h.norm.sum_le_tsum _ fun n _ => norm_nonneg _
    _ ≤ 1 / 2 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]; linarith

/-! ### The `L`-series identities -/

theorem convolution_eq_delta (a : ℕ → ℝ) (ha : a 1 = 1) :
    LSeries.convolution (cplx a) (cplx (dinv a ha)) = LSeries.delta := by
  funext n
  have h := congrArg (fun f : ArithmeticFunction ℝ => ((f n : ℝ) : ℂ)) (arith_mul_dinv a ha)
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  rw [LSeries.convolution_def]
  simp only [LSeries.delta]
  rw [show (if n = 1 then (1 : ℂ) else 0) = (((if n = 1 then 1 else 0 : ℝ)) : ℂ) by
    split_ifs <;> simp, ← h]
  push_cast
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Nat.mem_divisorsAntidiagonal.mp hp
  have h1 : p.1 ≠ 0 := fun h0 => hp'.2 (by rw [← hp'.1, h0, zero_mul])
  simp only [cplx, arith_apply h1]

theorem lamT_eq_convolution (a : ℕ → ℝ) (ha : a 1 = 1) :
    cplx (lamT a ha) = LSeries.convolution (LSeries.logMul (cplx a)) (cplx (dinv a ha)) := by
  funext n
  rw [LSeries.convolution_def]
  simp only [cplx, lamT, ArithmeticFunction.mul_apply, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.log_apply]
  push_cast
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Nat.mem_divisorsAntidiagonal.mp hp
  have h1 : p.1 ≠ 0 := fun h0 => hp'.2 (by rw [← hp'.1, h0, zero_mul])
  rw [arith_apply h1, LSeries.logMul, ← Complex.natCast_log]
  simp only [cplx]
  ring

/-- The `L`-series identities on a half-plane of absolute convergence of `a` and `a^{−1}`. -/
theorem lseries_identities (a : ℕ → ℝ) (ha : a 1 = 1) {s : ℂ}
    (hA : LSeriesSummable (cplx a) s) (hC : LSeriesSummable (cplx (dinv a ha)) s)
    (habs : LSeries.abscissaOfAbsConv (cplx a) < s.re) :
    LSeries (cplx a) s * LSeries (cplx (dinv a ha)) s = 1 ∧
      LSeriesSummable (cplx (lamT a ha)) s ∧
      LSeries (cplx (lamT a ha)) s = -deriv (LSeries (cplx a)) s / LSeries (cplx a) s := by
  have h1 : LSeries (cplx a) s * LSeries (cplx (dinv a ha)) s = 1 := by
    rw [← LSeries_convolution' hA hC, convolution_eq_delta, LSeries_delta, Pi.one_apply]
  have hlog : LSeriesSummable (LSeries.logMul (cplx a)) s := LSeriesSummable_logMul_of_lt_re habs
  refine ⟨h1, ?_, ?_⟩
  · rw [lamT_eq_convolution]
    exact hlog.convolution hC
  · have hT0 : LSeries (cplx a) s ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact zero_ne_one h1
    rw [lamT_eq_convolution, LSeries_convolution' hlog hC, LSeries_deriv habs, neg_neg,
      eq_div_iff hT0]
    linear_combination LSeries (LSeries.logMul (cplx a)) s * h1

/-! ### The twin datum and the Herglotz function -/

/-- **A degree-`d` twin of `ζ^d`**: real coefficients with `a(1) = 1`, absolutely convergent on
`Re s > σ₀`, whose completion `(s(s − 1)Γ_ℝ(s))^d T(s)` extends to an entire function `Λ` of finite
order with `Λ(1 − s) = Λ(s)`. -/
structure TwinDatum (d : ℕ) (a : ℕ → ℝ) (σ₀ : ℝ) (Λ : ℂ → ℂ) : Prop where
  one : a 1 = 1
  summable : ∀ s : ℂ, σ₀ < s.re → LSeriesSummable (cplx a) s
  entire : Differentiable ℂ Λ
  completion : ∀ s : ℂ, σ₀ < s.re →
    Λ s = (s * (s - 1) * Complex.Gammaℝ s) ^ d * LSeries (cplx a) s
  functional_equation : ∀ s, Λ (1 - s) = Λ s
  finite_order : ∃ ρ C : ℝ, ∀ s, ‖Λ s‖ ≤ C * Real.exp (‖s‖ ^ ρ)

variable {d : ℕ} {a : ℕ → ℝ} {σ₀ : ℝ} {Λ : ℂ → ℂ}

theorem TwinDatum.abscissa_le (hD : TwinDatum d a σ₀ Λ) :
    LSeries.abscissaOfAbsConv (cplx a) ≤ σ₀ :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    hD.summable y (by simpa using hy)

/-- With every zero on the critical line, `Re Λ'/Λ ≥ 0` on `Re s > ½`. -/
theorem re_logDeriv_nonneg (hD : TwinDatum d a σ₀ Λ) (hRH : ∀ s, Λ s = 0 → s.re = 1 / 2)
    {s : ℂ} (hs : 1 / 2 < s.re) : 0 ≤ (logDeriv Λ s).re := by
  obtain ⟨C, hC0, hC⟩ := CompletionGrowth.orderOneEnvelope_of_finiteOrder_abscissa hD.entire
    hD.finite_order (ε := 1) (by simp) (fun s => by rw [hD.functional_equation, one_mul])
    (g := cplx a) hD.summable hD.completion
  have hΛ2 : Λ 2 ≠ 0 := fun h0 => by have := hRH 2 h0; norm_num at this
  have hΛs : Λ s ≠ 0 := fun h0 => by have := hRH s h0; linarith
  have hsum := CompletionZeroPairs.hasSum_logDeriv_zeroPairs hD.entire one_ne_zero
    (fun s => by rw [hD.functional_equation, one_mul]) hC0 hC hΛ2 hΛs
  have hfd : AnalyticOnNhd ℂ (fun z => Λ (z + 2)) univ :=
    (hD.entire.comp (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ
  refine (Complex.hasSum_re hsum).nonneg fun q => ?_
  set ρ := zeroCopyPoint (fun z => Λ (z + 2)) q + 2 with hρ
  have hz : Λ ρ = 0 := CompletionZeroPairs.apply_zeroCopyPoint hfd q
  have hre : ρ.re = 1 / 2 := hRH ρ hz
  have hw1 : 0 ≤ (s - ρ).re := by rw [Complex.sub_re, hre]; linarith
  have hw2 : 0 ≤ (s - (1 - ρ)).re := by
    rw [Complex.sub_re, Complex.sub_re, Complex.one_re, hre]; linarith
  have key : ∀ w : ℂ, 0 ≤ w.re → 0 ≤ (1 / w).re := fun w hw => by
    rw [one_div, Complex.inv_re]; exact div_nonneg hw (Complex.normSq_nonneg w)
  rw [show (1 / 2 : ℂ) * WeilLineIntegral.gPair ρ s =
    ((1 / 2 : ℝ) : ℂ) * WeilLineIntegral.gPair ρ s by norm_num, Complex.re_ofReal_mul]
  refine mul_nonneg (by norm_num) ?_
  rw [WeilLineIntegral.gPair, Complex.add_re]
  exact add_nonneg (key _ hw1) (key _ hw2)

/-- `Λ'/Λ = d (1/s + 1/(s − 1) + Γ_ℝ'/Γ_ℝ) + T'/T` on the half-plane of absolute convergence. -/
theorem logDeriv_eq (hD : TwinDatum d a σ₀ Λ) {s : ℂ} (hs0 : σ₀ < s.re) (hs1 : 1 < s.re)
    (hΛs : Λ s ≠ 0) :
    logDeriv Λ s = d * (WeilLineIntegral.gPair 0 s + logDeriv Complex.Gammaℝ s) +
      logDeriv (LSeries (cplx a)) s := by
  set h : ℂ → ℂ := fun z => z * (z - 1) * Complex.Gammaℝ z with hh
  have hopen : IsOpen {z : ℂ | σ₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : Λ =ᶠ[𝓝 s] fun z => h z ^ d * LSeries (cplx a) z := by
    filter_upwards [hopen.mem_nhds hs0] with z hz
    exact hD.completion z hz
  have hsre : 0 < s.re := by linarith
  have hsne0 : s ≠ 0 := fun h0 => by rw [h0] at hs1; norm_num at hs1
  have hsne1 : s - 1 ≠ 0 := fun h0 => by
    rw [sub_eq_zero] at h0; rw [h0] at hs1; norm_num at hs1
  have hG0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hGd : DifferentiableAt ℂ Complex.Gammaℝ s := Zeta23.WeilEF.differentiableAt_Gammaℝ hsre
  have hhd : DifferentiableAt ℂ h s := by
    simp only [hh]
    exact ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hGd)
  have hh0 : h s ≠ 0 := mul_ne_zero (mul_ne_zero hsne0 hsne1) hG0
  have habs : LSeries.abscissaOfAbsConv (cplx a) < s.re :=
    lt_of_le_of_lt hD.abscissa_le (by exact_mod_cast hs0)
  have hLd : DifferentiableAt ℂ (LSeries (cplx a)) s := (LSeries_hasDerivAt habs).differentiableAt
  have hEeq : Λ s = h s ^ d * LSeries (cplx a) s := hD.completion s hs0
  have hL0 : LSeries (cplx a) s ≠ 0 := by
    intro h0; apply hΛs; rw [hEeq, h0, mul_zero]
  have hlogE : logDeriv Λ s = logDeriv (fun z => h z ^ d * LSeries (cplx a) z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hlogE, logDeriv_mul (f := fun z => h z ^ d) (g := LSeries (cplx a)) s (pow_ne_zero d hh0) hL0
    (hhd.pow d) hLd, logDeriv_fun_pow hhd d]
  have hlogh : logDeriv h s = WeilLineIntegral.gPair 0 s + logDeriv Complex.Gammaℝ s := by
    have hpd : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s :=
      differentiableAt_id.mul (differentiableAt_id.sub_const 1)
    rw [show h = fun z => (fun z : ℂ => z * (z - 1)) z * Complex.Gammaℝ z from rfl,
      logDeriv_mul (f := fun z : ℂ => z * (z - 1)) (g := Complex.Gammaℝ) s
        (mul_ne_zero hsne0 hsne1) hG0 hpd hGd]
    congr 1
    rw [logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s hsne0 hsne1
      differentiableAt_id (differentiableAt_id.sub_const 1)]
    rw [logDeriv_apply, logDeriv_apply, deriv_id'', deriv_sub_const, deriv_id'']
    simp [WeilLineIntegral.gPair]
  rw [hlogh]

theorem lamT_one (a : ℕ → ℝ) (ha : a 1 = 1) : lamT a ha 1 = 0 := by
  simp [lamT, ArithmeticFunction.mul_apply, ArithmeticFunction.pmul_apply]

/-- **`λ_T = dΛ` forces `T = ζ^d`.** -/
theorem eq_zetaPow_of_lamT {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ} (ha : a 1 = 1) {σ₀ : ℝ}
    (hsum : ∀ s : ℂ, σ₀ < s.re → LSeriesSummable (cplx a) s)
    (hvM : ∀ n, 2 ≤ n → lamT a ha n = d * (ArithmeticFunction.vonMangoldt n : ℝ)) :
    ∀ s : ℂ, max σ₀ 1 < s.re → LSeries (cplx a) s = riemannZeta s ^ d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have habs : LSeries.abscissaOfAbsConv (cplx a) ≤ σ₀ :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => hsum y (by simpa using hy)
  obtain ⟨σ₂, hσ₂1, hσ₂⟩ := exists_tail_le_half (a := a) (σ₁ := σ₀ + 1) (hsum _ (by simp))
  set σ₃ : ℝ := max σ₂ 2 with hσ₃
  have hσ₃2 : σ₂ ≤ σ₃ := le_max_left _ _
  have hσ₃0 : σ₀ < σ₃ := by linarith [le_max_left σ₂ 2]
  have hσ₃1 : 1 < σ₃ := by linarith [le_max_right σ₂ 2]
  have hdinv : ∀ s : ℂ, σ₃ ≤ s.re → LSeriesSummable (cplx (dinv a ha)) s := fun s hs =>
    (summable_dinv a ha (S := 1 / 2) (by norm_num) (hσ₂ σ₃ hσ₃2)).of_re_le_re (by simpa using hs)
  have hid : ∀ s : ℂ, σ₃ ≤ s.re →
      LSeries (cplx a) s * LSeries (cplx (dinv a ha)) s = 1 ∧
        LSeriesSummable (cplx (lamT a ha)) s ∧
        LSeries (cplx (lamT a ha)) s = -deriv (LSeries (cplx a)) s / LSeries (cplx a) s :=
    fun s hs => lseries_identities a ha (hsum s (by linarith)) (hdinv s hs)
      (lt_of_le_of_lt habs (by exact_mod_cast (show σ₀ < s.re by linarith)))
  -- `T'/T = d ζ'/ζ` on `Re s > σ₃`
  set T : ℂ → ℂ := LSeries (cplx a) with hT
  have hlamv : ∀ {n : ℕ}, n ≠ 0 → cplx (lamT a ha) n =
      ((d : ℂ) • fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) n := by
    intro n hn
    simp only [Pi.smul_apply, smul_eq_mul]
    rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | h2
    · simp [cplx, lamT_one]
    · have := hvM n h2
      simp only [cplx]
      rw [this]; push_cast; ring
  have hderT : ∀ s : ℂ, σ₃ < s.re → deriv T s = T s * (d * deriv riemannZeta s / riemannZeta s) := by
    intro s hs
    obtain ⟨h1, -, h3⟩ := hid s hs.le
    have hT0 : T s ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at h1; exact zero_ne_one h1
    have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
    have hL : LSeries (cplx (lamT a ha)) s =
        (d : ℂ) * (-deriv riemannZeta s / riemannZeta s) := by
      rw [LSeries_congr hlamv s, LSeries_smul,
        ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by linarith)]
    have key : deriv T s = -(T s * LSeries (cplx (lamT a ha)) s) := by
      rw [h3]; field_simp
    rw [key, hL]
    field_simp
  -- `T/ζ^d` is constant on `Re s > σ₃`
  set U : Set ℂ := {s : ℂ | σ₃ < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt σ₃).isPreconnected
  have hζne : ∀ s ∈ U, riemannZeta s ≠ 0 := fun s hs =>
    riemannZeta_ne_zero_of_one_lt_re (by simp only [hU, mem_setOf_eq] at hs; linarith)
  have hζd : ∀ s ∈ U, DifferentiableAt ℂ riemannZeta s := fun s hs =>
    differentiableAt_riemannZeta (fun h1 => by
      simp only [hU, mem_setOf_eq] at hs; rw [h1, Complex.one_re] at hs; linarith)
  have hTd : ∀ s ∈ U, DifferentiableAt ℂ T s := fun s hs =>
    (LSeries_hasDerivAt (lt_of_le_of_lt habs
      (by simp only [hU, mem_setOf_eq] at hs; exact_mod_cast (show σ₀ < s.re by linarith)))).differentiableAt
  set Q : ℂ → ℂ := fun s => T s / riemannZeta s ^ d with hQ
  have hQd : DifferentiableOn ℂ Q U := fun s hs =>
    ((hTd s hs).div ((hζd s hs).pow d) (pow_ne_zero d (hζne s hs))).differentiableWithinAt
  have hQ' : EqOn (deriv Q) 0 U := by
    intro s hs
    have hζ0 := hζne s hs
    have h := ((hTd s hs).hasDerivAt.div ((hζd s hs).hasDerivAt.pow d) (pow_ne_zero d hζ0)).deriv
    simp only [Pi.zero_apply]
    show deriv (T / riemannZeta ^ d) s = 0
    rw [h, hderT s hs, div_eq_zero_iff]
    left
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Pi.pow_apply]
    field_simp
    ring
  have hconst : ∀ x ∈ U, ∀ y ∈ U, Q x = Q y := fun x hx y hy =>
    hUo.is_const_of_deriv_eq_zero hUc hQd hQ' hx hy
  -- `Q(x) → 1` as `x → ∞`
  have hTlim : Tendsto (fun x : ℝ => T x) atTop (𝓝 1) := by
    have h := LSeries.tendsto_atTop (f := cplx a)
      (lt_of_le_of_lt habs (EReal.coe_lt_top σ₀))
    simpa [cplx, ha] using h
  have hζlim : Tendsto (fun x : ℝ => riemannZeta x) atTop (𝓝 1) := by
    have h := LSeries.tendsto_atTop (f := 1) (lt_of_le_of_lt
      (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) fun y hy =>
        LSeriesSummable_one_iff.mpr (by simpa using hy)) (EReal.coe_lt_top 1))
    refine (h.congr' ?_).trans (by simp)
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact LSeries_one_eq_riemannZeta (by simpa using hx)
  have hQlim : Tendsto (fun x : ℝ => Q x) atTop (𝓝 1) := by
    have h := hTlim.div (hζlim.pow d) (by simp)
    rw [one_pow, div_one] at h
    exact h
  have hQ1 : ∀ s ∈ U, Q s = 1 := by
    intro s hs
    have hev : (fun x : ℝ => Q x) =ᶠ[atTop] fun _ => Q s := by
      filter_upwards [eventually_gt_atTop σ₃] with x hx
      exact hconst x (by simpa [hU] using hx) s hs
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hQlim
  have hTζ : ∀ s ∈ U, T s = riemannZeta s ^ d := fun s hs => by
    have h := hQ1 s hs
    simp only [hQ] at h
    rwa [div_eq_one_iff_eq (pow_ne_zero d (hζne s hs))] at h
  -- the identity theorem on `Re s > max σ₀ 1`
  set V : Set ℂ := {s : ℂ | max σ₀ 1 < s.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVc : IsPreconnected V := (convex_halfSpace_re_gt (max σ₀ 1)).isPreconnected
  have hTV : DifferentiableOn ℂ T V := fun s hs =>
    (LSeries_hasDerivAt (lt_of_le_of_lt habs (by
      simp only [hV, mem_setOf_eq] at hs
      exact_mod_cast (show σ₀ < s.re by linarith [le_max_left σ₀ 1])))).differentiableAt.differentiableWithinAt
  have hZV : DifferentiableOn ℂ (fun s => riemannZeta s ^ d) V := fun s hs =>
    ((differentiableAt_riemannZeta (fun h1 => by
      simp only [hV, mem_setOf_eq] at hs; rw [h1, Complex.one_re] at hs
      linarith [le_max_right σ₀ 1])).pow d).differentiableWithinAt
  have hz₀ : ((σ₃ + 1 : ℝ) : ℂ) ∈ V := by
    simp only [hV, mem_setOf_eq, Complex.ofReal_re]
    have := le_max_left σ₀ 1; have := le_max_right σ₀ 1
    rcases le_total σ₀ 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hEq := (hTV.analyticOnNhd hVo).eqOn_of_preconnected_of_eventuallyEq (hZV.analyticOnNhd hVo)
    hVc hz₀ (by
      filter_upwards [hUo.mem_nhds (show ((σ₃ + 1 : ℝ) : ℂ) ∈ U by simp [hU])] with z hz
      exact hTζ z hz)
  intro s hs
  exact hEq hs

/-- **Twin rigidity.**  If every zero of the completion `Λ` of a degree-`d` twin of `ζ^d` lies on the
critical line, then the Riemann hypothesis holds and `T = ζ^d`. -/
theorem twin_rigidity (hd : 0 < d) (hD : TwinDatum d a σ₀ Λ)
    (hRH : ∀ s, Λ s = 0 → s.re = 1 / 2) :
    RiemannHypothesis ∧ ∀ s : ℂ, max σ₀ 1 < s.re → LSeries (cplx a) s = riemannZeta s ^ d := by
  have ha := hD.one
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- the abscissa `σ₃` of the identities
  obtain ⟨σ₂, hσ₂1, hσ₂⟩ := exists_tail_le_half (a := a) (σ₁ := σ₀ + 1)
    (hD.summable _ (by simp))
  set σ₃ : ℝ := max σ₂ 2 with hσ₃
  have hσ₃2 : σ₂ ≤ σ₃ := le_max_left _ _
  have hσ₃0 : σ₀ < σ₃ := by linarith [le_max_left σ₂ 2]
  have hσ₃1 : 1 < σ₃ := by linarith [le_max_right σ₂ 2]
  have hdinv : ∀ s : ℂ, σ₃ ≤ s.re → LSeriesSummable (cplx (dinv a ha)) s := fun s hs =>
    (summable_dinv a ha (S := 1 / 2) (by norm_num) (hσ₂ σ₃ hσ₃2)).of_re_le_re (by simpa using hs)
  have hid : ∀ s : ℂ, σ₃ ≤ s.re →
      LSeries (cplx a) s * LSeries (cplx (dinv a ha)) s = 1 ∧
        LSeriesSummable (cplx (lamT a ha)) s ∧
        LSeries (cplx (lamT a ha)) s = -deriv (LSeries (cplx a)) s / LSeries (cplx a) s :=
    fun s hs => lseries_identities a ha (hD.summable s (by linarith)) (hdinv s hs)
      (lt_of_le_of_lt hD.abscissa_le (by exact_mod_cast (show σ₀ < s.re by linarith)))
  -- the weights
  set lam : ℕ → ℝ := fun n => lamT a ha n / d with hlam
  have hsl : ∀ σ : ℝ, σ₃ < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
    intro σ hσ
    have hsum := ((hid σ (by simp; linarith)).2.1).norm
    refine (hsum.div_const d).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term, hlam, Real.zero_rpow (show σ ≠ 0 by linarith)]
    · rw [norm_term_cplx hn, hlam, abs_div, abs_of_pos hdR, Real.rpow_neg (Nat.cast_nonneg n)]
      field_simp
  -- the Herglotz function
  set Φ : ℂ → ℂ := fun s => ((1 / d : ℝ) : ℂ) * logDeriv Λ s with hΦ
  have hΛne : ∀ s : ℂ, 1 / 2 < s.re → Λ s ≠ 0 := fun s hs h0 => by
    have := hRH s h0; linarith
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    have hda := (hD.entire.analyticAt s).deriv.differentiableAt
    refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
    simp only [logDeriv]
    exact hda.div (hD.entire s) (hΛne s hs)
  have hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re := fun s hs => by
    simp only [hΦ, Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) (re_logDeriv_nonneg hD hRH hs)
  have hΦeq : ∀ s : ℂ, σ₃ < s.re → Φ s = WeilHerglotz.weilFunction lam s := by
    intro s hs
    obtain ⟨h1, -, h3⟩ := hid s hs.le
    have hT0 : LSeries (cplx a) s ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact zero_ne_one h1
    have hΛs : Λ s ≠ 0 := hΛne s (by linarith)
    have hlogT : logDeriv (LSeries (cplx a)) s = -LSeries (cplx (lamT a ha)) s := by
      rw [logDeriv_apply, h3]; field_simp
    have hlamC : LSeries (WeilHerglotz.lamC lam) s =
        ((1 / d : ℝ) : ℂ) * LSeries (cplx (lamT a ha)) s := by
      rw [← LSeries_smul]
      refine LSeries_congr (fun {n} hn => ?_) s
      simp only [WeilHerglotz.lamC, Pi.smul_apply, smul_eq_mul, cplx, hlam]
      split_ifs with h2
      · push_cast; ring
      · have hn1 : n = 1 := by omega
        subst hn1
        rw [lamT_one]; simp
    simp only [hΦ]
    rw [logDeriv_eq hD (by linarith) (by linarith) hΛs, hlogT,
      WeilLineIntegral.weilFunction_eq lam (by linarith), hlamC]
    push_cast
    field_simp
    ring
  -- Weil positivity, then the uniqueness of the Weil cone
  have hW := HerglotzBridgeAnyLine.weilPositiveFull_of_herglotz_abscissa hsl hΦd hΦre hΦeq
  obtain ⟨hRHζ, hvM⟩ := WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hW
  refine ⟨hRHζ, eq_zetaPow_of_lamT hd ha hD.summable fun n hn => ?_⟩
  have := hvM n hn
  simp only [hlam] at this
  rw [div_eq_iff (by positivity)] at this
  rw [this]
  ring

end RHTower.TwinRigidity

end
