import GaloisForLFunctions.RHTower.CosineProducerLocalPortObstruction

/-!
# No finite-shift local port from the cosine producer to Ξ

Let `A_h = cos(hD)Ξ = (Ξ(z − ih) + Ξ(z + ih))/2` (`cosineProducer`).

**Theorem** (`not_exists_shift_polynomial_port_cosineProducer`). For every real `h ≠ 0`, every
finite set `S` of reals and all complex polynomials `Q_{s,k}`,
`Σ_{s ∈ S} Σ_{k < K} Q_{s,k}(t) A_h^{(k)}(t + is) ≠ Ξ(t)` for some real `t`. So `Ξ` is not obtained
from the cosine producer by finitely many imaginary translations combined with
polynomial-coefficient differential operators. This includes `h ∈ 2ℤ` and every rational `h`,
which the exponent-class argument of `CosineProducerLocalPortObstruction` does not reach.

**Proof.**
* Exact grading (`KFun.eval_part_eq_zero`). Each kernel `u^a e^{βu} Φ^{(j)}(u)` is a cusp series
  `Σ_n e^{−πn²e^{2u}} (…)`. A vanishing kernel function has every cusp mode equal to zero
  (`KFun.headN_eq_zero_of_eval_eq_zero`, by mode separation `KFun.exists_modes_tail_le`). Its
  `n`-th mode is a polynomial in `n²` whose coefficients separate the exponent `β` exactly, not
  only modulo `2`. So every `e^{βu}`-part vanishes separately.
* Annihilation (`KFun.annihilation`). A polynomial-coefficient differential operator that kills
  `c e^{βu} Φ` (`c ≠ 0`) is zero. The head at the top exponent `β + 1/2 + 2(M + 2)` is
  `4π²(−2π)^M` times the leading coefficients (`KFun.head_apply_top`, `KFun.topPoly_opPoly`).
* Corollary (`polynomial_differential_translates_independent`). The imaginary translates
  `Ξ(z + is)`, `s ∈ S`, are linearly independent over polynomial-coefficient differential
  operators. The `e^{−su}`-parts are separated by the grading, and each is annihilated.
* Extreme shift. On kernels the translate `z ↦ z + is` multiplies by `e^{−su}`, so the port has
  exponents `±h − s` and `Ξ` has exponent `0`. The largest exponent `h − min S` (or, if it is `0`,
  the smallest, `−h − max S`) comes from a single block, whose operator therefore vanishes
  (`shiftPort_extreme_coeff_eq_zero`). Induction on `S` ends with `Ξ ≡ 0` on the real line, which is
  false (`not_forall_XiC_eq_zero`).
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

noncomputable section

namespace RHTower.LocalPort

/-! ## Cusp tails from an arbitrary index -/

/-- The terms `n ≥ m` of a cusp series are `O(e^{(1/2+2d)u} e^{-πm²e^{2u}})` for `u ≥ 0`. -/
theorem exists_abs_cuspSeries_tail_from_le (R : ℝ[X]) (m : ℕ) (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, 0 ≤ u →
      |∑' n : ℕ, cuspTerm R (n + m) u| ≤ B * Real.exp ((1 / 2 + 2 * R.natDegree) * u) *
        Real.exp (-(π * (m : ℝ) ^ 2) * Real.exp (2 * u)) := by
  set d := R.natDegree with hd
  set f : ℕ → ℝ := fun k => (k : ℝ) ^ (2 * d) * Real.exp (-π * k) with hf
  have hsum : Summable fun n : ℕ => f (n + m) :=
    (summable_nat_add_iff m).mpr (Real.summable_pow_mul_exp_neg_nat_mul (2 * d) Real.pi_pos)
  set S := ∑' n : ℕ, f (n + m) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by simp only [hf]; positivity
  have hP := polyAbsBound_nonneg R
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨polyAbsBound R * 2 ^ d * Real.exp (π * m) * S, by positivity, fun u hu => ?_⟩
  set Y := Real.exp (2 * u) with hY
  have hY1 : 1 ≤ Y := Real.one_le_exp (by linarith)
  set K := polyAbsBound R * 2 ^ d * Real.exp (π * m) * Real.exp ((1 / 2 + 2 * d) * u) *
    Real.exp (-(π * (m : ℝ) ^ 2) * Y) with hK
  have hterm : ∀ n : ℕ, |cuspTerm R (n + m) u| ≤ K * f (n + m) := by
    intro n
    set k : ℝ := ((n + m : ℕ) : ℝ) with hk
    have hkm : (m : ℝ) ≤ k := by rw [hk]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hk1 : 1 ≤ k := le_trans hm1 hkm
    have hR := abs_eval_le_polyAbsBound R (show 0 ≤ k ^ 2 * Y by positivity)
    have hpoly : (1 + k ^ 2 * Y) ^ d ≤ 2 ^ d * k ^ (2 * d) * Real.exp (2 * d * u) := by
      have h1 : 1 + k ^ 2 * Y ≤ 2 * (k ^ 2 * Y) := by nlinarith
      have h2 : (2 * (k ^ 2 * Y)) ^ d = 2 ^ d * k ^ (2 * d) * Y ^ d := by
        rw [mul_pow, mul_pow, pow_mul]; ring
      have h3 : Y ^ d = Real.exp (2 * d * u) := by
        rw [hY, ← Real.exp_nat_mul]; ring_nf
      calc (1 + k ^ 2 * Y) ^ d ≤ (2 * (k ^ 2 * Y)) ^ d := pow_le_pow_left₀ (by positivity) h1 d
        _ = _ := by rw [h2, h3]
    have hexp : Real.exp (-π * (k ^ 2 * Y)) ≤
        Real.exp (π * m) * Real.exp (-(π * (m : ℝ) ^ 2) * Y) * Real.exp (-π * k) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : k - m ≤ k ^ 2 - m ^ 2 := by nlinarith
      have h2 : (k ^ 2 - m ^ 2) * 1 ≤ (k ^ 2 - m ^ 2) * Y :=
        mul_le_mul_of_nonneg_left hY1 (by nlinarith)
      nlinarith [Real.pi_pos]
    unfold cuspTerm
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have hfm : f (n + m) = k ^ (2 * d) * Real.exp (-π * k) := by simp only [hf, hk]
    rw [hfm]
    have hsplit : Real.exp ((1 / 2 + 2 * d) * u) = Real.exp (u / 2) * Real.exp (2 * d * u) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (u / 2) * |R.eval (k ^ 2 * Y)| * Real.exp (-π * (k ^ 2 * Y))
        ≤ Real.exp (u / 2) * (polyAbsBound R * (2 ^ d * k ^ (2 * d) * Real.exp (2 * d * u))) *
            (Real.exp (π * m) * Real.exp (-(π * (m : ℝ) ^ 2) * Y) * Real.exp (-π * k)) := by
          gcongr
          exact hR.trans (mul_le_mul_of_nonneg_left hpoly hP)
      _ = K * (k ^ (2 * d) * Real.exp (-π * k)) := by rw [hK, hsplit]; ring
  have hsumK : Summable fun n : ℕ => K * f (n + m) := hsum.mul_left K
  have habs : Summable fun n : ℕ => |cuspTerm R (n + m) u| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hterm hsumK
  calc |∑' n : ℕ, cuspTerm R (n + m) u| ≤ ∑' n : ℕ, |cuspTerm R (n + m) u| := by
        have := norm_tsum_le_tsum_norm (f := fun n : ℕ => cuspTerm R (n + m) u) (by
          simpa [Real.norm_eq_abs] using habs)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' n : ℕ, K * f (n + m) := habs.tsum_le_tsum hterm hsumK
    _ = _ := by rw [tsum_mul_left, hK]; ring

/-! ## The `n`-th cusp head -/

/-- The exponential polynomial carried by the `n`-th cusp term of one monomial. -/
def KTerm.headN (t : KTerm) (n : ℕ) : ExpPoly :=
  ∑ i ∈ Finset.range ((cuspDeriv^[t.j] riemannCuspPoly).natDegree + 1),
    Finsupp.single (t.β + 1 / 2 + 2 * i)
      (C (t.c * ((cuspDeriv^[t.j] riemannCuspPoly).coeff i : ℂ) * (n : ℂ) ^ (2 * i)) * X ^ t.a)

theorem KTerm.headN_eval (t : KTerm) (n : ℕ) (u : ℝ) :
    t.c * (u : ℂ) ^ t.a * cexp (t.β * u) * (cuspTerm (cuspDeriv^[t.j] riemannCuspPoly) n u : ℂ) =
      (Real.exp (-π * ((n : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) * expPolyEval (t.headN n) u := by
  unfold KTerm.headN cuspTerm
  set R := cuspDeriv^[t.j] riemannCuspPoly with hR
  rw [eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_sum, Finset.mul_sum,
    expPolyEval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [expPolyEval_single]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  push_cast
  have e1 : ((n : ℂ) ^ 2 * cexp (2 * (u : ℂ))) ^ i = (n : ℂ) ^ (2 * i) * cexp (2 * i * u) := by
    rw [mul_pow, ← pow_mul, ← Complex.exp_nat_mul]; ring_nf
  have e2 : cexp (t.β * u) * cexp (u / 2) * cexp (2 * i * u) =
      cexp ((t.β + 1 / 2 + 2 * i) * u) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  rw [e1, ← e2]
  ring


/-- The `n`-th cusp head of a kernel function. -/
def KFun.headN (F : KFun) (n : ℕ) : ExpPoly := (F.map fun t => t.headN n).sum

/-- **Mode decomposition.** A kernel function is the sum of its first `N` cusp modes, each
`e^{-πk²e^{2u}}` times an exponential polynomial, up to `O(e^{Cu}e^{-π(N+1)²e^{2u}})` for
`u ≥ 0`. -/
theorem KFun.exists_modes_tail_le (F : KFun) (N : ℕ) : ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
    ∀ u : ℝ, 0 ≤ u → ‖KFun.eval F u - ∑ k ∈ Finset.range N,
        (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
          expPolyEval (KFun.headN F (k + 1)) u‖ ≤
      K * Real.exp (C * u) * Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) := by
  induction F with
  | nil =>
    refine ⟨0, 0, le_rfl, le_rfl, fun u _ => ?_⟩
    simp [KFun.headN, expPolyEval_zero]
  | cons t F ih =>
    obtain ⟨K₁, C₁, hK₁, hC₁, h₁⟩ := ih
    set R := cuspDeriv^[t.j] riemannCuspPoly with hR
    obtain ⟨B, hB, hBle⟩ := exists_abs_cuspSeries_tail_from_le R (N + 1) (by omega)
    set C₀ : ℝ := t.a + |t.β| + (1 / 2 + 2 * R.natDegree) with hC₀
    refine ⟨‖t.c‖ * B + K₁, max C₀ C₁, by positivity, le_max_of_le_right hC₁, fun u hu => ?_⟩
    have hsumR := summable_cuspTerm R u
    have hsplitR : cuspSeries R u = ∑ k ∈ Finset.range N, cuspTerm R (k + 1) u +
        ∑' n : ℕ, cuspTerm R (n + (N + 1)) u := by
      unfold cuspSeries
      rw [← hsumR.sum_add_tsum_nat_add N]
      rfl
    have hterm : ‖KTerm.eval t u - ∑ k ∈ Finset.range N,
          (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
            expPolyEval (t.headN (k + 1)) u‖ ≤
          ‖t.c‖ * B * Real.exp (C₀ * u) *
            Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) := by
        have hsplit : KTerm.eval t u = ∑ k ∈ Finset.range N,
            t.c * (u : ℂ) ^ t.a * cexp (t.β * u) * (cuspTerm R (k + 1) u : ℂ) +
            t.c * (u : ℂ) ^ t.a * cexp (t.β * u) *
              ((∑' n : ℕ, cuspTerm R (n + (N + 1)) u : ℝ) : ℂ) := by
          unfold KTerm.eval riemannKernelDeriv
          rw [← hR, hsplitR]
          push_cast
          rw [mul_add, Finset.mul_sum]
        rw [hsplit]
        have hmodes : ∑ k ∈ Finset.range N,
            t.c * (u : ℂ) ^ t.a * cexp (t.β * u) * (cuspTerm R (k + 1) u : ℂ) =
            ∑ k ∈ Finset.range N,
              (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
                expPolyEval (t.headN (k + 1)) u :=
          Finset.sum_congr rfl fun k _ => KTerm.headN_eval t (k + 1) u
        rw [hmodes, add_sub_cancel_left, norm_mul, norm_mul, norm_mul, norm_pow,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hu]
        have hpow : u ^ t.a ≤ Real.exp (t.a * u) := by
          calc u ^ t.a ≤ Real.exp u ^ t.a :=
                pow_le_pow_left₀ hu (by linarith [Real.add_one_le_exp u]) _
            _ = Real.exp (t.a * u) := by rw [← Real.exp_nat_mul]
        have hexp : ‖cexp (t.β * u)‖ ≤ Real.exp (|t.β| * u) := by
          rw [show (t.β : ℂ) * u = ((t.β * u : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
          exact Real.exp_le_exp.mpr (by nlinarith [le_abs_self t.β])
        have ht := hBle u hu
        calc ‖t.c‖ * u ^ t.a * ‖cexp (t.β * u)‖ * |∑' n : ℕ, cuspTerm R (n + (N + 1)) u|
            ≤ ‖t.c‖ * Real.exp (t.a * u) * Real.exp (|t.β| * u) *
                (B * Real.exp ((1 / 2 + 2 * R.natDegree) * u) *
                  Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u))) := by gcongr
          _ = ‖t.c‖ * B * Real.exp (C₀ * u) *
                Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) := by
              rw [hC₀, show (t.a + |t.β| + (1 / 2 + 2 * R.natDegree)) * u =
                t.a * u + |t.β| * u + (1 / 2 + 2 * R.natDegree) * u by ring,
                Real.exp_add, Real.exp_add]; ring
    have hrest := h₁ u hu
    have hhead : ∀ k, KFun.headN (t :: F) k = t.headN k + KFun.headN F k := fun k => by
      simp [KFun.headN]
    have hE0 : 0 ≤ Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) :=
      (Real.exp_pos _).le
    have hm1 : Real.exp (C₀ * u) ≤ Real.exp (max C₀ C₁ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
    have hm2 : Real.exp (C₁ * u) ≤ Real.exp (max C₀ C₁ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hu)
    have hsum_split : ∑ k ∈ Finset.range N,
        (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
          expPolyEval (KFun.headN (t :: F) (k + 1)) u =
        ∑ k ∈ Finset.range N,
          (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
            expPolyEval (t.headN (k + 1)) u +
        ∑ k ∈ Finset.range N,
          (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
            expPolyEval (KFun.headN F (k + 1)) u := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hhead, expPolyEval_add]; ring
    rw [KFun.eval_cons, hsum_split]
    calc ‖KTerm.eval t u + KFun.eval F u - (∑ k ∈ Finset.range N,
          (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
            expPolyEval (t.headN (k + 1)) u +
          ∑ k ∈ Finset.range N,
            (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
              expPolyEval (KFun.headN F (k + 1)) u)‖
        = ‖(KTerm.eval t u - ∑ k ∈ Finset.range N,
              (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
                expPolyEval (t.headN (k + 1)) u) +
            (KFun.eval F u - ∑ k ∈ Finset.range N,
              (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
                expPolyEval (KFun.headN F (k + 1)) u)‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hterm hrest)
      _ ≤ (‖t.c‖ * B + K₁) * Real.exp (max C₀ C₁ * u) *
            Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) := by
          have := mul_le_mul_of_nonneg_right hm1 (mul_nonneg (mul_nonneg (norm_nonneg t.c) hB) hE0)
          have := mul_le_mul_of_nonneg_right hm2 (mul_nonneg hK₁ hE0)
          nlinarith


/-- **Mode separation.** If a kernel function vanishes identically, so does each of its cusp
heads. -/
theorem KFun.headN_eq_zero_of_eval_eq_zero (F : KFun) (hF : ∀ u : ℝ, KFun.eval F u = 0)
    (n : ℕ) : KFun.headN F (n + 1) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨K, C, hK, hC, htail⟩ := KFun.exists_modes_tail_le F (n + 1)
    refine eq_zero_of_tendsto_mul_cexp _ fun M => ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hc : 0 < π * (2 * n + 3) := by positivity
    have hlim := (tendsto_exp_linear_sub_exp_two_mul (C := C + M) hc).const_mul K
    rw [mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with u hu
    have h := htail u hu
    have hprev : ∑ k ∈ Finset.range n,
        (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
          expPolyEval (KFun.headN F (k + 1)) u = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [ih k (Finset.mem_range.mp hk), expPolyEval_zero, mul_zero]
    rw [hF u, Finset.sum_range_succ, hprev, zero_add, zero_sub, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    set Y := Real.exp (2 * u) with hY
    have hsplit : Real.exp (-(π * ((n + 1 + 1 : ℕ) : ℝ) ^ 2) * Y) =
        Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) * Real.exp (-(π * (2 * n + 3)) * Y) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hsplit] at h
    have hE := Real.exp_pos (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y))
    have h2 : Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) *
          ‖expPolyEval (KFun.headN F (n + 1)) u‖ ≤
        Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) *
          (K * Real.exp (C * u) * Real.exp (-(π * (2 * n + 3)) * Y)) := by
      have e : K * Real.exp (C * u) * (Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) *
          Real.exp (-(π * (2 * n + 3)) * Y)) = Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) *
          (K * Real.exp (C * u) * Real.exp (-(π * (2 * n + 3)) * Y)) := by ring
      linarith [h, e]
    have h' := le_of_mul_le_mul_left h2 hE
    rw [norm_mul, show (M : ℂ) * u = ((M * u : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    calc ‖expPolyEval (KFun.headN F (n + 1)) u‖ * Real.exp (M * u)
        ≤ K * Real.exp (C * u) * Real.exp (-(π * (2 * n + 3)) * Y) * Real.exp (M * u) :=
          mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
      _ = K * Real.exp ((C + M) * u - π * (2 * n + 3) * Real.exp (2 * u)) := by
          rw [show (C + M) * u - π * (2 * n + 3) * Real.exp (2 * u) =
            C * u + -(π * (2 * n + 3)) * Y + M * u by rw [hY]; ring, Real.exp_add, Real.exp_add]
          ring


/-! ## Exact grading by the exponential `e^{βu}` -/

open Classical in
/-- The monomials of `F` with exponential `e^{βu}`. -/
def KFun.part (β : ℝ) (F : KFun) : KFun := F.filter fun t => t.β = β

/-- A degree bound for all cusp polynomials occurring in `F`. -/
def KFun.degBound (F : KFun) : ℕ :=
  (F.map fun t => (cuspDeriv^[t.j] riemannCuspPoly).natDegree + 1).sum

theorem KFun.natDegree_lt_degBound {F : KFun} {t : KTerm} (ht : t ∈ F) :
    (cuspDeriv^[t.j] riemannCuspPoly).natDegree < KFun.degBound F := by
  have := List.le_sum_of_mem (List.mem_map_of_mem
    (f := fun t : KTerm => (cuspDeriv^[t.j] riemannCuspPoly).natDegree + 1) ht)
  unfold KFun.degBound; omega

open Classical in
theorem list_sum_map_filter {α M : Type*} [AddCommMonoid M] (L : List α) (p : α → Prop)
    (f : α → M) :
    ((L.filter fun a => p a).map f).sum = (L.map fun a => if p a then f a else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases hp : p a
    · simp [hp, ih]
    · simp [hp, ih]

theorem list_sum_tsum_swap {α : Type*} (L : List α) (g : α → ℕ → ℂ) (hg : ∀ a, Summable (g a)) :
    (L.map fun a => ∑' m, g a m).sum = ∑' m, (L.map fun a => g a m).sum ∧
      Summable fun m => (L.map fun a => g a m).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, (hg a).add h2⟩
    simp only [List.map_cons, List.sum_cons]
    rw [h1, ← (hg a).tsum_add h2]

theorem finset_sum_list_sum_swap {α ι M : Type*} [AddCommMonoid M] (L : List α) (s : Finset ι)
    (f : ι → α → M) :
    ∑ i ∈ s, (L.map (f i)).sum = (L.map fun a => ∑ i ∈ s, f i a).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [Finset.sum_add_distrib, ih]

theorem polynomial_eval_list_sum {R : Type*} [CommSemiring R] (L : List R[X]) (x : R) :
    L.sum.eval x = (L.map fun p => p.eval x).sum := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

theorem polynomial_coeff_list_sum {R : Type*} [Semiring R] (L : List R[X]) (i : ℕ) :
    L.sum.coeff i = (L.map fun p => p.coeff i).sum := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

theorem finsupp_list_sum_apply {α M : Type*} [AddCommMonoid M] (L : List (α →₀ M)) (a : α) :
    L.sum a = (L.map fun f => f a).sum := by
  induction L with
  | nil => simp
  | cons f L ih => simp [ih]

open Classical in
/-- **Exact grading.** If a kernel function vanishes identically, so does each of its
`e^{βu}`-parts. -/
theorem KFun.eval_part_eq_zero (F : KFun) (hF : ∀ u : ℝ, KFun.eval F u = 0) (β u : ℝ) :
    KFun.eval (KFun.part β F) u = 0 := by
  set D := KFun.degBound F with hD
  set P : KTerm → ℝ[X] := fun t => cuspDeriv^[t.j] riemannCuspPoly with hP
  have hdeg : ∀ t ∈ F, (P t).natDegree < D := fun t ht => KFun.natDegree_lt_degBound ht
  -- the coefficient polynomials of the `β`-part
  set w : ℕ → ℂ[X] := fun i =>
    (F.map fun t => if t.β = β then C (t.c * ((P t).coeff i : ℂ)) * X ^ t.a else 0).sum with hw
  have hsep := KFun.headN_eq_zero_of_eval_eq_zero F hF
  have hw0 : ∀ i, w i = 0 := by
    intro i
    by_cases hiD : D ≤ i
    · simp only [hw]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      have hc : (P t).coeff i = 0 :=
        coeff_eq_zero_of_natDegree_lt ((hdeg t ht).trans_le hiD)
      simp [hc]
    · have hiD' : i < D := not_le.mp hiD
      set γ : ℝ := β + 1 / 2 + 2 * i with hγ
      set g : KTerm → Polynomial ℂ[X] := fun t => ∑ i' ∈ Finset.range D,
        if t.β + 1 / 2 + 2 * i' = γ then
          Polynomial.C (C (t.c * ((P t).coeff i' : ℂ)) * X ^ t.a) * Polynomial.X ^ i'
        else 0 with hg
      set Pz : Polynomial ℂ[X] := (F.map g).sum with hPz
      -- evaluation at `n²` is the `n`-th head at `γ`
      have hterm : ∀ t ∈ F, ∀ n : ℕ, (g t).eval (C ((n : ℂ) ^ 2)) = t.headN n γ := by
        intro t ht n
        simp only [hg, KTerm.headN]
        rw [Polynomial.eval_finsetSum, Finsupp.finsetSum_apply,
          ← Finset.sum_subset (Finset.range_subset_range.mpr (hdeg t ht))]
        · refine Finset.sum_congr rfl fun i' _ => ?_
          rw [Finsupp.single_apply]
          by_cases h : t.β + 1 / 2 + 2 * (i' : ℝ) = γ
          · rw [if_pos h, if_pos h, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
              Polynomial.eval_X, ← map_pow, ← pow_mul]
            simp only [hP, map_mul]
            ring
          · rw [if_neg h, if_neg h, Polynomial.eval_zero]
        · intro i' _ hi'
          have hcP : (P t).coeff i' = 0 := coeff_eq_zero_of_natDegree_lt
            (by simpa [Finset.mem_range] using hi')
          split_ifs <;> simp [hcP]
      have heval : ∀ n : ℕ, Pz.eval (C ((n : ℂ) ^ 2)) = KFun.headN F n γ := by
        intro n
        rw [hPz, polynomial_eval_list_sum, KFun.headN, finsupp_list_sum_apply, List.map_map,
          List.map_map]
        congr 1
        refine List.map_congr_left fun t ht => ?_
        exact hterm t ht n
      have hroot : ∀ n : ℕ, Pz.IsRoot (C (((n + 1 : ℕ) : ℂ) ^ 2)) := by
        intro n
        rw [Polynomial.IsRoot.def, heval, hsep n, Finsupp.coe_zero, Pi.zero_apply]
      have hPz0 : Pz = 0 := by
        refine Polynomial.eq_zero_of_infinite_isRoot Pz ?_
        refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => C (((n + 1 : ℕ) : ℂ) ^ 2))
          ?_ hroot
        intro a b hab
        simp only [C_inj] at hab
        have h1 : (a + 1) ^ 2 = (b + 1) ^ 2 := by exact_mod_cast hab
        have := Nat.pow_left_injective (by norm_num : 2 ≠ 0) h1
        omega
      have hcoeff : Pz.coeff i = w i := by
        rw [hPz, polynomial_coeff_list_sum, hw, List.map_map]
        congr 1
        refine List.map_congr_left fun t _ => ?_
        simp only [Function.comp_apply, hg]
        rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
        · by_cases h : t.β = β
          · have h' : t.β + 1 / 2 + 2 * (i : ℝ) = γ := by rw [hγ, h]
            rw [if_pos h', if_pos h, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
          · have h' : ¬ t.β + 1 / 2 + 2 * (i : ℝ) = γ := by
              rw [hγ]; intro hh; exact h (by linarith)
            rw [if_neg h', if_neg h, Polynomial.coeff_zero]
        · intro i' _ hi'
          split_ifs
          · rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hi')]
          · rw [Polynomial.coeff_zero]
        · intro hi; exact absurd (Finset.mem_range.mpr hiD') hi
      rw [← hcoeff, hPz0, Polynomial.coeff_zero]
  -- the `β`-part, mode by mode
  set gm : KTerm → ℕ → ℂ := fun t m => if t.β = β then
      t.c * (u : ℂ) ^ t.a * cexp (t.β * u) * (cuspTerm (P t) (m + 1) u : ℂ) else 0 with hgm
  have hsum : ∀ t, Summable (gm t) := by
    intro t
    by_cases h : t.β = β
    · simp only [hgm, h, if_true]
      exact (Complex.summable_ofReal.mpr (summable_cuspTerm (P t) u)).mul_left _
    · simp only [hgm, h, if_false]
      exact summable_zero
  have hmon : ∀ t, (if t.β = β then KTerm.eval t u else 0) = ∑' m, gm t m := by
    intro t
    by_cases h : t.β = β
    · simp only [hgm, h, if_true]
      unfold KTerm.eval riemannKernelDeriv cuspSeries
      rw [Complex.ofReal_tsum, ← tsum_mul_left, h]
    · simp [hgm, h]
  have hmode : ∀ m, (F.map fun t => gm t m).sum = 0 := by
    intro m
    set x : ℝ := ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) with hx
    set K : ℂ := cexp (β * u) * (Real.exp (u / 2) : ℂ) * (Real.exp (-π * x) : ℂ) with hK
    have hpt : ∀ t ∈ F, gm t m = K * ∑ i ∈ Finset.range D, (x : ℂ) ^ i *
        (if t.β = β then t.c * ((P t).coeff i : ℂ) * (u : ℂ) ^ t.a else 0) := by
      intro t ht
      by_cases h : t.β = β
      · simp only [hgm, h, if_true]
        unfold cuspTerm
        rw [← hx, eval_eq_sum_range' (hdeg t ht)]
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hK]
        push_cast
        ring
      · simp [hgm, h]
    have hwi : ∀ i, (F.map fun t =>
        (if t.β = β then t.c * ((P t).coeff i : ℂ) * (u : ℂ) ^ t.a else 0)).sum = 0 := by
      intro i
      have h0 := congrArg (fun q : ℂ[X] => q.eval (u : ℂ)) (hw0 i)
      simp only [Polynomial.eval_zero] at h0
      have hev : (w i).eval (u : ℂ) = (F.map fun t =>
          (if t.β = β then C (t.c * ((P t).coeff i : ℂ)) * X ^ t.a else 0).eval (u : ℂ)).sum := by
        simp only [hw]
        rw [polynomial_eval_list_sum, List.map_map]
        rfl
      rw [hev] at h0
      refine Eq.trans ?_ h0
      congr 1
      refine List.map_congr_left fun t _ => ?_
      by_cases h : t.β = β
      · rw [if_pos h, if_pos h, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
      · rw [if_neg h, if_neg h, Polynomial.eval_zero]
    rw [List.map_congr_left hpt, List.sum_map_mul_left, ← finset_sum_list_sum_swap]
    simp only [List.sum_map_mul_left, hwi, mul_zero, Finset.sum_const_zero]
  rw [KFun.part, KFun.eval, list_sum_map_filter, List.map_congr_left (fun t _ => hmon t),
    (list_sum_tsum_swap F gm hsum).1]
  simp [hmode]

/-! ## Annihilation: the top cusp coefficient -/

/-- All monomials of `F` have kernel-derivative order at most `J`. -/
def KFun.JLe (J : ℕ) (F : KFun) : Prop := ∀ t ∈ F, t.j ≤ J

/-- The monomials of order exactly `J`, as a polynomial in `u`. -/
def KFun.topPoly (J : ℕ) (F : KFun) : ℂ[X] :=
  (F.map fun t => if t.j = J then C t.c * X ^ t.a else 0).sum

theorem KFun.topPoly_append (J : ℕ) (F G : KFun) :
    KFun.topPoly J (F ++ G) = KFun.topPoly J F + KFun.topPoly J G := by
  simp [KFun.topPoly, List.map_append, List.sum_append]

theorem KFun.topPoly_flatMap (J : ℕ) (L : List ℕ) (G : ℕ → KFun) :
    KFun.topPoly J (L.flatMap G) = (L.map fun m => KFun.topPoly J (G m)).sum := by
  induction L with
  | nil => simp [KFun.topPoly]
  | cons m L ih => rw [List.flatMap_cons, KFun.topPoly_append, ih, List.map_cons, List.sum_cons]

theorem KFun.topPoly_smul (J : ℕ) (c : ℂ) (F : KFun) :
    KFun.topPoly J (KFun.smul c F) = C c * KFun.topPoly J F := by
  induction F with
  | nil => simp [KFun.topPoly, KFun.smul]
  | cons t F ih =>
    simp only [KFun.smul, KFun.topPoly, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    congr 1
    split_ifs <;> simp [map_mul, mul_assoc]

theorem KFun.topPoly_eq_zero_of_JLe {J M : ℕ} {F : KFun} (hF : KFun.JLe J F) (hJM : J < M) :
    KFun.topPoly M F = 0 := by
  unfold KFun.topPoly
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  have : t.j ≠ M := by have := hF t ht; omega
  simp [this]

theorem KFun.JLe.mono {J J' : ℕ} {F : KFun} (hF : KFun.JLe J F) (h : J ≤ J') : KFun.JLe J' F :=
  fun t ht => (hF t ht).trans h

theorem KFun.JLe.smul {J : ℕ} {F : KFun} (hF : KFun.JLe J F) (c : ℂ) :
    KFun.JLe J (KFun.smul c F) := by
  intro t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  exact hF t' ht'

theorem KFun.JLe.mulIU {J : ℕ} {F : KFun} (hF : KFun.JLe J F) : KFun.JLe J (KFun.mulIU F) := by
  intro t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  exact hF t' ht'

theorem KFun.JLe.iterate_mulIU_aux {c : ℂ} {β : ℝ} (k : ℕ) :
    KFun.JLe 0 (KFun.mulIU^[k] [⟨c, 0, β, 0⟩]) := by
  induction k with
  | zero => intro t ht; simp at ht; subst ht; simp
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.mulIU

theorem KFun.JLe.iD {J : ℕ} {F : KFun} (hF : KFun.JLe J F) : KFun.JLe (J + 1) (KFun.iD F) := by
  intro t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  obtain ⟨t'', ht'', hm⟩ := List.mem_flatMap.mp ht'
  have h := hF t'' ht''
  simp only [KTerm.d, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;> simp <;> omega

theorem KFun.JLe.iterate_iD {J : ℕ} {F : KFun} (hF : KFun.JLe J F) (m : ℕ) :
    KFun.JLe (J + m) (KFun.iD^[m] F) := by
  induction m with
  | zero => simpa using hF
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.iD

theorem KFun.topPoly_iD {J : ℕ} {F : KFun} (hF : KFun.JLe J F) :
    KFun.topPoly (J + 1) (KFun.iD F) = C I * KFun.topPoly J F := by
  unfold KFun.iD
  rw [KFun.topPoly_smul]
  congr 1
  induction F with
  | nil => simp [KFun.topPoly, KFun.d]
  | cons t F ih =>
    have hFt : KFun.JLe J F := fun t' ht' => hF t' (List.mem_cons_of_mem _ ht')
    have htJ := hF t List.mem_cons_self
    simp only [KFun.d, List.flatMap_cons] at ih ⊢
    rw [KFun.topPoly_append, ih hFt]
    simp only [KFun.topPoly, List.map_cons, List.sum_cons, KTerm.d, List.map_nil, List.sum_nil,
      add_zero]
    have h1 : t.j ≠ J + 1 := by omega
    by_cases h2 : t.j = J
    · simp [h2]
    · simp [h1, h2]

theorem KFun.topPoly_iterate_iD {F : KFun} (hF : KFun.JLe 0 F) (m : ℕ) :
    KFun.topPoly m (KFun.iD^[m] F) = C (I ^ m) * KFun.topPoly 0 F := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', KFun.topPoly_iD (by simpa using hF.iterate_iD m), ih]
    rw [pow_succ, map_mul]; ring

theorem KFun.JLe.opPoly {F : KFun} (hF : KFun.JLe 0 F) (q : ℂ[X]) :
    KFun.JLe q.natDegree (KFun.opPoly q F) := by
  intro t ht
  obtain ⟨m, hm, ht'⟩ := List.mem_flatMap.mp ht
  have hmq : m ≤ q.natDegree := by have := List.mem_range.mp hm; omega
  have := ((hF.iterate_iD m).smul (q.coeff m)) t ht'
  omega

theorem KFun.topPoly_opPoly {F : KFun} (hF : KFun.JLe 0 F) (q : ℂ[X]) {M : ℕ}
    (hM : q.natDegree ≤ M) :
    KFun.topPoly M (KFun.opPoly q F) = C (q.coeff M * I ^ M) * KFun.topPoly 0 F := by
  unfold KFun.opPoly
  rw [KFun.topPoly_flatMap]
  rcases hM.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt, zero_mul, map_zero, zero_mul]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    have hmM : m < M := by have := List.mem_range.mp hm; omega
    exact KFun.topPoly_eq_zero_of_JLe ((hF.iterate_iD m).smul _) (by simpa using hmM)
  · subst heq
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have h0 : (List.map (fun m => KFun.topPoly q.natDegree
        (KFun.smul (q.coeff m) (KFun.iD^[m] F))) (List.range q.natDegree)).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      exact KFun.topPoly_eq_zero_of_JLe ((hF.iterate_iD m).smul _)
        (by simpa using List.mem_range.mp hm)
    rw [h0, zero_add, KFun.topPoly_smul, KFun.topPoly_iterate_iD hF, ← mul_assoc, ← map_mul]

/-- The top coefficient `4π²(-2π)^J ≠ 0` of the cusp polynomial of `Φ^{(J)}`. -/
theorem cuspPoly_coeff_top_ne_zero (J : ℕ) :
    (cuspDeriv^[J] riemannCuspPoly).coeff (J + 2) ≠ 0 := by
  have h := coeff_riemannKernelPoly_top J
  unfold riemannKernelPoly at h
  rw [h]
  have := Real.pi_pos
  exact mul_ne_zero (by positivity) (pow_ne_zero _ (by linarith))

theorem KTerm.head_apply_top (t : KTerm) {J : ℕ} (hj : t.j ≤ J) :
    t.head (t.β + 1 / 2 + 2 * ((J + 2 : ℕ) : ℝ)) =
      C ((cuspDeriv^[J] riemannCuspPoly).coeff (J + 2) : ℂ) *
        (if t.j = J then C t.c * X ^ t.a else 0) := by
  unfold KTerm.head
  rw [Finsupp.finsetSum_apply]
  set R := cuspDeriv^[t.j] riemannCuspPoly with hR
  have hcoeff : (R.coeff (J + 2) : ℂ) = if t.j = J then
      ((cuspDeriv^[J] riemannCuspPoly).coeff (J + 2) : ℂ) else 0 := by
    split_ifs with h
    · rw [hR, h]
    · have hdeg := natDegree_riemannKernelPoly_le t.j
      unfold riemannKernelPoly at hdeg
      rw [← hR] at hdeg
      rw [coeff_eq_zero_of_natDegree_lt (by omega), Complex.ofReal_zero]
  have hsingle : ∀ i ∈ Finset.range (R.natDegree + 1),
      (Finsupp.single (t.β + 1 / 2 + 2 * (i : ℝ)) (C (t.c * (R.coeff i : ℂ)) * X ^ t.a))
        (t.β + 1 / 2 + 2 * ((J + 2 : ℕ) : ℝ)) =
      if i = J + 2 then C (t.c * (R.coeff i : ℂ)) * X ^ t.a else 0 := by
    intro i _
    rw [Finsupp.single_apply]
    by_cases h : i = J + 2
    · subst h; simp
    · have : t.β + 1 / 2 + 2 * (i : ℝ) ≠ t.β + 1 / 2 + 2 * ((J + 2 : ℕ) : ℝ) := by
        intro hh
        have : (i : ℝ) = ((J + 2 : ℕ) : ℝ) := by linarith
        exact h (by exact_mod_cast this)
      rw [if_neg this, if_neg h]
  rw [Finset.sum_congr rfl hsingle, Finset.sum_ite_eq']
  by_cases hmem : J + 2 ∈ Finset.range (R.natDegree + 1)
  · rw [if_pos hmem]
    by_cases h : t.j = J
    · have hc : (R.coeff (J + 2) : ℂ) = ((cuspDeriv^[J] riemannCuspPoly).coeff (J + 2) : ℂ) := by
        rw [hcoeff, if_pos h]
      rw [if_pos h, hc, map_mul]
      ring
    · have hc : (R.coeff (J + 2) : ℂ) = 0 := by rw [hcoeff, if_neg h]
      rw [if_neg h, hc, mul_zero, map_zero, zero_mul, mul_zero]
  · rw [if_neg hmem]
    by_cases h : t.j = J
    · exfalso
      have hR0 : R.coeff (J + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by
        simp only [Finset.mem_range, not_lt] at hmem; omega)
      subst h
      exact cuspPoly_coeff_top_ne_zero t.j hR0
    · rw [if_neg h, mul_zero]

/-- For a kernel function with a single exponential `e^{βu}` and orders `≤ J`, the head at the
top exponent `β + 1/2 + 2(J+2)` is the top polynomial times `4π²(-2π)^J`. -/
theorem KFun.head_apply_top {F : KFun} {β : ℝ} {J : ℕ} (hβ : KFun.BetaIn {β} F)
    (hJ : KFun.JLe J F) :
    KFun.head F (β + 1 / 2 + 2 * ((J + 2 : ℕ) : ℝ)) =
      C ((cuspDeriv^[J] riemannCuspPoly).coeff (J + 2) : ℂ) * KFun.topPoly J F := by
  induction F with
  | nil => simp [KFun.head, KFun.topPoly]
  | cons t F ih =>
    have hβt : t.β = β := hβ t List.mem_cons_self
    have hF : KFun.BetaIn {β} F := fun t' ht' => hβ t' (List.mem_cons_of_mem _ ht')
    have hJF : KFun.JLe J F := fun t' ht' => hJ t' (List.mem_cons_of_mem _ ht')
    have hhead : KFun.head (t :: F) = t.head + KFun.head F := by simp [KFun.head]
    rw [hhead, Finsupp.add_apply, ih hF hJF, ← hβt,
      KTerm.head_apply_top t (hJ t List.mem_cons_self)]
    simp only [KFun.topPoly, List.map_cons, List.sum_cons]
    ring

theorem KFun.topPoly_base (c : ℂ) (β : ℝ) (k : ℕ) :
    KFun.topPoly 0 (KFun.mulIU^[k] [⟨c, 0, β, 0⟩]) = C (I ^ k * c) * X ^ k := by
  have h : KFun.mulIU^[k] [⟨c, 0, β, 0⟩] = [⟨I ^ k * c, k, β, 0⟩] := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [KFun.mulIU, pow_succ]
      ring
  rw [h]
  simp [KFun.topPoly]

theorem KFun.JLe_base (c : ℂ) (β : ℝ) (k : ℕ) : KFun.JLe 0 (KFun.mulIU^[k] [⟨c, 0, β, 0⟩]) :=
  KFun.JLe.iterate_mulIU_aux k

/-- **Annihilation.** If the polynomial-coefficient differential operator `Σ_k Q_k(z) D^k`, read
on kernels, annihilates the monomial `c e^{βu} Φ(u)` (`c ≠ 0`), all `Q_k` vanish. -/
theorem KFun.annihilation {c : ℂ} (hc : c ≠ 0) (β : ℝ) (K : ℕ) (Q : ℕ → ℂ[X])
    (hH : ∀ u : ℝ, KFun.eval ((List.range K).flatMap fun k =>
      KFun.opPoly (Q k) (KFun.mulIU^[k] [⟨c, 0, β, 0⟩])) u = 0) :
    ∀ k < K, Q k = 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨k₀, hk₀K, hk₀⟩ := hne
  set T := (Finset.range K).filter fun k => Q k ≠ 0 with hT
  have hTne : T.Nonempty := ⟨k₀, by simp [hT, hk₀K, hk₀]⟩
  obtain ⟨kM, hkMT, hkMmax⟩ := T.exists_max_image (fun k => (Q k).natDegree) hTne
  set M := (Q kM).natDegree with hM
  have hkM : kM < K ∧ Q kM ≠ 0 := by simpa [hT] using hkMT
  have hdegM : ∀ k < K, (Q k).natDegree ≤ M := by
    intro k hk
    by_cases hq : Q k = 0
    · simp [hq]
    · exact hkMmax k (by simp [hT, hk, hq])
  set H := (List.range K).flatMap fun k =>
    KFun.opPoly (Q k) (KFun.mulIU^[k] [⟨c, 0, β, 0⟩]) with hHdef
  have hbase : ∀ k, KFun.BetaIn {β} (KFun.mulIU^[k] [⟨c, 0, β, 0⟩]) := fun k =>
    KFun.BetaIn.iterate_mulIU (fun t ht => by simp at ht; subst ht; simp) k
  have hβH : KFun.BetaIn {β} H := KFun.BetaIn.flatMap fun k => (hbase k).opPoly (Q k)
  have hJH : KFun.JLe M H := by
    intro t ht
    obtain ⟨k, hk, ht'⟩ := List.mem_flatMap.mp ht
    exact ((KFun.JLe_base c β k).opPoly (Q k)).mono (hdegM k (List.mem_range.mp hk)) t ht'
  have hhead := KFun.head_eq_zero_of_eval_eq_zero H hH
  have htop := KFun.head_apply_top hβH hJH
  rw [hhead, Finsupp.coe_zero, Pi.zero_apply] at htop
  have hC : C ((cuspDeriv^[M] riemannCuspPoly).coeff (M + 2) : ℂ) ≠ 0 := by
    rw [Ne, C_eq_zero, Complex.ofReal_eq_zero]
    exact cuspPoly_coeff_top_ne_zero M
  have hP0 : KFun.topPoly M H = 0 :=
    (mul_eq_zero.mp htop.symm).resolve_left hC
  have hsum : KFun.topPoly M H = ∑ k ∈ Finset.range K,
      C ((Q k).coeff M * I ^ M * (I ^ k * c)) * X ^ k := by
    rw [hHdef, KFun.topPoly_flatMap, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [KFun.topPoly_opPoly (KFun.JLe_base c β k) (Q k) (hdegM k (Finset.mem_range.mp hk)),
      KFun.topPoly_base, ← mul_assoc, ← map_mul]
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff kM) (hsum.symm.trans hP0)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero]
    at hcoeff
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hkM.1)] at hcoeff
  have hlead : (Q kM).coeff M ≠ 0 := by
    rw [hM]; exact leadingCoeff_ne_zero.mpr hkM.2
  exact (mul_ne_zero (mul_ne_zero hlead (pow_ne_zero _ I_ne_zero))
    (mul_ne_zero (pow_ne_zero _ I_ne_zero) hc)) hcoeff

/-! ## Imaginary shifts and the `e^{βu}`-parts of the operations -/

/-- Multiplication of the kernel by `e^{-su}`, i.e. the shift `z ↦ z + is` of the transform. -/
def KFun.shift (s : ℝ) (F : KFun) : KFun := F.map fun t => ⟨t.c, t.a, t.β - s, t.j⟩

theorem KFun.eval_shift (s : ℝ) (F : KFun) (u : ℝ) :
    KFun.eval (KFun.shift s F) u = cexp (-(s * u)) * KFun.eval F u := by
  induction F with
  | nil => simp [KFun.shift, KFun.eval]
  | cons t F ih =>
    simp only [KFun.shift, List.map_cons, KFun.eval_cons] at ih ⊢
    rw [ih, mul_add]
    congr 1
    simp only [KTerm.eval]
    push_cast
    rw [show ((t.β : ℂ) - s) * u = t.β * u + -(s * u) by ring, Complex.exp_add]
    ring

open Zeta23 in
theorem paperFT_kfun_shift (s : ℝ) (F : KFun) (z : ℂ) :
    paperFT (KFun.eval F) (z + s * I) = paperFT (KFun.eval (KFun.shift s F)) z := by
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [KFun.eval_shift]
  rw [show I * (z + s * I) * u = I * z * u + -(s * u) by ring_nf; rw [I_sq]; ring,
    Complex.exp_add]
  ring

theorem KFun.mulIU_iterate_single (c : ℂ) (b : ℝ) (k : ℕ) :
    KFun.mulIU^[k] [⟨c, 0, b, 0⟩] = [⟨I ^ k * c, k, b, 0⟩] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [KFun.mulIU, pow_succ]
    ring

theorem KFun.shift_mulIU_iterate_single (s : ℝ) (c : ℂ) (b : ℝ) (k : ℕ) :
    KFun.shift s (KFun.mulIU^[k] [⟨c, 0, b, 0⟩]) = KFun.mulIU^[k] [⟨c, 0, b - s, 0⟩] := by
  rw [KFun.mulIU_iterate_single, KFun.mulIU_iterate_single]
  simp [KFun.shift]

theorem KFun.mulIU_append (F G : KFun) :
    KFun.mulIU (F ++ G) = KFun.mulIU F ++ KFun.mulIU G := by
  simp [KFun.mulIU]

theorem KFun.mulIU_iterate_append (k : ℕ) (F G : KFun) :
    KFun.mulIU^[k] (F ++ G) = KFun.mulIU^[k] F ++ KFun.mulIU^[k] G := by
  induction k generalizing F G with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, KFun.mulIU_append, ih]

open Classical in
theorem KFun.part_append (β : ℝ) (F G : KFun) :
    KFun.part β (F ++ G) = KFun.part β F ++ KFun.part β G := by
  simp [KFun.part, List.filter_append]

open Classical in
theorem KFun.part_flatMap {α : Type*} (β : ℝ) (L : List α) (G : α → KFun) :
    KFun.part β (L.flatMap G) = L.flatMap fun a => KFun.part β (G a) := by
  simp [KFun.part, List.filter_flatMap]

open Classical in
theorem KFun.part_smul (β : ℝ) (c : ℂ) (F : KFun) :
    KFun.part β (KFun.smul c F) = KFun.smul c (KFun.part β F) := by
  simp [KFun.part, KFun.smul, List.filter_map, Function.comp_def]

open Classical in
theorem KFun.part_mulIU (β : ℝ) (F : KFun) :
    KFun.part β (KFun.mulIU F) = KFun.mulIU (KFun.part β F) := by
  simp [KFun.part, KFun.mulIU, List.filter_map, Function.comp_def]

open Classical in
theorem KFun.part_d (β : ℝ) (F : KFun) : KFun.part β (KFun.d F) = KFun.d (KFun.part β F) := by
  unfold KFun.part KFun.d
  rw [List.filter_flatMap]
  induction F with
  | nil => simp
  | cons t F ih =>
    rw [List.flatMap_cons, ih, List.filter_cons]
    by_cases h : t.β = β
    · simp [KTerm.d, h]
    · simp [KTerm.d, h]

theorem KFun.part_iD (β : ℝ) (F : KFun) : KFun.part β (KFun.iD F) = KFun.iD (KFun.part β F) := by
  unfold KFun.iD; rw [KFun.part_smul, KFun.part_d]

theorem KFun.part_iterate_iD (β : ℝ) (m : ℕ) (F : KFun) :
    KFun.part β (KFun.iD^[m] F) = KFun.iD^[m] (KFun.part β F) := by
  induction m generalizing F with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, KFun.part_iD]

theorem KFun.part_iterate_mulIU (β : ℝ) (k : ℕ) (F : KFun) :
    KFun.part β (KFun.mulIU^[k] F) = KFun.mulIU^[k] (KFun.part β F) := by
  induction k generalizing F with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, KFun.part_mulIU]

theorem KFun.part_opPoly (β : ℝ) (q : ℂ[X]) (F : KFun) :
    KFun.part β (KFun.opPoly q F) = KFun.opPoly q (KFun.part β F) := by
  unfold KFun.opPoly
  rw [KFun.part_flatMap]
  congr 1
  funext m
  rw [KFun.part_smul, KFun.part_iterate_iD]

open Classical in
theorem KFun.part_shift (β s : ℝ) (F : KFun) :
    KFun.part β (KFun.shift s F) = KFun.shift s (KFun.part (β + s) F) := by
  simp only [KFun.part, KFun.shift, List.filter_map, Function.comp_def]
  congr 1
  refine List.filter_congr fun t _ => ?_
  simp only [decide_eq_decide]
  constructor <;> intro h <;> linarith

open Classical in
theorem KFun.part_single (β : ℝ) (t : KTerm) :
    KFun.part β [t] = if t.β = β then [t] else [] := by
  by_cases h : t.β = β <;> simp [KFun.part, h]

theorem KFun.opPoly_nil (q : ℂ[X]) : KFun.opPoly q [] = [] := by
  have hi : ∀ m, KFun.iD^[m] ([] : KFun) = [] := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih]; rfl
  simp [KFun.opPoly, hi, KFun.smul]

theorem KFun.mulIU_iterate_nil (k : ℕ) : KFun.mulIU^[k] ([] : KFun) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

/-! ## No finite-shift local port -/

theorem cosineProducer_neg (h : ℝ) : cosineProducer (-h) = cosineProducer h := by
  funext z
  unfold cosineProducer
  congr 1
  funext u
  rw [neg_mul, Real.cosh_neg]

theorem cosineProducer_eq_paperFT (h : ℝ) :
    cosineProducer h = Zeta23.paperFT (KFun.eval (cosineKernel h)) := by
  funext z
  unfold cosineProducer
  congr 1
  funext u
  rw [cosineKernel_eval]

theorem kfun_eval_flatMap {α : Type*} (L : List α) (G : α → KFun) (u : ℝ) :
    KFun.eval (L.flatMap G) u = (L.map fun a => KFun.eval (G a) u).sum := by
  induction L with
  | nil => simp [KFun.eval]
  | cons a L ih => rw [List.flatMap_cons, KFun.eval_append, ih, List.map_cons, List.sum_cons]

theorem kfun_eval_flatMap_single {α : Type*} [DecidableEq α] {L : List α} (hL : L.Nodup) {a : α}
    (ha : a ∈ L) (G : α → KFun) (hG : ∀ x ∈ L, x ≠ a → G x = []) (u : ℝ) :
    KFun.eval (L.flatMap G) u = KFun.eval (G a) u := by
  induction L with
  | nil => simp at ha
  | cons x L ih =>
    rw [List.flatMap_cons, KFun.eval_append]
    rcases List.nodup_cons.mp hL with ⟨hxL, hL'⟩
    by_cases hx : x = a
    · subst hx
      have hrest : ∀ y ∈ L, G y = [] := fun y hy => hG y (List.mem_cons_of_mem _ hy)
        (fun hya => hxL (hya ▸ hy))
      have : KFun.eval (L.flatMap G) u = 0 := by
        rw [kfun_eval_flatMap]
        exact List.sum_eq_zero fun z hz => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
          rw [hrest y hy]; rfl
      rw [this, add_zero]
    · have haL : a ∈ L := (List.mem_cons.mp ha).resolve_left (Ne.symm hx)
      rw [hG x List.mem_cons_self hx, ih hL' haL fun y hy => hG y (List.mem_cons_of_mem _ hy)]
      simp [KFun.eval]

/-- `Ξ` does not vanish identically on the real line. -/
theorem not_forall_XiC_eq_zero : ¬ ∀ t : ℝ, XiC t = 0 := by
  intro h0
  set t₀ : KTerm := ⟨-1, 0, 0, 0⟩ with ht₀
  have hpf : ∀ t : ℝ, Zeta23.paperFT (KFun.eval [t₀]) t = 0 := by
    intro t
    rw [ht₀, paperFT_kfun_single_zero]
    simp [h0 t]
  have heval := eq_zero_of_paperFT_real_eq_zero (KFun.superExpDecay [t₀]) hpf
  have hhead := KFun.head_eq_zero_of_eval_eq_zero [t₀] fun u => by rw [heval]; rfl
  have h2 : KFun.head [t₀] (9 / 2) = C (-(4 * (π : ℂ) ^ 2)) := by
    simp only [KFun.head, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact head_negPhi_nine_halves
  rw [hhead, Finsupp.coe_zero, Pi.zero_apply] at h2
  have := h2.symm
  rw [C_eq_zero, neg_eq_zero] at this
  have hpi : (4 * (π : ℂ) ^ 2) ≠ 0 := by
    have := Real.pi_pos
    exact_mod_cast (by positivity : (4 * π ^ 2 : ℝ) ≠ 0)
  exact hpi this

open Zeta23 in
theorem paperFT_kfun_flatMap_gen {α : Type*} (L : List α) (G : α → KFun) (z : ℂ) :
    paperFT (KFun.eval (L.flatMap G)) z = (L.map fun a => paperFT (KFun.eval (G a)) z).sum := by
  induction L with
  | nil =>
    simp only [List.flatMap_nil, List.map_nil, List.sum_nil]
    unfold paperFT
    simp [KFun.eval]
  | cons a L ih =>
    rw [List.flatMap_cons, paperFT_kfun_append, ih, List.map_cons, List.sum_cons]

/-- The kernel side of a finite-shift polynomial port. -/
theorem shiftPort_kernel (h : ℝ) (S : Finset ℝ) (K : ℕ) (Q : ℝ → ℕ → ℂ[X]) (t : ℝ) :
    ∑ s ∈ S, ∑ k ∈ Finset.range K,
        (Q s k).eval (t : ℂ) * iteratedDeriv k (cosineProducer h) (t + s * I) =
      Zeta23.paperFT (KFun.eval (S.toList.flatMap fun s => (List.range K).flatMap fun k =>
        KFun.opPoly (Q s k) (KFun.shift s (KFun.mulIU^[k] (cosineKernel h))))) t := by
  rw [paperFT_kfun_flatMap_gen, ← List.sum_toFinset _ (Finset.nodup_toList S),
    Finset.toList_toFinset]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [paperFT_kfun_flatMap, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cosineProducer_eq_paperFT, iteratedDeriv_paperFT_kfun, paperFT_kfun_shift,
    polyEval_mul_paperFT_kfun]

/-- The extreme block: if `b - s⋆` is attained by no other pair `(s, ±h)` and is nonzero, the
port coefficients at `s⋆` vanish. -/
theorem shiftPort_extreme_coeff_eq_zero {h : ℝ} (hpos : 0 < h) {S : Finset ℝ} {K : ℕ}
    {Q : ℝ → ℕ → ℂ[X]}
    (hQ : ∀ t : ℝ, ∑ s ∈ S, ∑ k ∈ Finset.range K,
        (Q s k).eval (t : ℂ) * iteratedDeriv k (cosineProducer h) (t + s * I) = XiC t)
    {sstar b : ℝ} (hs : sstar ∈ S) (hb : b = h ∨ b = -h)
    (huniq : ∀ s ∈ S, ∀ b' : ℝ, (b' = h ∨ b' = -h) → b' - s = b - sstar → s = sstar ∧ b' = b)
    (hβ0 : b - sstar ≠ 0) : ∀ k < K, Q sstar k = 0 := by
  classical
  set F : KFun := S.toList.flatMap fun s => (List.range K).flatMap fun k =>
    KFun.opPoly (Q s k) (KFun.shift s (KFun.mulIU^[k] (cosineKernel h))) with hF
  set t₀ : KTerm := ⟨-1, 0, 0, 0⟩ with ht₀
  have hF0 : ∀ t : ℝ, Zeta23.paperFT (KFun.eval (F ++ [t₀])) t = 0 := by
    intro t
    rw [paperFT_kfun_append, ← shiftPort_kernel, hQ t, ht₀, paperFT_kfun_single_zero]
    simp
  have heval := eq_zero_of_paperFT_real_eq_zero (KFun.superExpDecay _) hF0
  set βs := b - sstar with hβs
  have hpart := KFun.eval_part_eq_zero (F ++ [t₀]) (fun u => by rw [heval]; rfl) βs
  -- the part of `cosineKernel h` seen at the shift `s`
  have hker : ∀ s ∈ S, KFun.part (βs + s) (cosineKernel h) =
      if s = sstar then [⟨1 / 2, 0, b, 0⟩] else [] := by
    intro s hsS
    have hsplit : cosineKernel h = [⟨1 / 2, 0, h, 0⟩] ++ [⟨1 / 2, 0, -h, 0⟩] := rfl
    rw [hsplit, KFun.part_append, KFun.part_single, KFun.part_single]
    have hne : h ≠ -h := by intro; linarith
    by_cases hss : s = sstar
    · subst hss
      rcases hb with rfl | rfl
      · simp [hβs, hne.symm]
      · simp [hβs, hne]
    · have h1 : ¬ (h = βs + s) := fun hh => hss (huniq s hsS h (Or.inl rfl) (by
        rw [hβs] at hh; linarith)).1
      have h2 : ¬ (-h = βs + s) := fun hh => hss (huniq s hsS (-h) (Or.inr rfl) (by
        rw [hβs] at hh; linarith)).1
      rw [if_neg h1, if_neg h2, if_neg hss]
      rfl
  have hpartF : KFun.part βs (F ++ [t₀]) = S.toList.flatMap fun s =>
      (List.range K).flatMap fun k => KFun.opPoly (Q s k)
        (KFun.shift s (KFun.mulIU^[k] (if s = sstar then [⟨1 / 2, 0, b, 0⟩] else []))) := by
    rw [KFun.part_append, KFun.part_single, if_neg (by simpa [ht₀] using Ne.symm hβ0),
      List.append_nil, hF, KFun.part_flatMap]
    refine List.flatMap_congr fun s hsL => ?_
    rw [KFun.part_flatMap]
    refine List.flatMap_congr fun k _ => ?_
    rw [KFun.part_opPoly, KFun.part_shift, KFun.part_iterate_mulIU,
      hker s (Finset.mem_toList.mp hsL)]
  have hblock : ∀ u : ℝ, KFun.eval ((List.range K).flatMap fun k =>
      KFun.opPoly (Q sstar k) (KFun.mulIU^[k] [⟨1 / 2, 0, βs, 0⟩])) u = 0 := by
    intro u
    have := hpart u
    rw [hpartF, kfun_eval_flatMap_single (Finset.nodup_toList S) (Finset.mem_toList.mpr hs)]
      at this
    · simpa [KFun.shift_mulIU_iterate_single, hβs] using this
    · intro x _ hx
      simp [hx, KFun.mulIU_iterate_nil, KFun.shift, KFun.opPoly_nil]
  exact KFun.annihilation (by norm_num) βs K (Q sstar) hblock

/-- **No finite-shift local port from the cosine producer to `Ξ`.** For every real `h ≠ 0`, no
finite family of polynomial-coefficient differential operators applied to finitely many imaginary
translates `A_h(· + is)` of `A_h = cos(hD)Ξ` sums to `Ξ` on the real line. -/
theorem not_exists_shift_polynomial_port_cosineProducer {h : ℝ} (hh : h ≠ 0) (K : ℕ) :
    ∀ (S : Finset ℝ) (Q : ℝ → ℕ → ℂ[X]), ¬ ∀ t : ℝ, ∑ s ∈ S, ∑ k ∈ Finset.range K,
        (Q s k).eval (t : ℂ) * iteratedDeriv k (cosineProducer h) (t + s * I) = XiC t := by
  classical
  wlog hpos : 0 < h generalizing h with H
  · intro S Q hQ
    have hneg : 0 < -h := by
      have := lt_of_le_of_ne (not_lt.mp hpos) hh; linarith
    exact H (neg_ne_zero.mpr hh) hneg S Q (by simpa [cosineProducer_neg] using hQ)
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro Q hQ
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact not_forall_XiC_eq_zero fun t => by simpa using (hQ t).symm
  set s₁ := S.min' hS with hs₁
  set s₂ := S.max' hS with hs₂
  have hs₁S : s₁ ∈ S := S.min'_mem hS
  have hs₂S : s₂ ∈ S := S.max'_mem hS
  -- choose the extreme block with nonzero exponent
  obtain ⟨sstar, hsS, hzero⟩ : ∃ sstar ∈ S, ∀ k < K, Q sstar k = 0 := by
    by_cases hz : h - s₁ = 0
    · refine ⟨s₂, hs₂S, shiftPort_extreme_coeff_eq_zero hpos hQ hs₂S (Or.inr rfl) ?_ ?_⟩
      · intro s hsS b' hb' heq
        have hle := S.le_max' s hsS
        rcases hb' with rfl | rfl
        · exfalso; rw [← hs₂] at hle; linarith
        · exact ⟨by rw [← hs₂] at hle; linarith, rfl⟩
      · have := S.min'_le s₂ hs₂S; rw [← hs₁] at this; linarith
    · refine ⟨s₁, hs₁S, shiftPort_extreme_coeff_eq_zero hpos hQ hs₁S (Or.inl rfl) ?_ hz⟩
      intro s hsS b' hb' heq
      have hle := S.min'_le s hsS
      rcases hb' with rfl | rfl
      · exact ⟨by rw [← hs₁] at hle; linarith, rfl⟩
      · exfalso; rw [← hs₁] at hle; linarith
  refine ih (S.erase sstar) (Finset.erase_ssubset hsS) Q fun t => ?_
  rw [← hQ t, ← Finset.add_sum_erase S _ hsS]
  have h0 : ∑ k ∈ Finset.range K, (Q sstar k).eval (t : ℂ) *
      iteratedDeriv k (cosineProducer h) (t + sstar * I) = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [hzero k (Finset.mem_range.mp hk)]; simp
  rw [h0, zero_add]

/-! ## Independence of imaginary translates -/

theorem XiC_eq_paperFT : XiC = Zeta23.paperFT (KFun.eval [⟨1, 0, 0, 0⟩]) := by
  funext z
  rw [paperFT_kfun_single_zero]
  simp

/-- **Imaginary translates of `Ξ` are independent over polynomial-coefficient differential
operators.** If `Σ_{s ∈ S} Σ_{k < K} Q_{s,k}(t) Ξ^{(k)}(t + is) = 0` for all real `t`, with `S` a
finite set of reals, then every `Q_{s,k}` vanishes. -/
theorem polynomial_differential_translates_independent (S : Finset ℝ) (K : ℕ)
    (Q : ℝ → ℕ → ℂ[X])
    (hQ : ∀ t : ℝ, ∑ s ∈ S, ∑ k ∈ Finset.range K,
      (Q s k).eval (t : ℂ) * iteratedDeriv k XiC (t + s * I) = 0) :
    ∀ s ∈ S, ∀ k < K, Q s k = 0 := by
  classical
  set F : KFun := S.toList.flatMap fun s => (List.range K).flatMap fun k =>
    KFun.opPoly (Q s k) (KFun.mulIU^[k] [⟨1, 0, -s, 0⟩]) with hF
  have hker : ∀ t : ℝ, Zeta23.paperFT (KFun.eval F) t = 0 := by
    intro t
    rw [← hQ t, hF, paperFT_kfun_flatMap_gen, ← List.sum_toFinset _ (Finset.nodup_toList S),
      Finset.toList_toFinset]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [paperFT_kfun_flatMap_gen, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [XiC_eq_paperFT, iteratedDeriv_paperFT_kfun, paperFT_kfun_shift,
      KFun.shift_mulIU_iterate_single, polyEval_mul_paperFT_kfun, zero_sub]
  have heval := eq_zero_of_paperFT_real_eq_zero (KFun.superExpDecay F) hker
  intro s₀ hs₀ k hk
  have hpart := KFun.eval_part_eq_zero F (fun u => by rw [heval]; rfl) (-s₀)
  have hpartF : KFun.part (-s₀) F = S.toList.flatMap fun s => (List.range K).flatMap fun k =>
      KFun.opPoly (Q s k) (KFun.mulIU^[k] (if s = s₀ then [⟨1, 0, -s, 0⟩] else [])) := by
    rw [hF, KFun.part_flatMap]
    refine List.flatMap_congr fun s _ => ?_
    rw [KFun.part_flatMap]
    refine List.flatMap_congr fun k _ => ?_
    rw [KFun.part_opPoly, KFun.part_iterate_mulIU, KFun.part_single]
    by_cases hs : s = s₀
    · simp [hs]
    · have : ¬ (-s = -s₀) := fun h => hs (by linarith)
      simp [hs, this]
  have hblock : ∀ u : ℝ, KFun.eval ((List.range K).flatMap fun k =>
      KFun.opPoly (Q s₀ k) (KFun.mulIU^[k] [⟨1, 0, -s₀, 0⟩])) u = 0 := by
    intro u
    have := hpart u
    rw [hpartF, kfun_eval_flatMap_single (Finset.nodup_toList S) (Finset.mem_toList.mpr hs₀)]
      at this
    · simpa using this
    · intro x _ hx
      simp [hx, KFun.mulIU_iterate_nil, KFun.opPoly_nil]
  exact KFun.annihilation one_ne_zero (-s₀) K (Q s₀) hblock k hk

end RHTower.LocalPort
