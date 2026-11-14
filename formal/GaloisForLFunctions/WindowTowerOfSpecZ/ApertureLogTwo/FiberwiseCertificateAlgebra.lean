import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.RationalQuadraticForms

/-!
# Fiberwise certificates at aperture `log 2`: shared algebra

The six-interval folding of `(0, 1)` turns the potential and prime-contact part of Weil's form
into integrals of tridiagonal fiber forms. This module provides the pieces used on every fiber:

* the exterior potential `vTrue x = log 2 - log (1 - x²) / 2` and its rational Taylor minorants
  (`TaylorBranch`, `qeval_poly_le_vTrue`);
* the dual test `phiFnQ`, a fixed rational combination of Legendre polynomials, with the exact
  pairing `∫₀¹ G · phiFnQ m = mᵀ Λ m` (`integral_mul_phiFnQ`) and its Lipschitz bound;
* square completions on coercive `4 × 4` and `2 × 2` tridiagonal fibers with perturbed sources
  (`tridiag4_complete_sq_all`, `tridiag2_complete_sq_all`);
* Gram identities for products of rational linear combinations (`integral_lin_mul_lin`).
-/

open Real MeasureTheory Set Finset intervalIntegral
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

open SelectivePositivityAndThresholdLaws

/-! ### Exterior potential and rational Taylor minorants -/

/-- The exterior potential of the half window. -/
noncomputable def vTrue (x : ℝ) : ℝ := Real.log 2 - Real.log (1 - x ^ 2) / 2

theorem vTrue_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) : vTrue x ≤ vTrue y := by
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  have hle : 1 - y ^ 2 ≤ 1 - x ^ 2 := by nlinarith
  have := Real.log_le_log hy2 hle
  unfold vTrue; linarith

/-- Rational enclosures of `log 2` and `log 3` used in base checks. -/
def log2LoQ : ℚ := 17328679513998632735430803 / 25000000000000000000000000
def log2HiQ : ℚ := 69314718055994530941723213 / 100000000000000000000000000
def log3LoQ : ℚ := 109861228866810969139524523 / 100000000000000000000000000
def log3HiQ : ℚ := 27465307216702742284881131 / 25000000000000000000000000

theorem log2_bounds_Q : (log2LoQ : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (log2HiQ : ℝ) := by
  have h := log_two_bounds_d26
  simp only [logTwoLo, logTwoHi] at h
  constructor <;> [refine le_trans (le_of_eq ?_) h.1; refine h.2.trans (le_of_eq ?_)] <;>
    norm_num [log2LoQ, log2HiQ]

theorem log3_bounds_Q : (log3LoQ : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (log3HiQ : ℝ) := by
  have h := log_three_bounds_d26
  simp only [logThreeLo, logThreeHi] at h
  constructor <;> [refine le_trans (le_of_eq ?_) h.1; refine h.2.trans (le_of_eq ?_)] <;>
    norm_num [log3LoQ, log3HiQ]

/-- Lower bound of `c · L` for `L ∈ [lo, hi]`. -/
def lowMul (c lo hi : ℚ) : ℚ := if 0 ≤ c then c * lo else c * hi

theorem lowMul_le {c lo hi : ℚ} {L : ℝ} (h1 : (lo : ℝ) ≤ L) (h2 : L ≤ hi) :
    (lowMul c lo hi : ℝ) ≤ c * L := by
  unfold lowMul
  split_ifs with hc
  · push_cast; exact mul_le_mul_of_nonneg_left h1 (by exact_mod_cast hc)
  · push_cast
    have : (c : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hc
    nlinarith

/-- Taylor data `(p, q, t₀, ω, base)` anchored at `1 - t₀ = ω = 2^p 3^q`. -/
structure TaylorBranch where
  p : ℤ
  q : ℤ
  t0 : ℚ
  om : ℚ
  base : ℚ

/-- `∑_{m=1}^{r} u^m / (2m)` on coefficient lists. -/
def tayTail (u : List ℚ) : ℕ → List ℚ × List ℚ
  | 0 => ([], [1])
  | r + 1 =>
    let pw := qmul (tayTail u r).2 u
    (qadd (tayTail u r).1 (qsmul (1 / (2 * ((r : ℚ) + 1))) pw), pw)

/-- The Taylor minorant `base + ∑_{m=1}^{r} (((x₀ + x₁ ξ)² - t₀) / ω)^m / (2m)` in `ξ`. -/
def TaylorBranch.poly (τ : TaylorBranch) (r : ℕ) (x0 x1 : ℚ) : List ℚ :=
  qadd [τ.base] (tayTail (qsmul (1 / τ.om) (qsub (qmul [x0, x1] [x0, x1]) [τ.t0])) r).1

/-- Validity of the anchor and the base. -/
def TaylorBranch.valid (τ : TaylorBranch) : Bool :=
  decide (τ.om = (2 : ℚ) ^ τ.p * (3 : ℚ) ^ τ.q) && decide (τ.t0 = 1 - τ.om) &&
    decide (τ.base ≤ lowMul (1 - (τ.p : ℚ) / 2) log2LoQ log2HiQ +
      lowMul (-(τ.q : ℚ) / 2) log3LoQ log3HiQ)

private theorem tayTail_eval (u : List ℚ) (ξ : ℝ) : ∀ r : ℕ,
    qeval (tayTail u r).1 ξ = ∑ m ∈ Finset.Icc 1 r, qeval u ξ ^ m / (2 * (m : ℝ)) ∧
      qeval (tayTail u r).2 ξ = qeval u ξ ^ r
  | 0 => by simp [tayTail]
  | r + 1 => by
    obtain ⟨h1, h2⟩ := tayTail_eval u ξ r
    simp only [tayTail, qeval_qadd, qeval_qsmul, qeval_qmul, h1, h2]
    refine ⟨?_, by ring⟩
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast; ring

theorem qeval_TaylorBranch_poly (τ : TaylorBranch) (r : ℕ) (x0 x1 : ℚ) (ξ : ℝ) :
    qeval (τ.poly r x0 x1) ξ = τ.base +
      ∑ m ∈ Finset.Icc 1 r, ((((x0 : ℝ) + x1 * ξ) ^ 2 - τ.t0) / τ.om) ^ m / (2 * (m : ℝ)) := by
  rw [TaylorBranch.poly, qeval_qadd, (tayTail_eval _ ξ r).1]
  simp only [qeval_qsmul, qeval_qsub, qeval_qmul, qeval_cons, qeval_nil]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun m _ => ?_
    push_cast; ring_nf

/-- A valid Taylor branch bounds the exterior potential from below at every point above its
anchor. -/
theorem qeval_poly_le_vTrue {τ : TaylorBranch} (hτ : τ.valid = true) (r : ℕ) (x0 x1 : ℚ)
    {ξ x : ℝ} (hlow : 0 ≤ (x0 : ℝ) + x1 * ξ) (hmin : (τ.t0 : ℝ) ≤ ((x0 : ℝ) + x1 * ξ) ^ 2)
    (hle : (x0 : ℝ) + x1 * ξ ≤ x) (hx1 : x < 1) :
    qeval (τ.poly r x0 x1) ξ ≤ vTrue x := by
  simp only [TaylorBranch.valid, Bool.and_eq_true, decide_eq_true_eq] at hτ
  obtain ⟨⟨hom, ht0⟩, hbase⟩ := hτ
  have hom' : (τ.om : ℝ) = (2 : ℝ) ^ τ.p * (3 : ℝ) ^ τ.q := by rw [hom]; push_cast; rfl
  have ht0' : (τ.t0 : ℝ) = 1 - τ.om := by rw [ht0]; push_cast; rfl
  have hb : (τ.base : ℝ) ≤ Real.log 2 - ((τ.p : ℝ) * Real.log 2 + (τ.q : ℝ) * Real.log 3) / 2 := by
    have h1 := lowMul_le (c := 1 - (τ.p : ℚ) / 2) log2_bounds_Q.1 log2_bounds_Q.2
    have h2 := lowMul_le (c := -(τ.q : ℚ) / 2) log3_bounds_Q.1 log3_bounds_Q.2
    have hb' : (τ.base : ℝ) ≤ (lowMul (1 - (τ.p : ℚ) / 2) log2LoQ log2HiQ : ℝ) +
        (lowMul (-(τ.q : ℚ) / 2) log3LoQ log3HiQ : ℝ) := by exact_mod_cast hbase
    push_cast at h1 h2
    linarith
  have hx2 : ((x0 : ℝ) + x1 * ξ) ^ 2 < 1 := by nlinarith
  have htay := exterior_log_potential_ge_shifted_taylor τ.p τ.q τ.t0 τ.om τ.base r hom' ht0' hb
    hmin hx2
  rw [qeval_TaylorBranch_poly]
  exact htay.trans (vTrue_mono hlow hle hx1)

/-! ### Square completion on tridiagonal fibers -/

/-- Square completion on a coercive `4 × 4` tridiagonal fiber whose sources carry perturbations
`z`; `ip` is the inverse of the penalty `pen`. -/
theorem tridiag4_complete_sq_all {d0 d1 d2 d3 e2 e3 pen ip : ℝ} (hpi : pen * ip = 1)
    (hip : 0 ≤ ip)
    (hcoerc : ∀ u0 u1 u2 u3 : ℝ, (17 / 16 : ℝ) * (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) ≤
      tridiag4Form d0 d1 d2 d3 e2 e3 u0 u1 u2 u3)
    (g0 g1 g2 g3 w0 w1 w2 w3 v0 v1 v2 v3 z0 z1 z2 z3 : ℝ) :
    -(w0 * (2 * v0 - (d0 * w0 + e2 * w1) + pen * w0) +
        w1 * (2 * v1 - (e2 * w0 + d1 * w1 + e3 * w2) + pen * w1) +
        w2 * (2 * v2 - (e3 * w1 + d2 * w2 + e2 * w3) + pen * w2) +
        w3 * (2 * v3 - (e2 * w2 + d3 * w3) + pen * w3)) -
      ((d0 * w0 + e2 * w1 - v0) ^ 2 + (e2 * w0 + d1 * w1 + e3 * w2 - v1) ^ 2 +
        (e3 * w1 + d2 * w2 + e2 * w3 - v2) ^ 2 + (e2 * w2 + d3 * w3 - v3) ^ 2) -
      (16 + ip) * (z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2) ≤
      tridiag4Form d0 d1 d2 d3 e2 e3 g0 g1 g2 g3 -
        2 * (g0 * (v0 + z0) + g1 * (v1 + z1) + g2 * (v2 + z2) + g3 * (v3 + z3)) := by
  have hQ := hcoerc (g0 - w0) (g1 - w1) (g2 - w2) (g3 - w3)
  have key : tridiag4Form d0 d1 d2 d3 e2 e3 g0 g1 g2 g3 -
      2 * (g0 * (v0 + z0) + g1 * (v1 + z1) + g2 * (v2 + z2) + g3 * (v3 + z3)) -
      (-(w0 * (2 * v0 - (d0 * w0 + e2 * w1) + pen * w0) +
        w1 * (2 * v1 - (e2 * w0 + d1 * w1 + e3 * w2) + pen * w1) +
        w2 * (2 * v2 - (e3 * w1 + d2 * w2 + e2 * w3) + pen * w2) +
        w3 * (2 * v3 - (e2 * w2 + d3 * w3) + pen * w3)) -
      ((d0 * w0 + e2 * w1 - v0) ^ 2 + (e2 * w0 + d1 * w1 + e3 * w2 - v1) ^ 2 +
        (e3 * w1 + d2 * w2 + e2 * w3 - v2) ^ 2 + (e2 * w2 + d3 * w3 - v3) ^ 2) -
      (16 + ip) * (z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2)) =
      (tridiag4Form d0 d1 d2 d3 e2 e3 (g0 - w0) (g1 - w1) (g2 - w2) (g3 - w3) -
        (17 / 16 : ℝ) * ((g0 - w0) ^ 2 + (g1 - w1) ^ 2 + (g2 - w2) ^ 2 + (g3 - w3) ^ 2)) +
      ((g0 - w0 + (d0 * w0 + e2 * w1 - v0)) ^ 2 +
        (g1 - w1 + (e2 * w0 + d1 * w1 + e3 * w2 - v1)) ^ 2 +
        (g2 - w2 + (e3 * w1 + d2 * w2 + e2 * w3 - v2)) ^ 2 +
        (g3 - w3 + (e2 * w2 + d3 * w3 - v3)) ^ 2) +
      (((g0 - w0) / 4 - 4 * z0) ^ 2 + ((g1 - w1) / 4 - 4 * z1) ^ 2 +
        ((g2 - w2) / 4 - 4 * z2) ^ 2 + ((g3 - w3) / 4 - 4 * z3) ^ 2) +
      ip * ((pen * w0 - z0) ^ 2 + (pen * w1 - z1) ^ 2 + (pen * w2 - z2) ^ 2 +
        (pen * w3 - z3) ^ 2) := by
    unfold tridiag4Form
    linear_combination (-(pen * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2 + w3 ^ 2)) +
      2 * (w0 * z0 + w1 * z1 + w2 * z2 + w3 * z3)) * hpi
  have h1 : 0 ≤ ip * ((pen * w0 - z0) ^ 2 + (pen * w1 - z1) ^ 2 + (pen * w2 - z2) ^ 2 +
      (pen * w3 - z3) ^ 2) := by positivity
  nlinarith [sq_nonneg (g0 - w0 + (d0 * w0 + e2 * w1 - v0)),
    sq_nonneg (g1 - w1 + (e2 * w0 + d1 * w1 + e3 * w2 - v1)),
    sq_nonneg (g2 - w2 + (e3 * w1 + d2 * w2 + e2 * w3 - v2)),
    sq_nonneg (g3 - w3 + (e2 * w2 + d3 * w3 - v3)),
    sq_nonneg ((g0 - w0) / 4 - 4 * z0), sq_nonneg ((g1 - w1) / 4 - 4 * z1),
    sq_nonneg ((g2 - w2) / 4 - 4 * z2), sq_nonneg ((g3 - w3) / 4 - 4 * z3)]

/-- Square completion on a coercive `2 × 2` fiber with perturbed sources. -/
theorem tridiag2_complete_sq_all {d0 d1 e2 pen ip : ℝ} (hpi : pen * ip = 1) (hip : 0 ≤ ip)
    (hcoerc : ∀ u0 u1 : ℝ, (17 / 16 : ℝ) * (u0 ^ 2 + u1 ^ 2) ≤ tridiag2Form d0 d1 e2 u0 u1)
    (g0 g1 w0 w1 v0 v1 z0 z1 : ℝ) :
    -(w0 * (2 * v0 - (d0 * w0 + e2 * w1) + pen * w0) +
        w1 * (2 * v1 - (e2 * w0 + d1 * w1) + pen * w1)) -
      ((d0 * w0 + e2 * w1 - v0) ^ 2 + (e2 * w0 + d1 * w1 - v1) ^ 2) -
      (16 + ip) * (z0 ^ 2 + z1 ^ 2) ≤
      tridiag2Form d0 d1 e2 g0 g1 - 2 * (g0 * (v0 + z0) + g1 * (v1 + z1)) := by
  have hQ := hcoerc (g0 - w0) (g1 - w1)
  have key : tridiag2Form d0 d1 e2 g0 g1 - 2 * (g0 * (v0 + z0) + g1 * (v1 + z1)) -
      (-(w0 * (2 * v0 - (d0 * w0 + e2 * w1) + pen * w0) +
        w1 * (2 * v1 - (e2 * w0 + d1 * w1) + pen * w1)) -
      ((d0 * w0 + e2 * w1 - v0) ^ 2 + (e2 * w0 + d1 * w1 - v1) ^ 2) -
      (16 + ip) * (z0 ^ 2 + z1 ^ 2)) =
      (tridiag2Form d0 d1 e2 (g0 - w0) (g1 - w1) -
        (17 / 16 : ℝ) * ((g0 - w0) ^ 2 + (g1 - w1) ^ 2)) +
      ((g0 - w0 + (d0 * w0 + e2 * w1 - v0)) ^ 2 + (g1 - w1 + (e2 * w0 + d1 * w1 - v1)) ^ 2) +
      (((g0 - w0) / 4 - 4 * z0) ^ 2 + ((g1 - w1) / 4 - 4 * z1) ^ 2) +
      ip * ((pen * w0 - z0) ^ 2 + (pen * w1 - z1) ^ 2) := by
    unfold tridiag2Form
    linear_combination (-(pen * (w0 ^ 2 + w1 ^ 2)) + 2 * (w0 * z0 + w1 * z1)) * hpi
  have h1 : 0 ≤ ip * ((pen * w0 - z0) ^ 2 + (pen * w1 - z1) ^ 2) := by positivity
  nlinarith [sq_nonneg (g0 - w0 + (d0 * w0 + e2 * w1 - v0)),
    sq_nonneg (g1 - w1 + (e2 * w0 + d1 * w1 - v1)),
    sq_nonneg ((g0 - w0) / 4 - 4 * z0), sq_nonneg ((g1 - w1) / 4 - 4 * z1)]

/-- Exact `LDLᵀ` pivots `> 0` of a `4 × 4` tridiagonal matrix with diagonal `β - 17/16`. -/
def pivots4Pos (b0 b1 b2 b3 e2 e3 : ℚ) : Bool :=
  let p0 := b0 - 17 / 16
  let p1 := b1 - 17 / 16 - e2 ^ 2 / p0
  let p2 := b2 - 17 / 16 - e3 ^ 2 / p1
  let p3 := b3 - 17 / 16 - e2 ^ 2 / p2
  decide (0 < p0) && decide (0 < p1) && decide (0 < p2) && decide (0 < p3)

theorem coercive4_of_pivots {b0 b1 b2 b3 e2 e3 : ℚ} (h : pivots4Pos b0 b1 b2 b3 e2 e3 = true)
    {d0 d1 d2 d3 : ℝ} (h0 : (b0 : ℝ) ≤ d0) (h1 : (b1 : ℝ) ≤ d1) (h2 : (b2 : ℝ) ≤ d2)
    (h3 : (b3 : ℝ) ≤ d3) (u0 u1 u2 u3 : ℝ) :
    (17 / 16 : ℝ) * (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) ≤
      tridiag4Form d0 d1 d2 d3 e2 e3 u0 u1 u2 u3 := by
  simp only [pivots4Pos, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp0, hp1⟩, hp2⟩, hp3⟩ := h
  exact tridiag4_ge_seventeen_sixteenths h0 h1 h2 h3 rfl (by exact_mod_cast hp0)
    (by push_cast; rfl) (by exact_mod_cast hp1) (by push_cast; rfl) (by exact_mod_cast hp2)
    (by push_cast; rfl) (by exact_mod_cast hp3) u0 u1 u2 u3

/-- Exact pivots `> 0` of a `2 × 2` matrix with diagonal `β - 17/16`. -/
def pivots2Pos (b0 b1 e2 : ℚ) : Bool :=
  decide (0 < b0 - 17 / 16) && decide (0 < b1 - 17 / 16 - e2 ^ 2 / (b0 - 17 / 16))

theorem coercive2_of_pivots {b0 b1 e2 : ℚ} (h : pivots2Pos b0 b1 e2 = true) {d0 d1 : ℝ}
    (h0 : (b0 : ℝ) ≤ d0) (h1 : (b1 : ℝ) ≤ d1) (u0 u1 : ℝ) :
    (17 / 16 : ℝ) * (u0 ^ 2 + u1 ^ 2) ≤ tridiag2Form d0 d1 e2 u0 u1 := by
  simp only [pivots2Pos, Bool.and_eq_true, decide_eq_true_eq] at h
  exact tridiag2_ge_seventeen_sixteenths h0 h1 rfl (by exact_mod_cast h.1)
    (by push_cast; rfl) (by exact_mod_cast h.2) u0 u1

/-! ### Gram identities for rational linear combinations -/

/-- `∑ᵢ mᵢ Aᵢ(ξ)` for a family of rational polynomials indexed by `Fin K`. -/
noncomputable def linQ {K : ℕ} (A : ℕ → List ℚ) (m : Fin K → ℝ) (ξ : ℝ) : ℝ :=
  ∑ i : Fin K, m i * qeval (A i) ξ

theorem continuous_linQ {K : ℕ} (A : ℕ → List ℚ) (m : Fin K → ℝ) : Continuous (linQ A m) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_qeval _)

/-- `∫₀¹ (∑ mᵢ Aᵢ)(∑ mⱼ Bⱼ) = ∑ᵢⱼ ⟨Aᵢ, Bⱼ⟩ mᵢ mⱼ`. -/
theorem integral_lin_mul_lin {K : ℕ} (A B : ℕ → List ℚ) (m : Fin K → ℝ) :
    (∫ ξ in (0 : ℝ)..1, linQ A m ξ * linQ B m ξ) =
      ∑ i : Fin K, ∑ j : Fin K, (dotQ (A i) (hilbVec (A i).length (B j)) : ℝ) * m i * m j := by
  have hfn : ∀ ξ, linQ A m ξ * linQ B m ξ =
      ∑ i : Fin K, ∑ j : Fin K, (m i * m j) * (qeval (A i) ξ * qeval (B j) ξ) := fun ξ => by
    simp only [linQ, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (continuous_finsetSum _ fun j _ => continuous_const.mul
      ((continuous_qeval _).mul (continuous_qeval _))).intervalIntegrable 0 1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    (continuous_const.mul ((continuous_qeval _).mul (continuous_qeval _))).intervalIntegrable 0 1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_qeval_mul_qeval]
  ring

/-- `(∑ mₖ Eₖ)² ≤ K ∑ ηₖ² mₖ²` whenever `|Eₖ| ≤ ηₖ`. -/
theorem sq_lin_le {K : ℕ} (E : Fin K → ℝ) (η : Fin K → ℝ) (hE : ∀ k, |E k| ≤ η k)
    (m : Fin K → ℝ) : (∑ k : Fin K, m k * E k) ^ 2 ≤ (K : ℝ) * ∑ k : Fin K, η k ^ 2 * m k ^ 2 := by
  have habs : |∑ k : Fin K, m k * E k| ≤ ∑ k : Fin K, η k * |m k| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
      rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hE k) (abs_nonneg _))
  have h1 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs] at h1
  have hcs := fin_sum_mul_sq_le K η (fun k => |m k|)
  simp only [sq_abs] at hcs
  linarith

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
