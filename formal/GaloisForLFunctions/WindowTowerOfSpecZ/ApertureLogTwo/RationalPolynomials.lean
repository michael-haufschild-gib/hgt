import GaloisForLFunctions.WindowTowerOfSpecZ.FiberwiseCapacityAndLagMomentsAtApertureLogTwo

/-!
# Rational polynomials and their real semantics

A rational polynomial is its coefficient list `List ℚ`, lowest degree first. All certificate
arithmetic at aperture `log 2` runs on such lists inside `decide`; this module relates every list
operation to the real function `qeval p : ℝ → ℝ` it denotes:

* ring operations and composition (`qeval_qadd`, `qeval_qmul`, `qeval_qcomp`);
* primitives, integrals over `[a, b]` and the Gram pairing `∫₀¹ p q` (`integral_qeval`,
  `integral_qeval_mul_qeval`);
* Legendre polynomials (`legP_eq_qeval_qleg`) and primitives anchored at `-1`
  (`iterPrim_qeval`);
* coefficient bounds on `[0, 1]` and `[-1, 1]`.
-/

open Real MeasureTheory Set intervalIntegral
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

open SelectivePositivityAndThresholdLaws

/-! ### Lists of rationals as polynomials -/

/-- Real evaluation of the coefficient list `p` (Horner form). -/
noncomputable def qeval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * qeval cs x

/-- Rational evaluation (Horner form). -/
def qevalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: cs, x => c + x * qevalQ cs x

def qadd : List ℚ → List ℚ → List ℚ
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: qadd as bs

def qsmul (c : ℚ) (p : List ℚ) : List ℚ := p.map (c * ·)

def qsub (p q : List ℚ) : List ℚ := qadd p (qsmul (-1) q)

def qmul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: as, bs => qadd (qsmul a bs) (0 :: qmul as bs)

/-- Composition `p ∘ q`. -/
def qcomp : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | c :: cs, q => qadd [c] (qmul q (qcomp cs q))

@[simp] theorem qeval_nil (x : ℝ) : qeval [] x = 0 := rfl
@[simp] theorem qeval_cons (c : ℚ) (cs : List ℚ) (x : ℝ) :
    qeval (c :: cs) x = c + x * qeval cs x := rfl

theorem qeval_ratCast : ∀ (p : List ℚ) (r : ℚ), qeval p r = ((qevalQ p r : ℚ) : ℝ)
  | [], _ => by simp [qevalQ]
  | c :: cs, r => by simp [qevalQ, qeval_ratCast cs r]

theorem qeval_qadd : ∀ (p q : List ℚ) (x : ℝ), qeval (qadd p q) x = qeval p x + qeval q x
  | [], _, _ => by simp [qadd]
  | _ :: _, [], _ => by simp [qadd]
  | a :: as, b :: bs, x => by simp only [qadd, qeval_cons, qeval_qadd as bs x]; push_cast; ring

theorem qeval_qsmul (c : ℚ) : ∀ (p : List ℚ) (x : ℝ), qeval (qsmul c p) x = c * qeval p x
  | [], _ => by simp [qsmul]
  | a :: as, x => by
    have h := qeval_qsmul c as x
    simp only [qsmul, List.map_cons, qeval_cons] at h ⊢
    rw [h]; push_cast; ring

theorem qeval_qsub (p q : List ℚ) (x : ℝ) : qeval (qsub p q) x = qeval p x - qeval q x := by
  rw [qsub, qeval_qadd, qeval_qsmul]; push_cast; ring

theorem qeval_qmul : ∀ (p q : List ℚ) (x : ℝ), qeval (qmul p q) x = qeval p x * qeval q x
  | [], _, _ => by simp [qmul]
  | a :: as, bs, x => by
    simp only [qmul, qeval_qadd, qeval_qsmul, qeval_cons, qeval_qmul as bs x]; push_cast; ring

theorem qeval_qcomp : ∀ (p q : List ℚ) (x : ℝ), qeval (qcomp p q) x = qeval p (qeval q x)
  | [], _, _ => by simp [qcomp]
  | c :: cs, q, x => by
    rw [qcomp, qeval_qadd, qeval_qmul, qeval_qcomp cs q x]; simp

/-- Affine reparametrisation `ξ ↦ x₀ + x₁ ξ`. -/
theorem qeval_qcomp_affine (p : List ℚ) (x0 x1 : ℚ) (ξ : ℝ) :
    qeval (qcomp p [x0, x1]) ξ = qeval p ((x0 : ℝ) + x1 * ξ) := by
  rw [qeval_qcomp]; congr 1; simp; ring

theorem continuous_qeval : ∀ p : List ℚ, Continuous (qeval p)
  | [] => (continuous_const (y := (0 : ℝ))).congr fun x => (qeval_nil x).symm
  | _ :: cs => continuous_const.add (continuous_id.mul (continuous_qeval cs))

/-! ### Primitives and integrals -/

/-- Coefficients `c_k / (n + k + 1)` of the primitive of `x ↦ ∑ c_k x^(n + k)` divided by
`x^(n + 1)`. -/
def qprimAux : ℕ → List ℚ → List ℚ
  | _, [] => []
  | n, c :: cs => c / ((n : ℚ) + 1) :: qprimAux (n + 1) cs

/-- The primitive vanishing at `0`. -/
def qprim (p : List ℚ) : List ℚ := 0 :: qprimAux 0 p

private theorem hasDerivAt_pow_mul_qprimAux :
    ∀ (p : List ℚ) (n : ℕ) (x : ℝ),
      HasDerivAt (fun y => y ^ (n + 1) * qeval (qprimAux n p) y) (x ^ n * qeval p x) x
  | [], n, x => by simpa [qprimAux] using hasDerivAt_const x (0 : ℝ)
  | c :: cs, n, x => by
    have ih := hasDerivAt_pow_mul_qprimAux cs (n + 1) x
    have h1 : HasDerivAt (fun y : ℝ => ((c / ((n : ℚ) + 1) : ℚ) : ℝ) * y ^ (n + 1))
        (((c / ((n : ℚ) + 1) : ℚ) : ℝ) * (((n + 1 : ℕ) : ℝ) * x ^ n)) x :=
      (hasDerivAt_pow (n + 1) x).const_mul _
    have hfun : (fun y : ℝ => y ^ (n + 1) * qeval (qprimAux n (c :: cs)) y) =
        fun y => ((c / ((n : ℚ) + 1) : ℚ) : ℝ) * y ^ (n + 1) +
          y ^ (n + 1 + 1) * qeval (qprimAux (n + 1) cs) y := by
      funext y; simp only [qprimAux, qeval_cons]; ring
    rw [hfun]
    refine (h1.add ih).congr_deriv ?_
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [qeval_cons]; push_cast
    field_simp
    ring

theorem hasDerivAt_qeval_qprim (p : List ℚ) (x : ℝ) :
    HasDerivAt (qeval (qprim p)) (qeval p x) x := by
  have h := hasDerivAt_pow_mul_qprimAux p 0 x
  simp only [zero_add, pow_one, pow_zero, one_mul] at h
  have hfun : qeval (qprim p) = fun y => y * qeval (qprimAux 0 p) y := by
    funext y; simp [qprim]
  rw [hfun]; exact h

/-- Fundamental theorem of calculus for rational polynomials. -/
theorem integral_qeval (p : List ℚ) (a b : ℝ) :
    (∫ x in a..b, qeval p x) = qeval (qprim p) b - qeval (qprim p) a :=
  integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_qeval_qprim p x)
    ((continuous_qeval p).intervalIntegrable _ _)

/-- `∑ c_k / (n + k + 1)`: the integral of `x^n p(x)` over `[0, 1]`. -/
def hilbRow : ℕ → List ℚ → ℚ
  | _, [] => 0
  | n, c :: cs => c / ((n : ℚ) + 1) + hilbRow (n + 1) cs

theorem integral_pow_mul_qeval :
    ∀ (p : List ℚ) (n : ℕ), (∫ x in (0 : ℝ)..1, x ^ n * qeval p x) = (hilbRow n p : ℝ)
  | [], n => by simp [hilbRow]
  | c :: cs, n => by
    have ih := integral_pow_mul_qeval cs (n + 1)
    have hfun : (fun x : ℝ => x ^ n * qeval (c :: cs) x) =
        fun x => (c : ℝ) * x ^ n + x ^ (n + 1) * qeval cs x := by
      funext x; simp only [qeval_cons]; ring
    have i1 : IntervalIntegrable (fun x : ℝ => (c : ℝ) * x ^ n) volume 0 1 :=
      (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x : ℝ => x ^ (n + 1) * qeval cs x) volume 0 1 :=
      ((continuous_pow _).mul (continuous_qeval cs)).intervalIntegrable _ _
    rw [hfun, intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      integral_pow, ih]
    simp only [hilbRow]; push_cast
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    simp

/-- The vector `(hilbRow 0 q, …, hilbRow (N - 1) q)`. -/
def hilbVec (N : ℕ) (q : List ℚ) : List ℚ := (List.range N).map fun n => hilbRow n q

def dotQ : List ℚ → List ℚ → ℚ
  | a :: as, b :: bs => a * b + dotQ as bs
  | _, _ => 0

private theorem integral_pow_mul_qeval_mul :
    ∀ (p q : List ℚ) (n : ℕ),
      (∫ x in (0 : ℝ)..1, x ^ n * (qeval p x * qeval q x)) =
        (dotQ p ((List.range p.length).map fun k => hilbRow (n + k) q) : ℝ)
  | [], _, _ => by simp [dotQ]
  | c :: cs, q, n => by
    have ih := integral_pow_mul_qeval_mul cs q (n + 1)
    have hfun : (fun x : ℝ => x ^ n * (qeval (c :: cs) x * qeval q x)) =
        fun x => (c : ℝ) * (x ^ n * qeval q x) + x ^ (n + 1) * (qeval cs x * qeval q x) := by
      funext x; simp only [qeval_cons]; ring
    have i1 : IntervalIntegrable (fun x : ℝ => (c : ℝ) * (x ^ n * qeval q x)) volume 0 1 :=
      (continuous_const.mul ((continuous_pow n).mul (continuous_qeval q))).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x : ℝ => x ^ (n + 1) * (qeval cs x * qeval q x)) volume 0 1 :=
      ((continuous_pow _).mul ((continuous_qeval cs).mul (continuous_qeval q))).intervalIntegrable _ _
    rw [hfun, intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      integral_pow_mul_qeval, ih]
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [dotQ, add_zero]
    push_cast
    congr 2
    congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply]
    congr 1; omega

/-- Gram pairing on `[0, 1]`: `∫₀¹ p q = p · hilbVec |p| q`. -/
theorem integral_qeval_mul_qeval (p q : List ℚ) :
    (∫ x in (0 : ℝ)..1, qeval p x * qeval q x) = (dotQ p (hilbVec p.length q) : ℝ) := by
  have h := integral_pow_mul_qeval_mul p q 0
  simp only [pow_zero, one_mul, zero_add] at h
  exact h

/-! ### Legendre polynomials -/

/-- One Bonnet step `P_{n+2} = ((2n+3) x P_{n+1} - (n+1) P_n) / (n+2)` on coefficient lists. -/
def qlegStep (n : ℕ) (p q : List ℚ) : List ℚ :=
  qsmul (1 / ((n : ℚ) + 2)) (qsub (qsmul (2 * (n : ℚ) + 3) (0 :: q)) (qsmul ((n : ℚ) + 1) p))

/-- The pair `(P_n, P_{n+1})`, computed linearly in `n`. -/
def qlegPair : ℕ → List ℚ × List ℚ
  | 0 => ([1], [0, 1])
  | n + 1 => ((qlegPair n).2, qlegStep n (qlegPair n).1 (qlegPair n).2)

/-- Coefficients of the Legendre polynomial `P_n`. -/
def qleg (n : ℕ) : List ℚ := (qlegPair n).1

private theorem legP_pair (x : ℝ) :
    ∀ n, legP n x = qeval (qlegPair n).1 x ∧ legP (n + 1) x = qeval (qlegPair n).2 x
  | 0 => by simp [qlegPair, legP_zero, legP_one]
  | n + 1 => by
    obtain ⟨h1, h2⟩ := legP_pair x n
    refine ⟨h2, ?_⟩
    simp only [qlegPair, qlegStep]
    rw [qeval_qsmul, qeval_qsub, qeval_qsmul, qeval_qsmul, qeval_cons, legP_succ_succ, ← h1, ← h2]
    push_cast
    have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

theorem legP_eq_qeval_qleg (n : ℕ) (x : ℝ) : legP n x = qeval (qleg n) x :=
  (legP_pair x n).1

/-! ### Primitives anchored at `-1` -/

/-- The primitive vanishing at `-1`. -/
def qprimNeg (p : List ℚ) : List ℚ := qsub (qprim p) [qevalQ (qprim p) (-1)]

/-- `k`-fold primitive anchored at `-1`. -/
def qiter : ℕ → List ℚ → List ℚ
  | 0, p => p
  | k + 1, p => qprimNeg (qiter k p)

theorem qeval_qprimNeg_neg_one (p : List ℚ) : qeval (qprimNeg p) (-1) = 0 := by
  rw [qprimNeg, qeval_qsub, show ((-1 : ℝ)) = ((-1 : ℚ) : ℝ) by push_cast; rfl, qeval_ratCast,
    qeval_ratCast]
  simp [qevalQ]

theorem iterPrim_qeval : ∀ (k : ℕ) (p : List ℚ) (y : ℝ),
    iterPrim k (qeval p) y = qeval (qiter k p) y
  | 0, _, _ => rfl
  | k + 1, p, y => by
    simp only [iterPrim, qiter]
    simp_rw [iterPrim_qeval k p]
    rw [integral_qeval]
    have h0 := qeval_qprimNeg_neg_one (qiter k p)
    rw [qprimNeg, qeval_qsub] at h0 ⊢
    simp only [qeval_cons, qeval_nil, mul_zero, add_zero] at h0 ⊢
    linarith

/-! ### Coefficient bounds -/

/-- Sum of absolute values of the coefficients. -/
def qabsSum (p : List ℚ) : ℚ := (p.map fun c => |c|).sum

theorem abs_qeval_le_qabsSum : ∀ (p : List ℚ) {x : ℝ}, |x| ≤ 1 → |qeval p x| ≤ qabsSum p
  | [], _, _ => by simp [qabsSum]
  | c :: cs, x, hx => by
    have ih := abs_qeval_le_qabsSum cs hx
    have hs : qabsSum (c :: cs) = |c| + qabsSum cs := by simp [qabsSum]
    rw [hs, qeval_cons, Rat.cast_add, Rat.cast_abs]
    calc |(c : ℝ) + x * qeval cs x| ≤ |(c : ℝ)| + |x| * |qeval cs x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(c : ℝ)| + 1 * (qabsSum cs : ℝ) :=
          add_le_add le_rfl (mul_le_mul hx ih (abs_nonneg _) zero_le_one)
      _ = _ := by rw [one_mul]

/-- All coefficients nonnegative. -/
def qnonneg (p : List ℚ) : Bool := p.all fun c => decide (0 ≤ c)

theorem qeval_nonneg_of_qnonneg : ∀ (p : List ℚ), qnonneg p = true → ∀ {x : ℝ}, 0 ≤ x →
    0 ≤ qeval p x
  | [], _, _, _ => by simp
  | c :: cs, h, x, hx => by
    simp only [qnonneg, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := qeval_nonneg_of_qnonneg cs h.2 hx
    simp only [qeval_cons]
    have hc : (0 : ℝ) ≤ c := by exact_mod_cast h.1
    positivity

/-- Rounding to the grid `ℤ / D` from below. -/
def qfloorD (D : ℕ) (x : ℚ) : ℚ := (⌊x * D⌋ : ℚ) / D

/-- Rounding to the nearest point of the grid `ℤ / D`. -/
def qroundD (D : ℕ) (x : ℚ) : ℚ := (⌊x * D + 1 / 2⌋ : ℚ) / D

theorem qfloorD_le {D : ℕ} (hD : 0 < D) (x : ℚ) : qfloorD D x ≤ x := by
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  rw [qfloorD, div_le_iff₀ hD']
  exact Int.floor_le _

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
