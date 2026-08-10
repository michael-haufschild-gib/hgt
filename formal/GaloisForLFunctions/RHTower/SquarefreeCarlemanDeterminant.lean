import GaloisForLFunctions.RHTower.SquarefreeCoronaPrimeCurrentField
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed

/-!
# The squarefree Carleman determinant and the first-trace reduction

The prime diagonal `A_s e_p = p^{-s} e_p` is Hilbert--Schmidt exactly on `Re s > 1/2`, and there
`I + A_s` is boundedly invertible: the direct-sum prime complex is uniformly acyclic.  Its second
regularized determinant

```text
D₂(s) = ∏_p (1 + p^{-s}) exp(-p^{-s})
```

converges there, is nowhere zero, and is holomorphic, because the Carleman-corrected logarithms
`log(1 + p^{-s}) - p^{-s}` are dominated by `2 p^{-2 Re s}`.  On `Re s > 1` the squarefree partition
factors as `Z(s) = D₂(s) exp(P(s))` with `P` the prime zeta function, so the entire divisor of the
squarefree Euler clock is carried by the single trace-class defect `exp(P)`; all higher determinant
orders form the nonvanishing factor `D₂`.
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-! ## The prime diagonal and its Euler multiplier -/

/-- The prime eigenvalue family `p ↦ p^{-s}` of the diagonal Euler operator. -/
def coronaPrimeEigenvalue (s : ℂ) (p : Nat.Primes) : ℂ := ((p : ℕ) : ℂ) ^ (-s)

/-- The Euler multiplier family `p ↦ 1 + p^{-s}` of `I + A_s`. -/
def coronaEulerMultiplier (s : ℂ) (p : Nat.Primes) : ℂ := 1 + coronaPrimeEigenvalue s p

theorem norm_coronaPrimeEigenvalue_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    ‖coronaPrimeEigenvalue s p‖ ≤ 3 / 4 :=
  norm_primeCpowNeg_le hs p

theorem norm_coronaEulerMultiplier_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    ‖coronaEulerMultiplier s p‖ ≤ 7 / 4 := by
  have h := norm_coronaPrimeEigenvalue_le hs p
  calc ‖coronaEulerMultiplier s p‖ ≤ ‖(1 : ℂ)‖ + ‖coronaPrimeEigenvalue s p‖ :=
        norm_add_le _ _
    _ ≤ 1 + 3 / 4 := by rw [norm_one]; linarith
    _ = 7 / 4 := by norm_num

theorem coronaEulerMultiplier_ne_zero {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    coronaEulerMultiplier s p ≠ 0 :=
  one_add_primeCpowNeg_ne_zero hs p

theorem norm_inv_coronaEulerMultiplier_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    ‖(coronaEulerMultiplier s p)⁻¹‖ ≤ 4 := by
  have hge : (1 : ℝ) / 4 ≤ ‖coronaEulerMultiplier s p‖ :=
    norm_one_add_primeCpowNeg_ge hs p
  have hpos : (0 : ℝ) < ‖coronaEulerMultiplier s p‖ := by linarith
  rw [norm_inv, inv_le_comm₀ hpos (by norm_num)]
  linarith

/-- The prime diagonal is square-summable exactly on the strict right half-plane. -/
theorem summable_norm_sq_coronaPrimeEigenvalue {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes => ‖coronaPrimeEigenvalue s p‖ ^ 2) := by
  have hfun : (fun p : Nat.Primes => ‖coronaPrimeEigenvalue s p‖ ^ 2) =
      fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by
    funext p
    rw [coronaPrimeEigenvalue, norm_primeCpowNeg,
      ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact Nat.Primes.summable_rpow.mpr (by linarith)

/-- **The prime diagonal operator** `A_s e_p = p^{-s} e_p` on `ℓ²(Primes)`. -/
def coronaPrimeDiagonal {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ] HTGeometry.IndexedEllTwo Nat.Primes :=
  HTGeometry.ellTwoDiagonal (coronaPrimeEigenvalue s) (norm_coronaPrimeEigenvalue_le hs)

/-- **The prime diagonal is Hilbert--Schmidt on `Re s > 1/2`.** -/
theorem isHilbertSchmidt_coronaPrimeDiagonal {s : ℂ} (hs : 1 / 2 < s.re) :
    ContinuousLinearMap.IsHilbertSchmidt (coronaPrimeDiagonal (le_of_lt hs)) :=
  (HTGeometry.isHilbertSchmidt_ellTwoDiagonal_iff (coronaPrimeEigenvalue s)
      (norm_coronaPrimeEigenvalue_le (le_of_lt hs))).mpr
    (summable_norm_sq_coronaPrimeEigenvalue hs)

/-- The diagonal operator `I + A_s`. -/
def coronaEulerOperator {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ] HTGeometry.IndexedEllTwo Nat.Primes :=
  HTGeometry.ellTwoDiagonal (coronaEulerMultiplier s) (norm_coronaEulerMultiplier_le hs)

/-- The diagonal inverse of `I + A_s`. -/
def coronaEulerInverse {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ] HTGeometry.IndexedEllTwo Nat.Primes :=
  HTGeometry.ellTwoDiagonal (fun p => (coronaEulerMultiplier s p)⁻¹)
    (norm_inv_coronaEulerMultiplier_le hs)

private theorem coronaEuler_mul_inv_bound {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    ‖coronaEulerMultiplier s p * (coronaEulerMultiplier s p)⁻¹‖ ≤ 1 := by
  rw [mul_inv_cancel₀ (coronaEulerMultiplier_ne_zero hs p), norm_one]

private theorem coronaEuler_inv_mul_bound {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    ‖(coronaEulerMultiplier s p)⁻¹ * coronaEulerMultiplier s p‖ ≤ 1 := by
  rw [inv_mul_cancel₀ (coronaEulerMultiplier_ne_zero hs p), norm_one]

private theorem ellTwoDiagonal_eq_id_of_eq_one {lam : Nat.Primes → ℂ} {C : ℝ}
    (hC : ∀ p, ‖lam p‖ ≤ C) (hlam : ∀ p, lam p = 1) :
    HTGeometry.ellTwoDiagonal lam hC =
      ContinuousLinearMap.id ℂ (HTGeometry.IndexedEllTwo Nat.Primes) := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext p
  rw [HTGeometry.ellTwoDiagonal_apply, hlam p, one_mul]
  rfl

/-- **Uniform acyclicity.**  `I + A_s` is boundedly invertible for every `Re s ≥ 1/2`: the
direct-sum prime complex has no `ℓ²` cohomology on the closed right half-plane. -/
theorem coronaEulerInverse_comp {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    coronaEulerInverse hs ∘L coronaEulerOperator hs =
      ContinuousLinearMap.id ℂ (HTGeometry.IndexedEllTwo Nat.Primes) := by
  rw [coronaEulerInverse, coronaEulerOperator,
    HTGeometry.ellTwoDiagonal_comp _ _ _ _ (coronaEuler_inv_mul_bound hs)]
  exact ellTwoDiagonal_eq_id_of_eq_one _ fun p =>
    inv_mul_cancel₀ (coronaEulerMultiplier_ne_zero hs p)

theorem coronaEulerOperator_comp {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    coronaEulerOperator hs ∘L coronaEulerInverse hs =
      ContinuousLinearMap.id ℂ (HTGeometry.IndexedEllTwo Nat.Primes) := by
  rw [coronaEulerInverse, coronaEulerOperator,
    HTGeometry.ellTwoDiagonal_comp _ _ _ _ (coronaEuler_mul_inv_bound hs)]
  exact ellTwoDiagonal_eq_id_of_eq_one _ fun p =>
    mul_inv_cancel₀ (coronaEulerMultiplier_ne_zero hs p)

/-! ## The Carleman logarithm -/

/-- The Carleman-corrected Euler logarithm `log(1 + p^{-s}) - p^{-s}`. -/
def squarefreeCarlemanLogFactor (s : ℂ) (p : Nat.Primes) : ℂ :=
  Complex.log (coronaEulerMultiplier s p) - coronaPrimeEigenvalue s p

theorem norm_squarefreeCarlemanLogFactor_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    ‖squarefreeCarlemanLogFactor s p‖ ≤ 2 * ‖coronaPrimeEigenvalue s p‖ ^ 2 := by
  have hnorm : ‖coronaPrimeEigenvalue s p‖ ≤ 3 / 4 := norm_coronaPrimeEigenvalue_le hs p
  have hlt : ‖coronaPrimeEigenvalue s p‖ < 1 := by linarith
  have hbase := Complex.norm_log_one_add_sub_self_le hlt
  have hinv : (1 - ‖coronaPrimeEigenvalue s p‖)⁻¹ ≤ 4 := by
    have hpos : (0 : ℝ) < 1 - ‖coronaPrimeEigenvalue s p‖ := by linarith
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  have hsqnn : (0 : ℝ) ≤ ‖coronaPrimeEigenvalue s p‖ ^ 2 := by positivity
  calc ‖squarefreeCarlemanLogFactor s p‖
      = ‖Complex.log (1 + coronaPrimeEigenvalue s p) - coronaPrimeEigenvalue s p‖ := by
        rw [squarefreeCarlemanLogFactor, coronaEulerMultiplier]
    _ ≤ ‖coronaPrimeEigenvalue s p‖ ^ 2 * (1 - ‖coronaPrimeEigenvalue s p‖)⁻¹ / 2 := hbase
    _ ≤ ‖coronaPrimeEigenvalue s p‖ ^ 2 * 4 / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        · exact mul_le_mul_of_nonneg_left hinv hsqnn
    _ = 2 * ‖coronaPrimeEigenvalue s p‖ ^ 2 := by ring

/-- The uniform Carleman majorant on a closed half-plane. -/
def squarefreeCarlemanMajorant (b : ℝ) (p : Nat.Primes) : ℝ :=
  2 * ((p : ℕ) : ℝ) ^ (-(2 * b))

theorem summable_squarefreeCarlemanMajorant {b : ℝ} (hb : 1 / 2 < b) :
    Summable (squarefreeCarlemanMajorant b) :=
  (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left 2

theorem norm_squarefreeCarlemanLogFactor_le_majorant {s : ℂ} {b : ℝ} (hb : 1 / 2 ≤ b)
    (hsb : b ≤ s.re) (p : Nat.Primes) :
    ‖squarefreeCarlemanLogFactor s p‖ ≤ squarefreeCarlemanMajorant b p := by
  have hs : 1 / 2 ≤ s.re := le_trans hb hsb
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_lt.le
  have hsq : ‖coronaPrimeEigenvalue s p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by
    rw [coronaPrimeEigenvalue, norm_primeCpowNeg,
      ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have hmono : ((p : ℕ) : ℝ) ^ (-(2 * s.re)) ≤ ((p : ℕ) : ℝ) ^ (-(2 * b)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  calc ‖squarefreeCarlemanLogFactor s p‖ ≤ 2 * ‖coronaPrimeEigenvalue s p‖ ^ 2 :=
        norm_squarefreeCarlemanLogFactor_le hs p
    _ = 2 * ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by rw [hsq]
    _ ≤ squarefreeCarlemanMajorant b p := by
        rw [squarefreeCarlemanMajorant]
        linarith

theorem summable_squarefreeCarlemanLogFactor {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (squarefreeCarlemanLogFactor s) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _)
    (fun p => norm_squarefreeCarlemanLogFactor_le_majorant (le_of_lt hs) le_rfl p)
    (summable_squarefreeCarlemanMajorant hs))

/-- The Carleman log-determinant `log det₂(I + A_s)`. -/
def squarefreeCarlemanLogDet (s : ℂ) : ℂ := ∑' p : Nat.Primes, squarefreeCarlemanLogFactor s p

/-- **The second regularized determinant** `det₂(I + A_s)`. -/
def squarefreeCarlemanDet (s : ℂ) : ℂ := Complex.exp (squarefreeCarlemanLogDet s)

/-- **`D₂` is nowhere zero on `Re s > 1/2`** — indeed everywhere, being an exponential. -/
theorem squarefreeCarlemanDet_ne_zero (s : ℂ) : squarefreeCarlemanDet s ≠ 0 :=
  Complex.exp_ne_zero _

/-- **The Weierstrass product form of the Carleman determinant.** -/
theorem hasProd_squarefreeCarlemanDet {s : ℂ} (hs : 1 / 2 < s.re) :
    HasProd (fun p : Nat.Primes =>
      coronaEulerMultiplier s p * Complex.exp (-coronaPrimeEigenvalue s p))
      (squarefreeCarlemanDet s) := by
  have hsum : HasSum (squarefreeCarlemanLogFactor s) (squarefreeCarlemanLogDet s) :=
    (summable_squarefreeCarlemanLogFactor hs).hasSum
  have hprod := hsum.cexp
  refine (hprod.congr_fun fun p => ?_)
  rw [Function.comp_apply, squarefreeCarlemanLogFactor,
    show Complex.log (coronaEulerMultiplier s p) - coronaPrimeEigenvalue s p =
      Complex.log (coronaEulerMultiplier s p) + (-coronaPrimeEigenvalue s p) by ring,
    Complex.exp_add, Complex.exp_log (coronaEulerMultiplier_ne_zero (le_of_lt hs) p)]

theorem squarefreeCarlemanDet_eq_tprod {s : ℂ} (hs : 1 / 2 < s.re) :
    squarefreeCarlemanDet s =
      ∏' p : Nat.Primes,
        coronaEulerMultiplier s p * Complex.exp (-coronaPrimeEigenvalue s p) :=
  (hasProd_squarefreeCarlemanDet hs).tprod_eq.symm

/-! ## Holomorphy -/

theorem differentiableOn_coronaPrimeEigenvalue (p : Nat.Primes) (U : Set ℂ) :
    DifferentiableOn ℂ (fun s : ℂ => coronaPrimeEigenvalue s p) U :=
  (differentiable_primeCpowNeg p).differentiableOn

theorem differentiableOn_squarefreeCarlemanLogFactor (p : Nat.Primes) {b : ℝ} (hb : 1 / 2 ≤ b) :
    DifferentiableOn ℂ (fun s : ℂ => squarefreeCarlemanLogFactor s p) {s : ℂ | b < s.re} := by
  have hlog : DifferentiableOn ℂ
      (fun s : ℂ => Complex.log (coronaEulerMultiplier s p)) {s : ℂ | b < s.re} := by
    intro s hs
    have hsre : b < s.re := hs
    have hslit : coronaEulerMultiplier s p ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      have hle : ‖coronaPrimeEigenvalue s p‖ ≤ 3 / 4 :=
        norm_coronaPrimeEigenvalue_le (by linarith) p
      have hre : |(coronaPrimeEigenvalue s p).re| ≤ ‖coronaPrimeEigenvalue s p‖ :=
        Complex.abs_re_le_norm _
      have : (coronaEulerMultiplier s p).re = 1 + (coronaPrimeEigenvalue s p).re := by
        rw [coronaEulerMultiplier, Complex.add_re, Complex.one_re]
      rw [this]
      cases abs_le.mp hre with
      | intro h1 h2 => linarith
    exact ((Complex.differentiableAt_log hslit).comp s
      (((differentiable_primeCpowNeg p).const_add 1).differentiableAt)).differentiableWithinAt
  exact hlog.sub (differentiableOn_coronaPrimeEigenvalue p _)

/-- **`log D₂` is holomorphic on `Re s > 1/2`.** -/
theorem differentiableOn_squarefreeCarlemanLogDet :
    DifferentiableOn ℂ squarefreeCarlemanLogDet {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hsre : 1 / 2 < s.re := hs
  set b : ℝ := (1 / 2 + s.re) / 2 with hbdef
  have hb : 1 / 2 < b := by rw [hbdef]; linarith
  have hbs : b < s.re := by rw [hbdef]; linarith
  have hopen : IsOpen {z : ℂ | b < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ squarefreeCarlemanLogDet {z : ℂ | b < z.re} := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := squarefreeCarlemanMajorant b) (summable_squarefreeCarlemanMajorant hb)
      (fun p => differentiableOn_squarefreeCarlemanLogFactor p (le_of_lt hb)) hopen ?_
    intro p w hw
    have hwre : b < w.re := hw
    exact norm_squarefreeCarlemanLogFactor_le_majorant (le_of_lt hb) (le_of_lt hwre) p
  exact ((hdiff.differentiableAt (hopen.mem_nhds hbs)).differentiableWithinAt)

/-- **`D₂` is holomorphic and nowhere zero on `Re s > 1/2`.** -/
theorem differentiableOn_squarefreeCarlemanDet :
    DifferentiableOn ℂ squarefreeCarlemanDet {s : ℂ | 1 / 2 < s.re} :=
  Complex.differentiable_exp.comp_differentiableOn differentiableOn_squarefreeCarlemanLogDet

/-! ## The prime zeta defect and the factorization -/

/-- The prime zeta function `P(s) = ∑_p p^{-s}`. -/
def coronaPrimeZeta (s : ℂ) : ℂ := ∑' p : Nat.Primes, coronaPrimeEigenvalue s p

theorem norm_coronaPrimeEigenvalue (s : ℂ) (p : Nat.Primes) :
    ‖coronaPrimeEigenvalue s p‖ = ((p : ℕ) : ℝ) ^ (-s.re) :=
  norm_primeCpowNeg s p

theorem summable_norm_coronaPrimeEigenvalue {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => ‖coronaPrimeEigenvalue s p‖) := by
  have hfun : (fun p : Nat.Primes => ‖coronaPrimeEigenvalue s p‖) =
      fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s.re) := by
    funext p
    exact norm_coronaPrimeEigenvalue s p
  rw [hfun]
  exact Nat.Primes.summable_rpow.mpr (by linarith)

theorem summable_coronaPrimeEigenvalue {s : ℂ} (hs : 1 < s.re) :
    Summable (coronaPrimeEigenvalue s) :=
  Summable.of_norm (summable_norm_coronaPrimeEigenvalue hs)

/-- **The trace-class defect.**  `exp(P(s))` is the product of the omitted Carleman corrections. -/
theorem hasProd_exp_coronaPrimeZeta {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => Complex.exp (coronaPrimeEigenvalue s p))
      (Complex.exp (coronaPrimeZeta s)) :=
  ((summable_coronaPrimeEigenvalue hs).hasSum).cexp

/-- **Sharp determinant-order reduction.**  On `Re s > 1` the squarefree partition is the Carleman
determinant times the exponential of the prime zeta function: every determinant order above the
first is absorbed into the nonvanishing factor `D₂`. -/
theorem squarefreePartition_eq_carleman_mul_exp {s : ℂ} (hs : 1 < s.re) :
    GaloisForLFunctions.squarefreePartition s =
      squarefreeCarlemanDet s * Complex.exp (coronaPrimeZeta s) := by
  have hhalf : 1 / 2 < s.re := by linarith
  have hprod := (hasProd_squarefreeCarlemanDet hhalf).mul (hasProd_exp_coronaPrimeZeta hs)
  have hfun : (fun p : Nat.Primes =>
      coronaEulerMultiplier s p * Complex.exp (-coronaPrimeEigenvalue s p) *
        Complex.exp (coronaPrimeEigenvalue s p)) =
      fun p : Nat.Primes => 1 + ((p : ℕ) : ℂ) ^ (-s) := by
    funext p
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one,
      coronaEulerMultiplier, coronaPrimeEigenvalue]
  rw [hfun] at hprod
  rw [GaloisForLFunctions.squarefreePartition, ← squarefree_eulerProduct_tprod hs,
    hprod.tprod_eq]

end RHTower
