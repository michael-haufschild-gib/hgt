import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeightedAdelicProductAdmitsStrictlyTemperedBarriers
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Summable adelic radial profiles on the rational torus

Submultiplicativity of the local matrix norm gives a triangle bound for
normalized radial products. On the base torus orbit their exact value is
`1 / (|num(q)| * den(q))`, including negative rationals. Transport therefore
bounds every restricted-vertex orbit by a summable height power whenever
the radial exponent exceeds one half. Equal-fibre exceptions are finite.
-/

set_option autoImplicit false
noncomputable section
open Filter Matrix
open scoped Classical BigOperators Topology
namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic AdelicRadial CoupledProductObstruction
local instance (p : Prime) : Fact p.1.Prime := ⟨p.2⟩

private theorem glFactor_mul_le (p : Prime) (g h : LocalGL p) :
    glFactor p g * glFactor p h ≤ glFactor p (g * h) := by
  have hd := matrixMaxNorm_pos p (g * h)
  have hm := entrySize_mul_le p g.val h.val
  unfold glFactor
  rw [GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul,
    Real.sqrt_mul (norm_nonneg _), div_mul_div_comm]
  exact div_le_div_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hd hm

private theorem pglFactor_mul_le (p : Prime) (g h : LocalPGL p) :
    pglFactor p g * pglFactor p h ≤ pglFactor p (g * h) := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g =>
    induction h using ProjGenLinGroup.induction_on with
    | mk h =>
      rw [← map_mul, pglFactor_mk, pglFactor_mk, pglFactor_mk]
      exact glFactor_mul_le p g h

/-- The normalized local Green factors satisfy the multiplicative triangle inequality. -/
theorem localFactor_triangle (p : Prime) (x y z : LocalVertex p) :
    localFactor p x y * localFactor p y z ≤ localFactor p x z := by
  induction x using Quotient.inductionOn with
  | h g =>
    induction y using Quotient.inductionOn with
    | h h =>
      induction z using Quotient.inductionOn with
      | h k =>
        simp only [localFactor_mk]
        have ht := pglFactor_mul_le p (g⁻¹ * h) (h⁻¹ * k)
        simpa only [mul_assoc, mul_inv_cancel_left] using ht

/-- The local triangle inequalities pass to the actual restricted adelic product. -/
theorem product_triangle (x y z : FiniteVertices) :
    finiteGreenProduct x y * finiteGreenProduct y z ≤ finiteGreenProduct x z := by
  have hxy := hasFiniteMulSupport_localFactor x y
  have hyz := hasFiniteMulSupport_localFactor y z
  have hxz := hasFiniteMulSupport_localFactor x z
  unfold finiteGreenProduct
  rw [← finprod_mul_distrib hxy hyz]
  exact finprod_le_finprod (hxy.mul hyz)
    (fun p => mul_nonneg (localFactor_pos p _ _).le (localFactor_pos p _ _).le)
    hxz (fun p => localFactor_triangle p _ _ _)

/-- A fixed change of endpoints costs a finite positive factor, uniformly in the adelic transport. -/
theorem product_transport_bound (a : FiniteAdelicGroup) (x y : FiniteVertices) :
    finiteGreenProduct x (a • y) ≤
      finiteGreenProduct finiteBase (a • finiteBase) /
        (finiteGreenProduct finiteBase x * finiteGreenProduct y finiteBase) := by
  apply (le_div_iff₀ (mul_pos (product_pos _ _) (product_pos _ _))).mpr
  have h₁ := product_triangle finiteBase x (a • y)
  have h₂ := product_triangle finiteBase (a • y) (a • finiteBase)
  rw [finiteGreenProduct_smul] at h₂
  have h₃ := (mul_le_mul_of_nonneg_right h₁ (product_pos y finiteBase).le).trans h₂
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h₃

/-- Product of the absolute reduced numerator and positive denominator. -/
def rationalTorusHeight (q : ℚˣ) : ℝ := ((q : ℚ).num.natAbs : ℝ) * (q : ℚ).den

/-- Finite component of the actual conjugated rational split torus. -/
def rationalTorusFinite (q : ℚˣ) : FiniteAdelicGroup :=
  (torusElem (q : ℚ) q.ne_zero).1.2

private theorem torus_conjugate_diagonal (q : ℚˣ) :
    OppositeAdelic.weyl⁻¹ * OppositeAdelic.diagonal (q : ℚ) q.ne_zero * OppositeAdelic.weyl =
      OppositeAdelic.diagonal (q : ℚ)⁻¹ (inv_ne_zero q.ne_zero) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [OppositeAdelic.weyl, OppositeAdelic.diagonal, Matrix.mul_apply, Fin.sum_univ_two]

private theorem rational_scalar_entry (u : ℚˣ) (i j : Fin 2) :
    (GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) ℚ) i j =
      if i = j then (u : ℚ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

/-- Exact radial height on the base torus orbit, for either sign of the rational parameter. -/
theorem product_base_rationalTorus (q : ℚˣ) :
    finiteGreenProduct finiteBase (rationalTorusFinite q • finiteBase) =
      1 / rationalTorusHeight q := by
  let a : ℕ := (q : ℚ).num.natAbs
  let b : ℕ := (q : ℚ).den
  have ha : 0 < a := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr q.ne_zero)
  have hb : 0 < b := (q : ℚ).den_pos
  let u : ℕ+ := ⟨b ^ 2, pow_pos hb 2⟩
  let v : ℕ+ := ⟨a ^ 2, pow_pos ha 2⟩
  have hn : ((q : ℚ).num : ℚ) ≠ 0 := by exact_mod_cast (Rat.num_ne_zero.mpr q.ne_zero)
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  let sc : ℚˣ := Units.mk0 (((q : ℚ).num : ℚ) * b) (mul_ne_zero hn hbq)
  have hq : (q : ℚ) = ((q : ℚ).num : ℚ) / b := (Rat.num_div_den _).symm
  have ha2 : (a : ℚ) ^ 2 = ((q : ℚ).num : ℚ) ^ 2 := by
    change ((q : ℚ).num.natAbs : ℚ) ^ 2 = _
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have hnum : (q : ℚ) * b = ((q : ℚ).num : ℚ) := (eq_div_iff hbq).mp hq
  have h00 : (q : ℚ)⁻¹ * (((q : ℚ).num : ℚ) * b) = (b : ℚ) ^ 2 := by
    calc
      _ = (q : ℚ)⁻¹ * (((q : ℚ) * b) * b) :=
        congrArg (fun n : ℚ => (q : ℚ)⁻¹ * (n * b)) hnum.symm
      _ = _ := by field_simp [q.ne_zero]
  have h11 : (q : ℚ) * (((q : ℚ).num : ℚ) * b) = (a : ℚ) ^ 2 := by
    calc
      _ = ((q : ℚ) * b) * ((q : ℚ).num : ℚ) := by ring
      _ = ((q : ℚ).num : ℚ) ^ 2 := by rw [hnum]; ring
      _ = _ := ha2.symm
  -- A signed scalar turns the diagonal entries into denominator and numerator squares.
  have hGL : SpecialLinearGroup.toGL
        (OppositeAdelic.diagonal (q : ℚ)⁻¹ (inv_ne_zero q.ne_zero)) *
        GeneralLinearGroup.scalar (Fin 2) sc = diagGL u v := by
    apply Units.ext
    ext i j
    simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      rational_scalar_entry]
    fin_cases i <;> fin_cases j
    · simpa [OppositeAdelic.diagonal, SpecialLinearGroup.toGL, diagGL,
        sc, u] using h00
    · simp [OppositeAdelic.diagonal, SpecialLinearGroup.toGL, diagGL]
    · simp [OppositeAdelic.diagonal, SpecialLinearGroup.toGL, diagGL]
    · simpa [OppositeAdelic.diagonal, SpecialLinearGroup.toGL, diagGL,
        sc, v] using h11
  have hloc (p : Prime) :
      localFactor p (finiteBase.1 p) ((rationalTorusFinite q • finiteBase).1 p) =
        glFactor p (localGLMap p (diagGL u v)) := by
    change localFactor p (baseVertex p)
      ((conjugateEmbedding (OppositeAdelic.diagonal (q : ℚ) q.ne_zero)).2 p • baseVertex p) = _
    rw [conjugateEmbedding_finite, torus_conjugate_diagonal, localProj_toGL]
    change pglFactor p (1⁻¹ * (ProjGenLinGroup.mk (localGLMap p
      (SpecialLinearGroup.toGL (OppositeAdelic.diagonal (q : ℚ)⁻¹ (inv_ne_zero q.ne_zero)))) * 1)) = _
    rw [inv_one, one_mul, mul_one, pglFactor_mk]
    rw [← hGL, map_mul]
    change glFactor p _ = glFactor p (_ * GeneralLinearGroup.map (Rat.castHom ℚ_[p.1])
      (GeneralLinearGroup.scalar (Fin 2) sc))
    rw [GeneralLinearGroup.map_scalar, glFactor_mul_scalar]
  unfold finiteGreenProduct
  simp_rw [hloc]
  rw [finprod_glFactor_diagGL]
  have hc : Nat.Coprime b a := (q : ℚ).reduced.symm
  have hcop : Nat.gcd (b ^ 2) (a ^ 2) = 1 := (hc.pow 2 2).gcd_eq_one
  change (Nat.gcd (b ^ 2) (a ^ 2) : ℝ) /
    Real.sqrt (((b ^ 2 : ℕ) : ℝ) * ((a ^ 2 : ℕ) : ℝ)) = _
  rw [hcop, Nat.cast_one, Nat.cast_pow, Nat.cast_pow, ← mul_pow,
    Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  unfold rationalTorusHeight
  dsimp only [a, b]
  rw [mul_comm]

/-- The reduced numerator-denominator embedding bounds the height sum by two convergent power series. -/
theorem summable_rationalTorusHeight_rpow (t : ℝ) (ht : 1 < t) :
    Summable (fun q : ℚˣ => rationalTorusHeight q ^ (-t)) := by
  have hi : Summable (fun k : ℤ => (k.natAbs : ℝ) ^ (-t)) :=
    (Real.summable_abs_int_rpow ht).congr fun k => by rw [Nat.cast_natAbs, Int.cast_abs]
  have hn : Summable (fun n : ℕ => (n : ℝ) ^ (-t)) :=
    Real.summable_nat_rpow.mpr (by linarith only [ht])
  have hp := hi.mul_of_nonneg hn (fun _ => by positivity) (fun _ => by positivity)
  let e : ℚˣ → ℤ × ℕ := fun q => ((q : ℚ).num, (q : ℚ).den)
  have he : Function.Injective e := by
    intro q r h
    have hnum := congrArg Prod.fst h
    have hden := congrArg Prod.snd h
    apply Units.ext
    rw [← Rat.num_div_den (q : ℚ), ← Rat.num_div_den (r : ℚ)]
    exact congrArg₂ (fun a : ℤ => fun b : ℕ => (a : ℚ) / b) hnum hden
  have hs := hp.comp_injective he
  refine hs.congr fun q => ?_
  exact (Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)).symm

theorem rationalTorusHeight_pos (q : ℚˣ) : 0 < rationalTorusHeight q := by
  unfold rationalTorusHeight
  have hn : 0 < (q : ℚ).num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr q.ne_zero)
  exact mul_pos (by exact_mod_cast hn) (by exact_mod_cast (q : ℚ).den_pos)

theorem powerProfile_rationalTorus_le (s : ℝ) (hs : 0 ≤ s)
    (x y : FiniteVertices) (q : ℚˣ) :
    powerProfile s x (rationalTorusFinite q • y) ≤
      (finiteGreenProduct finiteBase x * finiteGreenProduct y finiteBase) ^ (-(2 * s)) *
        rationalTorusHeight q ^ (-(2 * s)) := by
  have h := product_transport_bound (rationalTorusFinite q) x y
  rw [product_base_rationalTorus] at h
  have hd := mul_pos (product_pos finiteBase x) (product_pos y finiteBase)
  have hq := rationalTorusHeight_pos q
  calc
    _ ≤ ((1 / rationalTorusHeight q) /
        (finiteGreenProduct finiteBase x * finiteGreenProduct y finiteBase)) ^ (2 * s) :=
      Real.rpow_le_rpow (product_pos _ _).le h (mul_nonneg (by norm_num) hs)
    _ = _ := by
      rw [Real.div_rpow (one_div_pos.mpr hq).le hd.le,
        Real.div_rpow (by norm_num) hq.le, Real.one_rpow,
        Real.rpow_neg hd.le, Real.rpow_neg hq.le]
      ring

/-- Every strictly tempered radial profile is summable on every rational-torus orbit of restricted vertices. -/
theorem summable_powerProfile_rationalTorus (s : ℝ) (hs : 1 / 2 < s)
    (x y : FiniteVertices) :
    Summable (fun q : ℚˣ => powerProfile s x (rationalTorusFinite q • y)) := by
  have hs0 : 0 ≤ s := by linarith only [hs]
  have ht : 1 < 2 * s := by linarith only [hs]
  exact Summable.of_nonneg_of_le (fun q => (powerProfile_pos s x _).le)
    (fun q => powerProfile_rationalTorus_le s hs0 x y q)
    ((summable_rationalTorusHeight_rpow (2 * s) ht).mul_left _)

theorem summable_barrierProfile_rationalTorus (x y : FiniteVertices) :
    Summable (fun q : ℚˣ => barrierProfile x (rationalTorusFinite q • y)) :=
  summable_powerProfile_rationalTorus barrierExponent barrierExponent_gt_half x y

/-- Equal-fibre terms have profile one and therefore form a finite exceptional set. -/
theorem finite_rationalTorus_equal_fibres (x y : FiniteVertices) :
    {q : ℚˣ | x = rationalTorusFinite q • y}.Finite := by
  have he := (summable_barrierProfile_rationalTorus x y).tendsto_cofinite_zero.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)
  have hf : {q : ℚˣ | 1 ≤ barrierProfile x (rationalTorusFinite q • y)}.Finite := by
    simpa only [not_lt] using Filter.eventually_cofinite.mp he
  apply hf.subset
  intro q hq
  change x = rationalTorusFinite q • y at hq
  change 1 ≤ barrierProfile x (rationalTorusFinite q • y)
  simpa only [← hq, barrierProfile_self] using (le_rfl : (1 : ℝ) ≤ 1)

#print axioms product_base_rationalTorus
#print axioms summable_powerProfile_rationalTorus
#print axioms finite_rationalTorus_equal_fibres

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
