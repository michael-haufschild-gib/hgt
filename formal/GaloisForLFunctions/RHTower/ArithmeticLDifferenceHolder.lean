import GaloisForLFunctions.HTGeometry.DirichletRealizationLead
import GaloisForLFunctions.RHTower.GammaShiftZetaReadout

/-!
# Difference-category Hölder theorem for arithmetic L-functions

Any finite-abscissa Dirichlet series with infinite nonzero coefficient support has no nontrivial
finite-order linear additive-shift equation over `ℂ(s)`.  Coefficient extraction turns such an
equation into a Vandermonde system at distinct reciprocal support indices.  Faithful Dirichlet
realization transfers the algebraic result to actual upper-end meromorphic germs.

The final specialization identifies the source and every nonnegative integral shift with the
Riemann zeta function on its half-plane of absolute convergence.
-/

open Polynomial ArithmeticFunction Finset

namespace GaloisForLFunctions

noncomputable section

open HTGeometry

local instance arithmeticDifferenceUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

/-- A finite-abscissa arithmetic L-function with infinite nonzero
Dirichlet-coefficient support. -/
structure ArithmeticLFunction where
  source : finiteAbscissaArithmeticSubalgebra
  support_infinite : (Function.support source.1).Infinite

def ArithmeticLFunction.shiftSource (F : ArithmeticLFunction) (j : ℕ) :
    finiteAbscissaArithmeticSubalgebra :=
  finiteAbscissaDirichletShift (j : ℂ) F.source

theorem ArithmeticLFunction.shiftSource_apply (F : ArithmeticLFunction)
    (j : ℕ) {n : ℕ} :
    (F.shiftSource j).1 n = ((n : ℂ) ^ j)⁻¹ * F.source.1 n := by
  rw [ArithmeticLFunction.shiftSource, finiteAbscissaDirichletShift_apply, cpowWeight]
  rw [← Complex.cpow_natCast, Complex.cpow_neg, Complex.cpow_natCast]

def ArithmeticLFunction.shiftFAPoly (F : ArithmeticLFunction) (j : ℕ) : FAPoly :=
  Polynomial.C (F.shiftSource j)

theorem coeffPoly_faToDirPoly_arithmeticLShift (F : ArithmeticLFunction)
    (j : ℕ) (n : ℕ) :
    _root_.HTGeometry.DirPoly.coeffPoly (faToDirPoly (F.shiftFAPoly j)) n =
      Polynomial.C (((n : ℂ) ^ j)⁻¹ * F.source.1 n) := by
  rw [ArithmeticLFunction.shiftFAPoly]
  rw [faToDirPoly]
  change _root_.HTGeometry.DirPoly.coeffPoly
    ((Polynomial.C (F.shiftSource j)).map
      (finiteAbscissaArithmeticSubalgebra.val :
        finiteAbscissaArithmeticSubalgebra →+* ArithmeticFunction ℂ)) n = _
  rw [Polynomial.map_C]
  change _root_.HTGeometry.DirPoly.coeffPoly
    (Polynomial.C ((F.shiftSource j).1)) n = _
  rw [show Polynomial.C ((F.shiftSource j).1) =
      Polynomial.monomial 0 ((F.shiftSource j).1) by simp]
  rw [_root_.HTGeometry.DirPoly.coeffPoly_monomial,
    F.shiftSource_apply j]
  simp

theorem coeffPoly_faToDirPoly_faEmb_generic (p : ℂ[X]) (n : ℕ) :
    _root_.HTGeometry.DirPoly.coeffPoly (faToDirPoly (faEmb p)) n =
      if n = 1 then p else 0 := by
  rw [← _root_.HTGeometry.DirPoly.toDirFormal_apply, faToDirPoly_emb,
    _root_.HTGeometry.DirPoly.toDirFormal_emb,
    _root_.HTGeometry.DirFormal.embHom_apply]

theorem coeffPoly_faToDirPoly_faEmb_mul_arithmeticLShift
    (F : ArithmeticLFunction) (p : ℂ[X]) (j : ℕ) {n : ℕ} (hn : n ≠ 0) :
    _root_.HTGeometry.DirPoly.coeffPoly
        (faToDirPoly (faEmb p * F.shiftFAPoly j)) n =
      p * Polynomial.C (((n : ℂ) ^ j)⁻¹ * F.source.1 n) := by
  rw [map_mul, _root_.HTGeometry.DirPoly.coeffPoly_mul]
  rw [Finset.sum_eq_single (1, n)]
  · rw [coeffPoly_faToDirPoly_faEmb_generic, if_pos rfl,
      coeffPoly_faToDirPoly_arithmeticLShift F j n]
  · intro x hx hne
    have hx1 : x.1 ≠ 1 := by
      intro hx1
      obtain ⟨hprod, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      apply hne
      apply Prod.ext hx1
      simpa [hx1] using hprod
    rw [coeffPoly_faToDirPoly_faEmb_generic, if_neg hx1, zero_mul]
  · intro hmem
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn⟩) hmem

theorem coeffPoly_faToDirPoly_arithmeticLShift_relation
    (F : ArithmeticLFunction) {N : ℕ} (c : Fin (N + 1) → ℂ[X])
    {n : ℕ} (hn : n ≠ 0) :
    _root_.HTGeometry.DirPoly.coeffPoly
        (faToDirPoly (∑ j : Fin (N + 1), faEmb (c j) * F.shiftFAPoly j)) n =
      ∑ j : Fin (N + 1),
        c j * Polynomial.C (((n : ℂ) ^ (j : ℕ))⁻¹ * F.source.1 n) := by
  change (_root_.HTGeometry.DirPoly.toDirFormal
    (faToDirPoly (∑ j : Fin (N + 1), faEmb (c j) * F.shiftFAPoly j))) n = _
  rw [map_sum, map_sum]
  let ev : _root_.HTGeometry.DirFormal →+ ℂ[X] :=
    { toFun := fun f => f n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ j : Fin (N + 1),
    _root_.HTGeometry.DirPoly.toDirFormal
      (faToDirPoly (faEmb (c j) * F.shiftFAPoly j))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact coeffPoly_faToDirPoly_faEmb_mul_arithmeticLShift F (c j) j hn

theorem ArithmeticLFunction.shiftFAPoly_no_polynomial_relation
    (F : ArithmeticLFunction) {N : ℕ} (c : Fin (N + 1) → ℂ[X])
    (h : ∑ j : Fin (N + 1), faEmb (c j) * F.shiftFAPoly j = 0) :
    c = 0 := by
  letI : Infinite ↑(Function.support F.source.1) := F.support_infinite.to_subtype
  let supportIndex : ℕ ↪ ↑(Function.support F.source.1) :=
    Infinite.natEmbedding ↑(Function.support F.source.1)
  let node : Fin (N + 1) → ℂ[X] := fun i =>
    Polynomial.C ((((supportIndex i : ↑(Function.support F.source.1)) : ℕ) : ℂ)⁻¹)
  have hnode : Function.Injective node := by
    intro i j hij
    apply Fin.ext
    have hinv : ((((supportIndex i : ↑(Function.support F.source.1)) : ℕ) : ℂ)⁻¹) =
        ((((supportIndex j : ↑(Function.support F.source.1)) : ℕ) : ℂ)⁻¹) :=
      Polynomial.C_injective hij
    have hcast : (((supportIndex i : ↑(Function.support F.source.1)) : ℕ) : ℂ) =
        (((supportIndex j : ↑(Function.support F.source.1)) : ℕ) : ℂ) :=
      inv_injective hinv
    have hnat : ((supportIndex i : ↑(Function.support F.source.1)) : ℕ) =
        (supportIndex j : ℕ) := by
      exact_mod_cast hcast
    exact supportIndex.injective (Subtype.ext hnat)
  apply Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero hnode
  intro i
  have hindex_ne : ((supportIndex i : ↑(Function.support F.source.1)) : ℕ) ≠ 0 := by
    intro hi
    have hsupp := (supportIndex i).property
    rw [hi] at hsupp
    exact hsupp F.source.1.map_zero
  have hmap := congrArg faToDirPoly h
  have hmap' : faToDirPoly
      (∑ j : Fin (N + 1), faEmb (c j) * F.shiftFAPoly j) = 0 := by
    simpa using hmap
  have hcoeff := congrArg (fun P : _root_.HTGeometry.DirPoly =>
    _root_.HTGeometry.DirPoly.coeffPoly P (supportIndex i)) hmap'
  rw [coeffPoly_faToDirPoly_arithmeticLShift_relation F c
      hindex_ne,
    _root_.HTGeometry.DirPoly.coeffPoly_zero] at hcoeff
  have hfactor :
      (∑ j : Fin (N + 1), c j * node i ^ (j : ℕ)) *
          Polynomial.C (F.source.1 (supportIndex i)) = 0 := by
    rw [Finset.sum_mul]
    simpa [node, ← Polynomial.C_pow, inv_pow, mul_assoc] using hcoeff
  exact (mul_eq_zero.mp hfactor).resolve_right
    (Polynomial.C_ne_zero.mpr (supportIndex i).property)

def ArithmeticLFunction.shiftUpperEnd (F : ArithmeticLFunction) (j : ℕ) :
    upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero (F.shiftSource j)

theorem ArithmeticLFunction.dirRealize_faEmb_mul_shift
    (F : ArithmeticLFunction) (p : ℂ[X]) (j : ℕ) :
    dirRealize (faEmb p * F.shiftFAPoly j) =
      Polynomial.aeval dirCoordMero p * F.shiftUpperEnd j := by
  rw [map_mul, dirRealize_faEmb]
  simp [ArithmeticLFunction.shiftFAPoly, ArithmeticLFunction.shiftUpperEnd]

theorem ArithmeticLFunction.shiftUpperEnd_no_polynomial_relation
    (F : ArithmeticLFunction) {N : ℕ} (c : Fin (N + 1) → ℂ[X])
    (h : ∑ j : Fin (N + 1),
        Polynomial.aeval dirCoordMero (c j) * F.shiftUpperEnd j = 0) :
    c = 0 := by
  apply F.shiftFAPoly_no_polynomial_relation c
  apply dirRealize_injective
  rw [map_zero dirRealize]
  rw [map_sum]
  simpa only [F.dirRealize_faEmb_mul_shift] using h

/-- Rotate a polynomial in the upper-end coordinate to the Dirichlet coordinate. -/
def dirScalePolynomial (p : ℂ[X]) : ℂ[X] :=
  p.comp (Polynomial.C Complex.I * Polynomial.X)

theorem aeval_dirCoordMero_dirScalePolynomial (p : ℂ[X]) :
    Polynomial.aeval dirCoordMero (dirScalePolynomial p) =
      Polynomial.aeval coordMero p := by
  rw [dirScalePolynomial, Polynomial.aeval_def, Polynomial.eval₂_comp]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [dirCoordMero_eq]
  congr 1
  rw [← mul_assoc, ← map_mul]
  norm_num

theorem dirScalePolynomial_injective : Function.Injective dirScalePolynomial := by
  intro p q hpq
  apply aeval_coordMero_injective
  change Polynomial.aeval coordMero p = Polynomial.aeval coordMero q
  rw [← aeval_dirCoordMero_dirScalePolynomial p,
    ← aeval_dirCoordMero_dirScalePolynomial q, hpq]

theorem ArithmeticLFunction.shiftUpperEnd_no_coordinate_polynomial_relation
    (F : ArithmeticLFunction) {N : ℕ} (c : Fin (N + 1) → ℂ[X])
    (h : ∑ j : Fin (N + 1),
        Polynomial.aeval coordMero (c j) * F.shiftUpperEnd j = 0) :
    c = 0 := by
  have hscale : ∑ j : Fin (N + 1),
      Polynomial.aeval dirCoordMero (dirScalePolynomial (c j)) *
        F.shiftUpperEnd j = 0 := by
    simpa only [aeval_dirCoordMero_dirScalePolynomial] using h
  have hz := F.shiftUpperEnd_no_polynomial_relation
    (fun j => dirScalePolynomial (c j)) hscale
  funext j
  apply dirScalePolynomial_injective
  simpa [dirScalePolynomial] using congrFun hz j

theorem ArithmeticLFunction.shiftUpperEnd_no_rational_relation
    (F : ArithmeticLFunction) {N : ℕ} (r : Fin (N + 1) → RatFunc ℂ)
    (h : ∑ j : Fin (N + 1),
        upperEndRatfuncToMero (r j) * F.shiftUpperEnd j = 0) :
    r = 0 := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℂ[X]) r
  choose p hp using hd
  have hpoly : ∑ j : Fin (N + 1),
      Polynomial.aeval coordMero (p j) * F.shiftUpperEnd j = 0 := by
    calc
      ∑ j : Fin (N + 1),
          Polynomial.aeval coordMero (p j) * F.shiftUpperEnd j =
          upperEndRatfuncToMero
              (algebraMap ℂ[X] (RatFunc ℂ) (d : ℂ[X])) *
            ∑ j : Fin (N + 1),
              upperEndRatfuncToMero (r j) * F.shiftUpperEnd j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hpj := congrArg upperEndRatfuncToMero (hp j)
        rw [Algebra.smul_def, map_mul] at hpj
        rw [upperEndRatfuncToMero_algebraMap_polynomial] at hpj
        rw [← aeval_coordMero_eq] at hpj
        rw [hpj]
        ring
      _ = 0 := by rw [h, mul_zero]
  have hpzero := F.shiftUpperEnd_no_coordinate_polynomial_relation p hpoly
  funext j
  change r j = 0
  have hpj := hp j
  have hpj0 : p j = 0 := by simpa using congrFun hpzero j
  rw [hpj0, map_zero (algebraMap ℂ[X] (RatFunc ℂ)),
    Algebra.smul_def] at hpj
  have hdne : algebraMap ℂ[X] (RatFunc ℂ) (d : ℂ[X]) ≠ 0 := by
    intro hdzero
    apply nonZeroDivisors.ne_zero d.2
    apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
    exact hdzero.trans (map_zero (algebraMap ℂ[X] (RatFunc ℂ))).symm
  exact (mul_eq_zero.mp hpj.symm).resolve_left hdne

/-- Existence of a nonzero finite-order linear additive-shift equation over `ℂ(s)`. -/
def ArithmeticLFunction.HasFiniteOrderLinearShiftEquation
    (F : ArithmeticLFunction) : Prop :=
  ∃ (N : ℕ) (r : Fin (N + 1) → RatFunc ℂ), r ≠ 0 ∧
    ∑ j : Fin (N + 1),
      upperEndRatfuncToMero (r j) * F.shiftUpperEnd j = 0

/-- Difference-category Hölder theorem for every arithmetic L-function. -/
theorem ArithmeticLFunction.not_hasFiniteOrderLinearShiftEquation
    (F : ArithmeticLFunction) : ¬ F.HasFiniteOrderLinearShiftEquation := by
  rintro ⟨N, r, hr, hrelation⟩
  exact hr (F.shiftUpperEnd_no_rational_relation r hrelation)

theorem ArithmeticLFunction.LSeries_shiftSource_eq
    (F : ArithmeticLFunction) (j : ℕ) (s : ℂ) :
    LSeries (fun n => (F.shiftSource j).1 n) s =
      LSeries (fun n => F.source.1 n) (s + j) := by
  change LSeries (fun n => dirichletShift (j : ℂ) F.source.1 n) s = _
  rw [LSeries_dirichletShift]

/-- Arithmetic function whose L-series is the Riemann zeta function. -/
def zetaArithmeticFunction : ArithmeticFunction ℂ :=
  ⟨zetaValueCoeff, zetaValueCoeff_zero⟩

def zetaFiniteAbscissaSource : finiteAbscissaArithmeticSubalgebra := by
  refine ⟨zetaArithmeticFunction, 1, ?_⟩
  intro y hy
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
  · intro n hn
    change ‖if n = 0 then (0 : ℂ) else 1‖ ≤ 1
    rw [if_neg hn]
    norm_num
  · simpa using hy

@[simp] theorem zetaFiniteAbscissaSource_apply {n : ℕ} (hn : n ≠ 0) :
    zetaFiniteAbscissaSource.1 n = 1 := by
  simp [zetaFiniteAbscissaSource, zetaArithmeticFunction, zetaValueCoeff, hn]

theorem zetaFiniteAbscissaSource_support_infinite :
    (Function.support zetaFiniteAbscissaSource.1).Infinite := by
  refine (Set.infinite_range_of_injective Nat.succ_injective).mono ?_
  rintro n ⟨k, rfl⟩
  change zetaFiniteAbscissaSource.1 k.succ ≠ 0
  rw [zetaFiniteAbscissaSource_apply (Nat.succ_ne_zero k)]
  norm_num

/-- Riemann zeta as an arithmetic L-function in the difference-Hölder carrier. -/
def riemannZetaArithmeticLFunction : ArithmeticLFunction where
  source := zetaFiniteAbscissaSource
  support_infinite := zetaFiniteAbscissaSource_support_infinite

theorem LSeries_riemannZetaArithmeticLFunction_eq
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => riemannZetaArithmeticLFunction.source.1 n) s =
      riemannZeta s := by
  exact LSeries_zetaValueCoeff_eq_riemannZeta hs

theorem LSeries_riemannZetaArithmeticLFunction_shift_eq
    (j : ℕ) {s : ℂ} (hs : 1 < (s + j).re) :
    LSeries (fun n => (riemannZetaArithmeticLFunction.shiftSource j).1 n) s =
      riemannZeta (s + j) := by
  rw [riemannZetaArithmeticLFunction.LSeries_shiftSource_eq]
  exact LSeries_riemannZetaArithmeticLFunction_eq hs

/-- Difference-category Hölder theorem for the Riemann zeta function. -/
theorem riemannZeta_not_hasFiniteOrderLinearShiftEquation :
    ¬ riemannZetaArithmeticLFunction.HasFiniteOrderLinearShiftEquation :=
  riemannZetaArithmeticLFunction.not_hasFiniteOrderLinearShiftEquation

end

end GaloisForLFunctions
