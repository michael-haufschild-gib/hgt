/-
# Layer embeddings of the graded Mahler carrier

Each dyadic layer of the graded Mahler carrier is a copy of the two-variable rational
function field: the base variable maps to a positive Hahn monomial `t^{q₀}` and the
eigenvariable to `ℓ`.  This module constructs the embedding in stages — complex rational
functions evaluate at the monomial inside the complex-coefficient Hahn subfield, and the
eigenvariable layer follows on top — and proves the coefficient laws needed for injectivity.
-/
import Mathlib
import GaloisForLFunctions.U0.MahlerHahnCarrier
import GaloisForLFunctions.U0.MahlerTwoVariable

namespace GaloisForLFunctions

open Polynomial HahnSeries

noncomputable section

/-! ## Evaluation of complex polynomials at a positive Hahn monomial -/

/-- Evaluation of complex polynomials at the monomial `t^{q₀}`, inside complex-coefficient
Hahn series. -/
def monoPolyEval (q₀ : ℚ) : Polynomial ℂ →+* HahnSeries ℚ ℂ :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single q₀ 1)

theorem monoPolyEval_coeff {q₀ : ℚ} (hq₀ : 0 < q₀) (p : Polynomial ℂ) (j : ℕ) :
    (monoPolyEval q₀ p).coeff ((j : ℚ) * q₀) = p.coeff j := by
  classical
  rw [monoPolyEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def]
  have hpow : ∀ e : ℕ, (HahnSeries.single q₀ (1 : ℂ)) ^ e =
      HahnSeries.single ((e : ℚ) * q₀) 1 := by
    intro e
    induction e with
    | zero =>
      rw [pow_zero]
      have h0 : ((0 : ℕ) : ℚ) * q₀ = 0 := by push_cast; ring
      rw [h0]
      rfl
    | succ n ihn =>
      rw [pow_succ, ihn, HahnSeries.single_mul_single, one_mul]
      congr 1
      push_cast
      ring_nf
  have hterm : ∀ e ∈ p.support,
      (HahnSeries.C (p.coeff e) * HahnSeries.single q₀ (1 : ℂ) ^ e).coeff ((j : ℚ) * q₀) =
      if e = j then p.coeff j else 0 := by
    intro e _
    rw [hpow e]
    have hCmul : HahnSeries.C (p.coeff e) * HahnSeries.single ((e : ℚ) * q₀) (1 : ℂ) =
        HahnSeries.single ((e : ℚ) * q₀) (p.coeff e) := by
      rw [show (HahnSeries.C (p.coeff e) : HahnSeries ℚ ℂ) =
        HahnSeries.single 0 (p.coeff e) from rfl, HahnSeries.single_mul_single, zero_add,
        mul_one]
    rw [hCmul, HahnSeries.coeff_single]
    rcases eq_or_ne e j with rfl | he
    · rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (by
        intro hc
        apply he
        have h2 := mul_right_cancel₀ (ne_of_gt hq₀) hc
        symm
        exact_mod_cast h2), if_neg he]
  rw [HahnSeries.coeff_sum]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' p.support j (fun _ => p.coeff j)]
  by_cases hj : j ∈ p.support
  · rw [if_pos hj]
  · rw [if_neg hj]
    rw [Polynomial.notMem_support_iff] at hj
    exact hj.symm

theorem monoPolyEval_ne_zero {q₀ : ℚ} (hq₀ : 0 < q₀) {p : Polynomial ℂ} (hp : p ≠ 0) :
    monoPolyEval q₀ p ≠ 0 := by
  intro h
  have hlc : p.coeff p.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  apply hlc
  have hc := congrArg (fun g : HahnSeries ℚ ℂ => g.coeff ((p.natDegree : ℚ) * q₀)) h
  simpa [monoPolyEval_coeff hq₀] using hc

/-- Complex rational functions evaluated at the monomial `t^{q₀}` inside
complex-coefficient Hahn series. -/
def monoRatEvalC (q₀ : ℚ) (hq₀ : 0 < q₀) : RatFunc ℂ →+* HahnSeries ℚ ℂ :=
  RatFunc.liftRingHom (monoPolyEval q₀) (by
    intro x hx
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact monoPolyEval_ne_zero hq₀ hx)

/-- The layer evaluation of the base rational function field into the graded carrier. -/
def monoRatEval (q₀ : ℚ) (hq₀ : 0 < q₀) : RatFunc ℂ →+* HahnSeries ℚ (RatFunc ℂ) :=
  hahnBaseChange.comp (monoRatEvalC q₀ hq₀)

theorem monoRatEval_coeff (q₀ : ℚ) (hq₀ : 0 < q₀) (f : RatFunc ℂ) (q : ℚ) :
    (monoRatEval q₀ hq₀ f).coeff q =
      algebraMap ℂ (RatFunc ℂ) ((monoRatEvalC q₀ hq₀ f).coeff q) := rfl

/-! ## The eigenvariable layer -/

theorem mahlerEll_pow (e : ℕ) :
    mahlerEll ^ e = HahnSeries.single (0 : ℚ) ((RatFunc.X : RatFunc ℂ) ^ e) := by
  induction e with
  | zero =>
    rw [pow_zero, pow_zero]
    rfl
  | succ n ihn =>
    rw [pow_succ, ihn, mahlerEll, HahnSeries.single_mul_single, add_zero, ← pow_succ]

/-- Evaluation of outer-variable polynomials at the eigenvariable. -/
def layerPolyEval (q₀ : ℚ) (hq₀ : 0 < q₀) : Polynomial (RatFunc ℂ) →+*
    HahnSeries ℚ (RatFunc ℂ) :=
  Polynomial.eval₂RingHom (monoRatEval q₀ hq₀) mahlerEll

theorem layerPolyEval_coeff (q₀ : ℚ) (hq₀ : 0 < q₀) (W : Polynomial (RatFunc ℂ)) (q : ℚ) :
    (layerPolyEval q₀ hq₀ W).coeff q =
      ∑ e ∈ W.support,
        algebraMap ℂ (RatFunc ℂ) ((monoRatEvalC q₀ hq₀ (W.coeff e)).coeff q) *
          (RatFunc.X : RatFunc ℂ) ^ e := by
  classical
  rw [layerPolyEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def, HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [mahlerEll_pow, HahnSeries.coeff_mul_single_zero, monoRatEval_coeff]

theorem ratFuncC_eq_algebraMap (c : ℂ) : RatFunc.C c = algebraMap ℂ (RatFunc ℂ) c := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ), Polynomial.algebraMap_eq,
    RatFunc.algebraMap_C]

theorem layerPolyEval_ne_zero {q₀ : ℚ} (hq₀ : 0 < q₀) {W : Polynomial (RatFunc ℂ)}
    (hW : W ≠ 0) : layerPolyEval q₀ hq₀ W ≠ 0 := by
  classical
  intro h
  have hlc : W.coeff W.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hW
  have hCne : monoRatEvalC q₀ hq₀ (W.coeff W.natDegree) ≠ 0 := by
    rw [_root_.map_ne_zero]
    exact hlc
  obtain ⟨q, hq⟩ : ∃ q : ℚ, (monoRatEvalC q₀ hq₀ (W.coeff W.natDegree)).coeff q ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hCne (HahnSeries.ext (funext fun q => hall q))
  have hcoeff : (layerPolyEval q₀ hq₀ W).coeff q = (0 : HahnSeries ℚ (RatFunc ℂ)).coeff q := by
    rw [h]
  rw [layerPolyEval_coeff, HahnSeries.coeff_zero] at hcoeff
  -- the coefficient identity is an algebraic polynomial identity in the inner variable
  have hpoly : algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (∑ e ∈ W.support,
        Polynomial.C ((monoRatEvalC q₀ hq₀ (W.coeff e)).coeff q) * Polynomial.X ^ e) = 0 := by
    rw [map_sum]
    have hterm : ∀ e ∈ W.support,
        algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C ((monoRatEvalC q₀ hq₀ (W.coeff e)).coeff q) * Polynomial.X ^ e) =
        algebraMap ℂ (RatFunc ℂ) ((monoRatEvalC q₀ hq₀ (W.coeff e)).coeff q) *
          (RatFunc.X : RatFunc ℂ) ^ e := by
      intro e _
      rw [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
        ratFuncC_eq_algebraMap]
    rw [Finset.sum_congr rfl hterm]
    exact hcoeff
  have hzero : (∑ e ∈ W.support,
      Polynomial.C ((monoRatEvalC q₀ hq₀ (W.coeff e)).coeff q) * Polynomial.X ^ e) = 0 :=
    IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by rw [hpoly, map_zero])
  have hc : (∑ e ∈ W.support,
      Polynomial.C ((monoRatEvalC q₀ hq₀ (W.coeff e)).coeff q) * Polynomial.X ^ e).coeff
        W.natDegree = (0 : Polynomial ℂ).coeff W.natDegree := by
    rw [hzero]
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
  have hterm2 : ∀ e ∈ W.support,
      (Polynomial.C ((monoRatEvalC q₀ hq₀ (W.coeff e)).coeff q) *
        Polynomial.X ^ e).coeff W.natDegree =
      if e = W.natDegree then (monoRatEvalC q₀ hq₀ (W.coeff W.natDegree)).coeff q else 0 := by
    intro e _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases eq_or_ne e W.natDegree with rfl | he
    · rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg (fun hcon => he hcon.symm), if_neg he, mul_zero]
  rw [Finset.sum_congr rfl hterm2,
    Finset.sum_ite_eq' W.support W.natDegree
      (fun _ => (monoRatEvalC q₀ hq₀ (W.coeff W.natDegree)).coeff q)] at hc
  have hmem : W.natDegree ∈ W.support := by
    rw [Polynomial.mem_support_iff (p := W)]
    exact hlc
  rw [if_pos hmem] at hc
  exact hq hc

/-- **The layer embedding**: the two-variable rational function field maps into the graded
carrier with the base variable at `t^{q₀}` and the eigenvariable at `ℓ`. -/
theorem layerPolyEval_le_comap (q₀ : ℚ) (hq₀ : 0 < q₀) :
    nonZeroDivisors (Polynomial MahlerBase) ≤
      Submonoid.comap (layerPolyEval q₀ hq₀)
        (nonZeroDivisors (HahnSeries ℚ (RatFunc ℂ))) :=
  fun {_} hx => Submonoid.mem_comap.mpr (mem_nonZeroDivisors_of_ne_zero
    (layerPolyEval_ne_zero hq₀ (nonZeroDivisors.ne_zero hx)))

def layerEmbed (q₀ : ℚ) (hq₀ : 0 < q₀) :=
  RatFunc.liftRingHom (L := HahnSeries ℚ (RatFunc ℂ)) (layerPolyEval q₀ hq₀)
    (layerPolyEval_le_comap q₀ hq₀)

/-! ## Action on generators -/

theorem monoRatEvalC_algebraMap (q₀ : ℚ) (hq₀ : 0 < q₀) (p : Polynomial ℂ) :
    monoRatEvalC q₀ hq₀ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = monoPolyEval q₀ p := by
  have h := RatFunc.liftRingHom_apply_div (monoPolyEval q₀) (by
    intro x hx
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact monoPolyEval_ne_zero hq₀ hx) p 1
  simp only [map_one, div_one] at h
  exact h

theorem monoRatEval_X (q₀ : ℚ) (hq₀ : 0 < q₀) :
    monoRatEval q₀ hq₀ RatFunc.X = HahnSeries.single q₀ 1 := by
  show hahnBaseChange (monoRatEvalC q₀ hq₀ RatFunc.X) = _
  rw [show (RatFunc.X : RatFunc ℂ) =
    algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X from (RatFunc.algebraMap_X).symm,
    monoRatEvalC_algebraMap]
  rw [show monoPolyEval q₀ (Polynomial.X : Polynomial ℂ) = HahnSeries.single q₀ 1 from by
    rw [monoPolyEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]]
  ext x
  show algebraMap ℂ (RatFunc ℂ) ((HahnSeries.single q₀ (1:ℂ)).coeff x) =
    (HahnSeries.single q₀ (1 : RatFunc ℂ)).coeff x
  rw [HahnSeries.coeff_single, HahnSeries.coeff_single]
  rcases eq_or_ne x q₀ with rfl | hx
  · rw [if_pos rfl, if_pos rfl, map_one]
  · rw [if_neg hx, if_neg hx, map_zero]

theorem monoRatEval_ratFuncC (q₀ : ℚ) (hq₀ : 0 < q₀) (c : ℂ) :
    monoRatEval q₀ hq₀ (RatFunc.C c) =
      HahnSeries.single 0 (algebraMap ℂ (RatFunc ℂ) c) := by
  show hahnBaseChange (monoRatEvalC q₀ hq₀ (RatFunc.C c)) = _
  rw [show (RatFunc.C c : RatFunc ℂ) =
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) from (RatFunc.algebraMap_C c).symm,
    monoRatEvalC_algebraMap]
  rw [show monoPolyEval q₀ (Polynomial.C c) = HahnSeries.C c from by
    rw [monoPolyEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]]
  ext x
  show algebraMap ℂ (RatFunc ℂ) ((HahnSeries.single 0 c).coeff x) =
    (HahnSeries.single 0 (algebraMap ℂ (RatFunc ℂ) c)).coeff x
  rw [HahnSeries.coeff_single, HahnSeries.coeff_single]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hx, if_neg hx, map_zero]

/-- σ fixes the embedded complex constants. -/
theorem mahlerSigma_hahnConst (c : ℂ) :
    mahlerSigma (HahnSeries.single 0 (algebraMap ℂ (RatFunc ℂ) c)) =
      HahnSeries.single 0 (algebraMap ℂ (RatFunc ℂ) c) := by
  rw [mahlerSigma_single, mul_zero, ellScale_algebraMap_C]

/-- Inner intertwining on polynomial images. -/
theorem mahlerSigma_monoRatEval_poly (q₀ : ℚ) (hq₀ : 0 < q₀) (p : Polynomial ℂ) :
    mahlerSigma (monoRatEval q₀ hq₀ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)) =
      monoRatEval q₀ hq₀ ((MahlerPolynomial.mahlerHom 0)
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)) := by
  induction p using Polynomial.induction_on' with
  | add u v hu hv => simp only [map_add, hu, hv]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow]
    have hC : mahlerSigma (monoRatEval q₀ hq₀
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c))) =
        monoRatEval q₀ hq₀ ((MahlerPolynomial.mahlerHom 0)
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c))) := by
      rw [RatFunc.algebraMap_C, monoRatEval_ratFuncC, mahlerSigma_hahnConst]
      rw [show (MahlerPolynomial.mahlerHom 0) (RatFunc.C c) = RatFunc.C c from by
        rw [ratFuncC_eq_algebraMap]
        exact (MahlerPolynomial.mahlerHom 0).commutes c]
      rw [monoRatEval_ratFuncC]
    have hX : mahlerSigma (monoRatEval q₀ hq₀
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)) =
        monoRatEval q₀ hq₀ ((MahlerPolynomial.mahlerHom 0)
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)) := by
      rw [RatFunc.algebraMap_X, monoRatEval_X]
      rw [show mahlerSigma (HahnSeries.single q₀ (1 : RatFunc ℂ)) =
        HahnSeries.single (2 * q₀) 1 from by rw [mahlerSigma_single, map_one]]
      rw [show (MahlerPolynomial.mahlerHom 0) (RatFunc.X : RatFunc ℂ) =
        RatFunc.X * RatFunc.X from ?_]
      · rw [map_mul, monoRatEval_X, HahnSeries.single_mul_single, mul_one]
        congr 1
        ring_nf
      · rw [show (RatFunc.X : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          Polynomial.X from (RatFunc.algebraMap_X).symm,
          MahlerPolynomial.mahlerHom_algebraMap]
        rw [show (Polynomial.X : Polynomial ℂ).comp
          (Polynomial.X ^ (2 : ℕ) + Polynomial.C 0) = Polynomial.X ^ (2 : ℕ) from by
            rw [Polynomial.X_comp, map_zero, add_zero]]
        rw [map_pow, RatFunc.algebraMap_X, sq]
    rw [hC, hX]

/-- **Inner intertwining**: σ carries evaluation at the monomial through the coefficient
Mahler substitution. -/
theorem mahlerSigma_monoRatEval (q₀ : ℚ) (hq₀ : 0 < q₀) (f : RatFunc ℂ) :
    mahlerSigma (monoRatEval q₀ hq₀ f) =
      monoRatEval q₀ hq₀ ((MahlerPolynomial.mahlerHom 0) f) := by
  induction f using RatFunc.induction_on with
  | _ p q hq =>
    rw [map_div₀, map_div₀, map_div₀, map_div₀, mahlerSigma_monoRatEval_poly,
      mahlerSigma_monoRatEval_poly]

/-! ## The outer intertwining -/

theorem layerEmbed_apply_div (q₀ : ℚ) (hq₀ : 0 < q₀) (p q : Polynomial MahlerBase) :
    layerEmbed q₀ hq₀ (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) =
      layerPolyEval q₀ hq₀ p / layerPolyEval q₀ hq₀ q := by
  unfold layerEmbed
  exact RatFunc.liftRingHom_apply_div _ _ p q

theorem layerEmbed_algebraMap (q₀ : ℚ) (hq₀ : 0 < q₀) (W : Polynomial MahlerBase) :
    layerEmbed q₀ hq₀ (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) W) =
      layerPolyEval q₀ hq₀ W := by
  rw [← RatFunc.ofFractionRing_algebraMap]
  unfold layerEmbed
  exact RatFunc.liftRingHom_ofFractionRing_algebraMap _ _ _

theorem twoVarMahler_algebraMap (W : Polynomial MahlerBase) :
    twoVarMahler (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) W) =
      algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) (twoVarPolyHom W) := by
  conv_lhs => rw [← RatFunc.ofFractionRing_algebraMap, ← Localization.mk_one_eq_algebraMap]
  conv_rhs => rw [← RatFunc.ofFractionRing_algebraMap, ← Localization.mk_one_eq_algebraMap]
  have hcoe : twoVarMahler (RatFunc.ofFractionRing (Localization.mk W 1)) =
      RatFunc.map twoVarPolyHom (by
        intro q hq
        rw [mem_nonZeroDivisors_iff_ne_zero] at hq
        rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
        exact twoVarPolyHom_ne_zero hq)
        (RatFunc.ofFractionRing (Localization.mk W 1)) :=
    congrFun (RatFunc.coe_mapRingHom_eq_coe_map _ _) _
  rw [hcoe, RatFunc.map_apply_ofFractionRing_mk]
  congr 1
  congr 1
  exact Subtype.ext (by simp)

theorem twoVarPolyHom_C (e : MahlerBase) :
    twoVarPolyHom (Polynomial.C e) = Polynomial.C ((MahlerPolynomial.mahlerHom 0) e) := by
  letI : Invertible (2 : MahlerBase) := invertibleOfNonzero two_ne_zero
  show (algEquivCMulXAddC (2 : MahlerBase) 0)
    (Polynomial.map (MahlerPolynomial.mahlerHom 0).toRingHom (Polynomial.C e)) = _
  rw [Polynomial.map_C, algEquivCMulXAddC_apply, Polynomial.aeval_C]
  rfl

theorem layerPolyEval_C (q₀ : ℚ) (hq₀ : 0 < q₀) (e : MahlerBase) :
    layerPolyEval q₀ hq₀ (Polynomial.C e) = monoRatEval q₀ hq₀ e := by
  rw [layerPolyEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

theorem layerPolyEval_X (q₀ : ℚ) (hq₀ : 0 < q₀) :
    layerPolyEval q₀ hq₀ Polynomial.X = mahlerEll := by
  rw [layerPolyEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

theorem mahlerSigma_layerPolyEval (q₀ : ℚ) (hq₀ : 0 < q₀) (W : Polynomial MahlerBase) :
    mahlerSigma (layerPolyEval q₀ hq₀ W) = layerPolyEval q₀ hq₀ (twoVarPolyHom W) := by
  induction W using Polynomial.induction_on' with
  | add u v hu hv => simp only [map_add, hu, hv]
  | monomial n e =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow]
    rw [layerPolyEval_C, layerPolyEval_X, twoVarPolyHom_C, twoVarPolyHom_X,
      mahlerSigma_monoRatEval, mahlerSigma_mahlerEll]
    simp only [map_mul]
    rw [layerPolyEval_C, layerPolyEval_X, layerPolyEval_C]
    have h2 : monoRatEval q₀ hq₀ (2 : RatFunc ℂ) = 2 := by
      rw [show (2 : RatFunc ℂ) = ((2 : ℕ) : RatFunc ℂ) by norm_num, map_natCast]
      norm_num
    rw [h2]

/-- **The layer intertwining**: the graded Mahler automorphism restricts along each layer
embedding to the two-variable Mahler substitution. -/
theorem mahlerSigma_layerEmbed (q₀ : ℚ) (hq₀ : 0 < q₀) (f : RatFunc MahlerBase) :
    mahlerSigma (layerEmbed q₀ hq₀ f) = layerEmbed q₀ hq₀ (twoVarMahler f) := by
  induction f using RatFunc.induction_on with
  | _ p q hq =>
    have hσdiv : mahlerSigma (layerPolyEval q₀ hq₀ p / layerPolyEval q₀ hq₀ q) =
        mahlerSigma (layerPolyEval q₀ hq₀ p) / mahlerSigma (layerPolyEval q₀ hq₀ q) :=
      map_div₀ (f := mahlerSigma) (a := layerPolyEval q₀ hq₀ p)
        (b := layerPolyEval q₀ hq₀ q)
    have hτdiv : twoVarMahler (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p /
        algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) =
        twoVarMahler (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) p) /
          twoVarMahler (algebraMap (Polynomial MahlerBase) (RatFunc MahlerBase) q) :=
      map_div₀ twoVarMahler _ _
    rw [layerEmbed_apply_div, hσdiv, mahlerSigma_layerPolyEval, mahlerSigma_layerPolyEval,
      hτdiv, twoVarMahler_algebraMap, twoVarMahler_algebraMap, layerEmbed_apply_div]

end

end GaloisForLFunctions
