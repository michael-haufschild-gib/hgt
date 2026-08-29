import GaloisForLFunctions.HTGeometry.QPrimitiveExistence
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# The differentially algebraic scaling spectrum of a rational `q`-difference primitive

For a rational increment `r` regular and vanishing at the origin, the `q`-primitive `f` is
differentially transcendental exactly when `r` is not rationally `q`-summable, and the scaling
defect `f(ax) − f(x)` is differentially algebraic exactly when `S_a r − r` is `q`-summable.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

/-- Rational `q`-summability: the class in `K(x)/(σ−1)K(x)` vanishes. -/
def QSummable (q : K) (hq : q ≠ 0) (r : RatFunc K) : Prop :=
  ∃ k : RatFunc K, r = ratFuncScale q hq k - k

/-- The `q`-primitive of a rational increment. -/
def qPrimitiveOf (q : K) (r : RatFunc K) : LaurentSeries K :=
  qPrimitive q (algebraMap (RatFunc K) (LaurentSeries K) r)

theorem coeff_zero_algebraMap_eq_polePart (r : RatFunc K) :
    (algebraMap (RatFunc K) (LaurentSeries K) r).coeff 0 = polePart r 0 0 := by
  have h := coeff_algebraMap_ratFunc r 0
  simpa using h

theorem innerDilation_qPrimitiveOf {q : K} (hq : q ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) (r : RatFunc K) (hzero : polePart r 0 0 = 0) :
    innerDilation q hq (qPrimitiveOf q r)
      = qPrimitiveOf q r + algebraMap (RatFunc K) (LaurentSeries K) r :=
  innerDilation_qPrimitive hq hqtor _ ((coeff_zero_algebraMap_eq_polePart r).trans hzero)

/-- **The `q`-primitive of a nonsummable increment is differentially transcendental.** -/
theorem hypertranscendentalOver_qPrimitiveOf [CharZero K] [IsAlgClosed K] {q : K} (hq : q ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) (r : RatFunc K)
    (hzero : polePart r 0 0 = 0) (hreg : ∀ d : ℕ, 0 < d → polePart r 0 d = 0)
    (hns : ¬ QSummable q hq r) :
    letI := cylinderDifferential (1 : K)
    letI := innerDifferential (k := K)
    HypertranscendentalOver (RatFunc K) (qPrimitiveOf q r) := by
  letI := cylinderDifferential (1 : K)
  letI := innerDifferential (k := K)
  obtain ⟨a, ha, d, hd, hres⟩ :
      ∃ a : K, a ≠ 0 ∧ ∃ d : ℕ, 0 < d ∧ qOrbitResidue q a d r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hns (exists_dilationTelescoper_of_qOrbitResidue_vanish hq hqtor r hzero hreg
      fun a ha d hd => hcon a ha d hd)
  obtain ⟨D, hD, hresD, hvanish⟩ := exists_top_qOrbitResidue hd hres
  exact hypertranscendentalOver_of_qPrimitive_top_residue hq hqtor ha r hD hvanish hresD
    (qPrimitiveOf q r) (innerDilation_qPrimitiveOf hq hqtor r hzero)

/-- The scaling defect `f(ax) − f(x)`. -/
def qDefect (q a : K) (ha : a ≠ 0) (r : RatFunc K) : LaurentSeries K :=
  innerDilation a ha (qPrimitiveOf q r) - qPrimitiveOf q r

theorem innerDilation_qDefect {q : K} (hq : q ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {a : K} (ha : a ≠ 0)
    (r : RatFunc K) (hzero : polePart r 0 0 = 0) :
    innerDilation q hq (qDefect q a ha r)
      = qDefect q a ha r
        + algebraMap (RatFunc K) (LaurentSeries K) (ratFuncScale a ha r - r) := by
  have hcomm : innerDilation q hq (innerDilation a ha (qPrimitiveOf q r))
      = innerDilation a ha (innerDilation q hq (qPrimitiveOf q r)) := by
    refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
    rw [coeff_innerDilation, coeff_innerDilation, coeff_innerDilation, coeff_innerDilation]
    ring
  rw [qDefect, map_sub, hcomm, innerDilation_qPrimitiveOf hq hqtor r hzero, map_add,
    ← algebraMap_ratFuncScale, map_sub]
  ring

theorem polePart_ratFuncScale_sub_zero {a : K} (ha : a ≠ 0) (r : RatFunc K) (d : ℕ)
    (hr : polePart r 0 d = 0) : polePart (ratFuncScale a ha r - r) 0 d = 0 := by
  rw [sub_eq_add_neg, polePart_add, polePart_neg, polePart_ratFuncScale, mul_zero, hr]
  simp

/-- **The defect is differentially transcendental off the summability stabilizer.** -/
theorem hypertranscendentalOver_qDefect [CharZero K] [IsAlgClosed K] {q : K} (hq : q ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {a : K} (ha : a ≠ 0) (r : RatFunc K)
    (hzero : polePart r 0 0 = 0) (hreg : ∀ d : ℕ, 0 < d → polePart r 0 d = 0)
    (hns : ¬ QSummable q hq (ratFuncScale a ha r - r)) :
    letI := cylinderDifferential (1 : K)
    letI := innerDifferential (k := K)
    HypertranscendentalOver (RatFunc K) (qDefect q a ha r) := by
  letI := cylinderDifferential (1 : K)
  letI := innerDifferential (k := K)
  obtain ⟨b, hb, d, hd, hres⟩ :
      ∃ b : K, b ≠ 0 ∧ ∃ d : ℕ, 0 < d ∧ qOrbitResidue q b d (ratFuncScale a ha r - r) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hns (exists_dilationTelescoper_of_qOrbitResidue_vanish hq hqtor _
      (polePart_ratFuncScale_sub_zero ha r 0 hzero)
      (fun d hd => polePart_ratFuncScale_sub_zero ha r d (hreg d hd))
      fun b hb d hd => hcon b hb d hd)
  obtain ⟨D, hD, hresD, hvanish⟩ := exists_top_qOrbitResidue hd hres
  exact hypertranscendentalOver_of_qPrimitive_top_residue hq hqtor hb _ hD hvanish hresD
    (qDefect q a ha r) (innerDilation_qDefect hq hqtor ha r hzero)

/-- **The defect is differentially algebraic on the summability stabilizer.** -/
theorem differentialAlgebraicOver_qDefect {q : K} (hq : q ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {a : K} (ha : a ≠ 0) (r : RatFunc K)
    (hzero : polePart r 0 0 = 0)
    (hsum : QSummable q hq (ratFuncScale a ha r - r)) :
    letI := cylinderDifferential (1 : K)
    letI := innerDifferential (k := K)
    DifferentialAlgebraicOver (RatFunc K) (qDefect q a ha r) := by
  letI := cylinderDifferential (1 : K)
  letI := innerDifferential (k := K)
  obtain ⟨g, hg⟩ := hsum
  have hinv : innerDilation q hq
      (qDefect q a ha r - algebraMap (RatFunc K) (LaurentSeries K) g)
      = qDefect q a ha r - algebraMap (RatFunc K) (LaurentSeries K) g := by
    rw [map_sub, innerDilation_qDefect hq hqtor ha r hzero, hg, map_sub,
      ← algebraMap_ratFuncScale]
    ring
  obtain ⟨c, hc⟩ := exists_C_of_innerDilation_eq_self hq hqtor hinv
  have hval : qDefect q a ha r
      = algebraMap (RatFunc K) (LaurentSeries K) (g + algebraMap K (RatFunc K) c) := by
    rw [map_add]
    have : qDefect q a ha r = algebraMap (RatFunc K) (LaurentSeries K) g + HahnSeries.C c := by
      rw [← hc]
      ring
    rw [this]
    congr 1
    rw [algebraMap_const_laurentSeries, HahnSeries.C_apply]
  rw [hval]
  exact differentialAlgebraicOver_algebraMap _

end

end GaloisForLFunctions.HTGeometry
