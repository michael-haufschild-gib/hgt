import GaloisForLFunctions.LatticeSectionTheory.TheKunnethRiemannRoch
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceDeterminantalSectionsAndArithmeticRiemannRoch

/-!
# Bidegree counts see no primitive class

Every count built from the base `Spec ℤ` by its own operations — Gaussian lattice counts,
Poisson summation, products, convolution in the degree — is a function of the two fibre degrees
`(x · H, x · V)` of a class. Such a **bidegree count** `h_Φ(x) = Φ(x · H, x · V)` takes one value on
all primitive classes.

* **Blindness** (`riemannInequality_bidegree_iff`). With `κ = 0`, a bidegree count satisfies the
  Riemann inequality on a polar surface iff (i) the Hodge index holds and (ii) `Φ` satisfies the
  Riemann inequality of the pole plane, `ab ≤ Φ(a, b) + Φ(−a, −b)`. The count contributes nothing
  to the primitive part: its primitive `h¹` is exactly `½ δ`, whatever `Φ` is
  (`bidegree_h1_eq`).
* **The Künneth count** satisfies (ii) by Poisson summation on the base, so it is the canonical
  bidegree count; its effectivity on a surface is that surface's Hodge index.
* **Prime-free cycles** (`kunneth_effectivity_realTestsAt`,
  `kunneth_effectivity_primitiveSmoothRealTestsAt`). On the scaling subsurface of all tests of
  aperture `≤ 3/10`, and on the ample-orthogonal smooth tests of aperture `≤ (log 2 + 1/50)/2`
  (the prime-free window `½ log 2` and past the prime `2`), the Künneth count is an effectivity
  function: positive, Poisson-dual, quadratic Riemann inequality, bounded on degree levels. The
  Riemann inequality there is the Weil positivity proved by estimates in ACS; it is not derived
  from the count.

So a section count that can prove a sign must read the test component of a class beyond its two
degrees.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory ArithmeticOrientationGeometry

section Bidegree

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

/-- The bidegree count of `Φ`: `h_Φ(x) = Φ(x · H, x · V)`. -/
def bidegreeCount (Φ : ℝ → ℝ → ℝ) (x : E) : ℝ := Φ (S.pair x S.H) (S.pair x S.V)

/-- The Riemann inequality of the pole plane for `Φ` (canonical class `0`). -/
def PolePlaneRiemannInequality (Φ : ℝ → ℝ → ℝ) (χ₀ : ℝ) : Prop :=
  ∀ a b : ℝ, a * b + χ₀ ≤ Φ a b + Φ (-a) (-b)

/-- **The primitive `h¹` of a bidegree count is `½ δ`.** -/
theorem bidegree_h1_eq (Φ : ℝ → ℝ → ℝ) (χ₀ : ℝ) (x : E) :
    bidegreeCount S Φ x + bidegreeCount S Φ (0 - x) - eulerChar S 0 χ₀ x =
      (Φ (S.pair x S.H) (S.pair x S.V) + Φ (-S.pair x S.H) (-S.pair x S.V) -
        (S.pair x S.H * S.pair x S.V + χ₀)) + S.defect x x / 2 := by
  simp only [bidegreeCount, eulerChar, zero_sub, map_neg, LinearMap.neg_apply, sub_zero,
    S.defect_self]
  ring

/-- **Blindness.** A bidegree count satisfies the Riemann inequality iff the Hodge index holds and
`Φ` satisfies the Riemann inequality of the pole plane. -/
theorem riemannInequality_bidegree_iff (Φ : ℝ → ℝ → ℝ) (χ₀ : ℝ) :
    RiemannInequality S 0 χ₀ (bidegreeCount S Φ) ↔
      S.HodgeIndex ∧ PolePlaneRiemannInequality Φ χ₀ := by
  constructor
  · intro hRI
    refine ⟨fun x hH hV => ?_, fun a b => ?_⟩
    · by_contra hpos
      push Not at hpos
      set c := Φ 0 0 + Φ (-0) (-0) - χ₀
      set t : ℝ := Real.sqrt ((2 * |c| + 2) / S.pair x x)
      have ht : t ^ 2 = (2 * |c| + 2) / S.pair x x :=
        Real.sq_sqrt (div_nonneg (by positivity) hpos.le)
      have h := hRI (t • x)
      simp only [bidegreeCount, eulerChar, zero_sub, map_neg, map_smul, LinearMap.neg_apply,
        LinearMap.smul_apply, smul_eq_mul, hH, hV, mul_zero, sub_zero] at h
      have hq : t ^ 2 * S.pair x x = 2 * |c| + 2 := by rw [ht, div_mul_cancel₀ _ hpos.ne']
      have : t * (t * S.pair x x) = t ^ 2 * S.pair x x := by ring
      have hc : c = Φ 0 0 + Φ (-0) (-0) - χ₀ := rfl
      nlinarith [le_abs_self c]
    · -- evaluate on the pole-plane class `bH + aV`, of bidegree `(a, b)`
      have h := hRI (b • S.H + a • S.V)
      simp only [bidegreeCount, eulerChar, zero_sub, map_neg, map_add, map_smul,
        LinearMap.neg_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, sub_zero,
        S.pair_H_H, S.pair_V_V, S.pair_H_V, S.pair_V_H] at h
      simp only [mul_zero, mul_one, zero_add, add_zero] at h
      linarith
  · rintro ⟨hHI, hΦ⟩ x
    have hδ := (S.castelnuovoSeveri_iff_defect_nonneg.mp
      (S.hodgeIndex_iff_castelnuovoSeveri.mp hHI)) x
    have h1 := bidegree_h1_eq S Φ χ₀ x
    have h2 := hΦ (S.pair x S.H) (S.pair x S.V)
    linarith

/-- The Künneth count is the bidegree count of `(a, b) ↦ h⁰_ℤ(a) h⁰_ℤ(b)`. -/
theorem kunnethH0_eq_bidegreeCount :
    kunnethH0 S = bidegreeCount S (fun a b => arithH0 a * arithH0 b) := rfl

/-- **The Künneth count satisfies the pole-plane Riemann inequality** (Poisson summation). -/
theorem kunneth_polePlaneRiemannInequality :
    PolePlaneRiemannInequality (fun a b => arithH0 a * arithH0 b) 0 := by
  intro a b
  have h := arithH0_kunneth a b
  have h1 := mul_pos (arithH0_pos a) (arithH0_pos (-b))
  have h2 := mul_pos (arithH0_pos (-a)) (arithH0_pos b)
  simp only [add_zero]
  linarith

end Bidegree

/-! ### Prime-free cycles -/

/-- **The Künneth count is an effectivity on cycles of aperture `≤ 3/10`.** All tests supported in
`[−a, a]`, `a ≤ 3/10`, so that every prime is invisible: the count is positive, Poisson-dual,
satisfies the quadratic Riemann inequality and is bounded on degree levels. -/
theorem kunneth_effectivity_realTestsAt {a : ℝ} (ha : a ≤ 3 / 10) :
    RiemannInequality (scalingSubsurface (realTestsAt a)) 0 0
        (kunnethH0 (scalingSubsurface (realTestsAt a))) ∧
      DegreeBounded (scalingSubsurface (realTestsAt a))
        (kunnethH0 (scalingSubsurface (realTestsAt a))) :=
  (kunneth_effectivity_iff _).mpr (scalingSubsurface_all_hodgeIndex ha).1

/-- **Past the prime-free window.** On the ample-orthogonal smooth tests of aperture
`≤ (log 2 + 1/50)/2` — beyond `½ log 2`, where the prime `2` enters — the Künneth count is an
effectivity function. -/
theorem kunneth_effectivity_primitiveSmoothRealTestsAt {r : ℝ}
    (hr : r ≤ (Real.log 2 + 1 / 50) / 2) :
    RiemannInequality (scalingSubsurface (primitiveSmoothRealTestsAt r)) 0 0
        (kunnethH0 (scalingSubsurface (primitiveSmoothRealTestsAt r))) ∧
      DegreeBounded (scalingSubsurface (primitiveSmoothRealTestsAt r))
        (kunnethH0 (scalingSubsurface (primitiveSmoothRealTestsAt r))) :=
  (kunneth_effectivity_iff _).mpr (primitiveSmooth_scalingSubsurface_hodgeIndex_primeTwo hr)

/-- **On the scaling subsurface of a test space, effectivity of the Künneth count is Weil
positivity there.** -/
theorem kunneth_effectivity_scalingSubsurface_iff (V : Submodule ℝ realTests) :
    (RiemannInequality (scalingSubsurface V) 0 0 (kunnethH0 (scalingSubsurface V)) ∧
        DegreeBounded (scalingSubsurface V) (kunnethH0 (scalingSubsurface V))) ↔
      ∀ f : V, 0 ≤ weilPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) :=
  (kunneth_effectivity_iff _).trans (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg V)

end GaloisForLFunctions.LatticeSectionTheory
