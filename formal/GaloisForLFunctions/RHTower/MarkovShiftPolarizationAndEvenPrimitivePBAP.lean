import GaloisForLFunctions.RHTower.MarkovOddSectorFarkasAndOneSidedPBAP

/-!
# Markov Shift-Polarization Law, the Even Primitive Sector, Hodge-Index Projection, and the Three-Tier PBAP Hierarchy

This module advances Route HF and the Prime-Blind Archimedean Positivity (PBAP) program by uniting
the **shift-polarization (parallelogram) law** between `evenShift g h` and `oddShift g h`, the
**orthogonal parity decomposition of the primitive hyperplane** (`PrimitiveWeilTestFn ≅
EvenPrimitiveWeilTestFn ⊕ OddWeilTestFn`), the **Hodge-index primitive-hyperplane projection**
`primitiveProj Φ₀ F`, and the **three-tier PBAP cone hierarchy** (Full Cone $\implies$ Primitive
Hyperplane $\implies$ Odd Sector).

## Key Mathematical Results

1. **Section 1 (Universal Shift-Polarization / Parallelogram Law between `evenShift g h` and
   `oddShift g h`):**
   - For every real test `g ∈ C²_c(ℝ)` and every shift `h ∈ ℝ`,
     `evenShift g h x + oddShift g h x = g(x - h/2)` and
     `evenShift g h x - oddShift g h x = g(x + h/2)`.
   - Their autocorrelations satisfy the exact shift-independent parallelogram law
     `EF.weilTest (evenShift g h) + EF.weilTest (oddShift g h) = EF.weilTest g g`
     (`weilTest_evenShift_add_oddShift`) and the shift-difference formula
     `EF.weilTest (evenShift g h) y - EF.weilTest (oddShift g h) y = (k_g(y + h) + k_g(y - h)) / 2`
     (`weilTest_evenShift_sub_oddShift`).
   - Under `evenShift g h`, both hyperbolic half-moments scale by `cosh(h / 4)`
     (`coshHalfMoment_and_sinhHalfMoment_evenShift`), so the pole term scales by `cosh(h / 4)²`
     (`re_weilPoleTerm_evenShift`). Combined with `re_weilPoleTerm_oddShift` (`-sinh(h / 4)²`) and
     `cosh(h / 4)² - sinh(h / 4)² = 1`, the pole terms sum back to `(weilPoleTerm k_g).re`
     (`re_weilPoleTerm_evenShift_add_oddShift`).
   - Consequently, `paperFT`, `markovArchRe`, `weilArchRe`, `logValue`, `logVector`,
     `primeBlindCounterterm lam`, `(weilFullFunctional lam).re`, `markovCountertermEnergy lam`, and
     `markovEnergy` all satisfy exact shift-polarization additivity across `evenShift g h` and
     `oddShift g h` for every `h ∈ ℝ` and every counterterm sequence `lam : ℕ → ℝ`.

2. **Section 2 (Linearity of Hyperbolic Half-Moments, the Even Primitive Sector
   `EvenPrimitiveWeilTestFn`, and Orthogonal Parity Equivalence on the Primitive Hyperplane):**
   - On `EvenPrimitiveWeilTestFn` (even real tests with `coshHalfMoment f = 0`), both half-moments
     vanish (`coshHalfMoment = 0` and `sinhHalfMoment = 0`), so the pole term vanishes identically
     and `markovCountertermEnergy lam` coincides with `(weilFullFunctional lam).re`
     (`markovCountertermEnergy_evenPrimitive_eq_re_weilFullFunctional`).
   - We prove the orthogonal parity equivalence
     `MarkovPositivePrimitive lam ↔ MarkovPositiveEvenPrimitive lam ∧ MarkovPositiveOdd lam`
     (`markovPositivePrimitive_iff_evenPrimitive_and_odd`), and show that for any
     `g ∈ EvenPrimitiveWeilTestFn` and `h ∈ ℝ`, `evenShift g h ∈ EvenPrimitiveWeilTestFn` and
     `oddShift g h ∈ OddWeilTestFn` with `sinhHalfMoment (oddShift g h) = 0`.

3. **Section 3 (The Hodge-Index Primitive-Hyperplane Projection `primitiveProj Φ₀ F`):**
   - Given any reference test `Φ₀ ∈ C²_c(ℝ)` with `coshHalfMoment Φ₀ ≠ 0`, the projection
     `primitiveProj Φ₀ F x = F x - (coshHalfMoment F / coshHalfMoment Φ₀) * Φ₀ x` maps every real
     test `F ∈ C²_c(ℝ)` onto the primitive hyperplane `coshHalfMoment (primitiveProj Φ₀ F) = 0`.
   - When `Φ₀` is even, `primitiveProj Φ₀ F` preserves `oddPartReal F` and `sinhHalfMoment F`
     (`oddPartReal_primitiveProj`, `sinhHalfMoment_primitiveProj`), so its pole term is the pure
     nonpositive square `-2 * sinhHalfMoment F ^ 2 ≤ 0` (`re_weilPoleTerm_primitiveProj`).

4. **Section 4 (The Three-Tier PBAP Positivity and Cone Hierarchy and Cesàro Dominance Bridges):**
   - Across all three tiers (Full Cone $\implies$ Primitive Hyperplane $\implies$ Odd Sector), we
     establish the inclusion chain for prime-blind cones (`WeilOneSided.PrimeBlindPositive →
     PrimitivePrimeBlindPositive → OddPrimeBlindPositive`) and one-sided cones
     (`PositiveOnNonposCone U → PrimitivePositiveOnNonposCone U → OddPositiveOnNonposCone U`,
     `PositiveOnNonnegCone L → PrimitivePositiveOnNonnegCone L → OddPositiveOnNonnegCone L`),
     together with `m`-th Cesàro / iterated-prefix dominance bridges for `MarkovPositiveOdd` and
     `MarkovPositivePrimitive`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: Universal Shift-Polarization (Parallelogram) Law between `evenShift g h` and `oddShift g h` -/

/-- Pointwise sum of `evenShift g h` and `oddShift g h`:
`evenShift g h x + oddShift g h x = g (x - h / 2)`. -/
theorem evenShift_add_oddShift (g : ℝ → ℝ) (h x : ℝ) :
    evenShift g h x + oddShift g h x = g (x - h / 2) := by
  unfold evenShift oddShift; ring

/-- Pointwise difference of `evenShift g h` and `oddShift g h`:
`evenShift g h x - oddShift g h x = g (x + h / 2)`. -/
theorem evenShift_sub_oddShift (g : ℝ → ℝ) (h x : ℝ) :
    evenShift g h x - oddShift g h x = g (x + h / 2) := by
  unfold evenShift oddShift; ring

/-- **Shift-Polarization (Parallelogram) Identity for `EF.weilTest`**:
for every continuous compactly supported `g : ℝ → ℝ` and every shift `h ∈ ℝ`, the autocorrelations
of `evenShift g h` and `oddShift g h` sum identically to `EF.weilTest g g` at every `y ∈ ℝ`. -/
theorem weilTest_evenShift_add_oddShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h y : ℝ) :
    EF.weilTest (fun u => (evenShift g h u : ℂ)) (fun u => (evenShift g h u : ℂ)) y +
      EF.weilTest (fun u => (oddShift g h u : ℂ)) (fun u => (oddShift g h u : ℂ)) y =
      EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) y := by
  rw [weilTest_evenShift hg hgc, weilTest_oddShift hg hgc]
  have h1 : EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) y = ((autoCorr g y : ℝ) : ℂ) :=
    weilTest_liftC g y
  rw [h1]
  push_cast
  ring

/-- **Shift-Polarization Difference Identity for `EF.weilTest`**:
for every continuous compactly supported `g : ℝ → ℝ` and `h, y ∈ ℝ`,
`EF.weilTest (evenShift g h) y - EF.weilTest (oddShift g h) y = (EF.weilTest g g (y + h) + EF.weilTest g g (y - h)) / 2`. -/
theorem weilTest_evenShift_sub_oddShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h y : ℝ) :
    EF.weilTest (fun u => (evenShift g h u : ℂ)) (fun u => (evenShift g h u : ℂ)) y -
      EF.weilTest (fun u => (oddShift g h u : ℂ)) (fun u => (oddShift g h u : ℂ)) y =
      (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) (y + h) +
        EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) (y - h)) / 2 := by
  rw [weilTest_evenShift hg hgc, weilTest_oddShift hg hgc]
  have h1 : EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) (y + h) =
      ((autoCorr g (y + h) : ℝ) : ℂ) := weilTest_liftC g (y + h)
  have h2 : EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) (y - h) =
      ((autoCorr g (y - h) : ℝ) : ℂ) := weilTest_liftC g (y - h)
  rw [h1, h2]
  push_cast
  ring

/-- The transform of `evenShift u h`:
`paperFT (evenShift u h) z = ((e^{izh/2} + e^{-izh/2}) / 2) * paperFT u z`. -/
theorem paperFT_evenShift {u : ℝ → ℝ} (hu : Continuous u) (hcpt : HasCompactSupport u) (h : ℝ)
    (z : ℂ) :
    paperFT (fun x => (evenShift u h x : ℂ)) z =
      (cexp (I * z * (h / 2 : ℝ)) + cexp (I * z * (-(h / 2) : ℝ))) / 2 *
        paperFT (fun x => (u x : ℂ)) z := by
  set U : ℝ → ℂ := fun x => (u x : ℂ) with hU
  have hUc : Continuous U := Complex.continuous_ofReal.comp hu
  have hUs : HasCompactSupport U := hcpt.comp_left Complex.ofReal_zero
  have e : (fun x => (evenShift u h x : ℂ)) = fun x =>
      (1 / 2 : ℂ) * WeilSpectral.transl (h / 2) U x + (1 / 2 : ℂ) *
        WeilSpectral.transl (-(h / 2)) U x := by
    funext x
    simp only [evenShift, WeilSpectral.transl, hU, sub_neg_eq_add]
    push_cast; ring
  have hT : ∀ y : ℝ, Integrable fun x : ℝ => WeilSpectral.transl y U x * cexp (I * z * x) := by
    intro y
    refine integrable_mul_cexp_of_compact (hUc.comp (continuous_id.sub continuous_const)) ?_ z
    exact hUs.comp_homeomorph (Homeomorph.subRight y)
  rw [e, paperFT_smul_add_smul _ _ z (hT _) (hT _), WeilSpectral.paperFT_transl,
    WeilSpectral.paperFT_transl]
  ring

/-- Evaluation of `paperFT` of `evenShift g h` at `I / 2`:
`paperFT (evenShift g h) (I / 2) = cosh(h / 4) * paperFT g (I / 2)`. -/
theorem paperFT_evenShift_I_div_two {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    paperFT (fun x => (evenShift g h x : ℂ)) (I / 2) =
      ((Real.cosh (h / 4) : ℝ) : ℂ) * paperFT (fun x => (g x : ℂ)) (I / 2) := by
  rw [paperFT_evenShift hg hgc h (I / 2)]
  congr 1
  have e1 : I * (I / 2) * ((h / 2 : ℝ) : ℂ) = ((-(h / 4) : ℝ) : ℂ) := by
    rw [show I * (I / 2) * ((h / 2 : ℝ) : ℂ) = (I * I) * (h : ℂ) / 4 by push_cast; ring,
      Complex.I_mul_I]
    push_cast; ring
  have e2 : I * (I / 2) * ((-(h / 2) : ℝ) : ℂ) = ((h / 4 : ℝ) : ℂ) := by
    rw [show I * (I / 2) * ((-(h / 2) : ℝ) : ℂ) = -(I * I) * (h : ℂ) / 4 by push_cast; ring,
      Complex.I_mul_I]
    push_cast; ring
  rw [e1, e2, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Real.cosh_eq]
  push_cast
  ring

/-- Evaluation of `paperFT` of `evenShift g h` at `-I / 2`:
`paperFT (evenShift g h) (-I / 2) = cosh(h / 4) * paperFT g (-I / 2)`. -/
theorem paperFT_evenShift_neg_I_div_two {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    paperFT (fun x => (evenShift g h x : ℂ)) (-I / 2) =
      ((Real.cosh (h / 4) : ℝ) : ℂ) * paperFT (fun x => (g x : ℂ)) (-I / 2) := by
  rw [paperFT_evenShift hg hgc h (-I / 2)]
  congr 1
  have e1 : I * (-I / 2) * ((h / 2 : ℝ) : ℂ) = ((h / 4 : ℝ) : ℂ) := by
    rw [show I * (-I / 2) * ((h / 2 : ℝ) : ℂ) = -(I * I) * (h : ℂ) / 4 by push_cast; ring,
      Complex.I_mul_I]
    push_cast; ring
  have e2 : I * (-I / 2) * ((-(h / 2) : ℝ) : ℂ) = ((-(h / 4) : ℝ) : ℂ) := by
    rw [show I * (-I / 2) * ((-(h / 2) : ℝ) : ℂ) = (I * I) * (h : ℂ) / 4 by push_cast; ring,
      Complex.I_mul_I]
    push_cast; ring
  rw [e1, e2, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Real.cosh_eq]
  push_cast
  ring

/-- **Hyperbolic Half-Moment Scaling Law of `evenShift g h`**:
for any continuous compactly supported `g : ℝ → ℝ` and shift `h ∈ ℝ`,
`coshHalfMoment (evenShift g h) = Real.cosh (h / 4) * coshHalfMoment g` and
`sinhHalfMoment (evenShift g h) = Real.cosh (h / 4) * sinhHalfMoment g`. -/
theorem coshHalfMoment_and_sinhHalfMoment_evenShift {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (h : ℝ) :
    coshHalfMoment (evenShift g h) = Real.cosh (h / 4) * coshHalfMoment g ∧
      sinhHalfMoment (evenShift g h) = Real.cosh (h / 4) * sinhHalfMoment g := by
  have hed : Continuous (evenShift g h) := by
    unfold evenShift; fun_prop
  have hec : HasCompactSupport (evenShift g h) := hasCompactSupport_evenShift hgc h
  obtain ⟨hEp, hEm⟩ := integral_mul_exp_half_eq_cosh_add_sinh hed hec
  obtain ⟨hgp, hgm⟩ := integral_mul_exp_half_eq_cosh_add_sinh hg hgc
  have h1 := paperFT_evenShift_I_div_two hg hgc h
  have h2 := paperFT_evenShift_neg_I_div_two hg hgc h
  rw [paperFT_ofReal_I_div_two, paperFT_ofReal_I_div_two, hEm, hgm, ← Complex.ofReal_mul] at h1
  rw [paperFT_ofReal_neg_I_div_two, paperFT_ofReal_neg_I_div_two, hEp, hgp,
    ← Complex.ofReal_mul] at h2
  have h1r := congrArg Complex.re h1
  have h2r := congrArg Complex.re h2
  simp only [Complex.ofReal_re] at h1r h2r
  constructor <;> linarith

/-- First component of `coshHalfMoment_and_sinhHalfMoment_evenShift`:
`coshHalfMoment (evenShift g h) = Real.cosh (h / 4) * coshHalfMoment g`. -/
theorem coshHalfMoment_evenShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    coshHalfMoment (evenShift g h) = Real.cosh (h / 4) * coshHalfMoment g :=
  (coshHalfMoment_and_sinhHalfMoment_evenShift hg hgc h).1

/-- Second component of `coshHalfMoment_and_sinhHalfMoment_evenShift`:
`sinhHalfMoment (evenShift g h) = Real.cosh (h / 4) * sinhHalfMoment g`. -/
theorem sinhHalfMoment_evenShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    sinhHalfMoment (evenShift g h) = Real.cosh (h / 4) * sinhHalfMoment g :=
  (coshHalfMoment_and_sinhHalfMoment_evenShift hg hgc h).2

/-- **Universal Pole-Scaling Identity of `evenShift g h`**:
for every continuous compactly supported `g : ℝ → ℝ` and `h ∈ ℝ`, applying `evenShift g h` scales
`(weilPoleTerm k_g).re` by `cosh(h / 4)²`. -/
theorem re_weilPoleTerm_evenShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    (weilPoleTerm (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ)))).re =
      Real.cosh (h / 4) ^ 2 *
        (weilPoleTerm (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re := by
  have hed : Continuous (evenShift g h) := by
    unfold evenShift; fun_prop
  have hec : HasCompactSupport (evenShift g h) := hasCompactSupport_evenShift hgc h
  rw [re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hed hec,
    re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hg hgc,
    coshHalfMoment_evenShift hg hgc h, sinhHalfMoment_evenShift hg hgc h]
  ring

/-- **Hyperbolic Pole Conservation Law (`cosh²(h/4) - sinh²(h/4) = 1`)**:
the pole terms of `evenShift g h` and `oddShift g h` sum identically to the pole term of `g`. -/
theorem re_weilPoleTerm_evenShift_add_oddShift {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (h : ℝ) :
    (weilPoleTerm (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ)))).re +
      (weilPoleTerm (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ)))).re =
      (weilPoleTerm (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re := by
  rw [re_weilPoleTerm_evenShift hg hgc h, re_weilPoleTerm_oddShift hg hgc h]
  have hcs := Real.cosh_sq_sub_sinh_sq (h / 4)
  linear_combination
    (weilPoleTerm (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re * hcs

/-- **Shift-Polarization Additivity of `paperFT` of `EF.weilTest`**:
for every `g ∈ C²_c(ℝ)`, `h ∈ ℝ`, and `z ∈ ℂ`,
`paperFT (k_{evenShift g h}) z + paperFT (k_{oddShift g h}) z = paperFT k_g z`. -/
theorem paperFT_weilTest_evenShift_add_oddShift {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (h : ℝ) (z : ℂ) :
    paperFT (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ))) z +
      paperFT (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ))) z =
      paperFT (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) z := by
  set ke := EF.weilTest (fun u => (evenShift g h u : ℂ)) (fun u => (evenShift g h u : ℂ))
  set ko := EF.weilTest (fun u => (oddShift g h u : ℂ)) (fun u => (oddShift g h u : ℂ))
  have hed : ContDiff ℝ 2 fun u => (evenShift g h u : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_evenShift hg h)
  have hec : HasCompactSupport fun u => (evenShift g h u : ℂ) :=
    (hasCompactSupport_evenShift hgc h).comp_left Complex.ofReal_zero
  have hod : ContDiff ℝ 2 fun u => (oddShift g h u : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_oddShift hg h)
  have hoc : HasCompactSupport fun u => (oddShift g h u : ℂ) :=
    (hasCompactSupport_oddShift hgc h).comp_left Complex.ofReal_zero
  have hke_cont : Continuous ke := (EF.weilTest_contDiff hed hed.continuous hec).continuous
  have hke_cpt : HasCompactSupport ke := EF.weilTest_hasCompactSupport hec hec
  have hko_cont : Continuous ko := (EF.weilTest_contDiff hod hod.continuous hoc).continuous
  have hko_cpt : HasCompactSupport ko := EF.weilTest_hasCompactSupport hoc hoc
  have heq : EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) =
      fun y => (1 : ℂ) * ke y + (1 : ℂ) * ko y := by
    funext y
    simp only [one_mul, ke, ko, weilTest_evenShift_add_oddShift hg.continuous hgc h y]
  rw [heq, paperFT_smul_add_smul 1 1 z
    (integrable_mul_cexp_of_compact hke_cont hke_cpt z)
    (integrable_mul_cexp_of_compact hko_cont hko_cpt z), one_mul, one_mul]

/-- **Shift-Polarization Additivity of `markovArchRe`**:
for every `g ∈ C²_c(ℝ)` and `h ∈ ℝ`,
`markovArchRe (k_{evenShift g h}) + markovArchRe (k_{oddShift g h}) = markovArchRe k_g`. -/
theorem markovArchRe_evenShift_add_oddShift {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (h : ℝ) :
    markovArchRe (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ))) +
      markovArchRe (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ))) =
      markovArchRe (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) := by
  set Ue : ℝ → ℂ := fun u => (evenShift g h u : ℂ)
  set Uo : ℝ → ℂ := fun u => (oddShift g h u : ℂ)
  set U : ℝ → ℂ := fun u => (g u : ℂ)
  have hUed : ContDiff ℝ 2 Ue := Complex.ofRealCLM.contDiff.comp (contDiff_evenShift hg h)
  have hUec : HasCompactSupport Ue :=
    (hasCompactSupport_evenShift hgc h).comp_left Complex.ofReal_zero
  have hUod : ContDiff ℝ 2 Uo := Complex.ofRealCLM.contDiff.comp (contDiff_oddShift hg h)
  have hUoc : HasCompactSupport Uo :=
    (hasCompactSupport_oddShift hgc h).comp_left Complex.ofReal_zero
  rw [markovArchRe_eq_re_archIntegral, markovArchRe_eq_re_archIntegral,
    markovArchRe_eq_re_archIntegral]
  have harch : (∫ r : ℝ, paperFT (EF.weilTest U U) r * (EF.gammaBracket r : ℂ)) =
      (∫ r : ℝ, paperFT (EF.weilTest Ue Ue) r * (EF.gammaBracket r : ℂ)) +
        ∫ r : ℝ, paperFT (EF.weilTest Uo Uo) r * (EF.gammaBracket r : ℂ) := by
    rw [← integral_add
      (LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hUed hUec hUed hUec)
      (LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hUod hUoc hUod hUoc)]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [U, Ue, Uo, ← paperFT_weilTest_evenShift_add_oddShift hg hgc h r]
    ring
  rw [harch, mul_add, Complex.add_re]

/-- **Shift-Polarization Additivity of `weilArchRe`**:
for every `g ∈ C²_c(ℝ)` and `h ∈ ℝ`,
`weilArchRe (k_{evenShift g h}) + weilArchRe (k_{oddShift g h}) = weilArchRe k_g`. -/
theorem weilArchRe_evenShift_add_oddShift {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (h : ℝ) :
    weilArchRe (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ))) +
      weilArchRe (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ))) =
      weilArchRe (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) := by
  have hm := markovArchRe_evenShift_add_oddShift hg hgc h
  have hp := re_weilPoleTerm_evenShift_add_oddShift hg.continuous hgc h
  unfold markovArchRe at hm
  linarith

/-- **Shift-Polarization Additivity of `logValue`**:
for every continuous compactly supported `g : ℝ → ℝ`, `h ∈ ℝ`, and `n : ℕ`,
`logValue (evenShift g h) n + logValue (oddShift g h) n = logValue g n`. -/
theorem logValue_evenShift_add_oddShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) (n : ℕ) :
    logValue (fun u => (evenShift g h u : ℂ)) n +
      logValue (fun u => (oddShift g h u : ℂ)) n =
      logValue (fun u => (g u : ℂ)) n := by
  unfold logValue
  rw [← add_div]
  congr 1
  have h1 := weilTest_evenShift_add_oddShift hg hgc h (Real.log n)
  have h2 := weilTest_evenShift_add_oddShift hg hgc h (-Real.log n)
  rw [← Complex.add_re]
  congr 1
  linear_combination h1 + h2

/-- **Shift-Polarization Additivity of `logVector`**:
`logVector (evenShift g h) + logVector (oddShift g h) = logVector g`. -/
theorem logVector_evenShift_add_oddShift {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (h : ℝ) :
    logVector (realWeilTestFn (evenShift g h) (contDiff_evenShift hg h)
        (hasCompactSupport_evenShift hgc h)) +
      logVector (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
        (hasCompactSupport_oddShift hgc h)) =
      logVector (realWeilTestFn g hg hgc) := by
  ext j
  simp only [Finsupp.coe_add, Pi.add_apply, logVector_apply]
  exact logValue_evenShift_add_oddShift hg.continuous hgc h j

/-- **Shift-Polarization Additivity of `primeBlindCounterterm`**:
for every sequence `lam : ℕ → ℝ`, `g ∈ C²_c(ℝ)`, and `h ∈ ℝ`,
`primeBlindCounterterm lam (evenShift g h) + primeBlindCounterterm lam (oddShift g h) = primeBlindCounterterm lam g`. -/
theorem primeBlindCounterterm_evenShift_add_oddShift (lam : ℕ → ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (h : ℝ) :
    primeBlindCounterterm lam (realWeilTestFn (evenShift g h) (contDiff_evenShift hg h)
        (hasCompactSupport_evenShift hgc h)) +
      primeBlindCounterterm lam (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
        (hasCompactSupport_oddShift hgc h)) =
      primeBlindCounterterm lam (realWeilTestFn g hg hgc) := by
  unfold primeBlindCounterterm
  rw [← map_add, logVector_evenShift_add_oddShift hg hgc h]

/-- **Shift-Polarization Additivity of `(weilFullFunctional lam).re`**:
for every sequence `lam : ℕ → ℝ`, `g ∈ C²_c(ℝ)`, and `h ∈ ℝ`,
`(weilFullFunctional lam (k_{evenShift g h})).re + (weilFullFunctional lam (k_{oddShift g h})).re = (weilFullFunctional lam k_g).re`. -/
theorem re_weilFullFunctional_evenShift_add_oddShift (lam : ℕ → ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (h : ℝ) :
    (weilFullFunctional lam (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ)))).re +
      (weilFullFunctional lam (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ)))).re =
      (weilFullFunctional lam (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re := by
  have h1 : (weilFullFunctional lam (EF.weilTest (fun u => (evenShift g h u : ℂ))
      (fun u => (evenShift g h u : ℂ)))).re =
      weilArchRe (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn (evenShift g h) (contDiff_evenShift hg h)
        (hasCompactSupport_evenShift hgc h)) :=
    re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam
      (realWeilTestFn (evenShift g h) (contDiff_evenShift hg h) (hasCompactSupport_evenShift hgc h))
  have h2 : (weilFullFunctional lam (EF.weilTest (fun u => (oddShift g h u : ℂ))
      (fun u => (oddShift g h u : ℂ)))).re =
      weilArchRe (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
        (hasCompactSupport_oddShift hgc h)) :=
    re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam
      (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h) (hasCompactSupport_oddShift hgc h))
  have h3 : (weilFullFunctional lam (EF.weilTest (fun u => (g u : ℂ))
      (fun u => (g u : ℂ)))).re =
      weilArchRe (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn g hg hgc) :=
    re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam (realWeilTestFn g hg hgc)
  linarith [weilArchRe_evenShift_add_oddShift hg hgc h,
    primeBlindCounterterm_evenShift_add_oddShift lam hg hgc h]

/-- **Shift-Polarization Additivity of `markovCountertermEnergy`**:
for every sequence `lam : ℕ → ℝ`, `g ∈ C²_c(ℝ)`, and `h ∈ ℝ`,
`markovCountertermEnergy lam (evenShift g h) + markovCountertermEnergy lam (oddShift g h) = markovCountertermEnergy lam g`. -/
theorem markovCountertermEnergy_evenShift_add_oddShift (lam : ℕ → ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (h : ℝ) :
    markovCountertermEnergy lam (fun u => (evenShift g h u : ℂ)) +
      markovCountertermEnergy lam (fun u => (oddShift g h u : ℂ)) =
      markovCountertermEnergy lam (fun u => (g u : ℂ)) := by
  have h1 : markovCountertermEnergy lam (fun u => (evenShift g h u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn (evenShift g h) (contDiff_evenShift hg h)
        (hasCompactSupport_evenShift hgc h)) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam
      (realWeilTestFn (evenShift g h) (contDiff_evenShift hg h) (hasCompactSupport_evenShift hgc h))
  have h2 : markovCountertermEnergy lam (fun u => (oddShift g h u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
        (hasCompactSupport_oddShift hgc h)) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam
      (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h) (hasCompactSupport_oddShift hgc h))
  have h3 : markovCountertermEnergy lam (fun u => (g u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn g hg hgc) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn g hg hgc)
  linarith [markovArchRe_evenShift_add_oddShift hg hgc h,
    primeBlindCounterterm_evenShift_add_oddShift lam hg hgc h]

/-- **Shift-Polarization Additivity of `markovEnergy`**:
for every `g ∈ C²_c(ℝ)` and `h ∈ ℝ`,
`markovEnergy (evenShift g h) + markovEnergy (oddShift g h) = markovEnergy g`. -/
theorem markovEnergy_evenShift_add_oddShift {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (h : ℝ) :
    markovEnergy (fun u => (evenShift g h u : ℂ)) +
      markovEnergy (fun u => (oddShift g h u : ℂ)) =
      markovEnergy (fun u => (g u : ℂ)) := by
  rw [← markovCountertermEnergy_vonMangoldt_eq_markovEnergy,
    ← markovCountertermEnergy_vonMangoldt_eq_markovEnergy,
    ← markovCountertermEnergy_vonMangoldt_eq_markovEnergy]
  exact markovCountertermEnergy_evenShift_add_oddShift _ hg hgc h

/-! ## Section 2: Linearity of Hyperbolic Half-Moments, the Even Primitive Sector `EvenPrimitiveWeilTestFn`, and Orthogonal Parity Equivalence on the Primitive Hyperplane -/

/-- Linearity of `coshHalfMoment` under linear combinations of continuous compactly supported
functions. -/
theorem coshHalfMoment_linear_comb {F G : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hG : Continuous G) (hGc : HasCompactSupport G) (a b : ℝ) :
    coshHalfMoment (fun x => a * F x + b * G x) =
      a * coshHalfMoment F + b * coshHalfMoment G := by
  unfold coshHalfMoment
  have iF : Integrable fun x => F x * Real.cosh (x / 2) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  have iG : Integrable fun x => G x * Real.cosh (x / 2) :=
    (hG.mul (by fun_prop)).integrable_of_hasCompactSupport hGc.mul_right
  have e : (fun x => (a * F x + b * G x) * Real.cosh (x / 2)) =
      fun x => a * (F x * Real.cosh (x / 2)) + b * (G x * Real.cosh (x / 2)) := by
    funext x; ring
  rw [e, integral_add (iF.const_mul a) (iG.const_mul b), integral_const_mul, integral_const_mul]

/-- Linearity of `sinhHalfMoment` under linear combinations of continuous compactly supported
functions. -/
theorem sinhHalfMoment_linear_comb {F G : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hG : Continuous G) (hGc : HasCompactSupport G) (a b : ℝ) :
    sinhHalfMoment (fun x => a * F x + b * G x) =
      a * sinhHalfMoment F + b * sinhHalfMoment G := by
  unfold sinhHalfMoment
  have iF : Integrable fun x => F x * Real.sinh (x / 2) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  have iG : Integrable fun x => G x * Real.sinh (x / 2) :=
    (hG.mul (by fun_prop)).integrable_of_hasCompactSupport hGc.mul_right
  have e : (fun x => (a * F x + b * G x) * Real.sinh (x / 2)) =
      fun x => a * (F x * Real.sinh (x / 2)) + b * (G x * Real.sinh (x / 2)) := by
    funext x; ring
  rw [e, integral_add (iF.const_mul a) (iG.const_mul b), integral_const_mul, integral_const_mul]

/-- The type of **even primitive real Weil tests**: `f ∈ C²_c(ℝ)` satisfying `∀ x, f (-x) = f x`
and `coshHalfMoment f = 0`. -/
def EvenPrimitiveWeilTestFn : Type :=
  {f : ℝ → ℝ //
    ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ (∀ x, f (-x) = f x) ∧ coshHalfMoment f = 0}

/-- Inclusion of `EvenPrimitiveWeilTestFn` into `PrimitiveWeilTestFn`. -/
def EvenPrimitiveWeilTestFn.toPrimitiveWeilTestFn (f : EvenPrimitiveWeilTestFn) :
    PrimitiveWeilTestFn :=
  ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.2⟩

/-- Complex lift of `f : EvenPrimitiveWeilTestFn` into `WeilTestFn`. -/
def EvenPrimitiveWeilTestFn.toWeilTestFn (f : EvenPrimitiveWeilTestFn) : WeilTestFn :=
  realWeilTestFn f.1 f.2.1 f.2.2.1

@[simp]
theorem EvenPrimitiveWeilTestFn.toWeilTestFn_coe (f : EvenPrimitiveWeilTestFn) :
    f.toWeilTestFn.1 = fun x => (f.1 x : ℂ) := rfl

/-- Every even primitive test has vanishing `sinhHalfMoment`. -/
theorem EvenPrimitiveWeilTestFn.sinhHalfMoment_eq_zero (f : EvenPrimitiveWeilTestFn) :
    sinhHalfMoment f.1 = 0 :=
  sinhHalfMoment_eq_zero_of_even f.2.2.2.1

/-- Every even primitive test has identically vanishing real pole term
`(weilPoleTerm (EF.weilTest f f)).re = 0`. -/
theorem EvenPrimitiveWeilTestFn.re_weilPoleTerm_eq_zero (f : EvenPrimitiveWeilTestFn) :
    (weilPoleTerm (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)).re = 0 := by
  rw [EvenPrimitiveWeilTestFn.toWeilTestFn_coe,
    re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq f.2.1.continuous f.2.2.1,
    f.2.2.2.2, f.sinhHalfMoment_eq_zero]
  ring

/-- On `EvenPrimitiveWeilTestFn`, `markovArchRe` coincides with `weilArchRe`. -/
theorem EvenPrimitiveWeilTestFn.markovArchRe_eq_weilArchRe (f : EvenPrimitiveWeilTestFn) :
    markovArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1) =
      weilArchRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1) := by
  unfold markovArchRe
  rw [f.re_weilPoleTerm_eq_zero, sub_zero]

/-- **Exact Pole-Free Coincidence on `EvenPrimitiveWeilTestFn`**:
for every sequence `lam : ℕ → ℝ` and every `f : EvenPrimitiveWeilTestFn`,
`markovCountertermEnergy lam f = (weilFullFunctional lam k_f).re`. -/
theorem markovCountertermEnergy_evenPrimitive_eq_re_weilFullFunctional (lam : ℕ → ℝ)
    (f : EvenPrimitiveWeilTestFn) :
    markovCountertermEnergy lam f.toWeilTestFn.1 =
      (weilFullFunctional lam (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)).re := by
  rw [markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam f.toWeilTestFn,
    re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam f.toWeilTestFn,
    f.markovArchRe_eq_weilArchRe]

/-- Canonical even-part projection `PrimitiveWeilTestFn → EvenPrimitiveWeilTestFn`. -/
def PrimitiveWeilTestFn.evenPart (f : PrimitiveWeilTestFn) : EvenPrimitiveWeilTestFn :=
  ⟨evenPartReal f.1, contDiff_evenPartReal f.2.1, hasCompactSupport_evenPartReal f.2.2.1,
    evenPartReal_neg f.1, by
      rw [← coshHalfMoment_eq_evenPartReal f.2.1.continuous f.2.2.1]
      exact f.2.2.2⟩

/-- Canonical odd-part projection `PrimitiveWeilTestFn → OddWeilTestFn`. -/
def PrimitiveWeilTestFn.oddPart (f : PrimitiveWeilTestFn) : OddWeilTestFn :=
  ⟨oddPartReal f.1, contDiff_oddPartReal f.2.1, hasCompactSupport_oddPartReal f.2.2.1,
    oddPartReal_neg f.1⟩

/-- Markov positivity on the even primitive sector `EvenPrimitiveWeilTestFn`. -/
def MarkovPositiveEvenPrimitive (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
    (∀ x, f (-x) = f x) → coshHalfMoment f = 0 →
    0 ≤ markovCountertermEnergy lam (fun x => (f x : ℂ))

/-- **Orthogonal Parity Equivalence on the Primitive Hyperplane**:
for every counterterm sequence `lam : ℕ → ℝ`, `MarkovPositivePrimitive lam` holds if and only if
both `MarkovPositiveEvenPrimitive lam` and `MarkovPositiveOdd lam` hold. -/
theorem markovPositivePrimitive_iff_evenPrimitive_and_odd (lam : ℕ → ℝ) :
    MarkovPositivePrimitive lam ↔ MarkovPositiveEvenPrimitive lam ∧ MarkovPositiveOdd lam := by
  constructor
  · intro hP
    refine ⟨fun f hf hfc _ hcosh => hP f hf hfc hcosh,
      fun f hf hfc hodd => hP f hf hfc (coshHalfMoment_eq_zero_of_odd hodd)⟩
  · rintro ⟨hE, hO⟩ F hF hFc hcosh
    rw [markovCountertermEnergy_ofReal_eq_even_add_odd lam hF hFc]
    have hcosh_e : coshHalfMoment (evenPartReal F) = 0 := by
      rw [← coshHalfMoment_eq_evenPartReal hF.continuous hFc]
      exact hcosh
    exact add_nonneg
      (hE (evenPartReal F) (contDiff_evenPartReal hF) (hasCompactSupport_evenPartReal hFc)
        (evenPartReal_neg F) hcosh_e)
      (hO (oddPartReal F) (contDiff_oddPartReal hF) (hasCompactSupport_oddPartReal hFc)
        (oddPartReal_neg F))

/-- `evenShift` preserves `EvenPrimitiveWeilTestFn` for every shift `h ∈ ℝ`. -/
def EvenPrimitiveWeilTestFn.evenShiftFn (f : EvenPrimitiveWeilTestFn) (h : ℝ) :
    EvenPrimitiveWeilTestFn :=
  ⟨evenShift f.1 h, contDiff_evenShift f.2.1 h, hasCompactSupport_evenShift f.2.2.1 h,
    evenShift_neg_of_even f.2.2.2.1 h, by
      rw [coshHalfMoment_evenShift f.2.1.continuous f.2.2.1 h, f.2.2.2.2, mul_zero]⟩

/-- `oddShift` maps `EvenPrimitiveWeilTestFn` into `OddWeilTestFn` for every shift `h ∈ ℝ`, and
moreover its `sinhHalfMoment` is also zero (`sinhHalfMoment (oddShift f.1 h) = 0`). -/
def EvenPrimitiveWeilTestFn.oddShiftFn (f : EvenPrimitiveWeilTestFn) (h : ℝ) :
    OddWeilTestFn :=
  ⟨oddShift f.1 h, contDiff_oddShift f.2.1 h, hasCompactSupport_oddShift f.2.2.1 h,
    oddShift_neg f.2.2.2.1 h⟩

theorem EvenPrimitiveWeilTestFn.sinhHalfMoment_oddShiftFn_eq_zero
    (f : EvenPrimitiveWeilTestFn) (h : ℝ) :
    sinhHalfMoment (f.oddShiftFn h).1 = 0 := by
  change sinhHalfMoment (oddShift f.1 h) = 0
  rw [sinhHalfMoment_oddShift f.2.1.continuous f.2.2.1 h, f.2.2.2.2, mul_zero]

/-! ## Section 3: The Hodge-Index Primitive-Hyperplane Projection `primitiveProj Φ₀ F` -/

/-- The **Hodge-index primitive-hyperplane projection** of a test `F : ℝ → ℝ` along a reference test
`Φ₀ : ℝ → ℝ`:
`primitiveProj Φ₀ F x = F x - (coshHalfMoment F / coshHalfMoment Φ₀) * Φ₀ x`. -/
def primitiveProj (Φ₀ F : ℝ → ℝ) (x : ℝ) : ℝ :=
  F x - (coshHalfMoment F / coshHalfMoment Φ₀) * Φ₀ x

theorem primitiveProj_eq_linear_comb (Φ₀ F : ℝ → ℝ) :
    primitiveProj Φ₀ F =
      fun x => 1 * F x + (-(coshHalfMoment F / coshHalfMoment Φ₀)) * Φ₀ x := by
  funext x; unfold primitiveProj; ring

theorem contDiff_primitiveProj {Φ₀ F : ℝ → ℝ} (hΦ₀ : ContDiff ℝ 2 Φ₀) (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (primitiveProj Φ₀ F) :=
  hF.sub (contDiff_const.mul hΦ₀)

theorem hasCompactSupport_primitiveProj {Φ₀ F : ℝ → ℝ} (hΦ₀ : HasCompactSupport Φ₀)
    (hF : HasCompactSupport F) :
    HasCompactSupport (primitiveProj Φ₀ F) :=
  hF.sub hΦ₀.mul_left

/-- **Exact Vanishing of `coshHalfMoment` under `primitiveProj Φ₀`**:
whenever `coshHalfMoment Φ₀ ≠ 0`, `primitiveProj Φ₀ F` lies on the primitive hyperplane
`coshHalfMoment (primitiveProj Φ₀ F) = 0`. -/
theorem coshHalfMoment_primitiveProj {Φ₀ F : ℝ → ℝ} (hΦ₀ : Continuous Φ₀)
    (hΦ₀c : HasCompactSupport Φ₀) (hΦ₀_ne : coshHalfMoment Φ₀ ≠ 0) (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    coshHalfMoment (primitiveProj Φ₀ F) = 0 := by
  rw [primitiveProj_eq_linear_comb, coshHalfMoment_linear_comb hF hFc hΦ₀ hΦ₀c]
  field_simp [hΦ₀_ne]
  ring

/-- `primitiveProj Φ₀` leaves any test already on the primitive hyperplane (`coshHalfMoment F = 0`)
fixed. -/
theorem primitiveProj_eq_self_of_cosh_zero (Φ₀ : ℝ → ℝ) {F : ℝ → ℝ}
    (hcosh : coshHalfMoment F = 0) :
    primitiveProj Φ₀ F = F := by
  funext x
  simp [primitiveProj, hcosh]

/-- `primitiveProj Φ₀` leaves every odd test fixed. -/
theorem primitiveProj_eq_self_of_odd (Φ₀ : ℝ → ℝ) {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) :
    primitiveProj Φ₀ F = F :=
  primitiveProj_eq_self_of_cosh_zero Φ₀ (coshHalfMoment_eq_zero_of_odd hodd)

/-- When the reference test `Φ₀` is **even**, `primitiveProj Φ₀ F` preserves the odd part
`oddPartReal F` identically. -/
theorem oddPartReal_primitiveProj {Φ₀ : ℝ → ℝ} (heven : ∀ x, Φ₀ (-x) = Φ₀ x) (F : ℝ → ℝ) (x : ℝ) :
    oddPartReal (primitiveProj Φ₀ F) x = oddPartReal F x := by
  unfold oddPartReal primitiveProj
  rw [heven x]
  ring

/-- When the reference test `Φ₀` is **even**, `evenPartReal` commutes with `primitiveProj Φ₀`. -/
theorem evenPartReal_primitiveProj {Φ₀ : ℝ → ℝ} (heven : ∀ x, Φ₀ (-x) = Φ₀ x) (F : ℝ → ℝ)
    (hF : Continuous F) (hFc : HasCompactSupport F) (x : ℝ) :
    evenPartReal (primitiveProj Φ₀ F) x = primitiveProj Φ₀ (evenPartReal F) x := by
  have hcosh := coshHalfMoment_eq_evenPartReal hF hFc
  change (primitiveProj Φ₀ F x + primitiveProj Φ₀ F (-x)) / 2 =
    evenPartReal F x - (coshHalfMoment (evenPartReal F) / coshHalfMoment Φ₀) * Φ₀ x
  simp only [primitiveProj, evenPartReal, heven x, ← hcosh]
  ring

/-- When the reference test `Φ₀` is **even**, `primitiveProj Φ₀ F` preserves `sinhHalfMoment F`. -/
theorem sinhHalfMoment_primitiveProj {Φ₀ F : ℝ → ℝ} (hΦ₀ : Continuous Φ₀)
    (hΦ₀c : HasCompactSupport Φ₀) (heven : ∀ x, Φ₀ (-x) = Φ₀ x) (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    sinhHalfMoment (primitiveProj Φ₀ F) = sinhHalfMoment F := by
  rw [primitiveProj_eq_linear_comb, sinhHalfMoment_linear_comb hF hFc hΦ₀ hΦ₀c,
    sinhHalfMoment_eq_zero_of_even heven]
  ring

/-- **Pure Nonpositive Pole Law of the Primitive Projection**:
when `Φ₀` is even with `coshHalfMoment Φ₀ ≠ 0`, the pole term of `primitiveProj Φ₀ F` is the pure
nonpositive square `-2 * sinhHalfMoment F ^ 2 ≤ 0`. -/
theorem re_weilPoleTerm_primitiveProj {Φ₀ F : ℝ → ℝ} (hΦ₀ : Continuous Φ₀)
    (hΦ₀c : HasCompactSupport Φ₀) (heven : ∀ x, Φ₀ (-x) = Φ₀ x) (hΦ₀_ne : coshHalfMoment Φ₀ ≠ 0)
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    (weilPoleTerm (EF.weilTest (fun x => (primitiveProj Φ₀ F x : ℂ))
        (fun x => (primitiveProj Φ₀ F x : ℂ)))).re =
      -2 * sinhHalfMoment F ^ 2 := by
  have hP_cont : Continuous (primitiveProj Φ₀ F) := hF.sub (continuous_const.mul hΦ₀)
  have hP_cpt : HasCompactSupport (primitiveProj Φ₀ F) := hasCompactSupport_primitiveProj hΦ₀c hFc
  rw [re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hP_cont hP_cpt,
    coshHalfMoment_primitiveProj hΦ₀ hΦ₀c hΦ₀_ne hF hFc,
    sinhHalfMoment_primitiveProj hΦ₀ hΦ₀c heven hF hFc]
  ring

/-! ## Section 4: The Three-Tier PBAP Positivity and Cone Hierarchy and Cesàro Dominance Bridges -/

/-- **Full-Cone Weil Positivity Implies Odd-Sector Markov Positivity**:
for every sequence `lam : ℕ → ℝ`, `WeilPositiveFull lam → MarkovPositiveOdd lam`. -/
theorem markovPositiveOdd_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    MarkovPositiveOdd lam :=
  markovPositiveOdd_of_markovPositivePrimitive (markovPositivePrimitive_of_weilPositiveFull hW)

/-- **Full-Cone Weil Positivity Implies Even-Primitive Markov Positivity**:
for every sequence `lam : ℕ → ℝ`, `WeilPositiveFull lam → MarkovPositiveEvenPrimitive lam`. -/
theorem markovPositiveEvenPrimitive_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    MarkovPositiveEvenPrimitive lam :=
  fun f hf hfc _ hcosh =>
    markovPositivePrimitive_of_weilPositiveFull hW f hf hfc hcosh

/-- **Three-Tier Prime-Blind Cone Hierarchy (Full $\implies$ Primitive $\implies$ Odd)**:
1. `WeilOneSided.PrimeBlindPositive → PrimitivePrimeBlindPositive`
2. `PrimitivePrimeBlindPositive → OddPrimeBlindPositive`
3. `WeilOneSided.PrimeBlindPositive → OddPrimeBlindPositive`. -/
theorem primitivePrimeBlindPositive_of_primeBlindPositive (h : WeilOneSided.PrimeBlindPositive) :
    PrimitivePrimeBlindPositive := by
  obtain ⟨lam, hW⟩ := exists_weilPositiveFull_iff_primeBlindPositive.mpr h
  exact exists_markovPositivePrimitive_iff_primitivePrimeBlindPositive.mp
    ⟨lam, markovPositivePrimitive_of_weilPositiveFull hW⟩

theorem oddPrimeBlindPositive_of_primitivePrimeBlindPositive (h : PrimitivePrimeBlindPositive) :
    OddPrimeBlindPositive := by
  obtain ⟨lam, hP⟩ := exists_markovPositivePrimitive_iff_primitivePrimeBlindPositive.mpr h
  exact exists_markovPositiveOdd_iff_oddPrimeBlindPositive.mp
    ⟨lam, markovPositiveOdd_of_markovPositivePrimitive hP⟩

theorem oddPrimeBlindPositive_of_primeBlindPositive (h : WeilOneSided.PrimeBlindPositive) :
    OddPrimeBlindPositive :=
  oddPrimeBlindPositive_of_primitivePrimeBlindPositive
    (primitivePrimeBlindPositive_of_primeBlindPositive h)

/-- **Three-Tier One-Sided Nonpositive Cone Hierarchy (Full $\implies$ Primitive $\implies$ Odd)**:
1. `PositiveOnNonposCone U → PrimitivePositiveOnNonposCone U`
2. `PrimitivePositiveOnNonposCone U → OddPositiveOnNonposCone U`
3. `PositiveOnNonposCone U → OddPositiveOnNonposCone U`. -/
theorem primitivePositiveOnNonposCone_of_positiveOnNonposCone {U : ℕ → ℝ}
    (h : PositiveOnNonposCone U) :
    PrimitivePositiveOnNonposCone U := by
  obtain ⟨lam, hW, hle, _⟩ := exists_weilPositiveFull_le_of_positiveOnNonposCone h
  have hP := markovPositivePrimitive_of_weilPositiveFull hW
  intro c hc hnonpos
  have h1 : 0 ≤ c.sum fun f t => t * markovCountertermEnergy lam f.toWeilTestFn.1 :=
    Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (hP f.1 f.2.1 f.2.2.1 f.2.2.2)
  rw [sum_markovCountertermEnergy_primitive] at h1 ⊢
  have h2 : linearCombination ℝ (fun j : LogIndex => U j)
      (linearCombination ℝ (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn) c) ≤
      linearCombination ℝ (fun j : LogIndex => lam j)
        (linearCombination ℝ (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn) c) := by
    rw [linearCombination_apply, linearCombination_apply]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [smul_eq_mul]
    have hj : linearCombination ℝ (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn) c j ≤ 0 := by
      have h0 := hnonpos j j.2
      simpa only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
        logVector_apply, smul_eq_mul] using h0
    exact mul_le_mul_of_nonpos_left (hle j j.2) hj
  linarith

theorem oddPositiveOnNonposCone_of_primitivePositiveOnNonposCone {U : ℕ → ℝ}
    (h : PrimitivePositiveOnNonposCone U) :
    OddPositiveOnNonposCone U := by
  obtain ⟨lam, hP, hle, _⟩ := exists_markovPositivePrimitive_le_of_primitivePositiveOnNonposCone h
  have hO := markovPositiveOdd_of_markovPositivePrimitive hP
  intro c hc hnonpos
  have h1 : 0 ≤ c.sum fun f t => t * markovCountertermEnergy lam f.toWeilTestFn.1 :=
    Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (hO f.1 f.2.1 f.2.2.1 f.2.2.2)
  rw [sum_markovCountertermEnergy_odd] at h1 ⊢
  have h2 : linearCombination ℝ (fun j : LogIndex => U j)
      (linearCombination ℝ (fun f : OddWeilTestFn => logVector f.toWeilTestFn) c) ≤
      linearCombination ℝ (fun j : LogIndex => lam j)
        (linearCombination ℝ (fun f : OddWeilTestFn => logVector f.toWeilTestFn) c) := by
    rw [linearCombination_apply, linearCombination_apply]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [smul_eq_mul]
    have hj : linearCombination ℝ (fun f : OddWeilTestFn => logVector f.toWeilTestFn) c j ≤ 0 := by
      have h0 := hnonpos j j.2
      simpa only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
        logVector_apply, smul_eq_mul] using h0
    exact mul_le_mul_of_nonpos_left (hle j j.2) hj
  linarith

theorem oddPositiveOnNonposCone_of_positiveOnNonposCone {U : ℕ → ℝ}
    (h : PositiveOnNonposCone U) :
    OddPositiveOnNonposCone U :=
  oddPositiveOnNonposCone_of_primitivePositiveOnNonposCone
    (primitivePositiveOnNonposCone_of_positiveOnNonposCone h)

/-- **Three-Tier One-Sided Nonnegative Cone Hierarchy (Full $\implies$ Primitive $\implies$ Odd)**:
1. `PositiveOnNonnegCone L → PrimitivePositiveOnNonnegCone L`
2. `PrimitivePositiveOnNonnegCone L → OddPositiveOnNonnegCone L`
3. `PositiveOnNonnegCone L → OddPositiveOnNonnegCone L`. -/
theorem primitivePositiveOnNonnegCone_of_positiveOnNonnegCone {L : ℕ → ℝ}
    (h : PositiveOnNonnegCone L) :
    PrimitivePositiveOnNonnegCone L := by
  obtain ⟨lam, hW, hge, _⟩ := exists_weilPositiveFull_ge_of_positiveOnNonnegCone h
  have hP := markovPositivePrimitive_of_weilPositiveFull hW
  intro c hc hnonneg
  have h1 : 0 ≤ c.sum fun f t => t * markovCountertermEnergy lam f.toWeilTestFn.1 :=
    Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (hP f.1 f.2.1 f.2.2.1 f.2.2.2)
  rw [sum_markovCountertermEnergy_primitive] at h1 ⊢
  have h2 : linearCombination ℝ (fun j : LogIndex => L j)
      (linearCombination ℝ (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn) c) ≤
      linearCombination ℝ (fun j : LogIndex => lam j)
        (linearCombination ℝ (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn) c) := by
    rw [linearCombination_apply, linearCombination_apply]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [smul_eq_mul]
    have hj : 0 ≤ linearCombination ℝ (fun f : PrimitiveWeilTestFn => logVector f.toWeilTestFn) c j := by
      have h0 := hnonneg j j.2
      simpa only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
        logVector_apply, smul_eq_mul] using h0
    exact mul_le_mul_of_nonneg_left (hge j j.2) hj
  linarith

theorem oddPositiveOnNonnegCone_of_primitivePositiveOnNonnegCone {L : ℕ → ℝ}
    (h : PrimitivePositiveOnNonnegCone L) :
    OddPositiveOnNonnegCone L := by
  obtain ⟨lam, hP, hge, _⟩ := exists_markovPositivePrimitive_ge_of_primitivePositiveOnNonnegCone h
  have hO := markovPositiveOdd_of_markovPositivePrimitive hP
  intro c hc hnonneg
  have h1 : 0 ≤ c.sum fun f t => t * markovCountertermEnergy lam f.toWeilTestFn.1 :=
    Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (hO f.1 f.2.1 f.2.2.1 f.2.2.2)
  rw [sum_markovCountertermEnergy_odd] at h1 ⊢
  have h2 : linearCombination ℝ (fun j : LogIndex => L j)
      (linearCombination ℝ (fun f : OddWeilTestFn => logVector f.toWeilTestFn) c) ≤
      linearCombination ℝ (fun j : LogIndex => lam j)
        (linearCombination ℝ (fun f : OddWeilTestFn => logVector f.toWeilTestFn) c) := by
    rw [linearCombination_apply, linearCombination_apply]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [smul_eq_mul]
    have hj : 0 ≤ linearCombination ℝ (fun f : OddWeilTestFn => logVector f.toWeilTestFn) c j := by
      have h0 := hnonneg j j.2
      simpa only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
        logVector_apply, smul_eq_mul] using h0
    exact mul_le_mul_of_nonneg_left (hge j j.2) hj
  linarith

theorem oddPositiveOnNonnegCone_of_positiveOnNonnegCone {L : ℕ → ℝ}
    (h : PositiveOnNonnegCone L) :
    OddPositiveOnNonnegCone L :=
  oddPositiveOnNonnegCone_of_primitivePositiveOnNonnegCone
    (primitivePositiveOnNonnegCone_of_positiveOnNonnegCone h)

/-- **`m`-th Iterated-Prefix / Cesàro Dominance Bridge to `RiemannHypothesis` on the Odd Sector**:
if for every odd real test `f ∈ C²_c(ℝ)` there exist an order `m : ℕ` and a counterterm sequence
`μ : ℕ → ℝ` such that `0 ≤ markovCountertermEnergy μ f` and the `m`-th iterated prefix sums of `Λ`
vs `μ` satisfy the dominance condition against `iteratedForwardDiff m (logValue f)`, then
`RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_forall_odd_exists_iteratedPrefixSum_markov_nonneg
    (h : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → (∀ x, f (-x) = -f x) →
      ∃ (m : ℕ) (μ : ℕ → ℝ),
        0 ≤ markovCountertermEnergy μ (fun x => (f x : ℂ)) ∧
        (∀ n ≥ 2, 0 ≤ iteratedForwardDiff m (logValue (fun x => (f x : ℂ))) n) ∧
        (∀ n ≥ 2, countertermIteratedPrefixSum m
          (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) n ≤
          countertermIteratedPrefixSum m μ n)) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_forall_odd_markovEnergy_nonneg.mpr fun f hf hfc hodd => ?_
  obtain ⟨m, μ, hμ_nn, hdiff, hpref⟩ := h f hf hfc hodd
  obtain ⟨N, hN⟩ := exists_weilTest_log_eq_zero (realWeilTestFn f hf hfc)
  have h1 := markovCountertermEnergy_le_of_iteratedPrefixSum_le m hN
    (fun n hn => hdiff n (Finset.mem_Icc.mp hn).1)
    (fun n hn => hpref n (Finset.mem_Icc.mp hn).1)
  change markovCountertermEnergy μ (fun x => (f x : ℂ)) ≤
    markovCountertermEnergy (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
      (fun x => (f x : ℂ)) at h1
  rw [markovCountertermEnergy_vonMangoldt_eq_markovEnergy] at h1
  linarith

end RHTower

end
