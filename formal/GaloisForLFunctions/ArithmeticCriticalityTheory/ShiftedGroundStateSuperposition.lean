import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateReflectedCollarDefect

/-!
# Linear superpositions of shifted ground states

The folded single-shift generator is linear in `ω`, and for the shifted ground states all its pieces
are integrable and summable. Hence the folded generator, and the folded defect
`𝓛_N ω − Φ cosh(x/2) ω`, are linear on the span of the shifted ground states:

    𝓛_N(c₁ ω_a + c₂ ω_b) − Φ cosh(x/2) (c₁ ω_a + c₂ ω_b)
      = 2Φ(x) [ (c₁ sinh(a/2) + c₂ sinh(b/2)) sinh(x/2) − (c₁ C_a(x) + c₂ C_b(x)) ].

So whether a finite combination of shifted ground states is a folded supersolution at `x` is the
sign of a finite linear combination of the scalar functions `sinh(a/2) sinh(x/2) − C_a(x)`; no new
arithmetic enters. In particular a nonnegative combination is a folded supersolution at `x` only if
one of its constituents is.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

theorem foldedShiftGenerator_add (ω₁ ω₂ : ℝ → ℝ) (t x : ℝ) :
    foldedShiftGenerator (fun y => ω₁ y + ω₂ y) t x =
      foldedShiftGenerator ω₁ t x + foldedShiftGenerator ω₂ t x := by
  unfold foldedShiftGenerator
  ring

theorem foldedShiftGenerator_smul (c : ℝ) (ω : ℝ → ℝ) (t x : ℝ) :
    foldedShiftGenerator (fun y => c * ω y) t x = c * foldedShiftGenerator ω t x := by
  unfold foldedShiftGenerator
  ring

theorem integrableOn_archLevy_foldedShiftGenerator_shiftedGroundState {a x : ℝ} (ha : 0 < a)
    (hx : 0 < x) :
    IntegrableOn (fun t => archLevyDensity t * foldedShiftGenerator (shiftedGroundState a) t x)
      (Ioi 0) := by
  have h : IntegrableOn (fun t =>
      archLevyDensity t * twoSidedShiftGenerator (shiftedGroundState a) t x -
        2 * riemannKernelReal x * (archLevyDensity t * max (shiftDifference a (t - x)) 0)) (Ioi 0) :=
    (integrableOn_archLevy_twoSidedShiftGenerator_shiftedGroundState a x).sub
      ((integrableOn_archLevy_max_shiftDifference ha hx).const_mul _)
  exact h.congr_fun (fun t _ => (archLevy_foldedShiftGenerator_shiftedGroundState ha t x).symm)
    measurableSet_Ioi

theorem summable_atom_foldedShiftGenerator_shiftedGroundState {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Summable fun n : ℕ =>
      vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState a) (Real.log n) x :=
  ((summable_atom_twoSidedShiftGenerator_shiftedGroundState a x).sub
    ((summable_atom_max_shiftDifference a x).mul_left _)).congr fun n =>
      (atom_foldedShiftGenerator_shiftedGroundState ha x n).symm

/-- The folded generator is linear on the span of two shifted ground states. -/
theorem foldedGenerator_shiftedGroundState_combination {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (c₁ c₂ : ℝ) :
    foldedGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) x =
      c₁ * foldedGenerator (shiftedGroundState a) x + c₂ * foldedGenerator (shiftedGroundState b) x := by
  unfold foldedGenerator
  have hpt : ∀ t, foldedShiftGenerator (fun y => c₁ * shiftedGroundState a y +
      c₂ * shiftedGroundState b y) t x =
      c₁ * foldedShiftGenerator (shiftedGroundState a) t x +
        c₂ * foldedShiftGenerator (shiftedGroundState b) t x := by
    intro t
    rw [foldedShiftGenerator_add, foldedShiftGenerator_smul, foldedShiftGenerator_smul]
  have hA := integrableOn_archLevy_foldedShiftGenerator_shiftedGroundState ha hx
  have hB := integrableOn_archLevy_foldedShiftGenerator_shiftedGroundState hb hx
  have hSA := summable_atom_foldedShiftGenerator_shiftedGroundState ha x
  have hSB := summable_atom_foldedShiftGenerator_shiftedGroundState hb x
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      foldedShiftGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) t x) =
      c₁ * (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator (shiftedGroundState a) t x) +
        c₂ * ∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator (shiftedGroundState b) t x := by
    have hA' : IntegrableOn (fun t => c₁ *
        (archLevyDensity t * foldedShiftGenerator (shiftedGroundState a) t x)) (Ioi 0) :=
      hA.const_mul _
    have hB' : IntegrableOn (fun t => c₂ *
        (archLevyDensity t * foldedShiftGenerator (shiftedGroundState b) t x)) (Ioi 0) :=
      hB.const_mul _
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hA' hB']
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [hpt t]
    ring
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
      foldedShiftGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y)
        (Real.log n) x) =
      c₁ * (∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState a) (Real.log n) x) +
        c₂ * ∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState b) (Real.log n) x := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hSA.mul_left c₁).tsum_add (hSB.mul_left c₂)]
    refine tsum_congr fun n => ?_
    rw [hpt]
    ring
  rw [harch, hprime]
  ring

/-- **Folded defect of a combination of shifted ground states.** -/
theorem foldedDefect_shiftedGroundState_combination {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (c₁ c₂ : ℝ) :
    foldedGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) x -
        riemannKernelReal x * Real.cosh (x / 2) *
          (c₁ * shiftedGroundState a x + c₂ * shiftedGroundState b x) =
      2 * riemannKernelReal x *
        ((c₁ * Real.sinh (a / 2) + c₂ * Real.sinh (b / 2)) * Real.sinh (x / 2) -
          (c₁ * shiftedCollarMass a x + c₂ * shiftedCollarMass b x)) := by
  rw [foldedGenerator_shiftedGroundState_combination ha hb hx]
  have h1 := foldedGenerator_shiftedGroundState_sub_potential ha hx
  have h2 := foldedGenerator_shiftedGroundState_sub_potential hb hx
  linear_combination c₁ * h1 + c₂ * h2

/-- A nonnegative, nonzero combination of two shifted ground states is a folded supersolution at
`x` only if one of the two constituents is. -/
theorem exists_constituent_supersolution_of_combination {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc : 0 < c₁ ∨ 0 < c₂)
    (hsuper : riemannKernelReal x * Real.cosh (x / 2) *
        (c₁ * shiftedGroundState a x + c₂ * shiftedGroundState b x) ≤
      foldedGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) x) :
    shiftedCollarMass a x ≤ Real.sinh (a / 2) * Real.sinh (x / 2) ∨
      shiftedCollarMass b x ≤ Real.sinh (b / 2) * Real.sinh (x / 2) := by
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hd := foldedDefect_shiftedGroundState_combination ha hb hx c₁ c₂
  have hΦ := riemannKernelReal_pos x
  have hneg : (c₁ * Real.sinh (a / 2) + c₂ * Real.sinh (b / 2)) * Real.sinh (x / 2) -
      (c₁ * shiftedCollarMass a x + c₂ * shiftedCollarMass b x) < 0 := by
    rcases hc with hc | hc
    · nlinarith [mul_lt_mul_of_pos_left h1 hc, mul_le_mul_of_nonneg_left h2.le hc₂]
    · nlinarith [mul_le_mul_of_nonneg_left h1.le hc₁, mul_lt_mul_of_pos_left h2 hc]
  have hlt : foldedGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) x -
      riemannKernelReal x * Real.cosh (x / 2) *
        (c₁ * shiftedGroundState a x + c₂ * shiftedGroundState b x) < 0 := by
    rw [hd]
    exact mul_neg_of_pos_of_neg (by positivity) hneg
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
