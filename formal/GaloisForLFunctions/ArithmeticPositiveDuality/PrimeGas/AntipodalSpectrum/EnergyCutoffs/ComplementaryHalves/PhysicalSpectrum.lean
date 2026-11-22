import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.AdditiveHeat
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.CenteredPoles

/-!
# Complementary spectra of composition-balanced cutoffs

The digit coordinate preserves the actual cutoff label. The same shift
therefore gives half-integer two-copy levels, reflected additive heat,
and probability conservation at every pole in the centered strip.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

abbrev clockRadix (t : ExceptionalTime) (j : ℕ) : Radix :=
  ⟨(tailRadix t j).val,radix_gt_one t j⟩

abbrev Pair (t : ExceptionalTime) (j : ℕ) := BalancedCutoff t j × BalancedCutoff t j

def digits (t : ExceptionalTime) (j : ℕ) : BalancedCutoff t j ≃ Half (clockRadix t j) :=
  Equiv.subtypeEquivRight (fun n => adjacent_count_equality t j n)

def pairDigits (t : ExceptionalTime) (j : ℕ) : Pair t j ≃ Half (clockRadix t j) × Half (clockRadix t j) :=
  (digits t j).prodCongr (digits t j)

/-- Integer energy label obtained by interleaving both composition-balanced cutoffs. -/
def pairIndex (t : ExceptionalTime) (j : ℕ) : Pair t j ≃ ℕ :=
  (pairDigits t j).trans (interleave (clockRadix t j))

theorem pairIndex_apply (t : ExceptionalTime) (j : ℕ) (p : Pair t j) :
    pairIndex t j p = p.1.val+(tailRadix t j).val*p.2.val := rfl

def jointLevel (t : ExceptionalTime) (j : ℕ) (r a : ℝ) (p : Pair t j) : ℝ :=
  ((p.1.val:ℝ)+a)+r*((p.2.val:ℝ)+a)

abbrev centeredLevel (t : ExceptionalTime) (j : ℕ) :=
  jointLevel t j ((tailRadix t j).val:ℝ) (BalancedShift.center t j)

theorem centeredLevel_eq (t : ExceptionalTime) (j : ℕ) (p : Pair t j) :
    centeredLevel t j p = (pairIndex t j p:ℝ)+1/2 :=
  centered_level (clockRadix t j) (pairDigits t j p)

def ExactLevels (t : ExceptionalTime) (j : ℕ) (r a : ℝ) : Prop :=
  ∃ e : Pair t j ≃ ℕ, ∀ p, jointLevel t j r a p = (e p:ℝ)+1/2

/-- The complete two-copy spectrum determines the physical radix and centering shift. -/
theorem exact_levels_iff (t : ExceptionalTime) (j : ℕ) (r a : ℝ) :
    ExactLevels t j r a ↔ r = ((tailRadix t j).val:ℝ) ∧ a = BalancedShift.center t j := by
  change ExactLevels t j r a ↔ r = ((clockRadix t j).val:ℝ) ∧ a = midpoint (clockRadix t j)
  rw [← half_integer_rigidity (clockRadix t j) r a]
  let E := pairDigits t j
  constructor
  · rintro ⟨e,h⟩
    refine ⟨E.symm.trans e,fun p => ?_⟩
    have hp := h (E.symm p)
    change affineLevel r a (E (E.symm p)) = (e (E.symm p):ℝ)+1/2 at hp
    change affineLevel r a p = (e (E.symm p):ℝ)+1/2
    rwa [E.apply_symm_apply] at hp
  · rintro ⟨e,h⟩
    exact ⟨E.trans e,fun p => h (E p)⟩

def cutoffHeat (t : ExceptionalTime) (j : ℕ) (a v : ℝ) :=
  ∑' x : BalancedCutoff t j, Real.exp (-v*((x.val:ℝ)+a))

theorem cutoffHeat_eq (t : ExceptionalTime) (j : ℕ) (a v : ℝ) :
    cutoffHeat t j a v = singleHeat (clockRadix t j) a v :=
  (digits t j).tsum_eq (entry (clockRadix t j) a v)

theorem physical_heat_product (t : ExceptionalTime) (j : ℕ) (a : ℝ) (v : {u : ℝ // 0 < u}) :
    cutoffHeat t j a v.val*cutoffHeat t j a (((tailRadix t j).val:ℝ)*v.val) =
      kernel (clockRadix t j) a v.val := by
  rw [cutoffHeat_eq,cutoffHeat_eq]
  exact heat_product _ _ _

/-- A reflected pair of heat readings detects conservation on the entire one-copy pole set. -/
theorem reflected_heat_iff_isometry (t : ExceptionalTime) (j : ℕ) (a : BalancedShift.Shift)
    (v : {u : ℝ // 0 < u}) :
    kernel (clockRadix t j) a.val (-v.val) = -kernel (clockRadix t j) a.val v.val ↔
      ∀ s : {z : ℂ // -(3/2) < z.re ∧ meromorphicOrderAt (BalancedShift.extension t j a.val) z < 0},
        ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s.val f x :=
  (reflection_iff (clockRadix t j) a.val v).trans (BalancedShift.all_poles_isometric_iff_center t j a).symm

#print axioms pairIndex
#print axioms exact_levels_iff
#print axioms physical_heat_product
#print axioms reflected_heat_iff_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
