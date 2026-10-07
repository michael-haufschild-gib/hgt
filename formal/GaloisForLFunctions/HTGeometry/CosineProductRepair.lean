import GaloisForLFunctions.HTGeometry.CosineBasepointRepair

/-!
# A product-divisor repair with a lattice-confined 1-fiber

Cancelling the origin in a Cayley transform of the reflected product divisor
preserves both reflections. Equality of the entire homogeneous coordinates,
including any common zero, is confined to `3ℤ`. The other two marked fibers are
not classified here.
-/

namespace GaloisForLFunctions.HTGeometry.CosineProductRepair

open Complex LabeledCosineDescent
open CosineBasepointRepair (divided divided_entire divided_mul divided_conj source_deriv_zero_ne source_zero)
open scoped ComplexConjugate

noncomputable section

def numerator (w : ℂ) : ℂ := divided w + divided (-w) - I * w * divided w * divided (-w)
def denominator (w : ℂ) : ℂ := divided w + divided (-w) + I * w * divided w * divided (-w)
def repair (w : ℂ) : ℂ := numerator w / denominator w

theorem scaled_coordinates (w : ℂ) :
    w * numerator w = source w - source (-w) + I * (source w - source 0) * (source (-w) - source 0) ∧
    w * denominator w = source w - source (-w) - I * (source w - source 0) * (source (-w) - source 0) := by
  have h₁ : source w = w * divided w + source 0 := by linear_combination -divided_mul w
  have h₂ : source (-w) = (-w) * divided (-w) + source 0 := by linear_combination -divided_mul (-w)
  rw [h₁, h₂]
  dsimp [numerator, denominator]
  constructor <;> ring

theorem numerator_entire : Differentiable ℂ numerator := by
  exact (divided_entire.add (divided_entire.comp (by fun_prop))).sub
    ((((differentiable_id.const_mul I).mul divided_entire).mul (divided_entire.comp (by fun_prop))))

theorem denominator_entire : Differentiable ℂ denominator := by
  exact (divided_entire.add (divided_entire.comp (by fun_prop))).add
    ((((differentiable_id.const_mul I).mul divided_entire).mul (divided_entire.comp (by fun_prop))))

theorem neg_coordinates (w : ℂ) : numerator (-w) = denominator w ∧
    denominator (-w) = numerator w := by
  simp only [numerator, denominator, neg_neg]
  constructor <;> ring

theorem conjugate_coordinates (w : ℂ) : numerator (conj w) = conj (denominator w) ∧
    denominator (conj w) = conj (numerator w) := by
  simp [numerator, denominator, ← map_neg, divided_conj]
  ring

theorem repair_reciprocal (w : ℂ) : repair (-w) = (repair w)⁻¹ := by
  simp [repair, (neg_coordinates w).1, (neg_coordinates w).2]

theorem repair_conjugate (w : ℂ) : repair (conj w) = (conj (repair w))⁻¹ := by
  simp [repair, (conjugate_coordinates w).1, (conjugate_coordinates w).2]

theorem divided_zero_ne : divided 0 ≠ 0 := by
  simpa [divided] using source_deriv_zero_ne

theorem denominator_zero_ne : denominator 0 ≠ 0 := by
  simpa [denominator, two_mul] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) divided_zero_ne

theorem repair_zero : repair 0 = 1 := by
  apply (div_eq_one_iff_eq denominator_zero_ne).mpr
  simp [numerator, denominator]

theorem repair_analyticAt_zero : AnalyticAt ℂ repair 0 :=
  (numerator_entire.analyticAt 0).div (denominator_entire.analyticAt 0) denominator_zero_ne

theorem source_zero_fiber_lattice {w : ℂ} (h : source w = source 0) :
    ∃ n : ℤ, w = 3 * n := by
  have hh : source w = fiberValue (1 + 6 * 0) := by
    simpa [source_zero, fiberValue] using h
  simpa using labeled_fiber 0 hh

theorem coordinates_equal_lattice {w : ℂ} (h : numerator w = denominator w) :
    ∃ n : ℤ, w = 3 * n := by
  have hp : (2 * I) * w * divided w * divided (-w) = 0 := by
    dsimp [numerator, denominator] at h
    linear_combination -h
  have hc : w = 0 ∨ divided w = 0 ∨ divided (-w) = 0 := by
    simpa only [mul_eq_zero, two_ne_zero, I_ne_zero, false_or, or_assoc] using hp
  rcases hc with rfl | hw | hw
  · exact ⟨0, by simp⟩
  · have hs := divided_mul w
    rw [hw, mul_zero] at hs
    exact source_zero_fiber_lattice (sub_eq_zero.mp hs.symm)
  · have hs := divided_mul (-w)
    rw [hw, mul_zero] at hs
    obtain ⟨n, hn⟩ := source_zero_fiber_lattice (sub_eq_zero.mp hs.symm)
    refine ⟨-n, ?_⟩
    push_cast
    linear_combination -hn

theorem one_fiber_lattice {w : ℂ} (h : repair w = 1) : ∃ n : ℤ, w = 3 * n := by
  by_cases hd : denominator w = 0
  · simp [repair, hd] at h
  · exact coordinates_equal_lattice ((div_eq_one_iff_eq hd).mp h)

theorem common_zero_lattice {w : ℂ} (hn : numerator w = 0) (hd : denominator w = 0) :
    ∃ n : ℤ, w = 3 * n := coordinates_equal_lattice (hn.trans hd.symm)

theorem off_real_coordinates_distinct {w : ℂ} (hw : w.im ≠ 0) : numerator w ≠ denominator w := by
  intro h
  obtain ⟨n, rfl⟩ := coordinates_equal_lattice h
  simp at hw

theorem off_real_not_one {w : ℂ} (hw : w.im ≠ 0) : repair w ≠ 1 := by
  intro h
  obtain ⟨n, rfl⟩ := one_fiber_lattice h
  simp at hw

theorem repair_hasDerivAt_zero : HasDerivAt repair (-I * deriv source 0) 0 := by
  have hb : HasDerivAt divided (deriv divided 0) (0 : ℂ) := (divided_entire 0).hasDerivAt
  have hneg : HasDerivAt (fun w : ℂ ↦ divided (-w)) (-(deriv divided 0)) 0 := by
    simpa only [Function.comp_def, neg_zero, mul_neg_one] using
      (divided_entire (-(0 : ℂ))).hasDerivAt.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  have hp : HasDerivAt (fun w : ℂ ↦ I * w * divided w * divided (-w))
      (I * divided 0 ^ 2) 0 := by
    convert! ((((hasDerivAt_id (0 : ℂ)).const_mul I).mul hb).mul hneg) using 1
    simp [pow_two, mul_assoc]
  have hn : HasDerivAt numerator (-I * divided 0 ^ 2) 0 := by
    convert! (hb.add hneg).sub hp using 1
    simp
  have hd : HasDerivAt denominator (I * divided 0 ^ 2) 0 := by
    convert! (hb.add hneg).add hp using 1
    simp
  have h := hn.div hd denominator_zero_ne
  convert! h using 1
  dsimp [numerator, denominator]
  have hb₀ := divided_zero_ne
  rw [show deriv source 0 = divided 0 by simp [divided]]
  field_simp [hb₀]
  ring_nf

theorem repair_deriv_zero_ne : deriv repair 0 ≠ 0 := by
  rw [repair_hasDerivAt_zero.deriv]
  exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) source_deriv_zero_ne

theorem product_repair_certificate :
    Differentiable ℂ numerator ∧ Differentiable ℂ denominator ∧
    denominator 0 ≠ 0 ∧ repair 0 = 1 ∧ AnalyticAt ℂ repair 0 ∧ deriv repair 0 ≠ 0 ∧
    (∀ w, repair (-w) = (repair w)⁻¹) ∧
    (∀ w, repair (conj w) = (conj (repair w))⁻¹) ∧
    (∀ w, numerator w = denominator w → ∃ n : ℤ, w = 3 * n) :=
  ⟨numerator_entire, denominator_entire, denominator_zero_ne, repair_zero,
    repair_analyticAt_zero, repair_deriv_zero_ne, repair_reciprocal, repair_conjugate,
    fun _ ↦ coordinates_equal_lattice⟩

end

end GaloisForLFunctions.HTGeometry.CosineProductRepair
