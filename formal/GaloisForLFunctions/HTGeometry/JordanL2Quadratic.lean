import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-!
# Signed quadratic forms on the total-variation Hilbert space

The measurable Jordan sign acts as a bounded multiplier on `L²(P+N)`.
Its energy and bilinear pairings are exactly the differences of the
corresponding integrals against the mutually singular measures `P,N`.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [MeasurableSpace X] {P N : Measure X}

/-- The sign of a mutually singular difference, relative to its total variation. -/
def jordanSign (h : P ⟂ₘ N) : X → ℂ := by
  classical
  exact fun x => if x ∈ h.nullSet then -1 else 1

theorem measurable_jordanSign (h : P ⟂ₘ N) : Measurable (jordanSign h) := by
  classical
  exact measurable_const.piecewise h.measurableSet_nullSet measurable_const

theorem norm_jordanSign (h : P ⟂ₘ N) (x : X) : ‖jordanSign h x‖ = 1 := by
  classical
  by_cases hx : x ∈ h.nullSet <;> simp only [jordanSign, hx, if_true, if_false, norm_neg, norm_one]

theorem conj_jordanSign (h : P ⟂ₘ N) (x : X) : conj (jordanSign h x) = jordanSign h x := by
  classical
  by_cases hx : x ∈ h.nullSet <;> simp only [jordanSign, hx, if_true, if_false, map_neg, map_one]

theorem jordanSign_eq_one_ae (h : P ⟂ₘ N) : jordanSign h =ᵐ[P] fun _ => 1 := by
  classical
  have hs : ∀ᵐ x ∂P, x ∉ h.nullSet := by
    simpa only [ae_iff, not_not, Set.setOf_mem_eq] using h.measure_nullSet
  filter_upwards [hs] with x hx
  simp only [jordanSign, if_neg hx]

theorem jordanSign_eq_neg_one_ae (h : P ⟂ₘ N) : jordanSign h =ᵐ[N] fun _ => -1 := by
  classical
  have hs : ∀ᵐ x ∂N, x ∈ h.nullSet := ae_iff.mpr h.measure_compl_nullSet
  filter_upwards [hs] with x hx
  simp only [jordanSign, if_pos hx]

/-- Multiplication by the Jordan sign on the total-variation Hilbert space. -/
def jordanSignMul (h : P ⟂ₘ N) : Lp ℂ 2 (P + N) →L[ℂ] Lp ℂ 2 (P + N) :=
  lpBoundedMulCLM (measurable_jordanSign h) zero_le_one (fun x => (norm_jordanSign h x).le)

theorem jordanSignMul_coeFn (h : P ⟂ₘ N) (u : Lp ℂ 2 (P + N)) :
    (jordanSignMul h u : X → ℂ) =ᵐ[P + N] fun x => jordanSign h x * u x :=
  lpBoundedMulCLM_coeFn (measurable_jordanSign h) zero_le_one
    (fun x => (norm_jordanSign h x).le) u

/-- The sign multiplier recovers the signed squared norm. -/
theorem jordanSignMul_energy (h : P ⟂ₘ N) {f : X → ℂ} (hf : MemLp f 2 (P + N)) :
    (inner ℂ (jordanSignMul h (hf.toLp f)) (hf.toLp f)).re =
      (∫ x, ‖f x‖ ^ 2 ∂P) - ∫ x, ‖f x‖ ^ 2 ∂N := by
  let u := hf.toLp f
  have hae : (fun x => inner ℂ ((jordanSignMul h u) x) (u x)) =ᵐ[P + N]
      fun x => jordanSign h x * ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [jordanSignMul_coeFn h u, hf.coeFn_toLp] with x hx hfx
    rw [RCLike.inner_apply', hx, hfx, map_mul, conj_jordanSign, mul_assoc, Complex.conj_mul']
    push_cast
    rfl
  have hi := (L2.integrable_inner (jordanSignMul h u) u).congr hae
  have hip := (integrable_add_measure.mp hi).1
  have hin := (integrable_add_measure.mp hi).2
  have he : inner ℂ (jordanSignMul h u) u =
      ((∫ x, ‖f x‖ ^ 2 ∂P : ℝ) : ℂ) - ((∫ x, ‖f x‖ ^ 2 ∂N : ℝ) : ℂ) := by
    rw [L2.inner_def, integral_congr_ae hae, integral_add_measure hip hin]
    have hp : (∫ x, jordanSign h x * ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂P) =
        ∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂P :=
      integral_congr_ae ((jordanSign_eq_one_ae h).mono fun x hx => by dsimp only at hx ⊢; rw [hx, one_mul])
    have hn : (∫ x, jordanSign h x * ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂N) =
        ∫ x, -((‖f x‖ ^ 2 : ℝ) : ℂ) ∂N :=
      integral_congr_ae ((jordanSign_eq_neg_one_ae h).mono fun x hx => by dsimp only at hx ⊢; rw [hx, neg_one_mul])
    rw [hp, hn, integral_neg, integral_complex_ofReal, integral_complex_ofReal, sub_eq_add_neg]
  simpa only [Complex.sub_re, Complex.ofReal_re] using congrArg Complex.re he

/-- Bilinear pairing with a signed density is the difference of its two integrals. -/
theorem jordanSignMul_pairing (h : P ⟂ₘ N) {q f : X → ℂ}
    (hq : MemLp q 2 (P + N)) (hf : MemLp f 2 (P + N)) :
    _root_.HTGeometry.complexMulBilinear.lpPairing (P + N) 2 2
        (jordanSignMul h (hq.toLp q)) (hf.toLp f) =
      (∫ x, q x * f x ∂P) - ∫ x, q x * f x ∂N := by
  let u := hq.toLp q
  let v := hf.toLp f
  have hae : (fun x => (jordanSignMul h u) x * v x) =ᵐ[P + N]
      fun x => jordanSign h x * (q x * f x) := by
    filter_upwards [jordanSignMul_coeFn h u, hq.coeFn_toLp, hf.coeFn_toLp]
      with x hx hqx hfx
    rw [hx, hqx, hfx, mul_assoc]
  have hi := ((Lp.memLp (jordanSignMul h u)).integrable_mul (Lp.memLp v)).congr hae
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  change (∫ x, (jordanSignMul h u) x * v x ∂(P + N)) = _
  rw [integral_congr_ae hae, integral_add_measure (integrable_add_measure.mp hi).1
    (integrable_add_measure.mp hi).2]
  have hp : (∫ x, jordanSign h x * (q x * f x) ∂P) = ∫ x, q x * f x ∂P :=
    integral_congr_ae ((jordanSign_eq_one_ae h).mono fun x hx => by dsimp only at hx ⊢; rw [hx, one_mul])
  have hn : (∫ x, jordanSign h x * (q x * f x) ∂N) = ∫ x, -(q x * f x) ∂N :=
    integral_congr_ae ((jordanSign_eq_neg_one_ae h).mono fun x hx => by dsimp only at hx ⊢; rw [hx, neg_one_mul])
  rw [hp, hn, integral_neg, sub_eq_add_neg]

end

end GaloisForLFunctions.HTGeometry
