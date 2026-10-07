import GaloisForLFunctions.HTGeometry.LabeledCosineDescent
import GaloisForLFunctions.HTGeometry.TernaryLatticeCubic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Cube-root normalization of the nonperiodic cosine descent

The homogeneous coordinate pair retains poles. Its complete three distinguished
fibers are simple and separately labeled; conjugation exchanges the coordinates.
Translation periods are tested projectively, not through a chosen pole value.
-/

noncomputable section
open Complex Filter
open scoped Topology ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.LabeledCosineMobius

open LabeledCosineDescent
open TernaryLatticeCubic (omega omega_quadratic omega_cube omega_ne_one
  omega_sq_ne_one omega_ne_sq omega_conj)

def A : ℂ := labelValue 0
def B : ℂ := labelValue 1
def C : ℂ := labelValue 2

theorem A_ne_B : A ≠ B := fun h => (by intro he; have hh := congrArg Fin.val he; norm_num at hh : (0 : Fin 3) ≠ 1)
  (labelValue_injective h)
theorem A_ne_C : A ≠ C := fun h => (by intro he; have hh := congrArg Fin.val he; norm_num at hh : (0 : Fin 3) ≠ 2)
  (labelValue_injective h)
theorem B_ne_C : B ≠ C := fun h => (by intro he; have hh := congrArg Fin.val he; norm_num at hh : (1 : Fin 3) ≠ 2)
  (labelValue_injective h)

theorem labelValue_conj (j : Fin 3) : conj (labelValue j) = labelValue j := by
  simp [labelValue, fiberValue, ← cos_conj, map_ofNat]

def P (x : ℂ) : ℂ := (x - A) * (B - C)
def Q (x : ℂ) : ℂ := (x - C) * (B - A)
def numerator (x : ℂ) : ℂ := omega * P x + Q x
def denominator (x : ℂ) : ℂ := omega ^ 2 * P x + Q x
def mark : Fin 3 → ℂ := ![1, omega, omega ^ 2]
def coefficient : Fin 3 → ℂ :=
  ![(omega - omega ^ 2) * (B - C), (omega - 1) * (A - C),
    (1 - omega ^ 2) * (B - A)]
def N (w : ℂ) : ℂ := numerator (source w)
def D (w : ℂ) : ℂ := denominator (source w)
def latticeMap (w : ℂ) : ℂ := N w / D w

theorem omega_ne_zero : omega ≠ 0 := by
  intro h
  have hh := omega_cube
  norm_num [h] at hh

theorem mark_ne_zero (j : Fin 3) : mark j ≠ 0 := by
  fin_cases j <;> simp [mark, omega_ne_zero]

theorem coefficient_ne_zero (j : Fin 3) : coefficient j ≠ 0 := by
  fin_cases j <;> simp [coefficient, sub_ne_zero, omega_ne_sq, B_ne_C,
    omega_ne_one, A_ne_C, Ne.symm omega_sq_ne_one, Ne.symm A_ne_B]

theorem fiber_factor (j : Fin 3) (x : ℂ) :
    numerator x - mark j * denominator x = coefficient j * (x - labelValue j) := by
  have hfour : omega ^ 4 = omega := by
    linear_combination omega * omega_cube
  fin_cases j
  · dsimp [mark, coefficient, numerator, denominator, P, Q, A]
    ring
  · dsimp [mark, coefficient, numerator, denominator, P, Q, B]
    linear_combination -(x - A) * (labelValue 1 - C) * omega_cube
  · dsimp [mark, coefficient, numerator, denominator, P, Q, C]
    linear_combination -(x - A) * (B - labelValue 2) * hfour

theorem denominator_A : denominator A ≠ 0 := by
  simp [denominator, P, Q, sub_ne_zero, A_ne_C, Ne.symm A_ne_B]

theorem no_common_zero (x : ℂ) : ¬ (numerator x = 0 ∧ denominator x = 0) := by
  rintro ⟨hn, hd⟩
  have h := fiber_factor 0 x
  rw [hn, hd] at h
  have hx : x = A := by
    change x = labelValue 0
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp (by simpa only [mul_zero, sub_self] using h.symm)).resolve_left
      (coefficient_ne_zero 0)
  exact denominator_A (hx ▸ hd)

theorem D_ne_zero_of_fiber {j : Fin 3} {w : ℂ} (h : source w = labelValue j) : D w ≠ 0 := by
  intro hd
  have hf := fiber_factor j (source w)
  rw [show source w - labelValue j = 0 from sub_eq_zero.mpr h, mul_zero] at hf
  exact no_common_zero (source w) ⟨by
    change denominator (source w) = 0 at hd
    rw [hd, mul_zero, sub_zero] at hf
    exact hf, hd⟩

theorem latticeMap_fiber_iff (j : Fin 3) (w : ℂ) :
    latticeMap w = mark j ↔ source w = labelValue j := by
  by_cases hd : D w = 0
  · have hs : source w ≠ labelValue j := fun h => D_ne_zero_of_fiber h hd
    simp [latticeMap, hd, hs, Ne.symm (mark_ne_zero j)]
  · rw [latticeMap, div_eq_iff hd, ← sub_eq_zero]
    change numerator (source w) - mark j * denominator (source w) = 0 ↔ _
    rw [fiber_factor, mul_eq_zero]
    simp [coefficient_ne_zero, sub_eq_zero]

theorem numerator_entire : Differentiable ℂ N := by
  have hs := source_entire
  unfold N numerator P Q
  fun_prop

theorem denominator_entire : Differentiable ℂ D := by
  have hs := source_entire
  unfold D denominator P Q
  fun_prop

theorem latticeMap_meromorphic : ∀ w, MeromorphicAt latticeMap w := by
  intro w
  exact ((numerator_entire.analyticAt w).meromorphicAt).div
    (denominator_entire.analyticAt w).meromorphicAt

theorem conjugate_coordinates (w : ℂ) : N (conj w) = conj (D w) ∧
    D (conj w) = conj (N w) := by
  have ha : conj A = A := labelValue_conj 0
  have hb : conj B = B := labelValue_conj 1
  have hc : conj C = C := labelValue_conj 2
  have hfour : omega ^ 4 = omega := by linear_combination omega * omega_cube
  simp [N, D, numerator, denominator, P, Q, source_conj, ha, hb, hc,
    omega_conj, ← pow_mul, hfour]

theorem every_fiber_labeled_simple (j : Fin 3) {w : ℂ} (h : latticeMap w = mark j) :
    (∃ n : ℤ, w = (j : ℂ) + 3 * n) ∧
      analyticOrderAt (fun z => latticeMap z - mark j) w = 1 := by
  have hs := (latticeMap_fiber_iff j w).mp h
  refine ⟨labeled_fiber (j : ℤ) hs, ?_⟩
  have hd := D_ne_zero_of_fiber hs
  let u : ℂ → ℂ := fun z => coefficient j / D z
  have hu : AnalyticAt ℂ u w := analyticAt_const.div (denominator_entire.analyticAt w) hd
  have huo : analyticOrderAt u w = 0 := hu.analyticOrderAt_eq_zero.mpr
    (div_ne_zero (coefficient_ne_zero j) hd)
  have he : (fun z => latticeMap z - mark j) =ᶠ[𝓝 w]
      (fun z => source z - labelValue j) * u := by
    filter_upwards [(denominator_entire w).continuousAt.eventually_ne hd] with z hz
    have hf := fiber_factor j (source z)
    change N z - mark j * D z = coefficient j * (source z - labelValue j) at hf
    dsimp [latticeMap, u]
    field_simp
    linear_combination hf
  have ha : AnalyticAt ℂ (fun z => source z - labelValue j) w :=
    (source_entire.analyticAt w).sub analyticAt_const
  have hso : analyticOrderAt (fun z => source z - labelValue j) w = 1 :=
    labeled_fiber_simple (j : ℤ) hs
  rw [analyticOrderAt_congr he, analyticOrderAt_mul ha hu,
    hso, huo, add_zero]

theorem cross_difference (x y : ℂ) :
    numerator x * denominator y - numerator y * denominator x =
      (omega - omega ^ 2) * (B - C) * (B - A) * (A - C) * (x - y) := by
  dsimp [numerator, denominator, P, Q]
  ring

theorem projective_period_eq_zero {p : ℂ}
    (hper : ∀ w, N (w + p) * D w = N w * D (w + p)) : p = 0 := by
  apply source_period_eq_zero
  intro w
  have h := cross_difference (source (w + p)) (source w)
  change N (w + p) * D w - N w * D (w + p) = _ at h
  rw [hper, sub_self] at h
  have hk : (omega - omega ^ 2) * (B - C) * (B - A) * (A - C) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr omega_ne_sq)
      (sub_ne_zero.mpr B_ne_C)) (sub_ne_zero.mpr (Ne.symm A_ne_B)))
      (sub_ne_zero.mpr A_ne_C)
  exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hk)

theorem source_thirty : source 30 = labelValue 0 := by
  have hp : fiberPoint 1 1 = 30 := by norm_num [fiberPoint]
  simpa [hp, labelValue] using source_fiberPoint 1 1

theorem source_neg_thirty : source (-30) ≠ labelValue 0 := by
  intro h
  change source (-30) = fiberValue 1 at h
  obtain ⟨n, hn⟩ := (source_eq_fiberValue_iff (-30) 1).mp h
  have hc : (18 * (n : ℂ) + 1) ^ 2 = -359 := by
    dsimp [fiberPoint] at hn
    linear_combination -12 * hn
  have hi : (18 * n + 1) ^ 2 = (-359 : ℤ) := by exact_mod_cast hc
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let a : ZMod 7 := (18 * n + 1 : ℤ)
  have ha : a ^ 2 = (-359 : ZMod 7) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod 7)) hi
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_ofNat] using hh
  have hr : (-359 : ZMod 7) = 5 := by
    change ((-359 : ℤ) : ZMod 7) = ((5 : ℤ) : ZMod 7)
    exact (ZMod.intCast_eq_intCast_iff' (-359) 5 7).mpr (by norm_num)
  rw [hr] at ha
  have h125 : (5 : ZMod 7) ^ 3 = 6 := by
    calc
      _ = ((125 : ℕ) : ZMod 7) := by norm_num
      _ = _ := (ZMod.natCast_eq_natCast_iff' 125 6 7).mpr (by norm_num)
  have h5 : (5 : ZMod 7) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 5 7).not.mpr (by norm_num)
  have hf := ZMod.pow_card a
  have hg : a ^ 7 = 6 * a := by
    calc
      _ = a * (a ^ 2) ^ 3 := by ring
      _ = _ := by rw [ha, h125]; ring
  have hz : (5 : ZMod 7) * a = 0 := by linear_combination hf - hg
  have ha0 : a = 0 := (mul_eq_zero.mp hz).resolve_left h5
  exact h5 (by simpa only [ha0, zero_pow (by norm_num : 2 ≠ 0)] using ha.symm)

theorem not_reciprocal_coordinates :
    ¬ ∀ w, N (-w) * N w = D (-w) * D w := by
  intro h
  have hd := D_ne_zero_of_fiber source_thirty
  have h30 : N 30 = D 30 := by
    have hf := fiber_factor 0 (source 30)
    rw [source_thirty, sub_self, mul_zero] at hf
    simpa [N, D, mark, source_thirty] using sub_eq_zero.mp hf
  have he : N (-30) = D (-30) := by
    have hh := h 30
    rw [h30] at hh
    exact mul_right_cancel₀ hd hh
  have hf := fiber_factor 0 (source (-30))
  change N (-30) - mark 0 * D (-30) = _ at hf
  simp only [mark, Matrix.cons_val_zero, one_mul, he, sub_self] at hf
  exact source_neg_thirty (sub_eq_zero.mp
    ((mul_eq_zero.mp hf.symm).resolve_left (coefficient_ne_zero 0)))

/-- The exact cube-root model retains complete fibers, simple orders and real structure,
but has neither a nonzero projective period nor reciprocal reflection. -/
theorem nonperiodic_cube_root_model :
    Differentiable ℂ N ∧ Differentiable ℂ D ∧
    (∀ w, ¬ (N w = 0 ∧ D w = 0)) ∧
    (∀ w, N (conj w) = conj (D w) ∧ D (conj w) = conj (N w)) ∧
    (∀ j w, latticeMap w = mark j →
      (∃ n : ℤ, w = (j : ℂ) + 3 * n) ∧
        analyticOrderAt (fun z => latticeMap z - mark j) w = 1) ∧
    (∀ p, (∀ w, N (w + p) * D w = N w * D (w + p)) → p = 0) ∧
    (∃ q : ℤ → ℂ, Function.Injective q ∧ ∀ n, latticeMap (q n) = 1) ∧
    (¬ ∀ w, N (-w) * N w = D (-w) * D w) := by
  refine ⟨numerator_entire, denominator_entire, fun w => no_common_zero (source w),
    conjugate_coordinates, fun j _ => every_fiber_labeled_simple j,
    fun _ => projective_period_eq_zero, ?_, not_reciprocal_coordinates⟩
  refine ⟨fiberPoint 1, first_fiber_injective, fun n => ?_⟩
  change latticeMap (fiberPoint 1 n) = mark 0
  rw [latticeMap_fiber_iff]
  simpa [labelValue] using source_fiberPoint 1 n

end GaloisForLFunctions.HTGeometry.LabeledCosineMobius
