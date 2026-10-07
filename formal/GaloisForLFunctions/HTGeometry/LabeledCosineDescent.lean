import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-!
# A cosine descending through a quadratic branched cover

This leaf starts the exact nonperiodic labeled-fiber counterexample recorded in
`labeled-lattice-section-periodicity.md`. Cosine is invariant under the deck
involution of the square map, so its descent is entire, including the branch point.
No growth estimate or counting estimate is used.
-/

noncomputable section
open Complex Filter
open scoped Topology ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.LabeledCosineDescent

def descendedCos (z : ℂ) : ℂ := Complex.cos (Complex.sqrt z)

theorem sqrt_square (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  exact Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)

theorem descendedCos_of_square {z u : ℂ} (hu : u ^ 2 = z) :
    descendedCos z = Complex.cos u := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((sqrt_square z).trans hu.symm) with h | h
  · simp [descendedCos, h]
  · simp [descendedCos, h]

theorem descendedCos_square (u : ℂ) : descendedCos (u ^ 2) = Complex.cos u :=
  descendedCos_of_square rfl

theorem descendedCos_conj (z : ℂ) : descendedCos (conj z) = conj (descendedCos z) := by
  have hs : (conj (Complex.sqrt z)) ^ 2 = conj z := by
    rw [← map_pow, sqrt_square]
  rw [descendedCos_of_square hs, Complex.cos_conj]
  rfl

theorem descendedCos_rotated (z : ℂ) :
    descendedCos z = Complex.cos (Complex.I * Complex.sqrt (-z)) := by
  apply descendedCos_of_square
  rw [mul_pow, Complex.I_sq, sqrt_square]
  ring

theorem descendedCos_differentiableAt_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ descendedCos z := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with h | h
  · exact Complex.differentiable_cos.differentiableAt.comp z
      (Complex.differentiableAt_sqrt h)
  · have heq : descendedCos = fun w : ℂ =>
        Complex.cos (Complex.I * Complex.sqrt (-w)) := funext descendedCos_rotated
    rw [heq]
    exact Complex.differentiable_cos.differentiableAt.comp z
      (((Complex.differentiableAt_sqrt h).comp z (by fun_prop)).const_mul _)

theorem descendedCos_entire : Differentiable ℂ descendedCos := by
  intro z
  by_cases hz : z = 0
  · subst z
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (f := descendedCos) ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact descendedCos_differentiableAt_of_ne_zero hw
    · exact Complex.continuous_cos.continuousAt.comp
        (Complex.continuousAt_sqrt (Or.inl (by simp)))
  · exact descendedCos_differentiableAt_of_ne_zero hz

def source (w : ℂ) : ℂ :=
  descendedCos ((2 * (Real.pi : ℂ)) ^ 2 * ((w + 1 / 12) / 27))

theorem source_entire : Differentiable ℂ source := by
  exact descendedCos_entire.comp (by fun_prop)

theorem source_conj (z : ℂ) : source (conj z) = conj (source z) := by
  dsimp [source]
  rw [← descendedCos_conj]
  congr 1
  simp [map_ofNat]

def fiberValue (k : ℤ) : ℂ := Complex.cos ((Real.pi : ℂ) * k / 9)

def fiberPoint (k n : ℤ) : ℂ := (((18 * (n : ℂ) + k) ^ 2 - 1) / 12)

theorem source_fiberPoint (k n : ℤ) : source (fiberPoint k n) = fiberValue k := by
  have hs : ((Real.pi : ℂ) * (18 * n + k) / 9) ^ 2 =
      (2 * (Real.pi : ℂ)) ^ 2 * ((fiberPoint k n + 1 / 12) / 27) := by
    unfold fiberPoint
    ring
  rw [source, descendedCos_of_square hs]
  apply Complex.cos_eq_cos_iff.mpr
  refine ⟨-n, Or.inl ?_⟩
  push_cast
  ring

theorem source_eq_fiberValue_iff (w : ℂ) (k : ℤ) :
    source w = fiberValue k ↔ ∃ n : ℤ, w = fiberPoint k n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.cos_eq_cos_iff.mp h
    let Z : ℂ := (2 * (Real.pi : ℂ)) ^ 2 * ((w + 1 / 12) / 27)
    have hs : Z = ((Real.pi : ℂ) * k / 9 - 2 * n * Real.pi) ^ 2 := by
      rw [← sqrt_square Z]
      rcases hn with hn | hn
      · have he : Complex.sqrt Z = (Real.pi : ℂ) * k / 9 - 2 * n * Real.pi := by
          change (Real.pi : ℂ) * k / 9 = 2 * n * Real.pi + Complex.sqrt Z at hn
          linear_combination -hn
        rw [he]
      · have he : Complex.sqrt Z = -((Real.pi : ℂ) * k / 9 - 2 * n * Real.pi) := by
          change (Real.pi : ℂ) * k / 9 = 2 * n * Real.pi - Complex.sqrt Z at hn
          linear_combination hn
        rw [he, neg_sq]
    refine ⟨-n, ?_⟩
    have hp : (Real.pi : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
    apply mul_left_cancel₀ hp
    dsimp [Z] at hs
    unfold fiberPoint
    push_cast
    linear_combination (27 / 4 : ℂ) * hs
  · rintro ⟨n, rfl⟩
    exact source_fiberPoint k n

theorem labeled_fiber (j : ℤ) {w : ℂ} (h : source w = fiberValue (1 + 6 * j)) :
    ∃ n : ℤ, w = j + 3 * n := by
  obtain ⟨n, rfl⟩ := (source_eq_fiberValue_iff w (1 + 6 * j)).mp h
  refine ⟨9 * n ^ 2 + (1 + 6 * j) * n + j ^ 2, ?_⟩
  unfold fiberPoint
  push_cast
  ring

def squareCoordinate (u : ℂ) : ℂ := 27 * u ^ 2 / (4 * (Real.pi : ℂ) ^ 2) - 1 / 12

theorem source_squareCoordinate (u : ℂ) : source (squareCoordinate u) = Complex.cos u := by
  apply descendedCos_of_square
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  dsimp [squareCoordinate]
  field_simp
  ring

theorem source_jet_identity (k n : ℤ) :
    deriv source (fiberPoint k n) * (18 * n + k) =
      -(2 * (Real.pi : ℂ) / 3) * Complex.sin (Real.pi * k / 9) := by
  let u : ℂ := Real.pi * (18 * n + k) / 9
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : squareCoordinate u = fiberPoint k n := by
    dsimp [squareCoordinate, u, fiberPoint]
    field_simp
    ring
  have hg := (((hasDerivAt_id u).pow 2).const_mul 27 |>.div_const
    (4 * (Real.pi : ℂ) ^ 2) |>.sub_const (1 / 12))
  have hg' : HasDerivAt squareCoordinate (54 * u / (4 * (Real.pi : ℂ) ^ 2)) u := by
    apply hg.congr_deriv
    dsimp
    ring
  have hd := ((source_entire (squareCoordinate u)).hasDerivAt).comp u hg'
  have heq : source ∘ squareCoordinate = Complex.cos := funext source_squareCoordinate
  rw [heq] at hd
  have hdv := hd.unique (Complex.hasDerivAt_cos u)
  have hs : Complex.sin u = Complex.sin (Real.pi * k / 9) := by
    convert Complex.sin_add_int_mul_two_pi (Real.pi * k / 9 : ℂ) n using 1
    congr 1
    dsimp [u]
    ring
  rw [he, hs] at hdv
  calc
    _ = (2 * (Real.pi : ℂ) / 3) *
        (deriv source (fiberPoint k n) * (54 * u / (4 * (Real.pi : ℂ) ^ 2))) := by
      dsimp [u]
      field_simp
      ring
    _ = _ := by rw [hdv]; ring

theorem source_deriv_ne_zero (j n : ℤ) : deriv source (fiberPoint (1 + 6 * j) n) ≠ 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hdv := source_jet_identity (1 + 6 * j) n
  intro hz
  rw [hz, zero_mul] at hdv
  have hs : Complex.sin (Real.pi * (1 + 6 * j) / 9 : ℂ) = 0 := by
    simpa only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_ofNat] using
      (mul_eq_zero.mp hdv.symm).resolve_left (neg_ne_zero.mpr
        (div_ne_zero (mul_ne_zero (by norm_num) hp) (by norm_num)))
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp hs
  have hc : (1 + 6 * (j : ℂ)) = 9 * m := by
    apply mul_left_cancel₀ hp
    linear_combination 9 * hm
  have hi : 1 + 6 * j = 9 * m := by exact_mod_cast hc
  omega

theorem labeled_fiber_simple (j : ℤ) {w : ℂ} (h : source w = fiberValue (1 + 6 * j)) :
    analyticOrderAt (fun z => source z - fiberValue (1 + 6 * j)) w = 1 := by
  obtain ⟨n, rfl⟩ := (source_eq_fiberValue_iff w (1 + 6 * j)).mp h
  apply ((source_entire.analyticAt _).sub analyticAt_const).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · exact sub_eq_zero.mpr h
  · change deriv (fun z => source z - fiberValue (1 + 6 * j)) _ ≠ 0
    rw [deriv_sub_const]
    exact source_deriv_ne_zero j n

theorem source_period_eq_zero {p : ℂ} (hper : Function.Periodic source p) : p = 0 := by
  have hf0 : fiberPoint 1 0 = 0 := by norm_num [fiberPoint]
  have hs0 : source 0 = fiberValue 1 := by simpa [hf0] using source_fiberPoint 1 0
  have hp : source p = fiberValue 1 := by simpa [hs0] using hper 0
  obtain ⟨n, hn⟩ := (source_eq_fiberValue_iff p 1).mp hp
  have hd := ((source_entire (0 + p)).hasDerivAt).comp 0 ((hasDerivAt_id (0 : ℂ)).add_const p)
  have heq : (fun z => source (z + p)) = source := funext hper
  change HasDerivAt (fun z => source (z + p)) (deriv source (0 + p) * 1) 0 at hd
  simp only [zero_add, mul_one] at hd
  rw [heq] at hd
  have hv := hd.unique ((source_entire 0).hasDerivAt)
  have hj := source_jet_identity 1 n
  have hj0 := source_jet_identity 1 0
  simp only [Int.cast_zero, mul_zero, zero_add, Int.cast_one, mul_one, hf0] at hj0
  rw [← hn, hv] at hj
  simp only [Int.cast_one, mul_one] at hj
  have hd0 : deriv source 0 ≠ 0 := by simpa [hf0] using source_deriv_ne_zero 0 0
  have hm : 18 * (n : ℂ) + 1 = 1 := by
    apply mul_left_cancel₀ hd0
    linear_combination hj - hj0
  have hn0 : n = 0 := by
    have hc : (n : ℂ) = 0 := by linear_combination (1 / 18 : ℂ) * hm
    exact_mod_cast hc
  simpa [hn0, hf0] using hn

theorem first_fiber_injective : Function.Injective (fiberPoint 1) := by
  intro n m h
  have hs : (18 * (n : ℂ) + 1) ^ 2 = (18 * (m : ℂ) + 1) ^ 2 := by
    dsimp [fiberPoint] at h
    linear_combination 12 * h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
  · have hc : (n : ℂ) = m := by linear_combination (1 / 18 : ℂ) * he
    exact_mod_cast hc
  · have hi : 18 * n + 1 = -(18 * m + 1) := by exact_mod_cast he
    omega

def labelValue (j : Fin 3) : ℂ := fiberValue (1 + 6 * (j : ℤ))

theorem labelValue_injective : Function.Injective labelValue := by
  intro j l h
  have hj := source_fiberPoint (1 + 6 * (j : ℤ)) 0
  change source _ = labelValue j at hj
  rw [h] at hj
  obtain ⟨n, hn⟩ := labeled_fiber (l : ℤ) hj
  have he : fiberPoint (1 + 6 * (j : ℤ)) 0 = (j : ℂ) + 3 * (j : ℂ) ^ 2 := by
    dsimp [fiberPoint]
    push_cast
    ring
  rw [he] at hn
  have hi : (j : ℤ) + 3 * (j : ℤ) ^ 2 = (l : ℤ) + 3 * n := by exact_mod_cast hn
  have hjlt := j.isLt
  have hllt := l.isLt
  apply Fin.ext
  omega

/-- Complete simple fibers with separate integer labels do not force periodicity. -/
theorem exists_entire_nonperiodic_labeled_fibers :
    ∃ (f : ℂ → ℂ) (a : Fin 3 → ℂ), Differentiable ℂ f ∧ Function.Injective a ∧
      (∀ j w, f w = a j → (∃ n : ℤ, w = (j : ℂ) + 3 * n) ∧
        analyticOrderAt (fun z => f z - a j) w = 1) ∧
      (∀ p, Function.Periodic f p → p = 0) ∧
      (∃ q : ℤ → ℂ, Function.Injective q ∧ ∀ n, f (q n) = a 0) := by
  refine ⟨source, labelValue, source_entire, labelValue_injective, ?_,
    fun _ => source_period_eq_zero, fiberPoint 1, first_fiber_injective, ?_⟩
  · intro j w hw
    exact ⟨labeled_fiber (j : ℤ) hw, labeled_fiber_simple (j : ℤ) hw⟩
  · intro n
    simpa [labelValue] using source_fiberPoint 1 n

end GaloisForLFunctions.HTGeometry.LabeledCosineDescent
