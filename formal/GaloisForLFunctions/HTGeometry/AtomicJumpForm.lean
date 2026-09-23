import Mathlib

/-!
# The atomic jump form of a translation pair

A symmetric translation pair is not arbitrary forcing: the finite-difference Dirichlet form

`J_h(u, φ) = ∫ (u(x+h) − u(x)) (φ(x+h) − φ(x)) dx`

equals `2⟨u, φ⟩ − ⟨u(·+h), φ⟩ − ⟨u(·−h), φ⟩`, so a symmetric pair of translations is a positive
atomic Dirichlet form minus twice the identity.  Against a one-Lipschitz increasing truncation the
form is coercive: `J_h(u, T u) ≥ J_h(T u, T u) ≥ 0`.  Both statements are proved here for
continuous compactly supported data, and the von Mangoldt weights `Λ(n)/√n` are nonnegative, so a
finite positive combination of translation pairs inherits the sign.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-! ## The jump form -/

/-- Finite-difference Dirichlet form at displacement `h`. -/
noncomputable def jumpForm (h : ℝ) (u φ : ℝ → ℝ) : ℝ :=
  ∫ x, (u (x + h) - u x) * (φ (x + h) - φ x)

/-- The `L²` pairing. -/
noncomputable def l2Pairing (u φ : ℝ → ℝ) : ℝ := ∫ x, u x * φ x

private theorem integrable_shift_mul {u φ : ℝ → ℝ} (hu : Continuous u) (hφ : Continuous φ)
    (hcu : HasCompactSupport u) (s t : ℝ) :
    Integrable (fun x => u (x + s) * φ (x + t)) := by
  have hcont : Continuous fun x : ℝ => u (x + s) * φ (x + t) :=
    ((hu.comp (continuous_id.add continuous_const)).mul
      (hφ.comp (continuous_id.add continuous_const)))
  refine hcont.integrable_of_hasCompactSupport ?_
  have h1 : HasCompactSupport fun x : ℝ => u (x + s) :=
    hcu.comp_homeomorph (Homeomorph.addRight s)
  exact h1.mul_right

private theorem integral_shift (f : ℝ → ℝ) (s : ℝ) : ∫ x, f (x + s) = ∫ x, f x :=
  integral_add_right_eq_self f s

/-- **Translation-pair identity.**  The jump form is twice the pairing minus the two shifted
pairings, so a symmetric translation pair is a positive atomic Dirichlet form minus twice the
identity. -/
theorem jumpForm_eq_two_pairing_sub {u φ : ℝ → ℝ} (hu : Continuous u) (hφ : Continuous φ)
    (hcu : HasCompactSupport u) (h : ℝ) :
    jumpForm h u φ =
      2 * l2Pairing u φ - l2Pairing (fun x => u (x + h)) φ - l2Pairing (fun x => u (x - h)) φ := by
  have e1 : Integrable (fun x => u (x + h) * φ (x + h)) :=
    integrable_shift_mul hu hφ hcu h h
  have e2 : Integrable (fun x => u (x + h) * φ (x + 0)) :=
    integrable_shift_mul hu hφ hcu h 0
  have e3 : Integrable (fun x => u (x + 0) * φ (x + h)) :=
    integrable_shift_mul hu hφ hcu 0 h
  have e4 : Integrable (fun x => u (x + 0) * φ (x + 0)) :=
    integrable_shift_mul hu hφ hcu 0 0
  simp only [add_zero] at e2 e3 e4
  have hsplit : jumpForm h u φ =
      (∫ x, u (x + h) * φ (x + h)) - (∫ x, u (x + h) * φ x) - (∫ x, u x * φ (x + h)) +
        ∫ x, u x * φ x := by
    have hcongr : ∀ x : ℝ, (u (x + h) - u x) * (φ (x + h) - φ x) =
        u (x + h) * φ (x + h) - u (x + h) * φ x - u x * φ (x + h) + u x * φ x :=
      fun x => by ring
    have e12 : Integrable (fun x => u (x + h) * φ (x + h) - u (x + h) * φ x) := e1.sub e2
    have e123 : Integrable
        (fun x => u (x + h) * φ (x + h) - u (x + h) * φ x - u x * φ (x + h)) := e12.sub e3
    rw [jumpForm, integral_congr_ae (Filter.Eventually.of_forall hcongr),
      integral_add e123 e4, integral_sub e12 e3, integral_sub e1 e2]
  have hshift : ∫ x, u (x + h) * φ (x + h) = ∫ x, u x * φ x := by
    have := integral_shift (fun y => u y * φ y) h
    simpa using this
  have hminus : ∫ x, u x * φ (x + h) = ∫ x, u (x - h) * φ x := by
    have := integral_shift (fun y => u (y - h) * φ y) h
    simpa using this
  rw [hsplit, hshift, hminus, l2Pairing, l2Pairing, l2Pairing]
  ring

/-! ## Truncation coercivity -/

/-- The one-Lipschitz increasing truncation `s ↦ (s − t)⁺`. -/
noncomputable def truncPos (t s : ℝ) : ℝ := max (s - t) 0

theorem truncPos_sub_le (t r s : ℝ) : |truncPos t r - truncPos t s| ≤ |r - s| := by
  simp only [truncPos]
  exact abs_max_sub_max_le_abs _ _ _ |>.trans (by rw [sub_sub_sub_cancel_right])

theorem truncPos_mono (t : ℝ) : Monotone (truncPos t) := fun _ _ h =>
  max_le_max (by linarith) le_rfl

/-- **Pointwise truncation inequality.**  An increasing one-Lipschitz truncation satisfies
`(r − s)(T r − T s) ≥ (T r − T s)²`. -/
theorem sub_mul_truncPos_sub_ge (t r s : ℝ) :
    (truncPos t r - truncPos t s) ^ (2 : ℕ) ≤ (r - s) * (truncPos t r - truncPos t s) := by
  rcases le_total s r with hrs | hrs
  · have hmono : truncPos t s ≤ truncPos t r := truncPos_mono t hrs
    have hlip : truncPos t r - truncPos t s ≤ r - s := by
      have := truncPos_sub_le t r s
      rw [abs_le] at this
      have h2 : |r - s| = r - s := abs_of_nonneg (by linarith)
      rw [h2] at this
      exact this.2
    nlinarith [sub_nonneg.mpr hmono]
  · have hmono : truncPos t r ≤ truncPos t s := truncPos_mono t hrs
    have hlip : truncPos t s - truncPos t r ≤ s - r := by
      have := truncPos_sub_le t s r
      rw [abs_le] at this
      have h2 : |s - r| = s - r := abs_of_nonneg (by linarith)
      rw [h2] at this
      exact this.2
    nlinarith [sub_nonneg.mpr hmono]

/-- The truncation of a compactly supported function is compactly supported, for a nonnegative
level. -/
theorem hasCompactSupport_truncPos {u : ℝ → ℝ} (hc : HasCompactSupport u) {t : ℝ} (ht : 0 ≤ t) :
    HasCompactSupport (truncPos t ∘ u) := by
  refine HasCompactSupport.intro hc fun x hx => ?_
  have hzero : u x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp [Function.comp, truncPos, hzero, neg_nonpos.mpr ht]

/-- **Truncation coercivity.**  Testing the jump form of `u` against its truncation dominates the
jump form of the truncation, which is itself nonnegative.  Both integrability facts are discharged
from continuity and compact support of `u`, not assumed. -/
theorem jumpForm_truncPos_ge {u : ℝ → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u)
    (h : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ jumpForm h (truncPos t ∘ u) (truncPos t ∘ u) ∧
      jumpForm h (truncPos t ∘ u) (truncPos t ∘ u) ≤
        jumpForm h u (truncPos t ∘ u) := by
  have hTcont : Continuous (truncPos t ∘ u) := by
    refine Continuous.comp ?_ hu
    unfold truncPos
    fun_prop
  have hTsupp : HasCompactSupport (truncPos t ∘ u) := hasCompactSupport_truncPos hcu ht
  have hself : Integrable fun x =>
      (truncPos t (u (x + h)) - truncPos t (u x)) * (truncPos t (u (x + h)) - truncPos t (u x)) := by
    have hcont : Continuous fun x : ℝ =>
        (truncPos t (u (x + h)) - truncPos t (u x)) * (truncPos t (u (x + h)) - truncPos t (u x)) :=
      ((hTcont.comp (continuous_id.add continuous_const)).sub hTcont).mul
        ((hTcont.comp (continuous_id.add continuous_const)).sub hTcont)
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro
      (hTsupp.union (hTsupp.comp_homeomorph (Homeomorph.addRight h))) fun x hx => ?_
    have h1 : truncPos t (u x) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := truncPos t ∘ u)
        fun hmem => hx (Set.mem_union_left _ hmem)
    have h2 : truncPos t (u (x + h)) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := (truncPos t ∘ u) ∘ (Homeomorph.addRight h))
        fun hmem => hx (Set.mem_union_right _ hmem)
    rw [h1, h2]
    ring
  have hcross : Integrable fun x =>
      (u (x + h) - u x) * (truncPos t (u (x + h)) - truncPos t (u x)) := by
    have hcont : Continuous fun x : ℝ =>
        (u (x + h) - u x) * (truncPos t (u (x + h)) - truncPos t (u x)) :=
      ((hu.comp (continuous_id.add continuous_const)).sub hu).mul
        ((hTcont.comp (continuous_id.add continuous_const)).sub hTcont)
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro
      (hcu.union (hcu.comp_homeomorph (Homeomorph.addRight h))) fun x hx => ?_
    have h1 : u x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem => hx (Set.mem_union_left _ hmem)
    have h2 : u (x + h) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := u ∘ (Homeomorph.addRight h))
        fun hmem => hx (Set.mem_union_right _ hmem)
    rw [h1, h2]
    ring
  have hself' : jumpForm h (truncPos t ∘ u) (truncPos t ∘ u) =
      ∫ x, (truncPos t (u (x + h)) - truncPos t (u x)) *
        (truncPos t (u (x + h)) - truncPos t (u x)) := rfl
  have hcross' : jumpForm h u (truncPos t ∘ u) =
      ∫ x, (u (x + h) - u x) * (truncPos t (u (x + h)) - truncPos t (u x)) := rfl
  constructor
  · rw [hself']
    exact integral_nonneg fun x => mul_self_nonneg _
  · rw [hself', hcross']
    refine integral_mono hself hcross fun x => ?_
    have hpt := sub_mul_truncPos_sub_ge t (u (x + h)) (u x)
    nlinarith [hpt]

/-! ## The source weights -/

/-- Suzuki's critical prime-pair weight `Λ(n)/√n`. -/
noncomputable def primePairWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n

theorem primePairWeight_nonneg (n : ℕ) : 0 ≤ primePairWeight n := by
  refine div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- **Positive atomic combination.**  A finite nonnegatively weighted sum of jump forms of a
truncation is nonnegative. -/
theorem sum_weighted_jumpForm_nonneg {ι : Type*} (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hstep : ι → ℝ) (v : ℝ → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ jumpForm (hstep i) v v) :
    0 ≤ ∑ i ∈ s, c i * jumpForm (hstep i) v v :=
  Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (hnn i hi)

/-- The von Mangoldt specialization of the previous statement. -/
theorem sum_primePairWeight_jumpForm_nonneg (s : Finset ℕ) (hstep : ℕ → ℝ) (v : ℝ → ℝ)
    (hnn : ∀ n ∈ s, 0 ≤ jumpForm (hstep n) v v) :
    0 ≤ ∑ n ∈ s, primePairWeight n * jumpForm (hstep n) v v :=
  sum_weighted_jumpForm_nonneg s primePairWeight (fun n _ => primePairWeight_nonneg n) hstep v hnn

end GaloisForLFunctions.HTGeometry
