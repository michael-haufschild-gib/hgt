import GaloisForLFunctions.HTGeometry.DiscRootMultiset
import GaloisForLFunctions.HTGeometry.MultisetNewtonSolve
import GaloisForLFunctions.HTGeometry.WeierstrassParamLogDeriv

/-!
# Symmetric functions of the roots of a slice are holomorphic in the parameters

For a function of several complex variables whose slices in the distinguished variable do not
vanish on a fixed circle, the roots inside that circle form a multiset depending on the remaining
variables.  Its power sums are contour integrals, hence holomorphic; Newton's identity, solved for
the elementary symmetric function, then propagates holomorphy from the power sums to every
elementary symmetric function of the moving root multiset.

The elementary symmetric functions are the coefficients of the monic polynomial vanishing exactly
at the roots of the slice, so this is the holomorphy statement behind Weierstrass' preparation
theorem.

* `HTGeometry.SliceAdmissible`, `HTGeometry.sliceRoots`, `HTGeometry.sliceMoment`;
* `HTGeometry.sliceMoment_eq_powerSum`;
* `HTGeometry.differentiableOn_sliceMoment`;
* `HTGeometry.differentiableOn_esymm_sliceRoots`.
-/

open Complex Metric
open scoped Real Topology

namespace HTGeometry

variable {n : ℕ}

/-- Consing a first coordinate is continuous. -/
theorem continuous_consFirst (y : Fin n → ℂ) :
    Continuous fun z : ℂ => (Fin.cons z y : Fin (n + 1) → ℂ) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero => simpa using continuous_id'
  | succ j => simpa using continuous_const

/-- The slice of a function of several variables in the distinguished variable admits the disc of
radius `t`: the slice is holomorphic on a neighbourhood of the closed disc and does not vanish on
the bounding circle. -/
def SliceAdmissible (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (y : Fin n → ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ closedBall (0 : ℂ) t ⊆ U ∧
    DifferentiableOn ℂ (fun z => f (Fin.cons z y)) U ∧
    ∀ ζ ∈ sphere (0 : ℂ) t, f (Fin.cons ζ y) ≠ 0

open Classical in
/-- The multiset of roots of a slice inside the circle of radius `t`. -/
noncomputable def sliceRoots (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (y : Fin n → ℂ) : Multiset ℂ :=
  if h : 0 < t ∧ SliceAdmissible f t y then
    Classical.choose (exists_rootMultiset h.1 (Classical.choose_spec h.2).1
      (Classical.choose_spec h.2).2.1 (Classical.choose_spec h.2).2.2.1
      (Classical.choose_spec h.2).2.2.2)
  else 0

/-- The `p`-th moment of the logarithmic derivative of a slice along the circle of radius `t`. -/
noncomputable def sliceMoment (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (p : ℕ) (y : Fin n → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∮ ζ in C(0, t), ζ ^ p * logDeriv (fun z => f (Fin.cons z y)) ζ

/-- **The roots of a slice lie strictly inside the circle.** -/
theorem sliceRoots_norm_lt {f : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℂ} (hy : SliceAdmissible f t y) : ∀ u ∈ sliceRoots f t y, ‖u‖ < t := by
  have hpos : 0 < t ∧ SliceAdmissible f t y := ⟨ht, hy⟩
  have hspec := Classical.choose_spec (exists_rootMultiset hpos.1
    (Classical.choose_spec hpos.2).1 (Classical.choose_spec hpos.2).2.1
    (Classical.choose_spec hpos.2).2.2.1 (Classical.choose_spec hpos.2).2.2.2)
  have hroots : sliceRoots f t y = Classical.choose (exists_rootMultiset hpos.1
      (Classical.choose_spec hpos.2).1 (Classical.choose_spec hpos.2).2.1
      (Classical.choose_spec hpos.2).2.2.1 (Classical.choose_spec hpos.2).2.2.2) := by
    rw [sliceRoots, dif_pos hpos]
  rw [hroots]
  exact hspec.1

/-- **The moments are the power sums of the roots.** -/
theorem sliceMoment_eq_powerSum {f : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℂ} (hy : SliceAdmissible f t y) (p : ℕ) :
    sliceMoment f t p y = ((sliceRoots f t y).map (fun x => x ^ p)).sum := by
  have hpos : 0 < t ∧ SliceAdmissible f t y := ⟨ht, hy⟩
  have hspec := Classical.choose_spec (exists_rootMultiset hpos.1
    (Classical.choose_spec hpos.2).1 (Classical.choose_spec hpos.2).2.1
    (Classical.choose_spec hpos.2).2.2.1 (Classical.choose_spec hpos.2).2.2.2)
  have hroots : sliceRoots f t y = Classical.choose (exists_rootMultiset hpos.1
      (Classical.choose_spec hpos.2).1 (Classical.choose_spec hpos.2).2.1
      (Classical.choose_spec hpos.2).2.2.1 (Classical.choose_spec hpos.2).2.2.2) := by
    rw [sliceRoots, dif_pos hpos]
  rw [hroots, sliceMoment, hspec.2 p]
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp

/-- **The moments are holomorphic in the remaining variables.** -/
theorem differentiableOn_sliceMoment {f : (Fin (n + 1) → ℂ) → ℂ} {U : Set (Fin (n + 1) → ℂ)}
    {V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0) (p : ℕ) :
    DifferentiableOn ℂ (sliceMoment f t p) V := by
  have hcirc : ∀ (θ : ℝ) (y : Fin n → ℂ), ‖circleMap 0 t θ‖ = t := by
    intro θ _
    simpa using abs_of_pos ht
  have hmemU : ∀ (θ : ℝ) (y : Fin n → ℂ), y ∈ V →
      (Fin.cons (circleMap 0 t θ) y : Fin (n + 1) → ℂ) ∈ U :=
    fun θ y hy => hdisc y hy _ (le_of_eq (hcirc θ y))
  have hne : ∀ (θ : ℝ) (y : Fin n → ℂ), y ∈ V → f (Fin.cons (circleMap 0 t θ) y) ≠ 0 :=
    fun θ y hy => hnez y hy _ (hcirc θ y)
  intro y hy
  have hmoment : DifferentiableAt ℂ (fun w : Fin n → ℂ =>
      ∮ ζ in C(0, t), ζ ^ p • (partialFirst f (Fin.cons ζ w) / f (Fin.cons ζ w))) y :=
    differentiableAt_logDerivMoment hU hV hf ht hmemU hne p hy
  have hcongr : ∀ w ∈ V, (fun w : Fin n → ℂ =>
      ∮ ζ in C(0, t), ζ ^ p • (partialFirst f (Fin.cons ζ w) / f (Fin.cons ζ w))) w
      = (2 * (Real.pi : ℂ) * Complex.I) * sliceMoment f t p w := by
    intro w hw
    have hslice : ∀ ζ ∈ sphere (0 : ℂ) t,
        ζ ^ p • (partialFirst f (Fin.cons ζ w) / f (Fin.cons ζ w))
          = ζ ^ p * logDeriv (fun z => f (Fin.cons z w)) ζ := by
      intro ζ hζ
      have hζt : ‖ζ‖ = t := by simpa using mem_sphere_iff_norm.1 hζ
      have hmem : (Fin.cons ζ w : Fin (n + 1) → ℂ) ∈ U := hdisc w hw ζ (le_of_eq hζt)
      rw [logDeriv_apply, deriv_cons_slice hU hf hmem, smul_eq_mul]
    show (∮ ζ in C(0, t), ζ ^ p • (partialFirst f (Fin.cons ζ w) / f (Fin.cons ζ w)))
      = (2 * (Real.pi : ℂ) * Complex.I) * sliceMoment f t p w
    rw [circleIntegral.integral_congr ht.le hslice, sliceMoment]
    have hne0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp
  have hscaled : DifferentiableAt ℂ
      (fun w : Fin n → ℂ => (2 * (Real.pi : ℂ) * Complex.I) * sliceMoment f t p w) y := by
    refine hmoment.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem (hV.mem_nhds hy) fun w hw => (hcongr w hw).symm
  have hne0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have := (hscaled.const_mul (2 * (Real.pi : ℂ) * Complex.I)⁻¹)
  refine (DifferentiableAt.congr_of_eventuallyEq this ?_).differentiableWithinAt
  refine Filter.Eventually.of_forall fun w => ?_
  field_simp

/-- **Every elementary symmetric function of the moving root multiset is holomorphic.**  Newton's
identity solved for the elementary symmetric function expresses it in the power sums, which are the
moments, and in the lower elementary symmetric functions. -/
theorem differentiableOn_esymm_sliceRoots {f : (Fin (n + 1) → ℂ) → ℂ} {U : Set (Fin (n + 1) → ℂ)}
    {V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0)
    (hadm : ∀ y ∈ V, SliceAdmissible f t y) (j : ℕ) :
    DifferentiableOn ℂ (fun y => (sliceRoots f t y).esymm j) V := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have : (fun y : Fin n → ℂ => (sliceRoots f t y).esymm 0) = fun _ => (1 : ℂ) := by
        funext y
        simp [Multiset.esymm]
      rw [this]
      exact differentiableOn_const 1
    · set E : (Fin n → ℂ) → ℂ := fun y =>
        (-1) ^ (j + 1) * (j : ℂ)⁻¹ *
          (sliceMoment f t j y
            + ∑ a ∈ {a ∈ Finset.antidiagonal j | a.1 ∈ Set.Ioo 0 j},
                (-1) ^ a.1 * (sliceRoots f t y).esymm a.1 * sliceMoment f t a.2 y) with hE
      have hSdiff : DifferentiableOn ℂ (fun y : Fin n → ℂ =>
          sliceMoment f t j y
            + ∑ a ∈ {a ∈ Finset.antidiagonal j | a.1 ∈ Set.Ioo 0 j},
                (-1) ^ a.1 * (sliceRoots f t y).esymm a.1 * sliceMoment f t a.2 y) V := by
        refine (differentiableOn_sliceMoment hU hV hf ht hdisc hnez j).add ?_
        have hterm : ∀ a ∈ {a ∈ Finset.antidiagonal j | a.1 ∈ Set.Ioo 0 j},
            DifferentiableOn ℂ (fun y : Fin n → ℂ =>
              (-1) ^ a.1 * (sliceRoots f t y).esymm a.1 * sliceMoment f t a.2 y) V := by
          intro a ha
          have ha1 : a.1 < j := ((Finset.mem_filter.1 ha).2).2
          exact ((ih a.1 ha1).const_mul ((-1 : ℂ) ^ a.1)).mul
            (differentiableOn_sliceMoment hU hV hf ht hdisc hnez a.2)
        have hsum := DifferentiableOn.sum
          (u := {a ∈ Finset.antidiagonal j | a.1 ∈ Set.Ioo 0 j})
          (A := fun a (y : Fin n → ℂ) =>
            (-1) ^ a.1 * (sliceRoots f t y).esymm a.1 * sliceMoment f t a.2 y) hterm
        have hfun : (∑ a ∈ {a ∈ Finset.antidiagonal j | a.1 ∈ Set.Ioo 0 j},
            fun y : Fin n → ℂ => (-1) ^ a.1 * (sliceRoots f t y).esymm a.1 * sliceMoment f t a.2 y)
            = fun y : Fin n → ℂ =>
              ∑ a ∈ {a ∈ Finset.antidiagonal j | a.1 ∈ Set.Ioo 0 j},
                (-1) ^ a.1 * (sliceRoots f t y).esymm a.1 * sliceMoment f t a.2 y := by
          funext y
          rw [Finset.sum_apply]
        rw [hfun] at hsum
        exact hsum
      have hEdiff : DifferentiableOn ℂ E V :=
        hSdiff.const_mul ((-1 : ℂ) ^ (j + 1) * (j : ℂ)⁻¹)
      refine hEdiff.congr fun y hy => ?_
      have hM := GaloisForLFunctions.multiset_esymm_eq_of_powerSum (sliceRoots f t y) j hj
      have h1 : ∀ q : ℕ, sliceMoment f t q y
          = (Multiset.map (fun x => x ^ q) (sliceRoots f t y)).sum :=
        fun q => sliceMoment_eq_powerSum ht (hadm y hy) q
      show (sliceRoots f t y).esymm j = E y
      rw [hM, hE]
      simp only [h1]

end HTGeometry
