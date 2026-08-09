import GaloisForLFunctions.HTGeometry.ConstitutiveCompetitiveWorkHistory
import GaloisForLFunctions.HTGeometry.CompletionKernelPairTransversalityLaw
import Mathlib.Tactic

/-!
# Competitive path variation and observer descent

Mandatory and permissive composition of two exact work laws split every finite path into an
endpoint term and the positive/negative total variation of their relative potential. On closed
paths the endpoint term disappears. The same relative potential descends through an observer
exactly when every observer-collapsed two-cycle has zero competitive work.
-/

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*}

/-- Work accumulated along consecutive states of a finite path. -/
def constitutivePathWork (ω : ι → ι → ℝ) : List ι → ℝ
  | [] => 0
  | [_] => 0
  | i :: j :: xs => ω i j + constitutivePathWork ω (j :: xs)

/-- Total variation of a scalar mark along consecutive states of a finite path. -/
def constitutivePathVariation (D : ι → ℝ) : List ι → ℝ
  | [] => 0
  | [_] => 0
  | i :: j :: xs => |D j - D i| + constitutivePathVariation D (j :: xs)

/-- Endpoint change of a scalar mark, with empty paths assigned zero. -/
def constitutiveEndpointChange (A : ι → ℝ) : List ι → ℝ
  | [] => 0
  | i :: xs => A (xs.getLastD i) - A i

/-- A finite path is closed when its final state is its initial state. -/
def ConstitutiveClosedPath : List ι → Prop
  | [] => True
  | i :: xs => xs.getLastD i = i

/-- A scalar mark is constant along every edge of a path. -/
def ConstitutivePathConstant (D : ι → ℝ) : List ι → Prop
  | [] => True
  | [_] => True
  | i :: j :: xs => D i = D j ∧ ConstitutivePathConstant D (j :: xs)

/-- Exact path work telescopes to the endpoint change. -/
theorem constitutivePathWork_exact (A : ι → ℝ) (xs : List ι) :
    constitutivePathWork (constitutiveExactWork A) xs = constitutiveEndpointChange A xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      cases xs with
      | nil => simp [constitutivePathWork, constitutiveEndpointChange]
      | cons j xs =>
          rw [constitutivePathWork, constitutiveEndpointChange, List.getLastD_cons]
          have ih' := ih
          simp only [constitutiveEndpointChange] at ih'
          rw [ih']
          simp [constitutiveExactWork]

/-- Endpoint changes vanish on closed paths. -/
theorem constitutiveEndpointChange_eq_zero_of_closed (A : ι → ℝ) {xs : List ι}
    (hxs : ConstitutiveClosedPath xs) :
    constitutiveEndpointChange A xs = 0 := by
  cases xs with
  | nil => rfl
  | cons i xs =>
      simp only [ConstitutiveClosedPath] at hxs
      change A (xs.getLastD i) - A i = 0
      rw [hxs]
      ring

/-- Local positive-variation decomposition of a maximum. -/
theorem two_mul_max_eq_add_add_abs (a b : ℝ) :
    2 * max a b = a + b + |a - b| := by
  have hsum := max_add_min a b
  have hdiff := max_sub_min_eq_abs a b
  rw [abs_sub_comm] at hdiff
  linarith

/-- Local negative-variation decomposition of a minimum. -/
theorem two_mul_min_eq_add_sub_abs (a b : ℝ) :
    2 * min a b = a + b - |a - b| := by
  have hsum := max_add_min a b
  have hdiff := max_sub_min_eq_abs a b
  rw [abs_sub_comm] at hdiff
  linarith

/-- **Competitive path Jordan law.** Mandatory composition is the sum of the two endpoint changes
plus the total variation of the relative potential. -/
theorem constitutiveConjunctivePathWork_eq_endpoint_add_variation
    (A B : ι → ℝ) (xs : List ι) :
    2 * constitutivePathWork (constitutiveConjunctiveWork A B) xs =
      constitutiveEndpointChange A xs + constitutiveEndpointChange B xs +
        constitutivePathVariation (fun x => A x - B x) xs := by
  induction xs with
  | nil => simp [constitutivePathWork, constitutiveEndpointChange, constitutivePathVariation]
  | cons i xs ih =>
      cases xs with
      | nil => simp [constitutivePathWork, constitutiveEndpointChange, constitutivePathVariation]
      | cons j xs =>
          simp only [constitutivePathWork, constitutiveEndpointChange, constitutivePathVariation,
            List.getLastD_cons]
          have ih' := ih
          simp only [constitutiveEndpointChange] at ih'
          have hlocal := two_mul_max_eq_add_add_abs
            (constitutiveExactWork A i j) (constitutiveExactWork B i j)
          simp only [constitutiveConjunctiveWork]
          simp only [constitutiveExactWork] at hlocal ⊢
          ring_nf at hlocal ⊢
          nlinarith [ih', hlocal]

/-- Permissive composition carries the negative variation sector. -/
theorem constitutiveDisjunctivePathWork_eq_endpoint_sub_variation
    (A B : ι → ℝ) (xs : List ι) :
    2 * constitutivePathWork (constitutiveDisjunctiveWork A B) xs =
      constitutiveEndpointChange A xs + constitutiveEndpointChange B xs -
        constitutivePathVariation (fun x => A x - B x) xs := by
  induction xs with
  | nil => simp [constitutivePathWork, constitutiveEndpointChange, constitutivePathVariation]
  | cons i xs ih =>
      cases xs with
      | nil => simp [constitutivePathWork, constitutiveEndpointChange, constitutivePathVariation]
      | cons j xs =>
          simp only [constitutivePathWork, constitutiveEndpointChange, constitutivePathVariation,
            List.getLastD_cons]
          have ih' := ih
          simp only [constitutiveEndpointChange] at ih'
          have hlocal := two_mul_min_eq_add_sub_abs
            (constitutiveExactWork A i j) (constitutiveExactWork B i j)
          simp only [constitutiveDisjunctiveWork]
          simp only [constitutiveExactWork] at hlocal ⊢
          ring_nf at hlocal ⊢
          nlinarith [ih', hlocal]

/-- Closed mandatory histories carry exactly half the relative total variation. -/
theorem constitutiveConjunctivePathWork_closed_eq_half_variation
    (A B : ι → ℝ) {xs : List ι} (hxs : ConstitutiveClosedPath xs) :
    constitutivePathWork (constitutiveConjunctiveWork A B) xs =
      constitutivePathVariation (fun x => A x - B x) xs / 2 := by
  have h := constitutiveConjunctivePathWork_eq_endpoint_add_variation A B xs
  rw [constitutiveEndpointChange_eq_zero_of_closed A hxs,
    constitutiveEndpointChange_eq_zero_of_closed B hxs] at h
  linarith

/-- Closed permissive histories carry the opposite half-variation. -/
theorem constitutiveDisjunctivePathWork_closed_eq_neg_half_variation
    (A B : ι → ℝ) {xs : List ι} (hxs : ConstitutiveClosedPath xs) :
    constitutivePathWork (constitutiveDisjunctiveWork A B) xs =
      -constitutivePathVariation (fun x => A x - B x) xs / 2 := by
  have h := constitutiveDisjunctivePathWork_eq_endpoint_sub_variation A B xs
  rw [constitutiveEndpointChange_eq_zero_of_closed A hxs,
    constitutiveEndpointChange_eq_zero_of_closed B hxs] at h
  linarith

/-- Path variation is nonnegative. -/
theorem constitutivePathVariation_nonneg (D : ι → ℝ) (xs : List ι) :
    0 ≤ constitutivePathVariation D xs := by
  induction xs with
  | nil => simp [constitutivePathVariation]
  | cons i xs ih =>
      cases xs with
      | nil => simp [constitutivePathVariation]
      | cons j xs =>
          simp only [constitutivePathVariation]
          exact add_nonneg (abs_nonneg _) ih

/-- Zero path variation is exactly edgewise constancy of the relative law. -/
theorem constitutivePathVariation_eq_zero_iff_pathConstant (D : ι → ℝ) (xs : List ι) :
    constitutivePathVariation D xs = 0 ↔ ConstitutivePathConstant D xs := by
  induction xs with
  | nil => simp [constitutivePathVariation, ConstitutivePathConstant]
  | cons i xs ih =>
      cases xs with
      | nil => simp [constitutivePathVariation, ConstitutivePathConstant]
      | cons j xs =>
          simp only [constitutivePathVariation, ConstitutivePathConstant]
          constructor
          · intro hzero
            have htail_nonneg := constitutivePathVariation_nonneg D (j :: xs)
            have habs_nonneg : 0 ≤ |D j - D i| := abs_nonneg _
            have habs_zero : |D j - D i| = 0 := by linarith
            have htail_zero : constitutivePathVariation D (j :: xs) = 0 := by linarith
            exact ⟨(sub_eq_zero.mp (abs_eq_zero.mp habs_zero)).symm, ih.mp htail_zero⟩
          · rintro ⟨hij, htail⟩
            rw [ih.mpr htail]
            simp [hij]

/-- Closed mandatory history vanishes exactly when the relative law is edgewise constant. -/
theorem constitutiveConjunctivePathWork_closed_eq_zero_iff_pathConstant
    (A B : ι → ℝ) {xs : List ι} (hxs : ConstitutiveClosedPath xs) :
    constitutivePathWork (constitutiveConjunctiveWork A B) xs = 0 ↔
      ConstitutivePathConstant (fun x => A x - B x) xs := by
  rw [constitutiveConjunctivePathWork_closed_eq_half_variation A B hxs]
  constructor
  · intro h
    apply (constitutivePathVariation_eq_zero_iff_pathConstant _ _).mp
    linarith
  · intro h
    rw [(constitutivePathVariation_eq_zero_iff_pathConstant _ _).mpr h]
    norm_num

/-- The competitive two-cycle vanishes exactly when the relative potential agrees at its ends. -/
theorem constitutiveConjunctiveTwoCycle_eq_zero_iff_relative_eq
    (A B : ι → ℝ) (i j : ι) :
    constitutiveConjunctiveWork A B i j + constitutiveConjunctiveWork A B j i = 0 ↔
      A i - B i = A j - B j := by
  rw [constitutiveConjunctiveWork_twoCycle]
  constructor
  · intro h
    have hdiff := abs_eq_zero.mp h
    simp only [constitutiveExactWork] at hdiff
    linarith
  · intro h
    apply abs_eq_zero.mpr
    simp only [constitutiveExactWork]
    linarith

/-- **Observer memory-descent law.** The relative potential factors through the attained observer
range exactly when every observer-collapsed competitive two-cycle has zero work. -/
theorem relativePotential_factorsThroughRange_iff_collapsedTwoCycle_zero
    {Q : Type*} (q : ι → Q) (A B : ι → ℝ) :
    FactorsThroughRange q (fun x => A x - B x) ↔
      ∀ i j, q i = q j →
        constitutiveConjunctiveWork A B i j + constitutiveConjunctiveWork A B j i = 0 := by
  rw [factorsThroughRange_iff_kernelRefines]
  constructor
  · intro h i j hij
    apply (constitutiveConjunctiveTwoCycle_eq_zero_iff_relative_eq A B i j).mpr
    exact h i j hij
  · intro h i j hij
    exact (constitutiveConjunctiveTwoCycle_eq_zero_iff_relative_eq A B i j).mp (h i j hij)

/-- Failure of observer descent has a positive invisible-memory witness on one collapsed pair. -/
theorem exists_collapsed_positive_competitive_memory_of_not_factorsThroughRange
    {Q : Type*} (q : ι → Q) (A B : ι → ℝ)
    (h : ¬ FactorsThroughRange q (fun x => A x - B x)) :
    ∃ i j, q i = q j ∧
      0 < constitutiveConjunctiveWork A B i j + constitutiveConjunctiveWork A B j i := by
  rw [factorsThroughRange_iff_kernelRefines] at h
  simp only [KernelRefines, MapKernelPair] at h
  push Not at h
  obtain ⟨i, j, hij, hrelative⟩ := h
  refine ⟨i, j, hij, ?_⟩
  apply constitutiveConjunctiveWork_positive_twoCycle
  intro hwork
  apply hrelative
  simp only [constitutiveExactWork] at hwork
  linarith

/-- Adding one common potential changes mandatory work only by its exact work. -/
theorem constitutiveConjunctiveWork_add_common_potential
    (A B C : ι → ℝ) (i j : ι) :
    constitutiveConjunctiveWork (fun x => A x + C x) (fun x => B x + C x) i j =
      constitutiveExactWork C i j + constitutiveConjunctiveWork A B i j := by
  have hA : constitutiveExactWork (fun x => A x + C x) i j =
      constitutiveExactWork C i j + constitutiveExactWork A i j := by
    simp only [constitutiveExactWork]
    ring
  have hB : constitutiveExactWork (fun x => B x + C x) i j =
      constitutiveExactWork C i j + constitutiveExactWork B i j := by
    simp only [constitutiveExactWork]
    ring
  rw [constitutiveConjunctiveWork, hA, hB, max_add_add_left]
  rfl

/-- Path work is additive under pointwise addition of work laws. -/
theorem constitutivePathWork_add (ω η : ι → ι → ℝ) (xs : List ι) :
    constitutivePathWork (fun i j => ω i j + η i j) xs =
      constitutivePathWork ω xs + constitutivePathWork η xs := by
  induction xs with
  | nil => simp [constitutivePathWork]
  | cons i xs ih =>
      cases xs with
      | nil => simp [constitutivePathWork]
      | cons j xs =>
          simp only [constitutivePathWork]
          rw [ih]
          ring

/-- Closed competitive history is invariant under a common scalar-presentation change. -/
theorem constitutiveConjunctivePathWork_closed_add_common_potential
    (A B C : ι → ℝ) {xs : List ι} (hxs : ConstitutiveClosedPath xs) :
    constitutivePathWork
        (constitutiveConjunctiveWork (fun x => A x + C x) (fun x => B x + C x)) xs =
      constitutivePathWork (constitutiveConjunctiveWork A B) xs := by
  have hfun :
      constitutiveConjunctiveWork (fun x => A x + C x) (fun x => B x + C x) =
        fun i j => constitutiveExactWork C i j + constitutiveConjunctiveWork A B i j := by
    funext i j
    exact constitutiveConjunctiveWork_add_common_potential A B C i j
  rw [hfun, constitutivePathWork_add, constitutivePathWork_exact,
    constitutiveEndpointChange_eq_zero_of_closed C hxs, zero_add]

/-- Closed capstone: competitive selection produces precisely relative total variation, and the
observer retains it precisely when the relative law descends through the observer range. -/
theorem constitutiveCompetitiveHistoryProductionAndDescent
    {Q : Type*} (q : ι → Q) (A B : ι → ℝ) :
    (∀ (xs : List ι), ConstitutiveClosedPath xs →
      constitutivePathWork (constitutiveConjunctiveWork A B) xs =
        constitutivePathVariation (fun x => A x - B x) xs / 2) ∧
    (FactorsThroughRange q (fun x => A x - B x) ↔
      ∀ i j, q i = q j →
        constitutiveConjunctiveWork A B i j + constitutiveConjunctiveWork A B j i = 0) := by
  exact ⟨fun xs hxs => constitutiveConjunctivePathWork_closed_eq_half_variation A B hxs,
    relativePotential_factorsThroughRange_iff_collapsedTwoCycle_zero q A B⟩

end GaloisForLFunctions.HTGeometry

