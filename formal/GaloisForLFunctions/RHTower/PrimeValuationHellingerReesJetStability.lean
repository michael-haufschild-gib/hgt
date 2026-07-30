import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Operator.Asymptotics

/-!
# Prime-valuation Hellinger--Rees jet stability

Finite radial multiplicity packets cannot mask the distinction between finite Rees grade and
flatness beyond every grade.  This module isolates the unconditional asymptotic algebra behind
that statement: finite packets detect all-orders flatness coordinatewise, and every finite matrix
whose coefficients have finite Rees grade preserves the flat radical.  Consequently a
finite-Rees-moderate jet equivalence cannot sew an all-orders-flat face to a finite-grade face.
The same statement holds in arbitrary dimension whenever the full operator norm has finite Rees
grade; infinite rank alone is not an escape.

The prime-indexed Hellinger asymptotics that place the negative radial face at half-normal order
and the positive face in the all-orders-flat radical remain a separate analytic input.
-/

namespace RHTower

noncomputable section

open Filter Asymptotics

variable {α : Type*}

/-- A germ is in the all-orders-flat radical of the scale `a`. -/
def ReesAllOrdersFlat (l : Filter α) (a : α → ℝ) {E : Type*}
    [SeminormedAddCommGroup E] (f : α → E) : Prop :=
  ∀ N : ℕ, f =o[l] fun x => a x ^ N

/-- A germ has a specified finite Rees bound. -/
def ReesGradeAtMost (l : Filter α) (a : α → ℝ) {E : Type*}
    [SeminormedAddCommGroup E] (N : ℕ) (f : α → E) : Prop :=
  f =O[l] fun x => (a x)⁻¹ ^ N

/-- A finite packet is all-orders flat exactly when every coordinate is. -/
theorem reesAllOrdersFlat_pi_iff {ι : Type*} [Fintype ι]
    (l : Filter α) (a : α → ℝ) (v : ι → α → ℝ) :
    ReesAllOrdersFlat l a (fun x i => v i x) ↔
      ∀ i, ReesAllOrdersFlat l a (v i) := by
  simp only [ReesAllOrdersFlat]
  constructor
  · intro h i N
    exact (isLittleO_pi.mp (h N)) i
  · intro h N
    exact isLittleO_pi.mpr fun i => h i N

/-- A uniform finite Rees bound passes to and from a finite packet. -/
theorem reesGradeAtMost_pi_iff {ι : Type*} [Fintype ι]
    (l : Filter α) (a : α → ℝ) (N : ℕ) (v : ι → α → ℝ) :
    ReesGradeAtMost l a N (fun x i => v i x) ↔
      ∀ i, ReesGradeAtMost l a N (v i) := by
  simp only [ReesGradeAtMost, isBigO_pi]

/-- Constant finite jet-coordinate transformation. -/
def finiteJetTransform {ι κ : Type*} [Fintype ι]
    (A : κ → ι → ℝ) (v : ι → α → ℝ) : κ → α → ℝ :=
  fun k x => ∑ i, A k i * v i x

/-- The all-orders-flat radical is stable under every constant finite jet-coordinate map. -/
theorem reesAllOrdersFlat_finiteJetTransform {ι κ : Type*}
    [Fintype ι] [Fintype κ] (l : Filter α) (a : α → ℝ)
    (A : κ → ι → ℝ) (v : ι → α → ℝ)
    (hv : ReesAllOrdersFlat l a (fun x i => v i x)) :
    ReesAllOrdersFlat l a
      (fun x k => finiteJetTransform A v k x) := by
  rw [reesAllOrdersFlat_pi_iff] at hv ⊢
  intro k N
  apply IsLittleO.sum
  intro i hi
  exact (hv i N).const_mul_left (A k i)

/-- A uniform finite Rees bound is stable under every constant finite jet-coordinate map. -/
theorem reesGradeAtMost_finiteJetTransform {ι κ : Type*}
    [Fintype ι] [Fintype κ] (l : Filter α) (a : α → ℝ) (N : ℕ)
    (A : κ → ι → ℝ) (v : ι → α → ℝ)
    (hv : ReesGradeAtMost l a N (fun x i => v i x)) :
    ReesGradeAtMost l a N
      (fun x k => finiteJetTransform A v k x) := by
  rw [reesGradeAtMost_pi_iff] at hv ⊢
  intro k
  apply IsBigO.sum
  intro i hi
  exact (hv i).const_mul_left (A k i)

/-- An invertible constant finite jet-coordinate change cannot create or erase the
all-orders-flat radical. -/
theorem reesAllOrdersFlat_finiteJetTransform_iff_of_inverse
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l : Filter α) (a : α → ℝ)
    (A : κ → ι → ℝ) (B : ι → κ → ℝ) (v : ι → α → ℝ)
    (hleft :
      finiteJetTransform B (finiteJetTransform A v) = v) :
    ReesAllOrdersFlat l a
        (fun x k => finiteJetTransform A v k x) ↔
      ReesAllOrdersFlat l a (fun x i => v i x) := by
  constructor
  · intro h
    have hB := reesAllOrdersFlat_finiteJetTransform l a B
      (finiteJetTransform A v) h
    simpa only [hleft] using hB
  · exact reesAllOrdersFlat_finiteJetTransform l a A v

/-- Multiplication by a germ of any fixed finite Rees grade preserves all-orders flatness. -/
theorem reesAllOrdersFlat_mul_reesGradeAtMost
    (l : Filter α) (a r f : α → ℝ) (K : ℕ)
    (ha : ∀ᶠ x in l, a x ≠ 0)
    (hr : ReesGradeAtMost l a K r)
    (hf : ReesAllOrdersFlat l a f) :
    ReesAllOrdersFlat l a (fun x => r x * f x) := by
  intro N
  have hproduct :=
    hr.mul_isLittleO (hf (N + K))
  apply hproduct.congr' EventuallyEq.rfl
  filter_upwards [ha] with x hx
  rw [pow_add]
  calc
    (a x)⁻¹ ^ K * (a x ^ N * a x ^ K)
        = a x ^ N * ((a x)⁻¹ ^ K * a x ^ K) := by ring
    _ = a x ^ N := by
      rw [← mul_pow, inv_mul_cancel₀ hx, one_pow, mul_one]

/-- Finite jet-coordinate transformation whose coefficients may vary along the germ. -/
def finiteReesJetTransform {ι κ : Type*} [Fintype ι]
    (A : κ → ι → α → ℝ) (v : ι → α → ℝ) : κ → α → ℝ :=
  fun k x => ∑ i, A k i x * v i x

/-- Every finite matrix with a uniform finite Rees bound preserves the all-orders-flat radical. -/
theorem reesAllOrdersFlat_finiteReesJetTransform
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l : Filter α) (a : α → ℝ) (K : ℕ)
    (A : κ → ι → α → ℝ) (v : ι → α → ℝ)
    (ha : ∀ᶠ x in l, a x ≠ 0)
    (hA : ∀ k i, ReesGradeAtMost l a K (A k i))
    (hv : ReesAllOrdersFlat l a (fun x i => v i x)) :
    ReesAllOrdersFlat l a
      (fun x k => finiteReesJetTransform A v k x) := by
  rw [reesAllOrdersFlat_pi_iff] at hv ⊢
  intro k N
  apply IsLittleO.sum
  intro i hi
  exact (reesAllOrdersFlat_mul_reesGradeAtMost
    l a (A k i) (v i) K ha (hA k i) (hv i)) N

/-- A finite Rees-moderate jet equivalence cannot create or erase the all-orders-flat radical. -/
theorem reesAllOrdersFlat_finiteReesJetTransform_iff_of_inverse
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l : Filter α) (a : α → ℝ) (KA KB : ℕ)
    (A : κ → ι → α → ℝ) (B : ι → κ → α → ℝ)
    (v : ι → α → ℝ)
    (ha : ∀ᶠ x in l, a x ≠ 0)
    (hA : ∀ k i, ReesGradeAtMost l a KA (A k i))
    (hB : ∀ i k, ReesGradeAtMost l a KB (B i k))
    (hleft : finiteReesJetTransform B (finiteReesJetTransform A v) = v) :
    ReesAllOrdersFlat l a
        (fun x k => finiteReesJetTransform A v k x) ↔
      ReesAllOrdersFlat l a (fun x i => v i x) := by
  constructor
  · intro h
    have hback := reesAllOrdersFlat_finiteReesJetTransform
      l a KB B (finiteReesJetTransform A v) ha hB h
    simpa only [hleft] using hback
  · exact reesAllOrdersFlat_finiteReesJetTransform
      l a KA A v ha hA

/-- A family of continuous linear maps has a specified finite operator-norm Rees bound. -/
def ReesOperatorGradeAtMost
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (l : Filter α) (a : α → ℝ) (K : ℕ)
    (R : α → (E →L[ℝ] F)) : Prop :=
  ReesGradeAtMost l a K (fun x => ‖R x‖)

/-- Every operator family with a fixed finite Rees norm bound preserves all-orders flatness,
without a finite-dimensionality assumption. -/
theorem reesAllOrdersFlat_apply_reesOperatorGradeAtMost
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (l : Filter α) (a : α → ℝ) (K : ℕ)
    (R : α → (E →L[ℝ] F)) (f : α → E)
    (ha : ∀ᶠ x in l, a x ≠ 0)
    (hR : ReesOperatorGradeAtMost l a K R)
    (hf : ReesAllOrdersFlat l a f) :
    ReesAllOrdersFlat l a (fun x => R x (f x)) := by
  intro N
  have hop :
      (fun x => R x (f x)) =O[l]
        (fun x => ‖R x‖ * ‖f x‖) := by
    rw [isBigO_iff]
    refine ⟨1, Filter.Eventually.of_forall ?_⟩
    intro x
    simpa only [one_mul, Real.norm_eq_abs, abs_mul, abs_norm] using
      (R x).le_opNorm (f x)
  have hproduct :
      (fun x => ‖R x‖ * ‖f x‖) =o[l]
        (fun x => (a x)⁻¹ ^ K * a x ^ (N + K)) :=
    hR.mul_isLittleO ((hf (N + K)).norm_left)
  apply (hop.trans_isLittleO hproduct).congr' EventuallyEq.rfl
  filter_upwards [ha] with x hx
  rw [pow_add]
  calc
    (a x)⁻¹ ^ K * (a x ^ N * a x ^ K)
        = a x ^ N * ((a x)⁻¹ ^ K * a x ^ K) := by ring
    _ = a x ^ N := by
      rw [← mul_pow, inv_mul_cancel₀ hx, one_pow, mul_one]

end

end RHTower
