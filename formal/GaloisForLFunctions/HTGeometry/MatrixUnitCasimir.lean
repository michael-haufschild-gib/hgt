import GaloisForLFunctions.HTGeometry.WeightCasimirGap

/-!
# The abstract collective Casimir: centrality and the energy expansion

A matrix-unit family on a finite coordinate space is a family `gen a b` of matrices satisfying the
`gl` bracket relations, with `gen a b` adjoint to `gen b a`.  Its quadratic Casimir
`C = ∑_{a,b} gen a b * gen b a` is then Hermitian, commutes with every member of the family, and its
energy at a vector is the total energy of the family applied to that vector.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Inner

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The coordinate inner product. -/
def cinner (X Y : I → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (X i) * Y i

/-- The coordinate square norm. -/
def cnormSq (X : I → ℂ) : ℝ := ∑ i, ‖X i‖ ^ 2

theorem cnormSq_nonneg (X : I → ℂ) : 0 ≤ cnormSq X :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cinner_self (X : I → ℂ) : cinner X X = ((cnormSq X : ℝ) : ℂ) := by
  rw [cinner, cnormSq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Complex.conj_mul']
  push_cast
  ring

theorem cnormSq_eq_zero_iff (X : I → ℂ) : cnormSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    funext i
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖X j‖).mp h
    have hi := hall i (Finset.mem_univ i)
    have : ‖X i‖ = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hi
      exact this
    simpa using this
  · intro h
    rw [h, cnormSq]
    simp

/-- Moving a matrix across the inner product replaces it by its adjoint. -/
theorem cinner_mulVec (M : Matrix I I ℂ) (X Y : I → ℂ) :
    cinner X (M *ᵥ Y) = cinner (Mᴴ *ᵥ X) Y := by
  rw [cinner, cinner]
  have hL : ∀ i : I, (starRingEnd ℂ) (X i) * ((M *ᵥ Y) i)
      = ∑ j, (starRingEnd ℂ) (X i) * (M i j * Y j) := by
    intro i
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  have hR : ∀ j : I, (starRingEnd ℂ) ((Mᴴ *ᵥ X) j) * Y j
      = ∑ i, (starRingEnd ℂ) (X i) * (M i j * Y j) := by
    intro j
    rw [Matrix.mulVec, dotProduct, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]
    ring
  rw [Finset.sum_congr rfl fun i _ => hL i, Finset.sum_congr rfl fun j _ => hR j,
    Finset.sum_comm]

end Inner

section Family

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The bracket relations of a matrix-unit family. -/
def IsMatrixUnitFamily (gen : α → α → Matrix I I ℂ) : Prop :=
  (∀ a b, (gen a b)ᴴ = gen b a) ∧
    ∀ a b c d, gen a b * gen c d - gen c d * gen a b
      = (if b = c then gen a d else 0) - (if d = a then gen c b else 0)

/-- The quadratic Casimir of a matrix-unit family. -/
def familyCasimir (gen : α → α → Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ a, ∑ b, gen a b * gen b a

theorem familyCasimir_conjTranspose {gen : α → α → Matrix I I ℂ}
    (h : IsMatrixUnitFamily gen) : (familyCasimir gen)ᴴ = familyCasimir gen := by
  rw [familyCasimir, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.conjTranspose_mul, h.1 b a, h.1 a b]

/-- **The Casimir is central.** -/
theorem familyCasimir_commute {gen : α → α → Matrix I I ℂ}
    (h : IsMatrixUnitFamily gen) (c d : α) :
    familyCasimir gen * gen c d = gen c d * familyCasimir gen := by
  classical
  have hbr := h.2
  have hkey : ∀ a b : α,
      (gen a b * gen b a) * gen c d - gen c d * (gen a b * gen b a)
        = ((if b = c then gen a d else 0) - (if d = a then gen c b else 0)) * gen b a
          + gen a b * ((if a = c then gen b d else 0) - (if d = b then gen c a else 0)) := by
    intro a b
    have h1 := hbr a b c d
    have h2 := hbr b a c d
    have hexp : (gen a b * gen b a) * gen c d - gen c d * (gen a b * gen b a)
        = (gen a b * gen c d - gen c d * gen a b) * gen b a
          + gen a b * (gen b a * gen c d - gen c d * gen b a) := by
      noncomm_ring
    rw [hexp, h1, h2]
  have hsum : familyCasimir gen * gen c d - gen c d * familyCasimir gen
      = ∑ a, ∑ b, (((if b = c then gen a d else 0) - (if d = a then gen c b else 0)) * gen b a
          + gen a b * ((if a = c then gen b d else 0) - (if d = b then gen c a else 0))) := by
    rw [familyCasimir, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => hkey a b
  have hzero : (∑ a, ∑ b, (((if b = c then gen a d else 0) - (if d = a then gen c b else 0)) *
      gen b a + gen a b * ((if a = c then gen b d else 0) - (if d = b then gen c a else 0))))
      = 0 := by
    have hexpand : ∀ a b : α,
        (((if b = c then gen a d else 0) - (if d = a then gen c b else 0)) * gen b a
          + gen a b * ((if a = c then gen b d else 0) - (if d = b then gen c a else 0)))
        = ((if b = c then gen a d * gen b a else 0) - (if d = a then gen c b * gen b a else 0))
          + ((if a = c then gen a b * gen b d else 0)
            - (if d = b then gen a b * gen c a else 0)) := by
      intro a b
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : a = c <;> by_cases h4 : d = b <;>
        simp [h1, h2, h3, h4, Matrix.sub_mul, Matrix.mul_sub]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hexpand a b]
    have hS1 : (∑ a, ∑ b, (if b = c then gen a d * gen b a else 0))
        = ∑ a, gen a d * gen c a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_ite_eq' Finset.univ c (fun b => gen a d * gen b a)]
      simp
    have hS2 : (∑ a, ∑ b, (if d = a then gen c b * gen b a else 0))
        = ∑ b, gen c b * gen b d := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_ite_eq Finset.univ d (fun a => gen c b * gen b a)]
      simp
    have hS3 : (∑ a, ∑ b, (if a = c then gen a b * gen b d else 0))
        = ∑ b, gen c b * gen b d := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_ite_eq' Finset.univ c (fun a => gen a b * gen b d)]
      simp
    have hS4 : (∑ a, ∑ b, (if d = b then gen a b * gen c a else 0))
        = ∑ a, gen a d * gen c a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_ite_eq Finset.univ d (fun b => gen a b * gen c a)]
      simp
    have hsplit : (∑ a, ∑ b,
        (((if b = c then gen a d * gen b a else 0) - (if d = a then gen c b * gen b a else 0))
          + ((if a = c then gen a b * gen b d else 0)
            - (if d = b then gen a b * gen c a else 0))))
        = ((∑ a, ∑ b, (if b = c then gen a d * gen b a else 0))
            - ∑ a, ∑ b, (if d = a then gen c b * gen b a else 0))
          + ((∑ a, ∑ b, (if a = c then gen a b * gen b d else 0))
            - ∑ a, ∑ b, (if d = b then gen a b * gen c a else 0)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    rw [hsplit, hS1, hS2, hS3, hS4]
    abel
  rw [hzero] at hsum
  have := sub_eq_zero.mp hsum
  exact this

/-- **The Casimir energy is the total family energy.** -/
theorem cinner_familyCasimir {gen : α → α → Matrix I I ℂ}
    (h : IsMatrixUnitFamily gen) (Y : I → ℂ) :
    cinner Y (familyCasimir gen *ᵥ Y) = ∑ a, ∑ b, ((cnormSq (gen b a *ᵥ Y) : ℝ) : ℂ) := by
  have hstep : ∀ a b : α, cinner Y ((gen a b * gen b a) *ᵥ Y)
      = ((cnormSq (gen b a *ᵥ Y) : ℝ) : ℂ) := by
    intro a b
    have hmv : (gen a b * gen b a) *ᵥ Y = gen a b *ᵥ (gen b a *ᵥ Y) :=
      (Matrix.mulVec_mulVec Y (gen a b) (gen b a)).symm
    rw [hmv, cinner_mulVec, h.1 a b, ← cinner_self]
  rw [familyCasimir]
  have hvec : (∑ a, ∑ b, gen a b * gen b a) *ᵥ Y
      = ∑ a, ∑ b, ((gen a b * gen b a) *ᵥ Y) := by
    simp only [Matrix.sum_mulVec]
  rw [hvec]
  have hlin : ∀ (F : α → α → I → ℂ),
      cinner Y (∑ a, ∑ b, F a b) = ∑ a, ∑ b, cinner Y (F a b) := by
    intro F
    rw [cinner]
    have hexp : ∀ i : I, (starRingEnd ℂ) (Y i) * ((∑ a, ∑ b, F a b) i)
        = ∑ a, ∑ b, (starRingEnd ℂ) (Y i) * (F a b i) := by
      intro i
      simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => rfl
  rw [hlin]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hstep a b

end Family

end

end GaloisForLFunctions.HTGeometry
