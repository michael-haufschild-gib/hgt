import GaloisForLFunctions.HTGeometry.CayleyOuterJetChart
import GaloisForLFunctions.HTGeometry.ExponentialJetOpenness

/-!
# Smoothness of the jet charts

The exponential, inversion and affine jet recursions are built from field operations and the
exponential, so a smooth family of jet packets is carried to a smooth family.  Each recursion is
triangular, so the induction is on the jet order.

The Cayley outer chart is the composite of the three, and its packet form is therefore smooth on the
open set where the zeroth entry avoids `-i`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## The three recursions -/

theorem contDiffOn_expJetScalar_comp {V : Set X} {A : X → ℕ → ℂ}
    (hA : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A x j) V) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => expJetScalar (A x) k) V := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
        simp only [expJetScalar_zero]
        exact Complex.contDiff_exp.comp_contDiffOn (hA 0)
    | succ k =>
        simp only [expJetScalar_succ]
        refine ContDiffOn.sum fun i hi => ?_
        rw [Finset.mem_range] at hi
        exact (contDiffOn_const.mul (ih i (by omega))).mul (hA (k - i + 1))

theorem contDiffOn_affJetScalar_comp {V : Set X} {A : X → ℕ → ℂ}
    (hA : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A x j) V) (a b : ℂ) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => affJetScalar a b (A x) k) V := by
  by_cases hk : k = 0
  · subst hk
    simp only [affJetScalar]
    exact (contDiffOn_const.mul (hA 0)).add contDiffOn_const
  · simp only [affJetScalar, if_neg hk]
    exact contDiffOn_const.mul (hA k)

/-- The reciprocal jets, written as the triangular recursion they solve. -/
theorem invJetScalar_eq (y : ℕ → ℂ) (k : ℕ) :
    invJetScalar y k = ((if k = 0 then 1 else 0) - invJetLower y k (invJetScalar y)) / y 0 := by
  have h := triangularSolve_eq (y 0) (invJetLower y) (fun k => if k = 0 then 1 else 0) k
  have hcongr : (invJetLower y k fun j => if _ : j < k then
        triangularSolve (y 0) (invJetLower y) (fun k => if k = 0 then 1 else 0) j else 0)
      = invJetLower y k (invJetScalar y) := by
    refine invJetLower_congr y k _ _ ?_
    intro j hj
    rw [dif_pos hj]
    rfl
  rw [hcongr] at h
  exact h

theorem contDiffOn_invJetScalar_comp {V : Set X} {A : X → ℕ → ℂ}
    (hA : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A x j) V) (h0 : ∀ x ∈ V, A x 0 ≠ 0) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => invJetScalar (A x) k) V := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hlower : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x => invJetLower (A x) k (invJetScalar (A x))) V := by
      have hexp : (fun x => invJetLower (A x) k (invJetScalar (A x)))
          = fun x => ∑ i ∈ Finset.range k, ((k.choose (i + 1) : ℕ) : ℂ) * A x (i + 1)
              * invJetScalar (A x) (k - (i + 1)) := rfl
      rw [hexp]
      refine ContDiffOn.sum fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact (contDiffOn_const.mul (hA (i + 1))).mul (ih (k - (i + 1)) (by omega))
    have hnum : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x => (if k = 0 then (1 : ℂ) else 0) - invJetLower (A x) k (invJetScalar (A x))) V :=
      contDiffOn_const.sub hlower
    have hdiv : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x => ((if k = 0 then (1 : ℂ) else 0)
          - invJetLower (A x) k (invJetScalar (A x))) * (A x 0)⁻¹) V :=
      hnum.mul ((hA 0).inv h0)
    have hval : ∀ x : X, ((if k = 0 then (1 : ℂ) else 0)
        - invJetLower (A x) k (invJetScalar (A x))) * (A x 0)⁻¹ = invJetScalar (A x) k := by
      intro x
      rw [invJetScalar_eq, div_eq_mul_inv]
    simpa only [hval] using hdiv

/-! ## The Cayley outer chart -/

theorem contDiffOn_chiJetScalar_comp {V : Set X} {A : X → ℕ → ℂ}
    (hA : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A x j) V)
    (hne : ∀ x ∈ V, A x 0 + Complex.I ≠ 0) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => chiJetScalar (A x) k) V := by
  have h1 : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => affJetScalar 1 Complex.I (A x) j) V :=
    fun j => contDiffOn_affJetScalar_comp hA 1 Complex.I j
  have h1ne : ∀ x ∈ V, affJetScalar 1 Complex.I (A x) 0 ≠ 0 := by
    intro x hx
    simpa [affJetScalar] using hne x hx
  have h2 : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => invJetScalar (fun m => affJetScalar 1 Complex.I (A x) m) j) V :=
    fun j => contDiffOn_invJetScalar_comp
      (A := fun x m => affJetScalar 1 Complex.I (A x) m) h1 h1ne j
  have h3 : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => affJetScalar (-(2 * Complex.I)) 1
        (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I (A x) m) l) j) V :=
    fun j => contDiffOn_affJetScalar_comp
      (A := fun x l => invJetScalar (fun m => affJetScalar 1 Complex.I (A x) m) l) h2
      (-(2 * Complex.I)) 1 j
  exact contDiffOn_expJetScalar_comp
    (A := fun x j => affJetScalar (-(2 * Complex.I)) 1
      (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I (A x) m) l) j) h3 k

/-- The zero padding of a jet packet. -/
def jetExtend (n : ℕ) (y : Fin (n + 1) → ℂ) : ℕ → ℂ :=
  fun j => if h : j < n + 1 then y ⟨j, h⟩ else 0

theorem contDiffOn_jetExtend {n : ℕ} {V : Set (Fin (n + 1) → ℂ)} (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Fin (n + 1) → ℂ => jetExtend n y j) V := by
  by_cases hj : j < n + 1
  · simp only [jetExtend, dif_pos hj]
    exact (contDiff_apply ℝ ℂ (⟨j, hj⟩ : Fin (n + 1))).contDiffOn
  · simp only [jetExtend, dif_neg hj]
    exact contDiffOn_const

/-- **The Cayley outer packet chart is smooth off the polar locus.** -/
theorem contDiffOn_chiJetPacket (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chiJetPacket n)
      {y : Fin (n + 1) → ℂ | y 0 + Complex.I ≠ 0} := by
  rw [contDiffOn_pi]
  intro k
  have hA : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Fin (n + 1) → ℂ => jetExtend n y j)
      {y : Fin (n + 1) → ℂ | y 0 + Complex.I ≠ 0} := fun j => contDiffOn_jetExtend j
  have hne : ∀ y ∈ {y : Fin (n + 1) → ℂ | y 0 + Complex.I ≠ 0},
      jetExtend n y 0 + Complex.I ≠ 0 := by
    intro y hy
    simpa [jetExtend] using hy
  exact contDiffOn_chiJetScalar_comp (A := fun y j => jetExtend n y j) hA hne (k : ℕ)

end

end GaloisForLFunctions.HTGeometry
