import GaloisForLFunctions.RHTower.SuzukiLatticeBinomialTransfer

/-!
# Moment towers of finitely supported fields

A finitely supported field has all its coordinate moments in `ℓ²`, and the binomial transfer bounds
every moment of an adjacency image by the moments of the original field.  This is the bookkeeping
that keeps the polynomial group estimate sharp: no moment order is ever gained.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

omit [Fintype P] [DecidableEq P] in
theorem support_posPowField_subset (p : P) (j : ℕ) (f : (P → ℤ) → ℂ) :
    Function.support (posPowField p j f) ⊆ Function.support f := by
  intro ν hν
  simp only [Function.mem_support, posPowField] at hν ⊢
  intro hcon
  rw [hcon, mul_zero] at hν
  exact hν rfl

omit [Fintype P] [DecidableEq P] in
/-- A finitely supported field as an `ℓ²` element. -/
def l2OfFinSupp (f : (P → ℤ) → ℂ) (h : (Function.support f).Finite) : H :=
  ⟨f, memℓp_of_finite_support h⟩

omit [Fintype P] [DecidableEq P] in
@[simp]
theorem coe_l2OfFinSupp (f : (P → ℤ) → ℂ) (h : (Function.support f).Finite) :
    ((l2OfFinSupp f h : H) : (P → ℤ) → ℂ) = f := rfl

omit [Fintype P] [DecidableEq P] in
/-- An `ℓ²` bound for a finitely supported field is determined by the field alone. -/
theorem norm_l2OfFinSupp_congr {f g : (P → ℤ) → ℂ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (hfg : f = g) :
    ‖(l2OfFinSupp f hf : H)‖ = ‖(l2OfFinSupp g hg : H)‖ := by
  subst hfg
  rfl

omit [Fintype P] [DecidableEq P] in
/-- The adjacency is a bounded operator at the level of fields. -/
theorem norm_l2OfFinSupp_adjacencyField_le (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ)
    {f : (P → ℤ) → ℂ} (hf : (Function.support f).Finite) :
    ‖(l2OfFinSupp (adjacencyField Q c f) (support_adjacencyField_finite hf) : H)‖
      ≤ (∑ q ∈ Q, ‖c q‖) * ‖(l2OfFinSupp f hf : H)‖ := by
  have hcoe : (l2OfFinSupp (adjacencyField Q c f) (support_adjacencyField_finite hf) : H)
      = latticeAdjacency Q c (l2OfFinSupp f hf) := by
    refine lp.ext ?_
    funext ν
    rw [coe_l2OfFinSupp, latticeAdjacency_apply, coe_l2OfFinSupp]
  rw [hcoe]
  refine le_trans ((latticeAdjacency Q c).le_opNorm _) ?_
  exact mul_le_mul_of_nonneg_right (norm_latticeAdjacency_le Q c) (norm_nonneg _)

omit [Fintype P] [DecidableEq P] in
/-- **Every coordinate moment of an adjacency image is controlled by the moments of the field.**
The binomial transfer never raises the moment order. -/
theorem norm_posPow_adjacencyField_le (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (p : P) (j : ℕ)
    {f : (P → ℤ) → ℂ} (hf : (Function.support f).Finite) (M : ℝ)
    (hM : ∀ i ∈ Finset.range (j + 1),
      ‖(l2OfFinSupp (posPowField p i f)
          (hf.subset (support_posPowField_subset p i f)) : H)‖ ≤ M) :
    ‖(l2OfFinSupp (posPowField p j (adjacencyField Q c f))
        ((support_adjacencyField_finite hf).subset
          (support_posPowField_subset p j _)) : H)‖
      ≤ (∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ)
          * ∑ q ∈ Q, ‖stepPowWeighted p (j - i) c q‖) * M := by
  have hcoe : (l2OfFinSupp (posPowField p j (adjacencyField Q c f))
      ((support_adjacencyField_finite hf).subset (support_posPowField_subset p j _)) : H)
      = ∑ i ∈ Finset.range (j + 1), (((j.choose i : ℕ) : ℂ))
          • latticeAdjacency Q (stepPowWeighted p (j - i) c)
              (l2OfFinSupp (posPowField p i f)
                (hf.subset (support_posPowField_subset p i f))) := by
    refine lp.ext ?_
    funext r
    rw [coe_l2OfFinSupp, posPowField_adjacencyField, lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, latticeAdjacency_apply, coe_l2OfFinSupp]
  rw [hcoe]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [norm_smul]
  have hcast : ‖(((j.choose i : ℕ) : ℂ))‖ = ((j.choose i : ℕ) : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hcast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans ((latticeAdjacency Q (stepPowWeighted p (j - i) c)).le_opNorm _) ?_
  refine le_trans (mul_le_mul_of_nonneg_right
    (norm_latticeAdjacency_le Q (stepPowWeighted p (j - i) c)) (norm_nonneg _)) ?_
  exact mul_le_mul_of_nonneg_left (hM i hi) (by positivity)

end RHTower
