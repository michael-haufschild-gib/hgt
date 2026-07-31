import GaloisForLFunctions.HTGeometry.PencilOperatorSymbol
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialVandermonde

/-!
# The exact Stanley–Reisner kernel with differential-operator coefficients

The symbol identity of a constant operator carrier reads, after restricting each polynomial to a
facet and substituting `Y = X + 1`,

```text
∑_ν p_ν(m) · Z_ν^m = 0   for every m ≥ 1,   p_ν(T) = ∑_r coeff_ν(Qt_r) · (L_A w)^r · T^r,
```

with pairwise distinct nonzero nodes `Z_ν`.  The polynomial-coefficient Vandermonde theorem then
kills every `p_ν`, and since `L_A w ≠ 0` every coefficient of every `Qt_r` vanishes.  Ranging over
the facets, every monomial of every `P_r` has nonface support.

* `eval_ratio_pow_eq_sum_node`, `eval_ratio_pow_bind` — the node expansion of a symbol;
* `operatorKernel` — the kernel theorem with `ℂ[δ]` coefficients.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ} {α : Type*} [DecidableEq α] {facets : Finset (Finset α)}

/-! ### Generic restriction lemmas -/

/-- The shifted restriction only involves the facet's variables. -/
theorem vars_bind_restrictPoly (A : Finset α) (P : MvPolynomial α ℂ) :
    (bind₁ (fun j => (X j : MvPolynomial α ℂ) - 1) (restrictPoly A P)).vars ⊆ A := by
  have hXsub : ∀ i : α, ((X i : MvPolynomial α ℂ) - 1).vars ⊆ ({i} : Finset α) := by
    intro i
    have hrw : (X i : MvPolynomial α ℂ) - 1 = X i + C (-1 : ℂ) := by
      rw [map_neg, map_one]
      ring
    rw [hrw]
    refine (vars_add_subset _ _).trans ?_
    rw [vars_C, Finset.union_empty, vars_X]
  refine (vars_bind₁ _ _).trans ?_
  refine Finset.biUnion_subset.mpr fun i hi => ?_
  refine (hXsub i).trans ?_
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  exact vars_restrictPoly A P hi

/-- Undoing the shift recovers the facet restriction. -/
theorem bind_add_one_bind_sub_one (A : Finset α) (P : MvPolynomial α ℂ) :
    bind₁ (fun j => (X j : MvPolynomial α ℂ) + 1)
        (bind₁ (fun j => (X j : MvPolynomial α ℂ) - 1) (restrictPoly A P))
      = restrictPoly A P := by
  rw [bind₁_bind₁]
  have hid : (fun i => bind₁ (fun j => (X j : MvPolynomial α ℂ) + 1) (X i - 1))
      = fun i : α => (X i : MvPolynomial α ℂ) := by
    funext i
    simp
  rw [hid, bind₁_X_left]
  rfl


namespace PencilSeparation

variable {E : Type*} [AddCommMonoid E]

omit [DecidableEq α] in
/-- The node expansion of an evaluation at the ratio powers. -/
theorem eval_ratio_pow_eq_sum_node (S : PencilSeparation facets E) (A : Finset α)
    (Q : MvPolynomial α ℂ) (m : ℕ) :
    eval (fun j => S.ratio A j ^ m) Q = ∑ ν ∈ Q.support, coeff ν Q * (S.node A ν) ^ m := by
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  rw [node, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => by rw [pow_right_comm]

/-- The symbol of a polynomial, read on its facet restriction after the shift `Y = X + 1`. -/
theorem eval_ratio_pow_bind (S : PencilSeparation facets E) {A : Finset α} (hA : A ∈ facets)
    (P : MvPolynomial α ℂ) (m : ℕ) :
    eval (fun j => S.ratio A j ^ m)
        (bind₁ (fun j => (X j : MvPolynomial α ℂ) - 1) (restrictPoly A P))
      = symbHom S.ω (S.phase A) (m : ℂ) P := by
  have h2 : eval (fun j => S.ratio A j ^ m)
      (bind₁ (fun j => (X j : MvPolynomial α ℂ) - 1) (restrictPoly A P))
      = eval (fun j => S.ratio A j ^ m - 1) (restrictPoly A P) := by
    rw [← aeval_eq_eval', aeval_bind₁]
    refine congrArg (fun f => (aeval f) (restrictPoly A P)) ?_
    funext i
    rw [map_sub, aeval_X, map_one]
  have h3 : eval (fun j => S.ratio A j ^ m - 1) (restrictPoly A P)
      = eval (fun j => S.ratio A j ^ m - 1) P := by
    refine eval_restrictPoly P ?_
    intro j hj
    rw [S.ratio_eq_one hA hj, one_pow, sub_self]
  have h4 : eval (fun j => S.ratio A j ^ m - 1) P = symbHom S.ω (S.phase A) (m : ℂ) P := by
    rw [symbHom, aeval_eq_eval']
    refine congrArg (fun f => eval f P) ?_
    funext j
    rw [S.ratio_pow]
  rw [h2, h3, h4]

end PencilSeparation

/-! ### The kernel -/

/-- **The exact Stanley–Reisner kernel with differential-operator coefficients.**  If a
`ℂ[δ]`-combination of pencil carriers is constant, every coefficient polynomial lies in the
Stanley–Reisner ideal. -/
theorem operatorKernel (S : PencilSeparation facets (Fin d → ℂ))
    (Lin : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    (hLin : ∀ A ∈ facets, ∀ z, S.phase A z = Lin A z)
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (w : Fin d → ℂ)
    (hw : ∀ A ∈ facets, Lin A w ≠ 0) {n : ℕ} (P : Fin n → MvPolynomial α ℂ)
    (hconst : ∀ z z' : Fin d → ℂ,
      (∑ r : Fin n, (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r))) z
        = (∑ r : Fin n, (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r))) z')
    (r : Fin n) : P r ∈ stanleyReisnerIdeal ℂ facets := by
  classical
  have hrestrict : ∀ A ∈ facets, ∀ s : Fin n, restrictPoly A (P s) = 0 := by
    intro A hA
    set Qt : Fin n → MvPolynomial α ℂ :=
      fun s => bind₁ (fun j => (X j : MvPolynomial α ℂ) - 1) (restrictPoly A (P s)) with hQt
    set T : Finset (α →₀ ℕ) := Finset.univ.biUnion (fun s : Fin n => (Qt s).support) with hT
    have hsuppT : ∀ ν ∈ T, ν.support ⊆ A := by
      intro ν hν x hx
      obtain ⟨s, _, hνs⟩ := Finset.mem_biUnion.mp hν
      exact vars_bind_restrictPoly A (P s) (mem_vars_iff_mem_support x |>.mpr ⟨ν, hνs, hx⟩)
    set p : (α →₀ ℕ) → Polynomial ℂ := fun ν =>
      ∑ s : Fin n, Polynomial.C (coeff ν (Qt s) * (Lin A w) ^ (s : ℕ))
        * Polynomial.X ^ (s : ℕ) with hp
    have hpeval : ∀ (ν : α →₀ ℕ) (m : ℕ), (p ν).eval (m : ℂ)
        = ∑ s : Fin n, coeff ν (Qt s) * (Lin A w) ^ (s : ℕ) * (m : ℂ) ^ (s : ℕ) := by
      intro ν m
      rw [hp, Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl fun s _ => by simp
    have hsymb : ∀ (s : Fin n) (m : ℕ), ∑ ν ∈ T, coeff ν (Qt s) * (S.node A ν) ^ m
        = symbHom S.ω (S.phase A) (m : ℂ) (P s) := by
      intro s m
      have h1 : symbHom S.ω (S.phase A) (m : ℂ) (P s)
          = ∑ ν ∈ (Qt s).support, coeff ν (Qt s) * (S.node A ν) ^ m := by
        rw [← S.eval_ratio_pow_bind hA (P s) m]
        exact S.eval_ratio_pow_eq_sum_node A (Qt s) m
      rw [h1]
      refine (Finset.sum_subset (fun ν hν => Finset.mem_biUnion.mpr
        ⟨s, Finset.mem_univ s, hν⟩) ?_).symm
      intro ν _ hν
      rw [MvPolynomial.notMem_support_iff.mp hν, zero_mul]
    have hvan : ∀ m : ℕ, 1 ≤ m → ∑ ν ∈ T, (p ν).eval (m : ℂ) * (S.node A ν) ^ m = 0 := by
      intro m hm
      have hL : ∑ ν ∈ T, (p ν).eval (m : ℂ) * (S.node A ν) ^ m
          = ∑ ν ∈ T, ∑ s : Fin n,
            (coeff ν (Qt s) * (Lin A w) ^ (s : ℕ) * (m : ℂ) ^ (s : ℕ)) * (S.node A ν) ^ m := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [hpeval, Finset.sum_mul]
      have hR : ∑ ν ∈ T, ∑ s : Fin n,
            (coeff ν (Qt s) * (Lin A w) ^ (s : ℕ) * (m : ℂ) ^ (s : ℕ)) * (S.node A ν) ^ m
          = ∑ s : Fin n, ((m : ℂ) * Lin A w) ^ (s : ℕ)
            * ∑ ν ∈ T, coeff ν (Qt s) * (S.node A ν) ^ m := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [mul_pow]
        ring
      rw [hL, hR]
      have hfin : ∑ s : Fin n, ((m : ℂ) * Lin A w) ^ (s : ℕ)
          * ∑ ν ∈ T, coeff ν (Qt s) * (S.node A ν) ^ m
          = ∑ s : Fin n, ((m : ℂ) * Lin A w) ^ (s : ℕ)
            * symbHom S.ω (S.phase A) (m : ℂ) (P s) :=
        Finset.sum_congr rfl fun s _ => by rw [hsymb s m]
      rw [hfin]
      exact symbHom_combination_eq_zero S Lin hLin hanti w hA P hconst hm
    have hpzero : ∀ ν ∈ T, p ν = 0 := by
      refine expPolySum_eq_zero (S.node A) T ?_ ?_ p hvan
      · intro ν hν ν' hν' hzz
        exact S.node_injective hA (hsuppT ν (Finset.mem_coe.mp hν))
          (hsuppT ν' (Finset.mem_coe.mp hν')) hzz
      · intro ν _
        exact S.node_ne_zero A ν
    intro s
    have hQt0 : Qt s = 0 := by
      ext ν
      by_cases hν : ν ∈ (Qt s).support
      · have hνT : ν ∈ T := Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, hν⟩
        have hpv : p ν = ∑ b : Fin n, Polynomial.C (coeff ν (Qt b) * (Lin A w) ^ (b : ℕ))
            * Polynomial.X ^ (b : ℕ) := rfl
        have hcoefp : (p ν).coeff (s : ℕ) = coeff ν (Qt s) * (Lin A w) ^ (s : ℕ) := by
          calc (p ν).coeff (s : ℕ)
              = ∑ b : Fin n, (Polynomial.C (coeff ν (Qt b) * (Lin A w) ^ (b : ℕ))
                  * Polynomial.X ^ (b : ℕ)).coeff (s : ℕ) := by
                rw [hpv]
                exact Polynomial.finsetSum_coeff _ _ _
            _ = (Polynomial.C (coeff ν (Qt s) * (Lin A w) ^ (s : ℕ))
                  * Polynomial.X ^ (s : ℕ)).coeff (s : ℕ) := by
                refine Finset.sum_eq_single_of_mem s (Finset.mem_univ s) ?_
                intro b _ hb
                have hbs : (s : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.val_injective h.symm)
                rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hbs, mul_zero]
            _ = coeff ν (Qt s) * (Lin A w) ^ (s : ℕ) := by
                rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
        have hz : coeff ν (Qt s) * (Lin A w) ^ (s : ℕ) = 0 := by
          rw [← hcoefp, hpzero ν hνT, Polynomial.coeff_zero]
        have hLw : (Lin A w) ^ (s : ℕ) ≠ 0 := pow_ne_zero _ (hw A hA)
        rw [(mul_eq_zero.mp hz).resolve_right hLw, coeff_zero]
      · rw [MvPolynomial.notMem_support_iff.mp hν, coeff_zero]
    have hback : bind₁ (fun j => (X j : MvPolynomial α ℂ) + 1) (Qt s) = restrictPoly A (P s) :=
      bind_add_one_bind_sub_one A (P s)
    rw [← hback, hQt0, map_zero]
  refine (mem_stanleyReisnerIdeal_iff _ (P r)).mpr fun ν hν hface => ?_
  obtain ⟨A, hAmem, hνA⟩ := hface
  have hA : A ∈ facets := Finset.mem_coe.mp hAmem
  have hcoeff : coeff ν (P r) = 0 := by
    rw [← coeff_restrictPoly (P r) hνA, hrestrict A hA r, coeff_zero]
  exact (MvPolynomial.mem_support_iff.mp hν) hcoeff

end

end GaloisForLFunctions.HTGeometry
