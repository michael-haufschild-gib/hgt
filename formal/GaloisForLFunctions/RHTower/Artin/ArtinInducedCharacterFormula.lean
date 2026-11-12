import GaloisForLFunctions.RHTower.Artin.ArtinInducedDegree
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace

/-!
# The induced character formula

Let `H` be a subgroup of a finite group `G` and `ρ` a finite-dimensional complex representation
of `H`. With `r_q` a representative of the right coset `q ∈ H\G`,

  `χ_{Ind ρ}(g) = Σ_{q, r_q g r_q⁻¹ ∈ H} χ_ρ(r_q g r_q⁻¹)`   (`induced_character_apply`).

The coinduced representation is the space of functions `f : G → V` with `f(h x) = ρ(h) f(x)`,
on which `G` acts by right translation; evaluation at the representatives identifies it with
`H\G → V`. In these coordinates `g` acts by `(T_g a)(q) = ρ(r_q g r_{q·g}⁻¹) a(q·g)`
(`conj_coind_apply`). The trace of an operator on a product is the sum of the traces of its
diagonal blocks (`trace_pi_eq_sum_blocks`); the block at `q` is `ρ(r_q g r_q⁻¹)` if `q·g = q`
and zero otherwise, and `q·g = q` iff `r_q g r_q⁻¹ ∈ H` (`mk_out_mul_eq_iff`). Induction and
coinduction from a subgroup of finite index are isomorphic.

Since `χ_ρ` is a class function of `H` and every right coset has `|H|` elements,

  `χ_{Ind ρ}(g) = (1/|H|) Σ_{x ∈ G, x g x⁻¹ ∈ H} χ_ρ(x g x⁻¹)`   (`induced_character_apply_average`).
-/

open scoped Classical BigOperators

noncomputable section

universe u w

namespace GaloisForLFunctions

open Representation

/-! ### The trace of an operator on a product -/

/-- **The trace of an operator on `Q → V` is the sum of the traces of its diagonal blocks.** -/
theorem trace_pi_eq_sum_blocks {Q : Type*} [Fintype Q] [DecidableEq Q] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (T : (Q → V) →ₗ[ℂ] (Q → V)) :
    LinearMap.trace ℂ (Q → V) T =
      ∑ q, LinearMap.trace ℂ V
        ((LinearMap.proj q : (Q → V) →ₗ[ℂ] V) ∘ₗ T ∘ₗ LinearMap.single ℂ (fun _ : Q => V) q) := by
  let b := Module.finBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis fun _ : Q => b) T, Matrix.trace,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]

/-! ### The coinduced representation in the coordinates of the right cosets -/

variable {G : Type u} [Group G] (H : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)

/-- A function on a subgroup, extended by zero to the group. -/
def extendByZero (χ : H → ℂ) (x : G) : ℂ := if h : x ∈ H then χ ⟨x, h⟩ else 0

/-- An element differs from the representative of its right coset by an element of `H`. -/
theorem mul_out_inv_mem (x : G) :
    x * (Quotient.mk (QuotientGroup.rightRel H) x).out⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.mp (Quotient.mk_out (s := QuotientGroup.rightRel H) x)

/-- The coset of `r_q g` is `q` iff `r_q g r_q⁻¹ ∈ H`. -/
theorem mk_out_mul_eq_iff (q : Quotient (QuotientGroup.rightRel H)) (g : G) :
    Quotient.mk (QuotientGroup.rightRel H) (q.out * g) = q ↔ q.out * g * q.out⁻¹ ∈ H := by
  constructor
  · intro h
    have hmem := mul_out_inv_mem H (q.out * g)
    rwa [h] at hmem
  · intro h
    have hrel : (QuotientGroup.rightRel H) (q.out * g) q.out := by
      rw [QuotientGroup.rightRel_apply]
      have := H.inv_mem h
      simpa [mul_assoc] using this
    exact (Quotient.sound hrel).trans (Quotient.out_eq q)

/-- **The action of `g` in the coordinates of the right cosets.** -/
theorem conj_coind_apply (g : G) (a : Quotient (QuotientGroup.rightRel H) → V)
    (q : Quotient (QuotientGroup.rightRel H)) :
    ((coinducedRightCosetEquiv H ρ).conj (coind H.subtype ρ g) a) q =
      ρ ⟨q.out * g * (Quotient.mk (QuotientGroup.rightRel H) (q.out * g)).out⁻¹,
        mul_out_inv_mem H (q.out * g)⟩ (a (Quotient.mk (QuotientGroup.rightRel H) (q.out * g))) :=
  rfl

/-- The diagonal block of the action of `g` at the coset `q`: its trace is the character of `ρ`
at `r_q g r_q⁻¹`, extended by zero. -/
theorem trace_block_conj_coind [FiniteDimensional ℂ V] (g : G)
    (q : Quotient (QuotientGroup.rightRel H)) :
    LinearMap.trace ℂ V
        ((LinearMap.proj q : (Quotient (QuotientGroup.rightRel H) → V) →ₗ[ℂ] V) ∘ₗ
          (coinducedRightCosetEquiv H ρ).conj (coind H.subtype ρ g) ∘ₗ
          LinearMap.single ℂ (fun _ : Quotient (QuotientGroup.rightRel H) => V) q) =
      extendByZero H ρ.character (q.out * g * q.out⁻¹) := by
  by_cases hfix : Quotient.mk (QuotientGroup.rightRel H) (q.out * g) = q
  · have hmem : q.out * g * q.out⁻¹ ∈ H := (mk_out_mul_eq_iff H q g).mp hfix
    have hblock : ((LinearMap.proj q : (Quotient (QuotientGroup.rightRel H) → V) →ₗ[ℂ] V) ∘ₗ
        (coinducedRightCosetEquiv H ρ).conj (coind H.subtype ρ g) ∘ₗ
        LinearMap.single ℂ (fun _ : Quotient (QuotientGroup.rightRel H) => V) q) =
        ρ ⟨q.out * g * q.out⁻¹, hmem⟩ := by
      ext v
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
        conj_coind_apply]
      have hv : (Pi.single q v : Quotient (QuotientGroup.rightRel H) → V)
          (Quotient.mk (QuotientGroup.rightRel H) (q.out * g)) = v := by
        rw [hfix, Pi.single_eq_same]
      rw [hv]
      exact congrArg (fun h : H => ρ h v) (Subtype.ext
        (show q.out * g * (Quotient.mk (QuotientGroup.rightRel H) (q.out * g)).out⁻¹ =
          q.out * g * q.out⁻¹ by rw [hfix]))
    rw [hblock, extendByZero, dif_pos hmem]
    rfl
  · have hnot : q.out * g * q.out⁻¹ ∉ H := fun h => hfix ((mk_out_mul_eq_iff H q g).mpr h)
    have hblock : ((LinearMap.proj q : (Quotient (QuotientGroup.rightRel H) → V) →ₗ[ℂ] V) ∘ₗ
        (coinducedRightCosetEquiv H ρ).conj (coind H.subtype ρ g) ∘ₗ
        LinearMap.single ℂ (fun _ : Quotient (QuotientGroup.rightRel H) => V) q) = 0 := by
      ext v
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
        conj_coind_apply, LinearMap.zero_apply]
      rw [Pi.single_eq_of_ne hfix, map_zero]
    rw [hblock, map_zero, extendByZero, dif_neg hnot]

/-! ### The characters -/

variable [Fintype G] [FiniteDimensional ℂ V]

/-- **The character of the coinduced representation.** -/
theorem coind_character_apply (g : G) :
    (coind H.subtype ρ).character g =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        extendByZero H ρ.character (q.out * g * q.out⁻¹) := by
  rw [Representation.character,
    ← LinearMap.trace_conj' (coind H.subtype ρ g) (coinducedRightCosetEquiv H ρ),
    trace_pi_eq_sum_blocks]
  exact Finset.sum_congr rfl fun q _ => trace_block_conj_coind H ρ g q

/-- **The induced character formula.** -/
theorem induced_character_apply (g : G) :
    (Representation.ind H.subtype ρ).character g =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        extendByZero H ρ.character (q.out * g * q.out⁻¹) := by
  letI : H.FiniteIndex := by infer_instance
  letI : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  have h := Representation.char_iso (Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ)))
  exact (congrFun h g).trans (coind_character_apply H ρ g)

/-! ### The averaged form -/

omit [Fintype G] [FiniteDimensional ℂ V] in
/-- A character is a class function. -/
theorem character_conj (a b : H) : ρ.character (a * b * a⁻¹) = ρ.character b := by
  rw [Representation.char_mul_comm, inv_mul_cancel_left]

omit [Fintype G] in
/-- The extension by zero of a class function of `H` is invariant under conjugation by `H`. -/
theorem extendByZero_conj {χ : H → ℂ} (hχ : ∀ a b : H, χ (a * b * a⁻¹) = χ b) (h : H) (x : G) :
    extendByZero H χ ((h : G) * x * (h : G)⁻¹) = extendByZero H χ x := by
  unfold extendByZero
  by_cases hx : x ∈ H
  · have hx' : (h : G) * x * (h : G)⁻¹ ∈ H := H.mul_mem (H.mul_mem h.2 hx) (H.inv_mem h.2)
    rw [dif_pos hx', dif_pos hx]
    exact (congrArg χ (Subtype.ext rfl)).trans (hχ h ⟨x, hx⟩)
  · have hx' : (h : G) * x * (h : G)⁻¹ ∉ H := fun hh => hx (by
      have := H.mul_mem (H.mul_mem (H.inv_mem h.2) hh) h.2
      simpa [mul_assoc] using this)
    rw [dif_neg hx', dif_neg hx]

omit [Fintype G] in
/-- A group is the product of its right cosets and the subgroup, through the representatives of
the cosets. -/
def rightCosetProdEquiv : G ≃ Quotient (QuotientGroup.rightRel H) × H where
  toFun x := (Quotient.mk _ x,
    ⟨x * (Quotient.mk (QuotientGroup.rightRel H) x).out⁻¹, mul_out_inv_mem H x⟩)
  invFun p := (p.2 : G) * p.1.out
  left_inv x := by simp
  right_inv p := by
    obtain ⟨q, h⟩ := p
    have hq : Quotient.mk (QuotientGroup.rightRel H) ((h : G) * q.out) = q := by
      have hrel : (QuotientGroup.rightRel H) ((h : G) * q.out) q.out := by
        rw [QuotientGroup.rightRel_apply]
        simp
      exact (Quotient.sound hrel).trans (Quotient.out_eq q)
    refine Prod.ext hq (Subtype.ext ?_)
    show (h : G) * q.out * (Quotient.mk (QuotientGroup.rightRel H) ((h : G) * q.out)).out⁻¹ = h
    rw [hq]
    simp

omit [FiniteDimensional ℂ V] in
/-- The sum over the conjugates by the group is `|H|` times the sum over the conjugates by the
representatives of the right cosets, for a function invariant under conjugation by `H`. -/
theorem sum_conj_eq_card_mul_sum_out (F : G → ℂ)
    (hF : ∀ (h : H) (x : G), F ((h : G) * x * (h : G)⁻¹) = F x) (g : G) :
    ∑ x : G, F (x * g * x⁻¹) = (Nat.card H : ℂ) *
      ∑ q : Quotient (QuotientGroup.rightRel H), F (q.out * g * q.out⁻¹) := by
  rw [← Equiv.sum_comp (rightCosetProdEquiv H).symm (fun x => F (x * g * x⁻¹)),
    Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hterm : ∀ h : H, F ((rightCosetProdEquiv H).symm (q, h) * g *
      ((rightCosetProdEquiv H).symm (q, h))⁻¹) = F (q.out * g * q.out⁻¹) := fun h => by
    have e : (rightCosetProdEquiv H).symm (q, h) = (h : G) * q.out := rfl
    rw [e, ← hF h (q.out * g * q.out⁻¹)]
    congr 1
    simp [mul_assoc]
  rw [Finset.sum_congr rfl fun h _ => hterm h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

/-- **The induced character formula, averaged over the group.**
`χ_{Ind ρ}(g) = (1/|H|) Σ_{x ∈ G, x g x⁻¹ ∈ H} χ_ρ(x g x⁻¹)`. -/
theorem induced_character_apply_average (g : G) :
    (Representation.ind H.subtype ρ).character g =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendByZero H ρ.character (x * g * x⁻¹) := by
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [induced_character_apply,
    sum_conj_eq_card_mul_sum_out H _ (extendByZero_conj H (character_conj H ρ)) g, ← mul_assoc,
    inv_mul_cancel₀ hcard, one_mul]

end GaloisForLFunctions
