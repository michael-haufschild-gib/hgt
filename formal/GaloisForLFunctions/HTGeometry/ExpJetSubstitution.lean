import GaloisForLFunctions.HTGeometry.ExpJetTransfer

/-!
# The exponential jet transfer is an invertible substitution

Written in the variables `Yⱼ = exp(az)ʲ · g⁽ʲ⁾(exp(az))`, the transfer identity is a linear change of
variables with *constant* coefficients: `f⁽ᵏ⁾ = ∑ⱼ c_{k,j} Yⱼ`.  Its matrix is triangular with
diagonal `aᵏ`, so for `a ≠ 0` it is invertible, and the induced substitution on differential
polynomials is injective.

Injectivity is proved through evaluation rather than through an explicit inverse matrix: the linear
map is injective by triangular back-substitution, hence surjective on a finite-dimensional space,
hence every evaluation point of the source is hit — so a substituted polynomial vanishing identically
forces the original to vanish at every point, and a polynomial over an infinite domain vanishing
everywhere is zero.

* `expJetLinear`, **`expJetLinear_injective`**, `expJetLinear_surjective`;
* `expJetSubst` — the substitution on differential polynomials;
* **`bind₁_expJetSubst_ne_zero`** — it preserves nonzeroness.
-/

open Finset MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- The transfer matrix acting on the jet space. -/
noncomputable def expJetLinear (a : ℂ) (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v := fun k => ∑ i : Fin (n + 1), expJetCoeff a (k : ℕ) (i : ℕ) * v i
  map_add' u v := by
    funext k
    simp only [Pi.add_apply, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  map_smul' r v := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun i _ => by ring

@[simp] theorem expJetLinear_apply (a : ℂ) (n : ℕ) (v : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    expJetLinear a n v k = ∑ i : Fin (n + 1), expJetCoeff a (k : ℕ) (i : ℕ) * v i := rfl

/-- **Triangular back-substitution.**  The transfer matrix is injective whenever `a ≠ 0`: its
diagonal entries are the units `aᵏ`, and everything above the diagonal vanishes. -/
theorem expJetLinear_injective {a : ℂ} (ha : a ≠ 0) (n : ℕ) :
    Function.Injective (expJetLinear a n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hzero : ∀ m : ℕ, ∀ k : Fin (n + 1), (k : ℕ) = m → v k = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
        intro k hk
        have hk0 : expJetLinear a n v k = 0 := by rw [hv]; rfl
        rw [expJetLinear_apply] at hk0
        have hsingle : ∑ i : Fin (n + 1), expJetCoeff a (k : ℕ) (i : ℕ) * v i
            = expJetCoeff a (k : ℕ) (k : ℕ) * v k := by
          refine sum_eq_single_of_mem k (mem_univ k) (fun i _ hik => ?_)
          rcases lt_or_gt_of_ne (fun h => hik (Fin.ext h) : (i : ℕ) ≠ (k : ℕ)) with hlt | hgt
          · rw [ih (i : ℕ) (by omega) i rfl, mul_zero]
          · rw [expJetCoeff_eq_zero_of_lt a hgt, zero_mul]
        rw [hsingle, expJetCoeff_diag] at hk0
        exact (mul_eq_zero.mp hk0).resolve_left (pow_ne_zero _ ha)
  funext k
  exact hzero (k : ℕ) k rfl

theorem expJetLinear_surjective {a : ℂ} (ha : a ≠ 0) (n : ℕ) :
    Function.Surjective (expJetLinear a n) :=
  (LinearMap.injective_iff_surjective).mp (expJetLinear_injective ha n)

/-- The substitution on differential polynomials induced by the transfer. -/
noncomputable def expJetSubst (a : ℂ) (n : ℕ) : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ :=
  fun k => ∑ i : Fin (n + 1), C (expJetCoeff a (k : ℕ) (i : ℕ)) * X i

theorem eval_expJetSubst (a : ℂ) (n : ℕ) (v : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    eval v (expJetSubst a n k) = expJetLinear a n v k := by
  rw [expJetSubst, expJetLinear_apply, map_sum]
  exact sum_congr rfl fun i _ => by simp

/-- **The substitution preserves nonzeroness.**  A relation that becomes trivial after transfer was
already trivial. -/
theorem bind₁_expJetSubst_ne_zero {a : ℂ} (ha : a ≠ 0) {n : ℕ}
    {R : MvPolynomial (Fin (n + 1)) ℂ} (hR : R ≠ 0) : bind₁ (expJetSubst a n) R ≠ 0 := by
  intro h0
  apply hR
  refine MvPolynomial.funext fun u => ?_
  obtain ⟨v, hv⟩ := expJetLinear_surjective ha n u
  have hev : eval₂Hom (RingHom.id ℂ) v (bind₁ (expJetSubst a n) R) = 0 := by
    rw [h0, map_zero]
  rw [eval₂Hom_bind₁] at hev
  have hpt : (fun k => eval₂Hom (RingHom.id ℂ) v (expJetSubst a n k)) = u := by
    funext k
    rw [show eval₂Hom (RingHom.id ℂ) v (expJetSubst a n k) = eval v (expJetSubst a n k) from rfl,
      eval_expJetSubst, hv]
  rw [hpt] at hev
  rw [show eval u R = eval₂Hom (RingHom.id ℂ) u R from rfl, hev, map_zero]

end GaloisForLFunctions.HTGeometry
