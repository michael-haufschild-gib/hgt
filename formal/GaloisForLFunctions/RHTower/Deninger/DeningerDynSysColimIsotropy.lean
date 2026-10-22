import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysColimFraction
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysIsotropyCondition

/-!
# Isotropy of the `Q^{>0}_0`-action on `X̌ (C)`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Theorem 5.2 and the
remark following it.

A positive rational fixes a point of the colimit exactly when the two Frobenius powers of the
character agree after a further twist, and if the character has finite kernel over an
algebraically closed residue field that forces the rational to be `1`: the isotropy groups of the
`Q^{>0}_0`-action on `X̌ (C)` are trivial at such points.
-/

namespace RHTower

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C] {N₀ : Submonoid ℕ}

/-- **Deninger, Theorem 5.2.**  The isotropy condition on the colimit, read off on characters. -/
theorem deningerColimFrac_eq_self_iff_char (μ ν ν' : N₀) (x : X)
    (P : (X.residueField x)ˣ →* Cˣ) :
    deningerColimFrac N₀ ν ν' (deningerColimMk N₀ μ ⟨x, P⟩) = deningerColimMk N₀ μ ⟨x, P⟩
      ↔ ∃ a b : N₀, (μ : ℕ) * (a : ℕ) = (μ : ℕ) * (b : ℕ) ∧
          P ^ ((ν : ℕ) * (a : ℕ)) = P ^ ((ν' : ℕ) * (b : ℕ)) := by
  rw [deningerColimFrac_eq_self_iff, deningerColimFrobenius_mk, deningerColimFrobenius_mk,
    deningerColimMk_eq_iff]
  constructor
  · rintro ⟨a, b, h1, h2⟩
    refine ⟨a, b, h1, ?_⟩
    rw [deningerCharFrobenius_comp, deningerCharFrobenius_comp] at h2
    exact (deningerCharFrobenius_eq_iff x P P ((ν : ℕ) * (a : ℕ)) ((ν' : ℕ) * (b : ℕ))).1 h2
  · rintro ⟨a, b, h1, h2⟩
    refine ⟨a, b, h1, ?_⟩
    rw [deningerCharFrobenius_comp, deningerCharFrobenius_comp]
    exact (deningerCharFrobenius_eq_iff x P P ((ν : ℕ) * (a : ℕ)) ((ν' : ℕ) * (b : ℕ))).2 h2

/-- **Deninger, Theorem 5.2, the remark.**  Over an algebraically closed residue field a character
with finite kernel has trivial isotropy for the `Q^{>0}_0`-action. -/
theorem deningerColimFrac_isotropy_trivial (h0 : ∀ n ∈ N₀, n ≠ 0) (μ ν ν' : N₀) (x : X)
    [IsAlgClosed (X.residueField x)] (P : (X.residueField x)ˣ →* Cˣ) [Finite ↥P.ker]
    (h : deningerColimFrac N₀ ν ν' (deningerColimMk N₀ μ ⟨x, P⟩)
      = deningerColimMk N₀ μ ⟨x, P⟩) : (ν : ℕ) = (ν' : ℕ) := by
  obtain ⟨a, b, h1, h2⟩ := (deningerColimFrac_eq_self_iff_char μ ν ν' x P).1 h
  have hμ : (μ : ℕ) ≠ 0 := h0 _ μ.2
  have ha : (a : ℕ) ≠ 0 := h0 _ a.2
  have hab : (a : ℕ) = (b : ℕ) := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hμ) h1
  rw [← hab] at h2
  have hstep : (ν : ℕ) * (a : ℕ) = ((ν' : ℕ) * (a : ℕ)) * 1 := by
    refine deningerTwistExponent_eq_of_isotropy (MulEquiv.refl ((X.residueField x)ˣ)) 1
      (fun y => (pow_one y).symm) ((ν : ℕ) * (a : ℕ)) ((ν' : ℕ) * (a : ℕ)) P ?_
    have hcomp : P.comp (MulEquiv.refl ((X.residueField x)ˣ)).toMonoidHom = P := rfl
    rw [hcomp]
    exact h2
  rw [mul_one] at hstep
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ha) hstep

/-- **Deninger, Theorem 5.2.**  In the Galois-twisted situation — the isotropy condition on
`X̌₀ (C) = X̌ (C) / G` — the rational is the `c`-th power operator: if the character satisfies
`P^{ν a} = (P ∘ σ)^{ν' a}` for the `c`-th power automorphism `σ` of the residue field and has
finite kernel, then `ν = ν' c`.  For `σ = Frobenius^a` this is `q = p^a`. -/
theorem deningerColimFracTwisted_exponent (h0 : ∀ n ∈ N₀, n ≠ 0) (a ν ν' : N₀) (x : X)
    [IsAlgClosed (X.residueField x)] (P : (X.residueField x)ˣ →* Cˣ) [Finite ↥P.ker]
    (σ : (X.residueField x)ˣ ≃* (X.residueField x)ˣ) (c : ℕ) (hσ : ∀ y, σ y = y ^ c)
    (h : P ^ ((ν : ℕ) * (a : ℕ)) = (P.comp σ.toMonoidHom) ^ ((ν' : ℕ) * (a : ℕ))) :
    (ν : ℕ) = (ν' : ℕ) * c := by
  have hstep := deningerTwistExponent_eq_of_isotropy σ c hσ ((ν : ℕ) * (a : ℕ))
    ((ν' : ℕ) * (a : ℕ)) P h
  have ha : (a : ℕ) ≠ 0 := h0 _ a.2
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ha) ?_
  rw [hstep]
  ring

end RHTower
