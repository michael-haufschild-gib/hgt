import GaloisForLFunctions.RHTower.DeningerDynSysCharacterPoints
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The image of the Frobenius operator on character points

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 7.3 (`t9`),
equation (21).

Over an algebraically closed residue field the `ν`-th power map on the unit group is surjective
with kernel the `ν`-th roots of unity, so a character is a `ν`-th power exactly when it is trivial
on the `ν`-th roots of unity.  Hence

`F_ν (X̂ (C)) = {(x, ψ) | ψ is trivial on μ_ν (κ (x))}` .

Together with the injectivity of `F_ν` this identifies `X̂ (C)` with `F_ν (X̂ (C))` as sets.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C]

/-- Over an algebraically closed field the `ν`-th power map on the unit group is surjective. -/
theorem deningerUnitsPow_surjective {k : Type u} [Field k] [IsAlgClosed k] {ν : ℕ} (hν : 0 < ν) :
    Function.Surjective (powMonoidHom ν : kˣ →* kˣ) := by
  intro u
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((u : k)) hν
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, zero_pow hν.ne'] at hw
    exact u.ne_zero hw.symm
  refine ⟨Units.mk0 w hw0, ?_⟩
  apply Units.ext
  show w ^ ν = (u : k)
  exact hw

/-- **Deninger, Lemma 7.3 (`t9`).**  Over an algebraically closed field a character of the unit
group is a `ν`-th power exactly when it is trivial on the `ν`-th roots of unity. -/
theorem deningerChar_exists_pow_iff {k : Type u} [Field k] [IsAlgClosed k] {ν : ℕ} (hν : 0 < ν)
    (ψ : kˣ →* Cˣ) :
    (∃ χ : kˣ →* Cˣ, χ ^ ν = ψ) ↔ ∀ u : kˣ, u ^ ν = 1 → ψ u = 1 := by
  constructor
  · rintro ⟨χ, rfl⟩ u hu
    show χ u ^ ν = 1
    rw [← map_pow, hu, map_one]
  · intro hψ
    have hsurj : Function.Surjective (powMonoidHom ν : kˣ →* kˣ) :=
      deningerUnitsPow_surjective hν
    have hker : (powMonoidHom ν : kˣ →* kˣ).ker ≤ ψ.ker := by
      intro u hu
      exact hψ u hu
    set e : kˣ ⧸ (powMonoidHom ν : kˣ →* kˣ).ker ≃* kˣ :=
      QuotientGroup.quotientKerEquivOfSurjective _ hsurj with he
    refine ⟨(QuotientGroup.lift _ ψ hker).comp (e.symm : kˣ →* kˣ ⧸ _), ?_⟩
    refine MonoidHom.ext fun u => ?_
    show ((QuotientGroup.lift _ ψ hker) (e.symm u)) ^ ν = ψ u
    obtain ⟨w, hw⟩ := hsurj u
    have hew : e.symm u = QuotientGroup.mk w := by
      rw [he]
      refine (MulEquiv.symm_apply_eq _).2 ?_
      rw [QuotientGroup.quotientKerEquivOfSurjective]
      exact hw.symm
    rw [hew, QuotientGroup.lift_mk, ← map_pow]
    show ψ (w ^ ν) = ψ u
    rw [show w ^ ν = u from hw]

/-- **Deninger, Lemma 7.3 (`t9`), equation (21).**  The image of the Frobenius operator on the
character points consists of the points whose character is trivial on the `ν`-th roots of unity. -/
theorem deningerCharFrobenius_range (halg : ∀ x : X, IsAlgClosed (X.residueField x))
    {ν : ℕ} (hν : 0 < ν) :
    Set.range (deningerCharFrobenius (X := X) (C := C) ν)
      = {P : DeningerCharPoints X C | ∀ u : (X.residueField P.1)ˣ, u ^ ν = 1 → P.2 u = 1} := by
  ext P
  haveI := halg P.1
  constructor
  · rintro ⟨Q, rfl⟩ u hu
    exact (deningerChar_exists_pow_iff hν (Q.2 ^ ν)).1 ⟨Q.2, rfl⟩ u hu
  · intro hP
    obtain ⟨χ, hχ⟩ := (deningerChar_exists_pow_iff hν P.2).2 hP
    exact ⟨⟨P.1, χ⟩, Sigma.ext rfl (heq_of_eq hχ)⟩

end RHTower
