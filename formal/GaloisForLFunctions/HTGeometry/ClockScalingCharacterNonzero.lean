import GaloisForLFunctions.HTGeometry.ClockScalingCharacter
import GaloisForLFunctions.HTGeometry.MultiplicativeMonomialNonzero
import GaloisForLFunctions.HTGeometry.ClockChargeFamilyMultiplicative

/-!
# The charged clock chain over the multiplicative group `C^*`

The clock cocharacter is indexed by `C^*` (nonzero scalars): its semilinear members, their scalings,
and their character are defined only for `λ ≠ 0`.  This file reworks the charged-phase chain
(`ClockScalingCharacter`, `ClockChargeFamilyMultiplicative`, `AlgebraicCharacterMonomial`) with the
membership guard `λ ≠ 0` throughout, so it applies to the actual clock:

* the scaling character is multiplicative on `C^*`;
* a commuting clock family with an anchor scaling diagonalizes to a `C^*`-character;
* a polynomial character is `λ^k` (equation (2)) on `C^*`;
* the charged rigidity `σ y = e · y` follows, since it only tests one nonzero `λ`.

The final charged conclusion needs the clock at a single non-exceptional `λ`, which
`exists_pow_ne_one_ne_neg_one` supplies inside `C^*`, so nothing is lost by restricting the index.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- **Scaling character multiplicative on `C^*`.**  If `ρ_λ q = e(λ) q` for nonzero `λ` and the
family is a homomorphism at `q` on nonzero arguments, then `e(λμ) = e(λ)e(μ)` for nonzero `λ, μ`. -/
theorem scaling_character_multiplicative_of_nonzero
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (ρ : C → (E →ₐ[C] E)) {q : E} (hq : q ≠ 0) (e : C → C)
    (hscale : ∀ lam, lam ≠ 0 → ρ lam q = algebraMap C E (e lam) * q)
    (hmul : ∀ lam mu, lam ≠ 0 → mu ≠ 0 → ρ (lam * mu) q = ρ lam (ρ mu q)) :
    ∀ lam mu, lam ≠ 0 → mu ≠ 0 → e (lam * mu) = e lam * e mu := by
  intro lam mu hlam hmu
  have h := hmul lam mu hlam hmu
  rw [hscale (lam * mu) (mul_ne_zero hlam hmu), hscale mu hmu] at h
  rw [map_mul, AlgHom.commutes, hscale lam hlam, ← mul_assoc, ← map_mul] at h
  have h2 : algebraMap C E (e (lam * mu)) = algebraMap C E (e mu * e lam) :=
    mul_right_cancel₀ hq h
  have h4 : e (lam * mu) - e mu * e lam = 0 := by
    rw [← map_eq_zero (f := algebraMap C E), map_sub, h2, sub_self]
  exact (sub_eq_zero.mp h4).trans (mul_comm _ _)

/-- **Commuting clock family is a `C^*`-character.**  A clock family homomorphic at `q` on nonzero
arguments, each nonzero member Möbius on the generator and commuting with an anchor scaling
`ρ_{ν₀} q = ν q` (`ν ≠ 0, 1, -1`), yields a character `e : C → C` with `ρ_λ q = e(λ)·q` and
`e(λμ) = e(λ)e(μ)` on `C^*`. -/
theorem commuting_family_scaling_character_of_nonzero
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (ρ : C → (E →ₐ[C] E)) (ν₀ : C) {q : E} (hq : q ≠ 0) {ν : C}
    (hν0 : ν ≠ 0) (hν1 : ν ≠ 1) (hνm1 : ν ≠ -1)
    (hanchor : ρ ν₀ q = algebraMap C E ν * q)
    (hlin : ∀ x y z : C, algebraMap C E x + algebraMap C E y * q
        + algebraMap C E z * q ^ 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (hmob : ∀ lam, lam ≠ 0 → ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      ρ lam q * (algebraMap C E c * q + algebraMap C E d)
        = algebraMap C E a * q + algebraMap C E b)
    (hcomm : ∀ lam, lam ≠ 0 → ρ lam (ρ ν₀ q) = ρ ν₀ (ρ lam q))
    (hmul : ∀ lam mu, lam ≠ 0 → mu ≠ 0 → ρ (lam * mu) q = ρ lam (ρ mu q)) :
    ∃ e : C → C, (∀ lam, lam ≠ 0 → ρ lam q = algebraMap C E (e lam) * q)
      ∧ (∀ lam mu, lam ≠ 0 → mu ≠ 0 → e (lam * mu) = e lam * e mu) := by
  have hscale' : ∀ lam, ∃ elam : C, lam ≠ 0 → ρ lam q = algebraMap C E elam * q := by
    intro lam
    by_cases hlam : lam = 0
    · exact ⟨0, fun h => absurd hlam h⟩
    · obtain ⟨a, b, c, d, hinv, hΨq⟩ := hmob lam hlam
      obtain ⟨elam, helam⟩ := commuting_with_scaling_is_scaling (ρ lam) (ρ ν₀) q
        hν0 hν1 hνm1 hinv hlin hanchor hΨq (hcomm lam hlam)
      exact ⟨elam, fun _ => helam⟩
  choose e he using hscale'
  exact ⟨e, he, scaling_character_multiplicative_of_nonzero ρ hq e he hmul⟩

/-- **Equation (2) on `C^*`.**  A clock family scaling `q` by a nonzero polynomial character on
nonzero arguments, `ρ_λ q = P(λ)·q`, and homomorphic at `q` on `C^*`, acts by `ρ_λ q = λ^k·q`. -/
theorem charged_clock_family_pow_of_nonzero
    {C E : Type*} [Field C] [IsAlgClosed C] [Field E] [Algebra C E]
    (ρ : C → (E →ₐ[C] E)) {q : E} (hq : q ≠ 0) {P : Polynomial C} (hP : P ≠ 0)
    (hpoly_scale : ∀ lam, lam ≠ 0 → ρ lam q = algebraMap C E (P.eval lam) * q)
    (hmul : ∀ lam mu, lam ≠ 0 → mu ≠ 0 → ρ (lam * mu) q = ρ lam (ρ mu q)) :
    ∃ k : ℕ, ∀ lam, lam ≠ 0 → ρ lam q = algebraMap C E (lam ^ k) * q := by
  have hpmul : ∀ x y : C, x ≠ 0 → y ≠ 0 → P.eval (x * y) = P.eval x * P.eval y := by
    have h := scaling_character_multiplicative_of_nonzero ρ hq (fun lam => P.eval lam)
      hpoly_scale hmul
    intro x y hx hy; exact h x y hx hy
  have hX : P = Polynomial.X ^ P.natDegree := multiplicative_polynomial_eq_X_pow_of_nonzero hP hpmul
  have hkey : ∀ lam, P.eval lam = lam ^ P.natDegree := by
    intro lam; nth_rewrite 1 [hX]; rw [Polynomial.eval_pow, Polynomial.eval_X]
  exact ⟨P.natDegree, fun lam hlam => by rw [hpoly_scale lam hlam, hkey lam]⟩

/-- **Charged family rigidity on `C^*`.**  With the clock acting by the charged cocharacter
`ρ_λ y = λ^k y` for nonzero `λ` (`k > 0`) and each nonzero `ρ_λ` commuting with the constraint `σ`,
the constraint is multiplication by a single constant.  Only one non-exceptional `λ` is tested. -/
theorem clock_charge_family_multiplicative_of_nonzero
    {C E : Type*} [Field C] [IsAlgClosed C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) (ρ : C → (E →ₐ[C] E)) {y : E} {k : ℕ} (hk : 0 < k)
    (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hderiv : ∀ w : E, σ w′ = (σ w)′)
    (hρ : ∀ lam, lam ≠ 0 → (ρ lam) y = algebraMap C E (lam ^ k) * y)
    (hcomm : ∀ lam, lam ≠ 0 → σ.toAlgHom ((ρ lam) y) = (ρ lam) (σ.toAlgHom y)) :
    ∃ e : C, σ y = algebraMap C E e * y := by
  obtain ⟨lam, hlam0, hlam1, hlamm1⟩ := exists_pow_ne_one_ne_neg_one (C := C) hk
  exact differentialAlgEquiv_generator_multiplicative σ (ρ lam) hy hytop hderiv
    (pow_ne_zero k hlam0) hlam1 hlamm1 (hρ lam hlam0) (hcomm lam hlam0)

/-- **Charged branch on `C^*`, end-to-end.**  A differential automorphism `σ` commuting with a clock
cocharacter whose scaling character is a polynomial of positive degree on `C^*` is multiplication by
a single constant, `σ y = e · y`. -/
theorem charged_clock_polynomial_forces_multiplicative_of_nonzero
    {C E : Type*} [Field C] [IsAlgClosed C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) (ρ : C → (E →ₐ[C] E)) {y : E}
    (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hderiv : ∀ w : E, σ w′ = (σ w)′)
    {P : Polynomial C} (hPdeg : 0 < P.natDegree)
    (hpoly_scale : ∀ lam, lam ≠ 0 → ρ lam y = algebraMap C E (P.eval lam) * y)
    (hmulρ : ∀ lam mu, lam ≠ 0 → mu ≠ 0 → ρ (lam * mu) y = ρ lam (ρ mu y))
    (hcomm : ∀ lam, lam ≠ 0 → σ.toAlgHom ((ρ lam) y) = (ρ lam) (σ.toAlgHom y)) :
    ∃ e : C, σ y = algebraMap C E e * y := by
  have htrans : Transcendental C y := by
    simpa using hypertranscendentalOver_jet_transcendental hy 0
  have hq : y ≠ 0 := by rintro rfl; exact htrans isAlgebraic_zero
  have hP : P ≠ 0 := by rintro rfl; simp at hPdeg
  have hpmul : ∀ x y : C, x ≠ 0 → y ≠ 0 → P.eval (x * y) = P.eval x * P.eval y := by
    have h := scaling_character_multiplicative_of_nonzero ρ hq (fun lam => P.eval lam)
      hpoly_scale hmulρ
    intro x y hx hy'; exact h x y hx hy'
  have hX : P = Polynomial.X ^ P.natDegree := multiplicative_polynomial_eq_X_pow_of_nonzero hP hpmul
  have hρpow : ∀ lam, lam ≠ 0 → ρ lam y = algebraMap C E (lam ^ P.natDegree) * y := by
    intro lam hlam
    rw [hpoly_scale lam hlam]
    congr 2
    nth_rewrite 1 [hX]
    rw [Polynomial.eval_pow, Polynomial.eval_X]
  exact clock_charge_family_multiplicative_of_nonzero σ ρ hPdeg hy hytop hderiv hρpow hcomm

end GaloisForLFunctions.HTGeometry
