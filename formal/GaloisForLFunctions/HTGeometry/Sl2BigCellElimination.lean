import GaloisForLFunctions.HTGeometry.Sl2BigCellCartier
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialBaseChange
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Eliminating the fourth matrix coordinate on the big cell of `SL₂`

On the locus `X₀₀ ≠ 0` of `SL₂` the lower-right entry is determined by the other three, and so is
each of its jets: differentiating `X₀₀·X₁₁ = 1 + X₀₁·X₁₀` gives

```
    X₀₀^{k+1} · X₁₁^{(k)} = θ_k,     θ_0 = 1 + X₀₁X₁₀,
    θ_{k+1} = X₀₀ · δθ_k − (k+1) · X₀₀' · θ_k,
```

with every `θ_k` a differential polynomial in the three coordinates `X₀₀, X₀₁, X₁₀`.  Substituting
`X₁₁^{(k)} ↦ θ_k / X₀₀^{k+1}` is therefore an ordinary algebra map into the localization of the
three-variable differential polynomial ring away from `X₀₀`, and clearing the denominator produces,
for every differential polynomial `P` in the four matrix coordinates, an `N` and a differential
polynomial `Q` in the three coordinates with `Q(g) = g₀₀^N · P(g)` on the big cell of `SL₂`.

No differential structure on the localization is needed: the substitution is performed on the jet
variables, which is a plain `MvPolynomial` evaluation.

* `elimTheta`, `evalOver_elimTheta` — the elimination polynomials and their values;
* `exists_bigCell_elimination` — **the elimination itself.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]

/-! ### The three big-cell coordinates -/

/-- The three matrix coordinates other than the lower-right one. -/
def bigCellIndex : Fin 3 → Fin 2 × Fin 2 :=
  ![((0 : Fin 2), (0 : Fin 2)), ((0 : Fin 2), (1 : Fin 2)), ((1 : Fin 2), (0 : Fin 2))]

/-- A one-sided inverse of `bigCellIndex`, arbitrary at the lower-right coordinate. -/
def bigCellCoord (q : Fin 2 × Fin 2) : Fin 3 :=
  if q = ((0 : Fin 2), (0 : Fin 2)) then 0 else if q = ((0 : Fin 2), (1 : Fin 2)) then 1 else 2

theorem bigCellIndex_bigCellCoord {q : Fin 2 × Fin 2} (hq : q ≠ ((1 : Fin 2), (1 : Fin 2))) :
    bigCellIndex (bigCellCoord q) = q := by
  obtain ⟨i, j⟩ := q
  fin_cases i <;> fin_cases j <;> simp_all [bigCellIndex, bigCellCoord]

theorem bigCellIndex_ne (i : Fin 3) : bigCellIndex i ≠ ((1 : Fin 2), (1 : Fin 2)) := by
  fin_cases i <;> simp [bigCellIndex]

/-- The three big-cell coordinates of a matrix. -/
def bigCellTriple (g : Matrix (Fin 2) (Fin 2) C) : Fin 3 → C :=
  fun i => g (bigCellIndex i).1 (bigCellIndex i).2

omit [Field C] [Differential C] in
theorem bigCellTriple_eq (g : Matrix (Fin 2) (Fin 2) C) :
    bigCellTriple g = fun i => (fun q : Fin 2 × Fin 2 => g q.1 q.2) (bigCellIndex i) := rfl

omit [Field C] [Differential C] in
@[simp] theorem bigCellTriple_zero (g : Matrix (Fin 2) (Fin 2) C) :
    bigCellTriple g 0 = g 0 0 := by simp [bigCellTriple, bigCellIndex]

omit [Field C] [Differential C] in
@[simp] theorem bigCellTriple_one (g : Matrix (Fin 2) (Fin 2) C) :
    bigCellTriple g 1 = g 0 1 := by simp [bigCellTriple, bigCellIndex]

omit [Field C] [Differential C] in
@[simp] theorem bigCellTriple_two (g : Matrix (Fin 2) (Fin 2) C) :
    bigCellTriple g 2 = g 1 0 := by simp [bigCellTriple, bigCellIndex]

/-! ### The elimination polynomials -/

/-- `X₀₀` inside the three-variable differential polynomial ring. -/
def elimA (C : Type*) [Field C] [Differential C] : DifferentialPolynomial (Fin 3) C :=
  MvPolynomial.X ((0 : Fin 3), 0)

/-- The elimination polynomials: `θ_k` satisfies `X₀₀^{k+1} · X₁₁^{(k)} = θ_k` on `SL₂`. -/
def elimTheta (C : Type*) [Field C] [Differential C] : ℕ → DifferentialPolynomial (Fin 3) C
  | 0 => 1 + MvPolynomial.X ((1 : Fin 3), 0) * MvPolynomial.X ((2 : Fin 3), 0)
  | (k + 1) => elimA C * differentialPolynomialOverDerivation (Fin 3) C (elimTheta C k)
      - MvPolynomial.C ((k + 1 : ℕ) : C) * MvPolynomial.X ((0 : Fin 3), 1) * elimTheta C k

theorem evalOver_elimA (g : Matrix (Fin 2) (Fin 2) C) :
    differentialPolynomialEvalOver (K := C) (bigCellTriple g) (elimA C) = g 0 0 := by
  rw [elimA, differentialPolynomialEvalOver_X, differentialJet_zero]
  rfl

/-- **The elimination polynomials compute the jets of the lower-right entry.** -/
theorem evalOver_elimTheta {g : Matrix (Fin 2) (Fin 2) C} (hdet : g.det = 1) :
    ∀ k : ℕ, differentialPolynomialEvalOver (K := C) (bigCellTriple g) (elimTheta C k)
      = (g 0 0) ^ (k + 1) * differentialJet k (g 1 1) := by
  have hdet' : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  intro k
  induction k with
  | zero =>
      rw [elimTheta]
      simp only [map_add, map_one, map_mul, differentialPolynomialEvalOver_X, differentialJet_zero,
        bigCellTriple_one, bigCellTriple_two, zero_add, pow_one]
      linear_combination -hdet'
  | succ k ih =>
      rw [elimTheta]
      rw [map_sub, map_mul, map_mul, map_mul, evalOver_elimA,
        differentialPolynomialEvalOver_derivation, ih, differentialPolynomialEvalOver_C,
        differentialPolynomialEvalOver_X]
      have hjet : differentialJet 1 (bigCellTriple g (0 : Fin 3)) = (g 0 0)′ := by
        rw [differentialJet_succ, differentialJet_zero]
        rfl
      rw [hjet]
      have hpow : ∀ n : ℕ, ((g 0 0) ^ (n + 1))′ = ((n : C) + 1) * (g 0 0) ^ n * (g 0 0)′ := by
        intro n
        induction n with
        | zero => simp
        | succ m ihm =>
            rw [pow_succ, Derivation.leibniz]
            simp only [smul_eq_mul]
            rw [ihm]
            push_cast
            ring
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [hpow k, ← differentialJet_succ]
      push_cast
      ring

/-! ### The substitution -/

variable (C)

/-- The localization of the three-variable differential polynomial ring away from `X₀₀`. -/
abbrev ElimLoc : Type _ := Localization.Away (elimA C)

/-- The substitution point: `X₁₁^{(k)} ↦ θ_k / X₀₀^{k+1}`, the other coordinates unchanged. -/
def elimPoint : ((Fin 2 × Fin 2) × ℕ) → ElimLoc C := fun v =>
  if v.1 = ((1 : Fin 2), (1 : Fin 2)) then
    algebraMap (DifferentialPolynomial (Fin 3) C) (ElimLoc C) (elimTheta C v.2)
      * IsLocalization.Away.invSelf (elimA C) ^ (v.2 + 1)
  else
    algebraMap (DifferentialPolynomial (Fin 3) C) (ElimLoc C)
      (MvPolynomial.X (bigCellCoord v.1, v.2))

/-- The substitution, as a ring homomorphism. -/
def elimHom : DifferentialPolynomial (Fin 2 × Fin 2) C →+* ElimLoc C :=
  MvPolynomial.eval₂Hom
    ((algebraMap (DifferentialPolynomial (Fin 3) C) (ElimLoc C)).comp
      (MvPolynomial.C : C →+* DifferentialPolynomial (Fin 3) C)) (elimPoint C)

variable {C}

/-- **Eliminating the lower-right coordinate.**  Every differential polynomial in the four matrix
coordinates agrees, up to a power of `X₀₀`, with a differential polynomial in the other three, at
every point of `SL₂` with invertible upper-left entry. -/
theorem exists_bigCell_elimination (P : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    ∃ (N : ℕ) (Q : DifferentialPolynomial (Fin 2 × Fin 2) C),
      (∀ v ∈ Q.vars, v.1 ≠ ((1 : Fin 2), (1 : Fin 2))) ∧
      ∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 → g 0 0 ≠ 0 →
        differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => g q.1 q.2) Q
          = (g 0 0) ^ N *
            differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => g q.1 q.2) P := by
  classical
  obtain ⟨⟨Q₀, y⟩, hy⟩ := IsLocalization.surj (Submonoid.powers (elimA C)) (elimHom C P)
  obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff (y : DifferentialPolynomial (Fin 3) C)
    (elimA C)).mp y.2
  refine ⟨N, differentialRename bigCellIndex Q₀, ?_, ?_⟩
  · intro v hv
    have hsub := MvPolynomial.vars_rename (fun p : Fin 3 × ℕ => (bigCellIndex p.1, p.2)) Q₀
    have hv' := hsub hv
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hv'
    rw [← hw]
    exact bigCellIndex_ne w.1
  · intro g hdet hg00
    set ev : DifferentialPolynomial (Fin 3) C →+* C :=
      (differentialPolynomialEvalOver (K := C) (bigCellTriple g)).toRingHom with hev
    have hunit : ∀ z : Submonoid.powers (elimA C), IsUnit (ev z) := by
      rintro ⟨z, m, rfl⟩
      have : ev (elimA C ^ m) = (g 0 0) ^ m := by
        rw [map_pow]
        congr 1
        exact evalOver_elimA g
      rw [this]
      exact (isUnit_iff_ne_zero.mpr (pow_ne_zero m hg00))
    set lift : ElimLoc C →+* C := IsLocalization.lift hunit with hlift
    -- the lifted substitution is evaluation at `g`
    have hcomp : lift.comp (elimHom C)
        = (differentialPolynomialEvalOver (K := C)
            (fun q : Fin 2 × Fin 2 => g q.1 q.2)).toRingHom := by
      refine MvPolynomial.ringHom_ext ?_ ?_
      · intro a
        show lift (elimHom C (MvPolynomial.C a)) = _
        rw [elimHom, MvPolynomial.eval₂Hom_C]
        rw [hlift, RingHom.comp_apply, IsLocalization.lift_eq]
        simp [hev]
      · rintro ⟨qq, k⟩
        show lift (elimHom C (MvPolynomial.X (qq, k)))
          = differentialPolynomialEvalOver (K := C) (fun r : Fin 2 × Fin 2 => g r.1 r.2)
              (MvPolynomial.X (qq, k))
        rw [elimHom, MvPolynomial.eval₂Hom_X']
        show lift (elimPoint C (qq, k)) = _
        rw [differentialPolynomialEvalOver_X]
        by_cases hq : qq = ((1 : Fin 2), (1 : Fin 2))
        · rw [elimPoint, if_pos hq]
          rw [map_mul, map_pow]
          have hinv : lift (IsLocalization.Away.invSelf (elimA C)) = (g 0 0)⁻¹ := by
            have h1 : lift (algebraMap (DifferentialPolynomial (Fin 3) C) (ElimLoc C) (elimA C)
                * IsLocalization.Away.invSelf (elimA C)) = 1 := by
              rw [IsLocalization.Away.mul_invSelf, map_one]
            rw [map_mul, hlift, IsLocalization.lift_eq] at h1
            have h2 : ev (elimA C) = g 0 0 := evalOver_elimA g
            rw [h2] at h1
            field_simp
            linear_combination h1
          rw [hinv, hlift, IsLocalization.lift_eq]
          have hth : ev (elimTheta C k) = (g 0 0) ^ (k + 1) * differentialJet k (g 1 1) :=
            evalOver_elimTheta hdet k
          rw [hth, hq, inv_pow, mul_comm ((g 0 0) ^ (k + 1)) _, mul_assoc,
            mul_inv_cancel₀ (pow_ne_zero _ hg00), mul_one]
        · rw [elimPoint, if_neg hq, hlift, IsLocalization.lift_eq]
          show differentialPolynomialEvalOver (K := C) (bigCellTriple g)
            (MvPolynomial.X (bigCellCoord qq, k)) = _
          rw [differentialPolynomialEvalOver_X]
          congr 1
          show bigCellTriple g (bigCellCoord qq) = g qq.1 qq.2
          rw [bigCellTriple, bigCellIndex_bigCellCoord hq]
    -- transport the localization identity
    have hkey : lift (elimHom C P) * (g 0 0) ^ N = ev Q₀ := by
      have := congrArg lift hy
      rw [map_mul, hlift, IsLocalization.lift_eq, IsLocalization.lift_eq] at this
      rw [← hN] at this
      rw [map_pow] at this
      have h2 : ev (elimA C) = g 0 0 := evalOver_elimA g
      rw [h2] at this
      exact this
    have hP : lift (elimHom C P)
        = differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => g q.1 q.2) P := by
      have := congrArg (fun f : DifferentialPolynomial (Fin 2 × Fin 2) C →+* C => f P) hcomp
      exact this
    rw [differentialPolynomialEvalOver_differentialRename, ← bigCellTriple_eq]
    show ev Q₀ = _
    rw [← hkey, hP]
    ring

end

end GaloisForLFunctions.HTGeometry
