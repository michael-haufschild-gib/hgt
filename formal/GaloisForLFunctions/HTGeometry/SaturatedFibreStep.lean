import GaloisForLFunctions.HTGeometry.FamilyTorsionFree

/-!
# The two fibres as ideals, and the saturation step

```text
famEval                        evaluation of the extra variable at a point of the base line
map_famEval_zero_familyIdeal   ** the special fibre of the family ideal is the initial ideal **
map_famEval_one_familyIdeal    ** the generic fibre is the ideal itself **
saturated_sup_span_C
    ** adjoining a constant that is a nonzerodivisor on the special fibre keeps the family
       saturated **
```

The two fibre identities are the corpus's `familyIdeal_sup_X` and `familyIdeal_sup_X_sub_one` read
through the evaluation map, whose kernel is the ideal being adjoined there.

The saturation step is the elementary form of the local criterion of flatness.  If `t·F = G + l·H`
with `G` in the family ideal, evaluating at `t = 0` puts `l · H(0)` in the special fibre, so `H(0)`
lies there too; subtracting a family element with the same value writes `H = G' + t·H''`, and then
`t·(F − l·H'')` lies in the family ideal, which is saturated.  This is what lets a regular sequence
on the special fibre be carried along the family one element at a time.
-/

namespace GaloisForLFunctions.HTGeometry
open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- Evaluating the extra variable at a point of the base line. -/
noncomputable abbrev famEval (a : MvPolynomial σ K) :
    Polynomial (MvPolynomial σ K) →+* MvPolynomial σ K :=
  Polynomial.evalRingHom a

theorem famEval_comp_C (a : MvPolynomial σ K) :
    (famEval a).comp Polynomial.C = RingHom.id (MvPolynomial σ K) :=
  RingHom.ext fun p => by simp [famEval]

theorem famEval_surjective (a : MvPolynomial σ K) : Function.Surjective (famEval a) := by
  intro p
  exact ⟨Polynomial.C p, by simp [famEval]⟩

/-- **The special fibre of the family ideal is the initial ideal.** -/
theorem map_famEval_zero_familyIdeal (w : σ → ℤ) (I : Ideal (MvPolynomial σ K)) :
    Ideal.map (famEval (0 : MvPolynomial σ K)) (familyIdeal w I) = initialIdeal w I := by
  have hsup := congrArg (Ideal.map (famEval (0 : MvPolynomial σ K))) (familyIdeal_sup_X w I)
  rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_span, Ideal.map_map, famEval_comp_C,
    Ideal.map_id] at hsup
  simpa [famEval] using hsup

/-- **The generic fibre of the family ideal is the ideal.** -/
theorem map_famEval_one_familyIdeal (w : σ → ℤ) (I : Ideal (MvPolynomial σ K)) :
    Ideal.map (famEval (1 : MvPolynomial σ K)) (familyIdeal w I) = I := by
  have hsup := congrArg (Ideal.map (famEval (1 : MvPolynomial σ K)))
    (familyIdeal_sup_X_sub_one w I)
  rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_span, Ideal.map_map, famEval_comp_C,
    Ideal.map_id] at hsup
  simpa [famEval] using hsup

theorem map_famEval_sup_span_C (a : MvPolynomial σ K) (A : Ideal (Polynomial (MvPolynomial σ K)))
    (l : MvPolynomial σ K) :
    Ideal.map (famEval a) (A ⊔ Ideal.span {Polynomial.C l})
      = Ideal.map (famEval a) A ⊔ Ideal.span {l} := by
  rw [Ideal.map_sup, Ideal.map_span]
  congr 1
  simp [famEval]

/-- **The saturation step.**  Adjoining a constant that is a nonzerodivisor on the special fibre
keeps the family saturated in the extra variable. -/
theorem saturated_sup_span_C {A : Ideal (Polynomial (MvPolynomial σ K))}
    (hsat : ∀ F : Polynomial (MvPolynomial σ K), Polynomial.X * F ∈ A → F ∈ A)
    {l : MvPolynomial σ K}
    (hreg : ∀ g : MvPolynomial σ K,
      l * g ∈ Ideal.map (famEval (0 : MvPolynomial σ K)) A →
        g ∈ Ideal.map (famEval (0 : MvPolynomial σ K)) A)
    (F : Polynomial (MvPolynomial σ K))
    (hF : Polynomial.X * F ∈ A ⊔ Ideal.span {Polynomial.C l}) :
    F ∈ A ⊔ Ideal.span {Polynomial.C l} := by
  classical
  obtain ⟨G, hG, y, hy, hsum⟩ := Submodule.mem_sup.mp hF
  obtain ⟨H, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  -- evaluate at zero
  have hzero : famEval (0 : MvPolynomial σ K) G + l * famEval (0 : MvPolynomial σ K) H = 0 := by
    have hev := congrArg (famEval (0 : MvPolynomial σ K)) hsum
    rw [map_add, map_mul, map_mul] at hev
    have hX : famEval (0 : MvPolynomial σ K) Polynomial.X = 0 := by simp [famEval]
    have hC : famEval (0 : MvPolynomial σ K) (Polynomial.C l) = l := by simp [famEval]
    rw [hX, hC, zero_mul] at hev
    linear_combination hev
  have hmulmem : l * famEval (0 : MvPolynomial σ K) H
      ∈ Ideal.map (famEval (0 : MvPolynomial σ K)) A := by
    have hGmem : famEval (0 : MvPolynomial σ K) G
        ∈ Ideal.map (famEval (0 : MvPolynomial σ K)) A := Ideal.mem_map_of_mem _ hG
    have : l * famEval (0 : MvPolynomial σ K) H = -(famEval (0 : MvPolynomial σ K) G) := by
      linear_combination hzero
    rw [this]
    exact neg_mem hGmem
  obtain ⟨G', hG', hG'eq⟩ := Ideal.mem_map_iff_of_surjective _ (famEval_surjective _) |>.mp
    (hreg _ hmulmem)
  -- the difference is divisible by the extra variable
  have hdvd : Polynomial.X ∣ (H - G') := by
    rw [Polynomial.X_dvd_iff]
    have hc : (H - G').coeff 0
        = famEval (0 : MvPolynomial σ K) H - famEval (0 : MvPolynomial σ K) G' := by
      simp [famEval, ← Polynomial.coeff_zero_eq_eval_zero]
    rw [hc, hG'eq, sub_self]
  obtain ⟨H'', hH''⟩ := hdvd
  have hkey : Polynomial.X * (F - Polynomial.C l * H'') ∈ A := by
    have hHeq : H = G' + Polynomial.X * H'' := by
      have := hH''
      linear_combination this
    have hexp : Polynomial.X * (F - Polynomial.C l * H'')
        = G + Polynomial.C l * G' := by
      rw [mul_sub, ← hsum, hHeq]
      ring
    rw [hexp]
    exact Ideal.add_mem _ hG (Ideal.mul_mem_left _ _ hG')
  refine Submodule.mem_sup.mpr ⟨F - Polynomial.C l * H'', hsat _ hkey,
    Polynomial.C l * H'', Ideal.mem_span_singleton'.mpr ⟨H'', mul_comm _ _⟩, by ring⟩

end GaloisForLFunctions.HTGeometry
