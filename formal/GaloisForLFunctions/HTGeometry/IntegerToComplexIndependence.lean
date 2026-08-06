import GaloisForLFunctions.HTGeometry.CharacterLatticeFrequencyRank

/-!
# Independence of integer characters survives base change

A rationally independent family of rational coordinate vectors stays
independent over the complex numbers: injectivity of the assembling map gives a
rational left inverse, whose matrix identity persists under the ring
homomorphism into the complex numbers.

Together with the integer-to-rational step this shows that an integrally
independent family of integer characters is complex independent, which is what
turns a statement about the rank of the active lattice into a statement about
complex spans of gradients.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-- **Rational independence survives base change to the complex numbers.** -/
theorem linearIndependent_complex_of_rat {s : ℕ} {v : Fin s → (d → ℚ)}
    (hv : LinearIndependent ℚ v) :
    LinearIndependent ℂ (fun i : Fin s => fun j : d => ((v i j : ℚ) : ℂ)) := by
  classical
  let Λ : (Fin s → ℚ) →ₗ[ℚ] (d → ℚ) :=
    { toFun := fun a => fun j => ∑ i, a i * v i j
      map_add' := by
        intro a b
        funext j
        show (∑ i, (a i + b i) * v i j) = (∑ i, a i * v i j) + ∑ i, b i * v i j
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => add_mul _ _ _
      map_smul' := by
        intro c a
        funext j
        show (∑ i, (c * a i) * v i j) = c * ∑ i, a i * v i j
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _) }
  have hLam : ∀ (a : Fin s → ℚ) (j : d), Λ a j = ∑ i, a i * v i j := fun _ _ => rfl
  have hker : LinearMap.ker Λ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun a ha => ?_
    refine Fintype.linearIndependent_iff.1 hv a ?_ |> funext
    funext j
    have hj : Λ a j = 0 := congrFun ha j
    rw [hLam] at hj
    show (∑ i, a i • v i) j = (0 : d → ℚ) j
    rw [Finset.sum_apply]
    exact hj
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective Λ hker
  set Lm : Fin s → d → ℚ := fun i j => L (Pi.single j 1) i with hLmdef
  have hsingle : ∀ (w : d → ℚ), w = ∑ j, w j • (Pi.single j (1 : ℚ)) := by
    intro w
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hid : ∀ i k : Fin s,
      (∑ j, Lm i j * v k j) = if i = k then 1 else 0 := by
    intro i k
    have hΛk : Λ (Pi.single k (1 : ℚ)) = v k := by
      funext j
      rw [hLam]
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hl
        simp [Ne.symm hl]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    have hLvk : L (v k) = Pi.single k (1 : ℚ) := by
      rw [← hΛk]
      exact congrFun (congrArg (fun f : (Fin s → ℚ) →ₗ[ℚ] (Fin s → ℚ) => ⇑f) hL)
        (Pi.single k 1)
    have hsum : L (v k) i = ∑ j, v k j * Lm i j := by
      conv_lhs => rw [hsingle (v k)]
      rw [map_sum]
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by
        rw [map_smul]
        rfl
    have hval : (∑ j, v k j * Lm i j) = (Pi.single k 1 : Fin s → ℚ) i := by
      rw [← hsum]
      exact congrFun hLvk i
    rw [Pi.single_apply] at hval
    rw [← hval]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine Fintype.linearIndependent_iff.2 fun a ha i => ?_
  have hcoord : ∀ j : d, ∑ k, a k * ((v k j : ℚ) : ℂ) = 0 := by
    intro j
    have := congrFun ha j
    rw [Finset.sum_apply] at this
    exact this
  have hidC : ∀ k : Fin s,
      (∑ j, ((Lm i j : ℚ) : ℂ) * ((v k j : ℚ) : ℂ)) = if i = k then 1 else 0 := by
    intro k
    by_cases hik : i = k
    · have hq := hid i k
      rw [if_pos hik] at hq
      have hc := congrArg (fun q : ℚ => (q : ℂ)) hq
      push_cast at hc
      rw [if_pos hik]
      exact hc
    · have hq := hid i k
      rw [if_neg hik] at hq
      have hc := congrArg (fun q : ℚ => (q : ℂ)) hq
      push_cast at hc
      rw [if_neg hik]
      exact hc
  calc a i = ∑ k, a k * (if i = k then (1 : ℂ) else 0) := by
        have hterm : ∀ k : Fin s,
            a k * (if i = k then (1 : ℂ) else 0) = if i = k then a k else 0 := by
          intro k
          by_cases hik : i = k
          · rw [if_pos hik, if_pos hik, mul_one]
          · rw [if_neg hik, if_neg hik, mul_zero]
        rw [Finset.sum_congr rfl fun k _ => hterm k,
          Finset.sum_ite_eq Finset.univ i a, if_pos (Finset.mem_univ i)]
    _ = ∑ k, a k * ∑ j, ((Lm i j : ℚ) : ℂ) * ((v k j : ℚ) : ℂ) := by
        exact Finset.sum_congr rfl fun k _ => by rw [hidC k]
    _ = ∑ j, ((Lm i j : ℚ) : ℂ) * ∑ k, a k * ((v k j : ℚ) : ℂ) := by
        have h1 : ∀ k : Fin s,
            a k * ∑ j, ((Lm i j : ℚ) : ℂ) * ((v k j : ℚ) : ℂ)
              = ∑ j, ((Lm i j : ℚ) : ℂ) * (a k * ((v k j : ℚ) : ℂ)) := by
          intro k
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hcoord j, mul_zero]

/-- **Integral independence of integer characters gives complex
independence.** -/
theorem linearIndependent_complex_of_int {s : ℕ} {v : Fin s → (d → ℤ)}
    (hv : LinearIndependent ℤ v) :
    LinearIndependent ℂ (fun i : Fin s => fun j : d => ((v i j : ℤ) : ℂ)) := by
  have h1 : LinearIndependent ℤ (fun i : Fin s => intCharacterToRat (v i)) :=
    hv.map' intCharacterToRat (LinearMap.ker_eq_bot.2 injective_intCharacterToRat)
  have h2 : LinearIndependent ℚ (fun i : Fin s => intCharacterToRat (v i)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1 h1
  have h3 := linearIndependent_complex_of_rat h2
  have hfun : (fun i : Fin s => fun j : d =>
      ((intCharacterToRat (v i) j : ℚ) : ℂ))
      = fun i : Fin s => fun j : d => ((v i j : ℤ) : ℂ) := by
    funext i j
    rw [intCharacterToRat_apply]
    push_cast
    rfl
  rwa [hfun] at h3

end

end GaloisForLFunctions.HTGeometry
