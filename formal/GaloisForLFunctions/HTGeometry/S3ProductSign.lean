import GaloisForLFunctions.HTGeometry.S3SignConjugation

/-!
# Independent signs force the full product of cubic permutation groups

A subdirect product of S3 copies has no residual entanglement once its sign
patterns are independent. Squaring and conjugation isolate each coordinate A3.
-/

open Equiv.Perm
namespace GaloisForLFunctions.HTGeometry

/-- A subdirect product of S3 copies with every sign pattern is the full product. -/
theorem s3_subgroup_eq_top_of_sign_surjective {ι : Type*} [Finite ι]
    (H : Subgroup (ι → Equiv.Perm (Fin 3)))
    (hcoord : ∀ i, Function.Surjective (fun h : H => (h : ι → Equiv.Perm (Fin 3)) i))
    (hsign : Function.Surjective
      (fun h : H => fun i => sign ((h : ι → Equiv.Perm (Fin 3)) i))) : H = ⊤ := by
  classical
  have hsingle (i : ι) (p : Equiv.Perm (Fin 3)) (hp : sign p = 1) :
      Pi.mulSingle i p ∈ H := by
    obtain ⟨x, hx⟩ := hcoord i cubicPermRotation
    let r : ι → Equiv.Perm (Fin 3) := (x : ι → Equiv.Perm (Fin 3)) ^ 2
    have hrH : r ∈ H := H.pow_mem x.property 2
    have hrs (j : ι) : sign (r j) = 1 := by
      simp only [r, Pi.pow_apply, map_pow, Int.units_pow_two]
    have hri : r i ≠ 1 := by
      intro h
      have h2 : cubicPermRotation ^ 2 = 1 := by simpa only [r, Pi.pow_apply, hx] using h
      have h3 := cubic_even_pow_three cubicPermRotation cubicPermRotation_sign
      change cubicPermRotation ^ (2 + 1) = 1 at h3
      rw [pow_succ, h2, one_mul] at h3
      exact cubicPermRotation_ne_one h3
    let ε : ι → ℤˣ := Function.update (fun _ => 1) i (-1)
    obtain ⟨h, hh⟩ := hsign ε
    have hhi : sign ((h : ι → Equiv.Perm (Fin 3)) i) = -1 := by
      simpa [ε] using congrFun hh i
    have hhj (j : ι) (hji : j ≠ i) : sign ((h : ι → Equiv.Perm (Fin 3)) j) = 1 := by
      simpa [ε, hji] using congrFun hh j
    let c : ι → Equiv.Perm (Fin 3) :=
      (h : ι → Equiv.Perm (Fin 3)) * r * (h : ι → Equiv.Perm (Fin 3))⁻¹ * r⁻¹
    have hcH : c ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem h.property hrH) (H.inv_mem h.property)) (H.inv_mem hrH)
    have hc : c = Pi.mulSingle i (r i) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp only [c, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same]
        rw [cubic_odd_conj_even _ _ hhi (hrs i)]
        have h3 := cubic_even_pow_three (r i) (hrs i)
        have he := congrArg (fun t => (r i)⁻¹ * (r i)⁻¹ * t) h3
        simpa [pow_succ, mul_assoc] using he.symm
      · simp only [c, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hji]
        rw [(cubic_even_commute _ _ (hhj j hji) (hrs j)).eq]
        simp [mul_assoc]
    obtain ⟨k, hk⟩ := cubic_even_exists_pow (hrs i) hri hp
    rw [← hk, Pi.mulSingle_pow]
    exact H.pow_mem (hc ▸ hcH) k
  apply le_antisymm le_top
  intro g _
  obtain ⟨h, hh⟩ := hsign (fun i => sign (g i))
  let y : ι → Equiv.Perm (Fin 3) := (h : ι → Equiv.Perm (Fin 3))⁻¹ * g
  have hy (i : ι) : sign (y i) = 1 := by
    simp only [y, Pi.mul_apply, Pi.inv_apply, map_mul, map_inv, congrFun hh i,
      inv_mul_cancel]
  have hyH : y ∈ H := Subgroup.pi_mem_of_mulSingle_mem y (fun i => hsingle i (y i) (hy i))
  have hg := H.mul_mem h.property hyH
  simpa [y, mul_assoc] using hg

end GaloisForLFunctions.HTGeometry
