import GaloisForLFunctions.HTGeometry.SteinbergTWTAbsorption
import GaloisForLFunctions.HTGeometry.SteinbergTorusAction
import GaloisForLFunctions.HTGeometry.SteinbergGroupFiniteGeneration

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- The complement of the `(0,1)` root in the exact `Fin 4` upper collector remains upper
after conjugation by the inverse simple Weyl factor. -/
theorem fin4_w01_neg_conj_upper_complement (b c d e f : F) :
    steinbergWeyl (by decide : (0 : Fin 4) ≠ 1) (-1 : Fˣ)
        * (steinbergX (by decide : (0 : Fin 4) ≠ 2) b
          * steinbergX (by decide : (1 : Fin 4) ≠ 2) c
          * steinbergX (by decide : (0 : Fin 4) ≠ 3) d
          * steinbergX (by decide : (1 : Fin 4) ≠ 3) e
          * steinbergX (by decide : (2 : Fin 4) ≠ 3) f)
        * (steinbergWeyl (by decide : (0 : Fin 4) ≠ 1) (-1 : Fˣ))⁻¹
      ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
  let s : SteinbergWeylWord F (Fin 4) := .snoc .one 0 1 (by decide) (-1 : Fˣ)
  have hs : s.eval = steinbergWeyl (by decide : (0 : Fin 4) ≠ 1) (-1 : Fˣ) := by rfl
  have hspare : ∀ i j : Fin 4, i ≠ j → ∃ m : Fin 4, i ≠ m ∧ j ≠ m := by
    intro i j _
    obtain ⟨m, hmi, hmj⟩ := exists_third_index (by decide) i j
    exact ⟨m, hmi.symm, hmj.symm⟩
  rw [← hs]
  have h02 : s.perm 0 < s.perm 2 := by
    change (1 : Fin 4) < Equiv.swap 0 1 2
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    decide
  have h12 : s.perm 1 < s.perm 2 := by
    change (0 : Fin 4) < Equiv.swap 0 1 2
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    decide
  have h03 : s.perm 0 < s.perm 3 := by
    change (1 : Fin 4) < Equiv.swap 0 1 3
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    decide
  have h13 : s.perm 1 < s.perm 3 := by
    change (0 : Fin 4) < Equiv.swap 0 1 3
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    decide
  have h23 : s.perm 2 < s.perm 3 := by
    change Equiv.swap 0 1 2 < Equiv.swap 0 1 3
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide),
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    decide
  have hu02 := weylWord_conj_root_mem_upper s hspare (by decide : (0 : Fin 4) ≠ 2) b h02
  have hu12 := weylWord_conj_root_mem_upper s hspare (by decide : (1 : Fin 4) ≠ 2) c h12
  have hu03 := weylWord_conj_root_mem_upper s hspare (by decide : (0 : Fin 4) ≠ 3) d h03
  have hu13 := weylWord_conj_root_mem_upper s hspare (by decide : (1 : Fin 4) ≠ 3) e h13
  have hu23 := weylWord_conj_root_mem_upper s hspare (by decide : (2 : Fin 4) ≠ 3) f h23
  rw [show s.eval
        * (steinbergX (by decide : (0 : Fin 4) ≠ 2) b
          * steinbergX (by decide : (1 : Fin 4) ≠ 2) c
          * steinbergX (by decide : (0 : Fin 4) ≠ 3) d
          * steinbergX (by decide : (1 : Fin 4) ≠ 3) e
          * steinbergX (by decide : (2 : Fin 4) ≠ 3) f)
        * s.eval⁻¹
      = (s.eval * steinbergX (by decide : (0 : Fin 4) ≠ 2) b * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (1 : Fin 4) ≠ 2) c * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (0 : Fin 4) ≠ 3) d * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (1 : Fin 4) ≠ 3) e * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (2 : Fin 4) ≠ 3) f * s.eval⁻¹) by group]
  exact (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
    ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
      ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
        ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem hu02 hu12) hu03) hu13) hu23

/-- The exact `Fin 4` `TWT` collector is stable under appending the first simple Weyl factor.
This combines root isolation in the tetrahedral normal form with the descent-absorption theorem. -/
theorem fin4_steinbergTWT_mul_w01 {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4)) :
    g * steinbergWeyl (by decide : (0 : Fin 4) ≠ 1) (1 : Fˣ)
      ∈ steinbergTWT (F := F) (n := Fin 4) := by
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  let h02 : (0 : Fin 4) ≠ 2 := by decide
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  rcases hg with ⟨t₁, w, t₂, ht₁, hw, ht₂, rfl⟩
  obtain ⟨word, hword⟩ := SteinbergWeylWord.exists_of_mem_subgroup hw
  rw [upperSteinbergSubgroup_fin4_eq_tetrahedron] at ht₂
  obtain ⟨a, b, c, d, e, f, ht₂⟩ := ht₂
  let q : SteinbergGroup F (Fin 4) :=
    steinbergX h02 b * steinbergX h12 c * steinbergX h03 d
      * steinbergX h13 e * steinbergX h23 f
  have ht₂' : t₂ = steinbergX h01 a * q := by
    rw [ht₂]
    simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn, q]
    group
  have hspare : ∀ i j : Fin 4, i ≠ j → ∃ m : Fin 4, i ≠ m ∧ j ≠ m := by
    intro i j _
    obtain ⟨m, hmi, hmj⟩ := exists_third_index (by decide) i j
    exact ⟨m, hmi.symm, hmj.symm⟩
  have habs : word.eval * steinbergX h01 a * steinbergWeyl h01 (1 : Fˣ)
      ∈ steinbergTWT (F := F) (n := Fin 4) :=
    weylWord_upper_root_simpleWeyl_mem_TWT word hspare h01 (by decide) a
  obtain ⟨u₁, v, u₂, hu₁, hv, hu₂, habs_eq⟩ := habs
  have hminus : steinbergWeyl h01 (-1 : Fˣ) = (steinbergWeyl h01 (1 : Fˣ))⁻¹ := by
    simpa using steinbergWeyl_neg h01 (1 : Fˣ)
  have hq : steinbergWeyl h01 (-1 : Fˣ) * q * steinbergWeyl h01 (1 : Fˣ)
      ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
    have hq' := fin4_w01_neg_conj_upper_complement (F := F) b c d e f
    have hminus_inv : (steinbergWeyl h01 (-1 : Fˣ))⁻¹ = steinbergWeyl h01 (1 : Fˣ) := by
      rw [hminus, inv_inv]
    rw [hminus_inv] at hq'
    simpa [q] using hq'
  refine ⟨t₁ * u₁, v, u₂ * (steinbergWeyl h01 (-1 : Fˣ) * q * steinbergWeyl h01 (1 : Fˣ)),
    (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem ht₁ hu₁, hv,
    (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem hu₂ hq, ?_⟩
  rw [← hword, ht₂']
  calc
    t₁ * word.eval * (steinbergX h01 a * q) * steinbergWeyl h01 (1 : Fˣ)
      = t₁ * (word.eval * steinbergX h01 a * steinbergWeyl h01 (1 : Fˣ))
          * (steinbergWeyl h01 (-1 : Fˣ) * q * steinbergWeyl h01 (1 : Fˣ)) := by
          rw [hminus]
          group
    _ = (t₁ * u₁) * v * (u₂ * (steinbergWeyl h01 (-1 : Fˣ) * q
          * steinbergWeyl h01 (1 : Fˣ))) := by rw [habs_eq]; group

/-- The collected complement of the `(1,2)` root remains upper after conjugation by the
inverse second simple Weyl factor. -/
theorem fin4_w12_neg_conj_upper_complement (a b c d e f : F) :
    steinbergWeyl (by decide : (1 : Fin 4) ≠ 2) (-1 : Fˣ)
        * (steinbergX (by decide : (0 : Fin 4) ≠ 2) (a * c)
          * steinbergX (by decide : (0 : Fin 4) ≠ 1) a
          * steinbergX (by decide : (0 : Fin 4) ≠ 2) b
          * steinbergX (by decide : (0 : Fin 4) ≠ 3) d
          * steinbergX (by decide : (1 : Fin 4) ≠ 3) e
          * steinbergX (by decide : (2 : Fin 4) ≠ 3) f)
        * (steinbergWeyl (by decide : (1 : Fin 4) ≠ 2) (-1 : Fˣ))⁻¹
      ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
  let s : SteinbergWeylWord F (Fin 4) := .snoc .one 1 2 (by decide) (-1 : Fˣ)
  have hs : s.eval = steinbergWeyl (by decide : (1 : Fin 4) ≠ 2) (-1 : Fˣ) := by rfl
  have hspare : ∀ i j : Fin 4, i ≠ j → ∃ m : Fin 4, i ≠ m ∧ j ≠ m := by
    intro i j _
    obtain ⟨m, hmi, hmj⟩ := exists_third_index (by decide) i j
    exact ⟨m, hmi.symm, hmj.symm⟩
  rw [← hs]
  have h02 : s.perm 0 < s.perm 2 := by
    change (0 : Fin 4) < Equiv.swap 1 2 2
    rw [Equiv.swap_apply_right]
    decide
  have h01 : s.perm 0 < s.perm 1 := by
    change (0 : Fin 4) < Equiv.swap 1 2 1
    rw [Equiv.swap_apply_left]
    decide
  have h03 : s.perm 0 < s.perm 3 := by
    change (0 : Fin 4) < Equiv.swap 1 2 3
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    decide
  have h13 : s.perm 1 < s.perm 3 := by
    change Equiv.swap 1 2 1 < Equiv.swap 1 2 3
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    decide
  have h23 : s.perm 2 < s.perm 3 := by
    change Equiv.swap 1 2 2 < Equiv.swap 1 2 3
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    decide
  have hu02a := weylWord_conj_root_mem_upper s hspare (by decide : (0 : Fin 4) ≠ 2) (a * c) h02
  have hu01 := weylWord_conj_root_mem_upper s hspare (by decide : (0 : Fin 4) ≠ 1) a h01
  have hu02b := weylWord_conj_root_mem_upper s hspare (by decide : (0 : Fin 4) ≠ 2) b h02
  have hu03 := weylWord_conj_root_mem_upper s hspare (by decide : (0 : Fin 4) ≠ 3) d h03
  have hu13 := weylWord_conj_root_mem_upper s hspare (by decide : (1 : Fin 4) ≠ 3) e h13
  have hu23 := weylWord_conj_root_mem_upper s hspare (by decide : (2 : Fin 4) ≠ 3) f h23
  rw [show s.eval
        * (steinbergX (by decide : (0 : Fin 4) ≠ 2) (a * c)
          * steinbergX (by decide : (0 : Fin 4) ≠ 1) a
          * steinbergX (by decide : (0 : Fin 4) ≠ 2) b
          * steinbergX (by decide : (0 : Fin 4) ≠ 3) d
          * steinbergX (by decide : (1 : Fin 4) ≠ 3) e
          * steinbergX (by decide : (2 : Fin 4) ≠ 3) f)
        * s.eval⁻¹
      = (s.eval * steinbergX (by decide : (0 : Fin 4) ≠ 2) (a * c) * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (0 : Fin 4) ≠ 1) a * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (0 : Fin 4) ≠ 2) b * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (0 : Fin 4) ≠ 3) d * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (1 : Fin 4) ≠ 3) e * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (2 : Fin 4) ≠ 3) f * s.eval⁻¹) by group]
  exact (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
    ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
      ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
        ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
          ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem hu02a hu01) hu02b) hu03) hu13) hu23

/-- Exact extraction of the `(1,2)` root from the tetrahedral collector. -/
theorem fin4_tetrahedron_factor_w12 (a b c d e f : F) :
    steinbergUpperTetrahedron (by decide : (0 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 3) a b c d e f
    = steinbergX (by decide : (1 : Fin 4) ≠ 2) c
      * (steinbergX (by decide : (0 : Fin 4) ≠ 2) (a * c)
        * steinbergX (by decide : (0 : Fin 4) ≠ 1) a
        * steinbergX (by decide : (0 : Fin 4) ≠ 2) b
        * steinbergX (by decide : (0 : Fin 4) ≠ 3) d
        * steinbergX (by decide : (1 : Fin 4) ≠ 3) e
        * steinbergX (by decide : (2 : Fin 4) ≠ 3) f) := by
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  let h02 : (0 : Fin 4) ≠ 2 := by decide
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  change steinbergUpperTetrahedron h01 h12 h02 h03 h13 h23 a b c d e f
    = steinbergX h12 c * (steinbergX h02 (a * c) * steinbergX h01 a * steinbergX h02 b
      * steinbergX h03 d * steinbergX h13 e * steinbergX h23 f)
  have hchain : steinbergX h01 a * steinbergX h12 c
      = steinbergX h02 (a * c) * steinbergX h12 c * steinbergX h01 a := by
    calc
      steinbergX h01 a * steinbergX h12 c
        = (steinbergX h01 a * steinbergX h12 c * (steinbergX h01 a)⁻¹) * steinbergX h01 a := by group
      _ = (steinbergX h02 (a * c) * steinbergX h12 c) * steinbergX h01 a := by
        rw [steinbergX_conj_chain h01 h12 h02]
      _ = steinbergX h02 (a * c) * steinbergX h12 c * steinbergX h01 a := by group
  have hcomm : steinbergX h02 (a * c) * steinbergX h12 c
      = steinbergX h12 c * steinbergX h02 (a * c) :=
    steinbergX_commute_col h02 h12 _ _
  rw [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn]
  calc
    (steinbergX h01 a * steinbergX h02 b * steinbergX h12 c)
        * (steinbergX h03 d * steinbergX h13 e * steinbergX h23 f)
      = (steinbergX h01 a * steinbergX h12 c) * steinbergX h02 b
        * (steinbergX h03 d * steinbergX h13 e * steinbergX h23 f) := by
          calc
            _ = steinbergX h01 a * (steinbergX h02 b * steinbergX h12 c)
                * (steinbergX h03 d * steinbergX h13 e * steinbergX h23 f) := by group
            _ = steinbergX h01 a * (steinbergX h12 c * steinbergX h02 b)
                * (steinbergX h03 d * steinbergX h13 e * steinbergX h23 f) := by
                  rw [steinbergX_commute_col h02 h12]
            _ = _ := by group
    _ = (steinbergX h02 (a * c) * steinbergX h12 c * steinbergX h01 a) * steinbergX h02 b
        * (steinbergX h03 d * steinbergX h13 e * steinbergX h23 f) := by rw [hchain]
    _ = steinbergX h12 c * (steinbergX h02 (a * c) * steinbergX h01 a * steinbergX h02 b
        * steinbergX h03 d * steinbergX h13 e * steinbergX h23 f) := by rw [hcomm]; group

/-- The exact `Fin 4` `TWT` collector is stable under appending the second simple Weyl factor. -/
theorem fin4_steinbergTWT_mul_w12 {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4)) :
    g * steinbergWeyl (by decide : (1 : Fin 4) ≠ 2) (1 : Fˣ)
      ∈ steinbergTWT (F := F) (n := Fin 4) := by
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  let h02 : (0 : Fin 4) ≠ 2 := by decide
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  rcases hg with ⟨t₁, w, t₂, ht₁, hw, ht₂, rfl⟩
  obtain ⟨word, hword⟩ := SteinbergWeylWord.exists_of_mem_subgroup hw
  rw [upperSteinbergSubgroup_fin4_eq_tetrahedron] at ht₂
  obtain ⟨a, b, c, d, e, f, ht₂⟩ := ht₂
  let q : SteinbergGroup F (Fin 4) :=
    steinbergX h02 (a * c) * steinbergX h01 a * steinbergX h02 b
      * steinbergX h03 d * steinbergX h13 e * steinbergX h23 f
  have ht₂' : t₂ = steinbergX h12 c * q := by
    rw [ht₂, fin4_tetrahedron_factor_w12]
  have hspare : ∀ i j : Fin 4, i ≠ j → ∃ m : Fin 4, i ≠ m ∧ j ≠ m := by
    intro i j _
    obtain ⟨m, hmi, hmj⟩ := exists_third_index (by decide) i j
    exact ⟨m, hmi.symm, hmj.symm⟩
  have habs : word.eval * steinbergX h12 c * steinbergWeyl h12 (1 : Fˣ)
      ∈ steinbergTWT (F := F) (n := Fin 4) :=
    weylWord_upper_root_simpleWeyl_mem_TWT word hspare h12 (by decide) c
  obtain ⟨u₁, v, u₂, hu₁, hv, hu₂, habs_eq⟩ := habs
  have hminus : steinbergWeyl h12 (-1 : Fˣ) = (steinbergWeyl h12 (1 : Fˣ))⁻¹ := by
    simpa using steinbergWeyl_neg h12 (1 : Fˣ)
  have hq : steinbergWeyl h12 (-1 : Fˣ) * q * steinbergWeyl h12 (1 : Fˣ)
      ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
    have hq' := fin4_w12_neg_conj_upper_complement (F := F) a b c d e f
    have hminus_inv : (steinbergWeyl h12 (-1 : Fˣ))⁻¹ = steinbergWeyl h12 (1 : Fˣ) := by
      rw [hminus, inv_inv]
    rw [hminus_inv] at hq'
    simpa [q] using hq'
  refine ⟨t₁ * u₁, v, u₂ * (steinbergWeyl h12 (-1 : Fˣ) * q * steinbergWeyl h12 (1 : Fˣ)),
    (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem ht₁ hu₁, hv,
    (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem hu₂ hq, ?_⟩
  rw [← hword, ht₂']
  calc
    t₁ * word.eval * (steinbergX h12 c * q) * steinbergWeyl h12 (1 : Fˣ)
      = t₁ * (word.eval * steinbergX h12 c * steinbergWeyl h12 (1 : Fˣ))
          * (steinbergWeyl h12 (-1 : Fˣ) * q * steinbergWeyl h12 (1 : Fˣ)) := by
          rw [hminus]
          group
    _ = (t₁ * u₁) * v * (u₂ * (steinbergWeyl h12 (-1 : Fˣ) * q
          * steinbergWeyl h12 (1 : Fˣ))) := by rw [habs_eq]; group

end GaloisForLFunctions.HTGeometry
