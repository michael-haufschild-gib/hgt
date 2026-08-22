import GaloisForLFunctions.HTGeometry.SteinbergTWTClosureFinFour

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- Exact extraction of the final simple root from the four-index upper collector. -/
theorem fin4_tetrahedron_factor_w23 (a b c d e f : F) :
    steinbergUpperTetrahedron (by decide : (0 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 3) a b c d e f
    = steinbergX (by decide : (2 : Fin 4) ≠ 3) f
      * (steinbergX (by decide : (0 : Fin 4) ≠ 1) a
        * steinbergX (by decide : (1 : Fin 4) ≠ 3) (c * f)
        * steinbergX (by decide : (0 : Fin 4) ≠ 3) (b * f)
        * steinbergX (by decide : (0 : Fin 4) ≠ 2) b
        * steinbergX (by decide : (1 : Fin 4) ≠ 2) c
        * steinbergX (by decide : (0 : Fin 4) ≠ 3) d
        * steinbergX (by decide : (1 : Fin 4) ≠ 3) e) := by
  let h01 : (0 : Fin 4) ≠ 1 := by decide
  let h12 : (1 : Fin 4) ≠ 2 := by decide
  let h02 : (0 : Fin 4) ≠ 2 := by decide
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  change steinbergUpperTetrahedron h01 h12 h02 h03 h13 h23 a b c d e f
    = steinbergX h23 f * (steinbergX h01 a * steinbergX h13 (c * f)
      * steinbergX h03 (b * f) * steinbergX h02 b * steinbergX h12 c
      * steinbergX h03 d * steinbergX h13 e)
  have hEF : steinbergX h13 e * steinbergX h23 f = steinbergX h23 f * steinbergX h13 e :=
    steinbergX_commute_col h13 h23 _ _
  have hDF : steinbergX h03 d * steinbergX h23 f = steinbergX h23 f * steinbergX h03 d :=
    steinbergX_commute_col h03 h23 _ _
  have hCF : steinbergX h12 c * steinbergX h23 f
      = steinbergX h13 (c * f) * steinbergX h23 f * steinbergX h12 c := by
    calc
      steinbergX h12 c * steinbergX h23 f
        = (steinbergX h12 c * steinbergX h23 f * (steinbergX h12 c)⁻¹) * steinbergX h12 c := by group
      _ = (steinbergX h13 (c * f) * steinbergX h23 f) * steinbergX h12 c := by
        rw [steinbergX_conj_chain h12 h23 h13]
      _ = steinbergX h13 (c * f) * steinbergX h23 f * steinbergX h12 c := by group
  have hBE : steinbergX h02 b * steinbergX h13 (c * f)
      = steinbergX h13 (c * f) * steinbergX h02 b :=
    steinbergX_commute h02 h13 (Ne.symm h12) h03 _ _
  have hBF : steinbergX h02 b * steinbergX h23 f
      = steinbergX h03 (b * f) * steinbergX h23 f * steinbergX h02 b := by
    calc
      steinbergX h02 b * steinbergX h23 f
        = (steinbergX h02 b * steinbergX h23 f * (steinbergX h02 b)⁻¹) * steinbergX h02 b := by group
      _ = (steinbergX h03 (b * f) * steinbergX h23 f) * steinbergX h02 b := by
        rw [steinbergX_conj_chain h02 h23 h03]
      _ = steinbergX h03 (b * f) * steinbergX h23 f * steinbergX h02 b := by group
  have hDnewF : steinbergX h03 (b * f) * steinbergX h23 f
      = steinbergX h23 f * steinbergX h03 (b * f) :=
    steinbergX_commute_col h03 h23 _ _
  have hEnewF : steinbergX h13 (c * f) * steinbergX h23 f
      = steinbergX h23 f * steinbergX h13 (c * f) :=
    steinbergX_commute_col h13 h23 _ _
  have hAF : steinbergX h01 a * steinbergX h23 f
      = steinbergX h23 f * steinbergX h01 a :=
    steinbergX_commute h01 h23 h12 h03 _ _
  rw [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn]
  calc
    (steinbergX h01 a * steinbergX h02 b * steinbergX h12 c)
        * (steinbergX h03 d * steinbergX h13 e * steinbergX h23 f)
      = steinbergX h01 a * steinbergX h02 b * steinbergX h12 c
        * (steinbergX h23 f * steinbergX h03 d * steinbergX h13 e) := by
          calc
            _ = steinbergX h01 a * steinbergX h02 b * steinbergX h12 c
                * steinbergX h03 d * (steinbergX h13 e * steinbergX h23 f) := by group
            _ = steinbergX h01 a * steinbergX h02 b * steinbergX h12 c
                * steinbergX h03 d * (steinbergX h23 f * steinbergX h13 e) := by rw [hEF]
            _ = steinbergX h01 a * steinbergX h02 b * steinbergX h12 c
                * (steinbergX h03 d * steinbergX h23 f) * steinbergX h13 e := by group
            _ = steinbergX h01 a * steinbergX h02 b * steinbergX h12 c
                * (steinbergX h23 f * steinbergX h03 d) * steinbergX h13 e := by rw [hDF]
            _ = _ := by group
    _ = steinbergX h01 a * steinbergX h02 b * steinbergX h13 (c * f)
        * steinbergX h23 f * steinbergX h12 c * steinbergX h03 d * steinbergX h13 e := by
          calc
            _ = steinbergX h01 a * steinbergX h02 b * (steinbergX h12 c * steinbergX h23 f)
                * steinbergX h03 d * steinbergX h13 e := by group
            _ = steinbergX h01 a * steinbergX h02 b
                * (steinbergX h13 (c * f) * steinbergX h23 f * steinbergX h12 c)
                * steinbergX h03 d * steinbergX h13 e := by rw [hCF]
            _ = _ := by group
    _ = steinbergX h01 a * steinbergX h13 (c * f) * steinbergX h02 b
        * steinbergX h23 f * steinbergX h12 c * steinbergX h03 d * steinbergX h13 e := by
          calc
            _ = steinbergX h01 a * (steinbergX h02 b * steinbergX h13 (c * f))
                * steinbergX h23 f * steinbergX h12 c * steinbergX h03 d * steinbergX h13 e := by group
            _ = steinbergX h01 a * (steinbergX h13 (c * f) * steinbergX h02 b)
                * steinbergX h23 f * steinbergX h12 c * steinbergX h03 d * steinbergX h13 e := by rw [hBE]
            _ = _ := by group
    _ = steinbergX h01 a * steinbergX h13 (c * f) * steinbergX h03 (b * f)
        * steinbergX h23 f * steinbergX h02 b * steinbergX h12 c * steinbergX h03 d * steinbergX h13 e := by
          calc
            _ = steinbergX h01 a * steinbergX h13 (c * f)
                * (steinbergX h02 b * steinbergX h23 f) * steinbergX h12 c
                * steinbergX h03 d * steinbergX h13 e := by group
            _ = steinbergX h01 a * steinbergX h13 (c * f)
                * (steinbergX h03 (b * f) * steinbergX h23 f * steinbergX h02 b) * steinbergX h12 c
                * steinbergX h03 d * steinbergX h13 e := by rw [hBF]
            _ = _ := by group
    _ = steinbergX h23 f * (steinbergX h01 a * steinbergX h13 (c * f)
        * steinbergX h03 (b * f) * steinbergX h02 b * steinbergX h12 c
        * steinbergX h03 d * steinbergX h13 e) := by
          calc
            _ = steinbergX h01 a * steinbergX h13 (c * f)
                * (steinbergX h03 (b * f) * steinbergX h23 f)
                * steinbergX h02 b * steinbergX h12 c * steinbergX h03 d * steinbergX h13 e := by group
            _ = steinbergX h01 a * steinbergX h13 (c * f)
                * (steinbergX h23 f * steinbergX h03 (b * f))
                * steinbergX h02 b * steinbergX h12 c * steinbergX h03 d * steinbergX h13 e := by rw [hDnewF]
            _ = steinbergX h01 a * (steinbergX h13 (c * f) * steinbergX h23 f)
                * steinbergX h03 (b * f) * steinbergX h02 b * steinbergX h12 c
                * steinbergX h03 d * steinbergX h13 e := by group
            _ = steinbergX h01 a * (steinbergX h23 f * steinbergX h13 (c * f))
                * steinbergX h03 (b * f) * steinbergX h02 b * steinbergX h12 c
                * steinbergX h03 d * steinbergX h13 e := by rw [hEnewF]
            _ = (steinbergX h01 a * steinbergX h23 f) * steinbergX h13 (c * f)
                * steinbergX h03 (b * f) * steinbergX h02 b * steinbergX h12 c
                * steinbergX h03 d * steinbergX h13 e := by group
            _ = (steinbergX h23 f * steinbergX h01 a) * steinbergX h13 (c * f)
                * steinbergX h03 (b * f) * steinbergX h02 b * steinbergX h12 c
                * steinbergX h03 d * steinbergX h13 e := by rw [hAF]
            _ = _ := by group

/-- Conjugating the collected complement of the final simple root by the inverse simple
Weyl factor keeps every factor positive. -/
theorem fin4_w23_neg_conj_upper_complement (a b c d e f : F) :
    steinbergWeyl (by decide : (2 : Fin 4) ≠ 3) (-1 : Fˣ)
        * (steinbergX (by decide : (0 : Fin 4) ≠ 1) a
          * steinbergX (by decide : (1 : Fin 4) ≠ 3) (c * f)
          * steinbergX (by decide : (0 : Fin 4) ≠ 3) (b * f)
          * steinbergX (by decide : (0 : Fin 4) ≠ 2) b
          * steinbergX (by decide : (1 : Fin 4) ≠ 2) c
          * steinbergX (by decide : (0 : Fin 4) ≠ 3) d
          * steinbergX (by decide : (1 : Fin 4) ≠ 3) e)
        * (steinbergWeyl (by decide : (2 : Fin 4) ≠ 3) (-1 : Fˣ))⁻¹
      ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
  let s : SteinbergWeylWord F (Fin 4) := .snoc .one 2 3 (by decide) (-1 : Fˣ)
  have hs : s.eval = steinbergWeyl (by decide : (2 : Fin 4) ≠ 3) (-1 : Fˣ) := by rfl
  have hspare : ∀ i j : Fin 4, i ≠ j → ∃ m : Fin 4, i ≠ m ∧ j ≠ m := by
    intro i j _
    obtain ⟨m, hmi, hmj⟩ := exists_third_index (by decide) i j
    exact ⟨m, hmi.symm, hmj.symm⟩
  rw [← hs]
  have h01 : s.perm 0 < s.perm 1 := by
    change Equiv.swap 2 3 0 < Equiv.swap 2 3 1
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide),
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    decide
  have h13 : s.perm 1 < s.perm 3 := by
    change Equiv.swap 2 3 1 < Equiv.swap 2 3 3
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), Equiv.swap_apply_right]
    decide
  have h03 : s.perm 0 < s.perm 3 := by
    change Equiv.swap 2 3 0 < Equiv.swap 2 3 3
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), Equiv.swap_apply_right]
    decide
  have h02 : s.perm 0 < s.perm 2 := by
    change Equiv.swap 2 3 0 < Equiv.swap 2 3 2
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), Equiv.swap_apply_left]
    decide
  have h12 : s.perm 1 < s.perm 2 := by
    change Equiv.swap 2 3 1 < Equiv.swap 2 3 2
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), Equiv.swap_apply_left]
    decide
  have hu01 := weylWord_conj_root_mem_upper s hspare (by decide : (0 : Fin 4) ≠ 1) a h01
  have hu13cf := weylWord_conj_root_mem_upper s hspare (by decide : (1 : Fin 4) ≠ 3) (c * f) h13
  have hu03bf := weylWord_conj_root_mem_upper s hspare (by decide : (0 : Fin 4) ≠ 3) (b * f) h03
  have hu02 := weylWord_conj_root_mem_upper s hspare (by decide : (0 : Fin 4) ≠ 2) b h02
  have hu12 := weylWord_conj_root_mem_upper s hspare (by decide : (1 : Fin 4) ≠ 2) c h12
  have hu03d := weylWord_conj_root_mem_upper s hspare (by decide : (0 : Fin 4) ≠ 3) d h03
  have hu13e := weylWord_conj_root_mem_upper s hspare (by decide : (1 : Fin 4) ≠ 3) e h13
  rw [show s.eval
        * (steinbergX (by decide : (0 : Fin 4) ≠ 1) a
          * steinbergX (by decide : (1 : Fin 4) ≠ 3) (c * f)
          * steinbergX (by decide : (0 : Fin 4) ≠ 3) (b * f)
          * steinbergX (by decide : (0 : Fin 4) ≠ 2) b
          * steinbergX (by decide : (1 : Fin 4) ≠ 2) c
          * steinbergX (by decide : (0 : Fin 4) ≠ 3) d
          * steinbergX (by decide : (1 : Fin 4) ≠ 3) e)
        * s.eval⁻¹
      = (s.eval * steinbergX (by decide : (0 : Fin 4) ≠ 1) a * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (1 : Fin 4) ≠ 3) (c * f) * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (0 : Fin 4) ≠ 3) (b * f) * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (0 : Fin 4) ≠ 2) b * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (1 : Fin 4) ≠ 2) c * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (0 : Fin 4) ≠ 3) d * s.eval⁻¹)
          * (s.eval * steinbergX (by decide : (1 : Fin 4) ≠ 3) e * s.eval⁻¹) by group]
  exact (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
    ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
      ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
        ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
          ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
            ((upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem hu01 hu13cf) hu03bf) hu02) hu12) hu03d) hu13e

/-- The exact `Fin 4` `TWT` collector is stable under appending the final simple Weyl factor. -/
theorem fin4_steinbergTWT_mul_w23 {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4)) :
    g * steinbergWeyl (by decide : (2 : Fin 4) ≠ 3) (1 : Fˣ)
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
    steinbergX h01 a * steinbergX h13 (c * f) * steinbergX h03 (b * f)
      * steinbergX h02 b * steinbergX h12 c * steinbergX h03 d * steinbergX h13 e
  have ht₂' : t₂ = steinbergX h23 f * q := by
    rw [ht₂, fin4_tetrahedron_factor_w23]
  have hspare : ∀ i j : Fin 4, i ≠ j → ∃ m : Fin 4, i ≠ m ∧ j ≠ m := by
    intro i j _
    obtain ⟨m, hmi, hmj⟩ := exists_third_index (by decide) i j
    exact ⟨m, hmi.symm, hmj.symm⟩
  have habs : word.eval * steinbergX h23 f * steinbergWeyl h23 (1 : Fˣ)
      ∈ steinbergTWT (F := F) (n := Fin 4) :=
    weylWord_upper_root_simpleWeyl_mem_TWT word hspare h23 (by decide) f
  obtain ⟨u₁, v, u₂, hu₁, hv, hu₂, habs_eq⟩ := habs
  have hminus : steinbergWeyl h23 (-1 : Fˣ) = (steinbergWeyl h23 (1 : Fˣ))⁻¹ := by
    simpa using steinbergWeyl_neg h23 (1 : Fˣ)
  have hq : steinbergWeyl h23 (-1 : Fˣ) * q * steinbergWeyl h23 (1 : Fˣ)
      ∈ upperSteinbergSubgroup (F := F) (Fin 4) := by
    have hq' := fin4_w23_neg_conj_upper_complement (F := F) a b c d e f
    have hminus_inv : (steinbergWeyl h23 (-1 : Fˣ))⁻¹ = steinbergWeyl h23 (1 : Fˣ) := by
      rw [hminus, inv_inv]
    rw [hminus_inv] at hq'
    simpa [q] using hq'
  refine ⟨t₁ * u₁, v, u₂ * (steinbergWeyl h23 (-1 : Fˣ) * q * steinbergWeyl h23 (1 : Fˣ)),
    (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem ht₁ hu₁, hv,
    (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem hu₂ hq, ?_⟩
  rw [← hword, ht₂']
  calc
    t₁ * word.eval * (steinbergX h23 f * q) * steinbergWeyl h23 (1 : Fˣ)
      = t₁ * (word.eval * steinbergX h23 f * steinbergWeyl h23 (1 : Fˣ))
          * (steinbergWeyl h23 (-1 : Fˣ) * q * steinbergWeyl h23 (1 : Fˣ)) := by
          rw [hminus]
          group
    _ = (t₁ * u₁) * v * (u₂ * (steinbergWeyl h23 (-1 : Fˣ) * q
          * steinbergWeyl h23 (1 : Fˣ))) := by rw [habs_eq]; group

end GaloisForLFunctions.HTGeometry
