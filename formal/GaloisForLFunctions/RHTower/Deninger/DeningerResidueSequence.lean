import GaloisForLFunctions.RHTower.Deninger.DeningerCohomologyBasis

/-!
# The logarithmic residue sequence of a stage and its divisor

On the constant forms of a character stage, extending along the projection that forgets the last
coordinate and taking the residue along that coordinate — contract against its direction and restrict
to the divisor — form a short exact sequence.  Exactness in the middle is the statement that a form
whose residue vanishes involves no logarithmic differential of the last coordinate.

* `deningerExtendForm`, `deningerResidueForm` : the two maps of the residue sequence.
* `deningerResidue_exact` : the sequence is exact in the middle.
* `deningerResidueForm_surjective` : the residue is onto, by the Pascal identity.
-/

namespace RHTower

open Complex

section ResidueMaps

variable {r n : ℕ}

/-- Forgetting the last coordinate. -/
noncomputable def deningerProjCLM (r : ℕ) : (Fin (r + 1) → ℂ) →L[ℂ] (Fin r → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) i.castSucc

@[simp]
theorem deningerProjCLM_apply (w : Fin (r + 1) → ℂ) (i : Fin r) :
    deningerProjCLM r w i = w i.castSucc := rfl

/-- Adjoining a zero last coordinate. -/
noncomputable def deningerInclCLM (r : ℕ) : (Fin r → ℂ) →L[ℂ] (Fin (r + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i : Fin (r + 1) =>
    if h : (i : ℕ) < r then
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) ⟨(i : ℕ), h⟩
    else 0

theorem deningerInclCLM_apply (w : Fin r → ℂ) (i : Fin (r + 1)) :
    deningerInclCLM r w i = if h : (i : ℕ) < r then w ⟨(i : ℕ), h⟩ else 0 := by
  show (if h : (i : ℕ) < r then
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) ⟨(i : ℕ), h⟩
    else 0) w = _
  by_cases h : (i : ℕ) < r
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]
    rfl

theorem deningerInclCLM_castSucc (w : Fin r → ℂ) (j : Fin r) :
    deningerInclCLM r w j.castSucc = w j := by
  rw [deningerInclCLM_apply, dif_pos (by simp : ((j.castSucc : Fin (r + 1)) : ℕ) < r)]
  congr 1

theorem deningerProj_incl (w : Fin r → ℂ) : deningerProjCLM r (deningerInclCLM r w) = w := by
  funext j
  rw [deningerProjCLM_apply, deningerInclCLM_castSucc]

/-- The projection kills the direction of the last coordinate. -/
theorem deningerProjCLM_single_last :
    deningerProjCLM r (Pi.single (Fin.last r) (1 : ℂ) : Fin (r + 1) → ℂ) = 0 := by
  funext i
  show (Pi.single (Fin.last r) (1 : ℂ) : Fin (r + 1) → ℂ) i.castSucc = 0
  rw [Pi.single_apply, if_neg (Fin.castSucc_lt_last i).ne]

/-- Extending a constant form along the projection that forgets the last coordinate. -/
noncomputable def deningerExtendAlternating (α : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) :
    (Fin (r + 1) → ℂ) [⋀^Fin n]→L[ℂ] ℂ :=
  α.compContinuousLinearMap (deningerProjCLM r)

theorem deningerExtendAlternating_apply (α : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ)
    (v : Fin n → (Fin (r + 1) → ℂ)) :
    deningerExtendAlternating α v = α fun a => deningerProjCLM r (v a) := rfl

/-- The residue of a constant form along the last coordinate. -/
noncomputable def deningerResidueFun (α : (Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) :
    (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ :=
  ContinuousAlternatingMap.compContinuousLinearMap
    (deningerContractCLM (Pi.single (Fin.last r) (1 : ℂ) : Fin (r + 1) → ℂ) α)
    (deningerInclCLM r)

theorem deningerResidueFun_apply (α : (Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (v : Fin n → (Fin r → ℂ)) :
    deningerResidueFun α v =
      α (Fin.cons (Pi.single (Fin.last r) (1 : ℂ) : Fin (r + 1) → ℂ)
        fun a => deningerInclCLM r (v a)) := rfl

/-- **Extending a constant form along the projection**, as a linear map. -/
noncomputable def deningerExtendForm (r n : ℕ) :
    ((Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) →ₗ[ℂ] ((Fin (r + 1) → ℂ) [⋀^Fin n]→L[ℂ] ℂ) where
  toFun := deningerExtendAlternating
  map_add' α β := by
    ext v
    rfl
  map_smul' c α := by
    ext v
    rfl

/-- **The residue along the last coordinate**, as a linear map. -/
noncomputable def deningerResidueForm (r n : ℕ) :
    ((Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) →ₗ[ℂ] ((Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) where
  toFun := deningerResidueFun
  map_add' α β := by
    ext v
    rfl
  map_smul' c α := by
    ext v
    rfl

theorem deningerExtendForm_eq (α : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) :
    deningerExtendForm r n α = deningerExtendAlternating α := rfl

theorem deningerResidueForm_eq (α : (Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) :
    deningerResidueForm r n α = deningerResidueFun α := rfl

end ResidueMaps

end RHTower

namespace RHTower

open Complex

section Exactness

variable {r n : ℕ}

/-- **The residue of an extended form vanishes.** -/
theorem deningerResidue_comp_extend (α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) :
    deningerResidueForm r n (deningerExtendForm r (n + 1) α) = 0 := by
  ext v
  rw [deningerResidueForm_eq, deningerResidueFun_apply, deningerExtendForm_eq,
    deningerExtendAlternating_apply]
  refine (ContinuousMultilinearMap.map_coord_zero α.toContinuousMultilinearMap 0 ?_).trans ?_
  · show deningerProjCLM r ((Fin.cons (Pi.single (Fin.last r) (1 : ℂ) : Fin (r + 1) → ℂ)
      (fun a => deningerInclCLM r (v a)) : Fin (n + 1) → (Fin (r + 1) → ℂ)) 0) = 0
    rw [Fin.cons_zero]
    exact deningerProjCLM_single_last
  · rfl

/-- **Extension is injective**, because the projection has a section. -/
theorem deningerExtendForm_injective : Function.Injective (deningerExtendForm r n) := by
  refine (injective_iff_map_eq_zero _).2 fun α hα => ?_
  ext v
  have hv := congrArg (fun A : (Fin (r + 1) → ℂ) [⋀^Fin n]→L[ℂ] ℂ =>
    A fun a => deningerInclCLM r (v a)) hα
  simp only [deningerExtendForm_eq, deningerExtendAlternating_apply, deningerProj_incl] at hv
  rw [hv]
  rfl

/-- A coordinate vector other than the last is the image of a coordinate vector of the divisor. -/
theorem deningerIncl_basis {j : Fin (r + 1)} (hj : j ≠ Fin.last r) :
    deningerInclCLM r (Pi.single (j.castPred hj) (1 : ℂ) : Fin r → ℂ) =
      (Pi.single j (1 : ℂ) : Fin (r + 1) → ℂ) := by
  funext i
  rw [deningerInclCLM_apply]
  by_cases h : (i : ℕ) < r
  · rw [dif_pos h, Pi.single_apply, Pi.single_apply]
    by_cases hij : (⟨(i : ℕ), h⟩ : Fin r) = j.castPred hj
    · rw [if_pos hij, if_pos]
      exact Fin.ext (by simpa using congrArg Fin.val hij)
    · rw [if_neg hij, if_neg]
      intro hcon
      exact hij (Fin.ext (by simpa using congrArg Fin.val hcon))
  · rw [dif_neg h, Pi.single_apply, if_neg]
    intro hcon
    apply h
    rw [hcon]
    exact Fin.val_lt_last hj

/-- The projection sends a coordinate vector other than the last to the corresponding coordinate
vector of the divisor. -/
theorem deningerProj_basis {j : Fin (r + 1)} (hj : j ≠ Fin.last r) :
    deningerProjCLM r (Pi.single j (1 : ℂ) : Fin (r + 1) → ℂ) =
      (Pi.single (j.castPred hj) (1 : ℂ) : Fin r → ℂ) := by
  rw [← deningerIncl_basis hj, deningerProj_incl]

/-- **A form with vanishing residue is extended from the divisor.**  On a tuple of coordinate
vectors avoiding the last coordinate both sides agree because the projection and the inclusion are
inverse there; on a tuple containing the last coordinate the extension vanishes because the
projection kills it, and the form itself vanishes because moving that entry to the front turns it
into the residue. -/
theorem deningerResidue_exact (α : (Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (hα : deningerResidueForm r n α = 0) :
    α = deningerExtendForm r (n + 1)
      (ContinuousAlternatingMap.compContinuousLinearMap α (deningerInclCLM r)) := by
  classical
  set β : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ :=
    ContinuousAlternatingMap.compContinuousLinearMap α (deningerInclCLM r) with hβ
  refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
  refine (Pi.basisFun ℂ (Fin (r + 1))).ext_alternating fun φ hφ => ?_
  have hbasis : ∀ j : Fin (r + 1), (Pi.basisFun ℂ (Fin (r + 1))) j =
      (Pi.single j (1 : ℂ) : Fin (r + 1) → ℂ) := fun j => by simp [Pi.basisFun_apply]
  simp only [hbasis]
  show α (fun a => (Pi.single (φ a) (1 : ℂ) : Fin (r + 1) → ℂ)) =
    deningerExtendForm r (n + 1) β fun a => (Pi.single (φ a) (1 : ℂ) : Fin (r + 1) → ℂ)
  rw [deningerExtendForm_eq, deningerExtendAlternating_apply]
  by_cases hlast : ∀ a, φ a ≠ Fin.last r
  · have hproj : ∀ a, deningerProjCLM r (Pi.single (φ a) (1 : ℂ) : Fin (r + 1) → ℂ) =
        (Pi.single ((φ a).castPred (hlast a)) (1 : ℂ) : Fin r → ℂ) :=
      fun a => deningerProj_basis (hlast a)
    simp only [hproj]
    rw [hβ]
    show _ = α fun a => deningerInclCLM r
      (Pi.single ((φ a).castPred (hlast a)) (1 : ℂ) : Fin r → ℂ)
    simp only [deningerIncl_basis]
  · push Not at hlast
    obtain ⟨a₀, ha₀⟩ := hlast
    -- the extension vanishes: the projection kills the last coordinate vector
    have hright : (α.compContinuousLinearMap (deningerInclCLM r))
        (fun a => deningerProjCLM r (Pi.single (φ a) (1 : ℂ) : Fin (r + 1) → ℂ)) = 0 := by
      refine ContinuousMultilinearMap.map_coord_zero
        (ContinuousAlternatingMap.compContinuousLinearMap α
          (deningerInclCLM r)).toContinuousMultilinearMap a₀ ?_
      show deningerProjCLM r (Pi.single (φ a₀) (1 : ℂ) : Fin (r + 1) → ℂ) = 0
      rw [ha₀]
      exact deningerProjCLM_single_last
    -- the form itself vanishes: move the last coordinate vector to the front
    have hleft : α (fun a => (Pi.single (φ a) (1 : ℂ) : Fin (r + 1) → ℂ)) = 0 := by
      set v : Fin (n + 1) → (Fin (r + 1) → ℂ) :=
        fun a => (Pi.single (φ a) (1 : ℂ) : Fin (r + 1) → ℂ) with hv
      set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 a₀ with hσ
      have hzero : α (v ∘ σ) = 0 := by
        have hhead : (v ∘ σ) 0 = (Pi.single (Fin.last r) (1 : ℂ) : Fin (r + 1) → ℂ) := by
          show v (Equiv.swap 0 a₀ 0) = _
          rw [Equiv.swap_apply_left]
          show (Pi.single (φ a₀) (1 : ℂ) : Fin (r + 1) → ℂ) = _
          rw [ha₀]
        have htail : ∀ a : Fin n, ∃ u : Fin r → ℂ,
            deningerInclCLM r u = Fin.tail (v ∘ σ) a := by
          intro a
          have hne : φ (σ a.succ) ≠ Fin.last r := by
            intro hcon
            have hinj : σ a.succ = a₀ := hφ (by rw [hcon, ha₀])
            have hsucc : a.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero a
            rcases eq_or_ne a.succ a₀ with h | h
            · rw [hσ, h, Equiv.swap_apply_right] at hinj
              exact hsucc (hinj ▸ h)
            · rw [hσ, Equiv.swap_apply_of_ne_of_ne hsucc h] at hinj
              exact h hinj
          refine ⟨(Pi.single ((φ (σ a.succ)).castPred hne) (1 : ℂ) : Fin r → ℂ), ?_⟩
          rw [deningerIncl_basis hne]
          rfl
        choose u hu using htail
        have hcons : (v ∘ σ) = Fin.cons ((v ∘ σ) 0) (Fin.tail (v ∘ σ)) :=
          (Fin.cons_self_tail _).symm
        rw [hcons, hhead]
        have hval : α (Fin.cons (Pi.single (Fin.last r) (1 : ℂ) : Fin (r + 1) → ℂ)
            (Fin.tail (v ∘ σ))) = deningerResidueForm r n α u := by
          rw [deningerResidueForm_eq, deningerResidueFun_apply]
          congr 1
          funext a
          refine Fin.cases rfl (fun b => ?_) a
          rw [Fin.cons_succ, Fin.cons_succ, hu b]
        rw [hval, hα]
        rfl
      have hsign : α (v ∘ σ) = Equiv.Perm.sign σ • α v := α.map_perm v σ
      rw [hzero] at hsign
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1] at hsign
      · simpa using hsign.symm
      · have := hsign.symm
        simpa using neg_eq_zero.1 (by simpa using this)
    rw [hleft, hβ]
    exact hright.symm

end Exactness

end RHTower

namespace RHTower

open Complex

section Surjectivity

variable {r n : ℕ}

instance deningerAlt_finiteDimensional (r k : ℕ) :
    FiniteDimensional ℂ ((Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ) :=
  Module.Finite.of_basis (deningerDetFormBasis r k)

/-- **The dimension of the constant alternating forms** is the number of coordinate subsets. -/
theorem deningerAlt_finrank (r k : ℕ) :
    Module.finrank ℂ ((Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ) = r.choose k := by
  rw [Module.finrank_eq_card_basis (deningerDetFormBasis r k)]
  rw [Fintype.card_finset_len]
  simp

/-- **The residue is onto.**  Its kernel is the image of the extension, whose dimension is the
number of subsets avoiding the last coordinate, and the Pascal identity leaves exactly the dimension
of the forms on the divisor. -/
theorem deningerResidueForm_surjective : Function.Surjective (deningerResidueForm r n) := by
  have hker : LinearMap.ker (deningerResidueForm r n) =
      LinearMap.range (deningerExtendForm r (n + 1)) := by
    refine le_antisymm (fun α hα => ?_) (fun α hα => ?_)
    · exact ⟨ContinuousAlternatingMap.compContinuousLinearMap α (deningerInclCLM r),
        (deningerResidue_exact α hα).symm⟩
    · obtain ⟨β, rfl⟩ := hα
      exact deningerResidue_comp_extend β
  have hrange : Module.finrank ℂ (LinearMap.range (deningerExtendForm r (n + 1))) =
      r.choose (n + 1) := by
    rw [LinearMap.finrank_range_of_inj deningerExtendForm_injective, deningerAlt_finrank]
  have hsum := LinearMap.finrank_range_add_finrank_ker (deningerResidueForm r n)
  rw [hker, hrange, deningerAlt_finrank] at hsum
  have hpascal : (r + 1).choose (n + 1) = r.choose n + r.choose (n + 1) := Nat.choose_succ_succ r n
  have hfin : Module.finrank ℂ (LinearMap.range (deningerResidueForm r n)) = r.choose n := by
    omega
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hfin, deningerAlt_finrank]

/-- **The logarithmic residue sequence of a stage and its divisor is exact**: a constant form on
the stage has vanishing residue exactly when it is extended from the divisor. -/
theorem deningerResidue_exact_sequence :
    Function.Exact (deningerExtendForm r (n + 1)) (deningerResidueForm r n) := by
  intro α
  constructor
  · intro h
    exact ⟨ContinuousAlternatingMap.compContinuousLinearMap α (deningerInclCLM r),
      (deningerResidue_exact α h).symm⟩
  · rintro ⟨β, rfl⟩
    exact deningerResidue_comp_extend β

end Surjectivity

end RHTower
