import GaloisForLFunctions.HTGeometry.ArithmeticMinimum

/-!
# The thick part of the cone of positive definite forms

The forms whose arithmetic minimum exceeds a given bound are an **open**, `SL(n, ℤ)`-invariant
subset of the cone.  Openness is not a finite intersection of conditions — there are infinitely many
lattice vectors — but only finitely many of them can come close to the bound at a given form, and
the remaining ones are handled uniformly by comparing with a slightly shrunken copy of that form.

* `thickPart` : the forms with arithmetic minimum above `c`.
* `isOpen_thickPart` : **it is open.**
* `thickPart_smul` : **it is invariant.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The forms whose value on every nonzero integer vector exceeds `c`. -/
def thickPart (c : ℝ) : Set (posDefCone n) :=
  {A | ∀ v : Fin n → ℤ, v ≠ 0 → c < quadForm A (intVec v)}

theorem continuous_quadForm_fixed (y : Fin n → ℝ) :
    Continuous fun A : posDefCone n => quadForm A y := by
  unfold quadForm
  simp only [dotProduct, Matrix.mulVec]
  refine continuous_finsetSum _ fun i _ => ?_
  refine Continuous.mul continuous_const ?_
  refine continuous_finsetSum _ fun j _ => ?_
  refine Continuous.mul ?_ continuous_const
  exact (continuous_apply j).comp ((continuous_apply i).comp
    (continuous_subtype_val.comp continuous_subtype_val))

theorem quadForm_nonneg_of_posDef {A : symmMatrices n}
    (hA : (A : Matrix (Fin n) (Fin n) ℝ).PosDef) (y : Fin n → ℝ) :
    0 ≤ y ⬝ᵥ ((A : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) := by
  by_cases hy : y = 0
  · subst hy
    rw [Matrix.mulVec_zero, dotProduct_zero]
  · have h3 : 0 < y ⬝ᵥ ((A : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) := by
      simpa using (Matrix.posDef_iff_dotProduct_mulVec.mp hA).2 hy
    exact h3.le

/-- **The thick part is invariant.** -/
theorem thickPart_smul (c : ℝ) (g : Matrix.SpecialLinearGroup (Fin n) ℤ) {A : posDefCone n}
    (hA : A ∈ thickPart (n := n) c) : g • A ∈ thickPart (n := n) c := by
  intro v hv
  rw [quadForm_smul_group]
  have hval : (slReal g)ᵀ *ᵥ (intVec v) = intVec ((g : Matrix (Fin n) (Fin n) ℤ)ᵀ *ᵥ v) := by
    funext i
    show ∑ j, ((slReal g)ᵀ i j) * (v j : ℝ) = ((∑ j, ((g : Matrix (Fin n) (Fin n) ℤ)ᵀ i j) * v j : ℤ) : ℝ)
    push_cast
    rfl
  rw [hval]
  refine hA _ ?_
  intro hcon
  apply hv
  have hinj : Function.Injective
      (fun w : Fin n → ℤ => (g : Matrix (Fin n) (Fin n) ℤ)ᵀ *ᵥ w) := by
    intro a b hab
    have hdet : IsUnit ((g : Matrix (Fin n) (Fin n) ℤ)ᵀ).det := by
      rw [Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe]
      exact isUnit_one
    exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hdet) hab
  refine hinj (show (g : Matrix (Fin n) (Fin n) ℤ)ᵀ *ᵥ v = (g : Matrix (Fin n) (Fin n) ℤ)ᵀ *ᵥ 0 from ?_)
  rw [hcon, Matrix.mulVec_zero]


/-- Domination of quadratic forms from positive definiteness of the difference. -/
theorem quadForm_ge_of_sub_posDef {A B : posDefCone n} {t : ℝ}
    (h : (((A : symmMatrices n) - t • (B : symmMatrices n) : symmMatrices n) :
        Matrix (Fin n) (Fin n) ℝ).PosDef) (y : Fin n → ℝ) :
    t * quadForm B y ≤ quadForm A y := by
  have hnn := quadForm_nonneg_of_posDef h y
  have hval : (((A : symmMatrices n) - t • (B : symmMatrices n) : symmMatrices n) :
      Matrix (Fin n) (Fin n) ℝ)
      = ((A : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ)
        - t • ((B : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [hval, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul] at hnn
  unfold quadForm
  linarith

/-- **The thick part is open.**  Infinitely many lattice vectors have to be controlled at once.
Only finitely many of them take a value near the bound, and those are handled by continuity; all the
remaining ones are handled uniformly, by comparing with a shrunken copy of the given form — a
comparison that persists on a neighbourhood because the positive definite cone is open. -/
theorem isOpen_thickPart (c : ℝ) (hn : 0 < n) : IsOpen (thickPart (n := n) c) := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro A₀ hA₀
  set S : Set (Fin n → ℤ) := {v | v ≠ 0 ∧ quadForm A₀ (intVec v) ≤ 2 * c + 2} with hSdef
  have hSfin : S.Finite :=
    (finite_latticePoints_le A₀ hn (2 * c + 2)).subset (fun v hv => hv.2)
  have hcontshift : Continuous fun A : posDefCone n =>
      ((A : symmMatrices n) - (1 / 2 : ℝ) • (A₀ : symmMatrices n)) :=
    (continuous_subtype_val).sub continuous_const
  have hUopen : IsOpen ((fun A : posDefCone n =>
      ((A : symmMatrices n) - (1 / 2 : ℝ) • (A₀ : symmMatrices n))) ⁻¹' posDefCone n) :=
    isOpen_posDefCone.preimage hcontshift
  have hA₀U : A₀ ∈ (fun A : posDefCone n =>
      ((A : symmMatrices n) - (1 / 2 : ℝ) • (A₀ : symmMatrices n))) ⁻¹' posDefCone n := by
    show (((A₀ : symmMatrices n) - (1 / 2 : ℝ) • (A₀ : symmMatrices n) : symmMatrices n) :
      Matrix (Fin n) (Fin n) ℝ).PosDef
    have hval : (((A₀ : symmMatrices n) - (1 / 2 : ℝ) • (A₀ : symmMatrices n) : symmMatrices n) :
        Matrix (Fin n) (Fin n) ℝ)
        = (1 / 2 : ℝ) • ((A₀ : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ) := by
      show ((A₀ : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ)
          - (1 / 2 : ℝ) • ((A₀ : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ) = _
      module
    rw [hval]
    exact A₀.2.smul (by norm_num)
  have hVopen : IsOpen (⋂ v ∈ S, {A : posDefCone n | c < quadForm A (intVec v)}) :=
    hSfin.isOpen_biInter fun v _ => isOpen_lt continuous_const (continuous_quadForm_fixed _)
  have hA₀V : A₀ ∈ ⋂ v ∈ S, {A : posDefCone n | c < quadForm A (intVec v)} :=
    Set.mem_iInter₂.2 fun v hv => hA₀ v hv.1
  refine Filter.mem_of_superset
    (Filter.inter_mem (hUopen.mem_nhds hA₀U) (hVopen.mem_nhds hA₀V)) ?_
  rintro A ⟨hAU, hAV⟩ v hv
  by_cases hvS : v ∈ S
  · exact Set.mem_iInter₂.1 hAV v hvS
  · have hbig : 2 * c + 2 < quadForm A₀ (intVec v) := by
      by_contra hcon
      exact hvS ⟨hv, not_lt.1 hcon⟩
    have hge : (1 / 2 : ℝ) * quadForm A₀ (intVec v) ≤ quadForm A (intVec v) :=
      quadForm_ge_of_sub_posDef hAU _
    linarith

end GaloisForLFunctions.HTGeometry
