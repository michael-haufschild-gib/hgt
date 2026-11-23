import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveChartMorphisms

/-! Pulling back chart ratios and evaluating at the generic point turns
the regular coordinate ratios into quotients of the origin-chart coordinates. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] {d : ℕ}
  (f : X ⟶ PSpace K d)

private abbrev chart (i : Fin (d + 1)) := f ⁻¹ᵁ PSpace.coordinateOpen K d i

/-- The germ of the coordinate ratio Xⱼ/Xᵢ at the generic point of the source. -/
def genericProjectiveRatio (i : Fin (d + 1)) (hi : genericPoint X ∈ chart f i) (j : Fin (d + 1)) :
    X.functionField :=
  (X.presheaf.germ (chart f i) (genericPoint X) hi).hom (pspacePullRatio f (chart f i) i le_rfl j)

/-- Evaluating a ratio at the generic point commutes with restriction
to any smaller open containing that point. -/
theorem germ_pspacePullRatio (U : X.Opens) (hu : genericPoint X ∈ U) (i j : Fin (d + 1))
    (hU : U ≤ chart f i) :
    (X.presheaf.germ U (genericPoint X) hu).hom (pspacePullRatio f U i hU j) =
      genericProjectiveRatio f i (hU hu) j := by
  let V := PSpace.coordinateOpen K d i
  let a := pspaceChartRatio K i j
  have e : pspacePullRatio f (chart f i) i le_rfl j = (f.app V).hom a :=
    congrArg (fun m : Γ(PSpace K d, V) ⟶ Γ(X, chart f i) => m.hom a) f.appLE_eq_app
  change (X.presheaf.germ U (genericPoint X) hu).hom
    ((X.presheaf.map (homOfLE hU).op).hom ((f.app V).hom a)) = _
  have h := X.presheaf.germ_res_apply (homOfLE hU) (genericPoint X) hu ((f.app V).hom a)
  exact h.trans (congrArg (X.presheaf.germ (chart f i) _ (hU hu)).hom e.symm)

theorem genericProjectiveRatio_ne_zero (i j : Fin (d + 1))
    (hi : genericPoint X ∈ chart f i) (hj : genericPoint X ∈ chart f j) :
    genericProjectiveRatio f i hi j ≠ 0 := by
  let a := pspacePullRatio f (chart f i) i le_rfl j
  have e : X.basicOpen a = chart f i ⊓ chart f j := basicOpen_pspacePullRatio f _ i le_rfl j
  have h : genericPoint X ∈ X.basicOpen a := e.symm ▸ show genericPoint X ∈ chart f i ⊓ chart f j from ⟨hi, hj⟩
  exact ((Scheme.mem_basicOpen X a (genericPoint X) hi).mp h).ne_zero

theorem genericProjectiveRatio_mul (i j k : Fin (d + 1))
    (hi : genericPoint X ∈ chart f i) (hj : genericPoint X ∈ chart f j) :
    genericProjectiveRatio f i hi j * genericProjectiveRatio f j hj k =
      genericProjectiveRatio f i hi k := by
  let U := chart f i ⊓ chart f j
  have hU : genericPoint X ∈ U := ⟨hi, hj⟩
  let g := (X.presheaf.germ U (genericPoint X) hU).hom
  have h := congrArg g (pspacePullRatio_mul f U i j k inf_le_left inf_le_right)
  rw [map_mul] at h
  change (X.presheaf.germ U (genericPoint X) hU).hom (pspacePullRatio f U i inf_le_left j) *
    (X.presheaf.germ U (genericPoint X) hU).hom (pspacePullRatio f U j inf_le_right k) =
    (X.presheaf.germ U (genericPoint X) hU).hom (pspacePullRatio f U i inf_le_left k) at h
  rwa [germ_pspacePullRatio, germ_pspacePullRatio, germ_pspacePullRatio] at h

/-- The generic ratio on any chart is a quotient of two coordinates from
the same origin chart. -/
theorem genericProjectiveRatio_eq_div (i j : Fin (d + 1))
    (h₀ : genericPoint X ∈ chart f 0) (hi : genericPoint X ∈ chart f i) :
    genericProjectiveRatio f i hi j =
      genericProjectiveRatio f 0 h₀ j / genericProjectiveRatio f 0 h₀ i := by
  apply (eq_div_iff (genericProjectiveRatio_ne_zero f 0 i h₀ hi)).mpr
  calc
    _ = genericProjectiveRatio f 0 h₀ i * genericProjectiveRatio f i hi j := mul_comm _ _
    _ = _ := genericProjectiveRatio_mul f 0 i j h₀ hi

end GlobalTheory.SchemeCohomology
