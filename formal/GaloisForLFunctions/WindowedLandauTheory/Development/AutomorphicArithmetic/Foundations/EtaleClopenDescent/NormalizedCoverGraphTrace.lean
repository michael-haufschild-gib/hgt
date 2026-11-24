import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteCoverGraphTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphOriginZeros
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedChartCocycle
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedAffineColumnExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AboveDimensionTrace

/-! On a normalized projective cover the graph residue computes
the actual pullback–trace action on Hodge cohomology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace UpperTheory.Cb
open GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR TensorProduct

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y]
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {c₁ c₂ : Y ⟶ Z} [IsFinite c₁] [Etale c₁] [IsDominant c₁] [IsFinite c₂] [IsDominant c₂]
  {d : ℕ} [Smooth s] [SmoothOfRelativeDimension d t] [IsSeparated s]

open Classical in
/-- The normalized fixed-fibre values are the alternating Hodge
trace, with the graph intersection determinants in the denominator. -/
theorem alternatingHodgeTrace_eq_fixedOrigin (h₁ : c₁ ≫ s = t) (h₂ : c₂ ≫ s = t) (hp : IsProjOver s) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    letI := c₁.functionFieldPullback.hom.toAlgebra
    letI := functionFieldPullback_scalarTower h₁
    ∀ {F : Type} [Field F] [Algebra k F] [Algebra F Z.functionField] [Algebra F Y.functionField]
      [IsScalarTower k F Z.functionField] [IsScalarTower k F Y.functionField]
      [IsScalarTower F Z.functionField Y.functionField]
      (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens)
      (hE : IsFinCover k Z.functionField x) (hL : IsFinCover k Y.functionField x)
      (hZ : IsAffCover s U (rB k Z.functionField x))
      (hY : IsAffCover t (fun i => c₁ ⁻¹ᵁ U i) (rB k Y.functionField x))
      [IsReduced ((rB k Z.functionField x {0}) ⧸ originIdeal k Z.functionField x)]
      [IsReduced ((rB k Y.functionField x {0}) ⧸ originIdeal k Y.functionField x)],
      let V (i : Fin (d + 1)) := c₁ ⁻¹ᵁ U i
      let B₀ := rB k Y.functionField x {0}
      let j₂ := functionFieldPullbackAlg c₂ h₂
      let Fixed (f : OriginFibrePoint k Y.functionField x) :=
        IsFix B₀ f.1 j₂ (rB k Z.functionField x {0})
      (∀ y : Y.BaseFieldPointOver k t, y.hom ≫ c₁ = y.hom ≫ c₂ →
        ∃ hy : y.hom default ∈ ({0} : Finset (Fin (d + 1))).inf V,
          ∀ j : Fin d, hY.chartPointEquiv {0} (Finset.singleton_nonempty 0) ⟨y, hy⟩
            ⟨_, tco_mem k Y.functionField x j⟩ = 0) →
      ∀ (A : OriginFibrePoint k Y.functionField x → Matrix (Fin d) (Fin d) k),
      (∀ f, Fixed f → ∀ m, ∃ (c : B₀) (g : Fin d → B₀), f.1 c ≠ 0 ∧
        (c : Y.functionField) * j₂ (algebraMap F Z.functionField (x m.succ / x 0)) =
          ∑ l, (g l : Y.functionField) * algebraMap F Y.functionField (x l.succ / x 0) ∧
        ∀ l, f.1 (g l) = f.1 c * A f m l) →
      (∀ f, Fixed f → (1 - A f).det ≠ 0) →
      ∀ p : ℕ,
      ∑ m ∈ Finset.range (d + 1), (-1 : k) ^ m *
        LinearMap.trace k _ (hodgeTrace h₁ p m ∘ₗ hodgePullback h₂ p m) =
      ∑ᶠ f : OriginFibrePoint k Y.functionField x,
        if Fixed f then
          (1 + (Polynomial.X : Polynomial k) • (A f).map Polynomial.C).det.coeff p / (1 - A f).det
        else 0 := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  letI := c₁.functionFieldPullback.hom.toAlgebra
  letI := functionFieldPullback_scalarTower h₁
  letI := finiteDimensional_functionFieldPullback c₁
  letI := functionFieldPullback_etale (f := c₁) s
  letI : Smooth t := SmoothOfRelativeDimension.smooth d t
  intro F _ _ _ _ _ _ _ x U hE hL hZ hY hredE hredL V B₀ j₂ Fixed hpin A hrow hdet p
  have hff : algebraMap Z.functionField Y.functionField = c₁.functionFieldPullback.hom := rfl
  let R (I J : Finset (Fin (d + 1))) := RY x j₂ I J
  let V₂ (i : Fin (d + 1)) := c₂ ⁻¹ᵁ U i
  let C := cech (fun I => omB k Z.functionField (rB k Z.functionField x I) p)
  let D := cech (fun S : Finset (ChartPair d) => omB k Y.functionField (R (lft S) (rgt S)) p)
  let e (m : ℕ) := hZ.hodgeCechEquiv p m
  let u (m : ℕ) : C.H (m : ℤ) →ₗ[k] C.H (m : ℤ) :=
    (e m).conj (hodgeTrace h₁ p m ∘ₗ hodgePullback h₂ p m)
  letI (m : ℕ) : Module.Finite k (C.H (m : ℤ)) :=
    hZ.finiteDimensional_rationalCech_of_projective hp p m
  have htrace (m : ℕ) :
      LinearMap.trace k _ (hodgeTrace h₁ p m ∘ₗ hodgePullback h₂ p m) =
        LinearMap.trace k _ (u m) := by
    letI := hodgeCohomology_finite_of_projective s hp p m
    exact (LinearMap.trace_conj' (hodgeTrace h₁ p m ∘ₗ hodgePullback h₂ p m) (e m)).symm
  simp_rw [htrace]
  by_cases hp' : p ≤ d
  · let q := d - p
    have hqp : q + p = d := Nat.sub_add_cancel hp'
    have hG := isAffCover_joined_normalized h₁ h₂ hff x U hE hZ
    have hV₂ := isAffCover_pullbackChartAlgebra d h₂ U (rB k Z.functionField x) hZ
    have hne {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) : (uni I J).Nonempty := by
      rw [← Finset.card_pos, card_uni]
      have hi := Finset.card_pos.mpr hI
      omega
    have hfinite (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (_ : J.Nonempty) :
        Algebra.FiniteType k (R I J) := by
      have hR : R (lft (uni I J)) (rgt (uni I J)) = R I J := by
        rw [lft_uni, rgt_uni]
      have hsmooth : Algebra.Smooth k (R (lft (uni I J)) (rgt (uni I J))) :=
        hG.smooth (uni I J) (hne hI)
      letI : Algebra.Smooth k (R I J) :=
        (congrArg (fun B : Subalgebra k Y.functionField => Algebra.Smooth k B) hR).mp hsmooth
      infer_instance
    have hchart (S S' : Finset (ChartPair d)) (hS : S.Nonempty) (hSS' : S ⊆ S') :
        R (lft S) (rgt S) ≤ R (lft S') (rgt S') := hG.algebra_le hS hSS'
    have joined (P : Finset (Fin (d + 1)) → Finset (Fin (d + 1)) → Prop)
        (I J : Finset (Fin (d + 1))) :
        P (lft (uni I J)) (rgt (uni I J)) → P I J := by
      rw [lft_uni, rgt_uni]
      exact id
    let GraphZeroTest {m : ℕ} {n : Fin m → ℕ × ℕ} {z : Fin m → Z.functionField ⊗[k] Z.functionField}
        (hz : NormalizedDiagonalEquations hE.pd n z)
        (I J : Finset (Fin (d + 1))) : Prop :=
      ∀ {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) (ev : R I J →ₐ[k] k),
        (∀ l, ev ⟨_, graphAffineWeight_mem hE.pd j₂ hz hi hj l⟩ = 0) →
        I = {0} ∧ J = {0} ∧
          ∃ f : OriginFibrePoint k Y.functionField x, Fixed f ∧
            ∀ a b, Val (R I J) ev a b ↔ Val B₀ f.1 a b
    have hgraph {m : ℕ} {n : Fin m → ℕ × ℕ} {z : Fin m → Z.functionField ⊗[k] Z.functionField}
        (hz : NormalizedDiagonalEquations hE.pd n z) (I J : Finset (Fin (d + 1))) :
        GraphZeroTest hz I J := by
      refine joined (GraphZeroTest hz) I J ?_
      intro i j hi hj
      have hi' : i ∈ I := by simpa only [lft_uni] using hi
      exact exists_fixedOriginFibre_of_graphWeights_zero j₂ hE.pd hY hG
        (fun a y hy => isFix_normalized_iff h₁ h₂ hff x U hZ hY
          (Finset.singleton_nonempty a) y hy) hpin hz (S := uni I J) (hne ⟨i, hi'⟩) hi hj
    let OriginZeroTest (I J : Finset (Fin (d + 1))) : Prop :=
      ∀ {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) (ev : R I J →ₐ[k] k),
        (∀ l, ev ⟨_, originAffineWeight_mem hE.pd j₂ hi hj l⟩ = 0) →
        I = {0} ∧ ∃ f : OriginFibrePoint k Y.functionField x,
          ∀ a b, Val (R I J) ev a b ↔ Val B₀ f.1 a b
    have horigin (I J : Finset (Fin (d + 1))) : OriginZeroTest I J := by
      refine joined OriginZeroTest I J ?_
      intro i j hi hj
      have hi' : i ∈ I := by simpa only [lft_uni] using hi
      exact exists_originFibre_of_originWeights_zero hE.pd j₂ hY hG
        (S := uni I J) (hne ⟨i, hi'⟩) hi hj
    have hlift (m : ℕ) (a : C.Z (m : ℤ)) :
        ∃ b ∈ D.Z (m : ℤ), (∀ J, b (uni ∅ J) = pullbackDR j₂ (a.val J)) ∧
          ∃ a' : C.Z (m : ℤ), (∀ I, a'.val I = traceDR k Z.functionField Y.functionField (b (uni I ∅))) ∧
            u m (Submodule.Quotient.mk a) = Submodule.Quotient.mk a' := by
      obtain ⟨b, hb, a', ha', h⟩ := exists_joinedChartCocycle h₁ h₂ x hE hZ p m a
      refine ⟨b.val, b.property, hb, a', ha', ?_⟩
      simpa only [u, e, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] using h
    have he₀ (I : Finset (Fin (d + 1))) : R I ∅ = rB k Y.functionField x I := by
      change rB k Y.functionField x I ⊔ pullbackChartAlgebra j₂ (rB k Z.functionField x ∅) = _
      rw [pullbackChartAlgebra_rB_empty, sup_bot_eq]
    have hedge (a : Finset (Fin (d + 1)) → DR k Y.functionField)
        (ha : a ∈ (cech (fun I => omB k Y.functionField (rB k Y.functionField x I) d)).Z (d : ℤ))
        (hb : edge1 a ∈ (mixedCech (fun I J => omB k Y.functionField (R I J) d)).B ((d : ℤ) + 2)) :
        a ∈ (cech (fun I => omB k Y.functionField (rB k Y.functionField x I) d)).B (d : ℤ) := by
      let L (I : Finset (Fin (d + 1))) :=
        let J : Finset (ChartPair d) := uni I ∅
        omB k Y.functionField (R (lft J) (rgt J)) d
      have hL' : L = fun I => omB k Y.functionField (rB k Y.functionField x I) d := by
        funext I
        simp only [L, lft_uni, rgt_uni, he₀]
      have ha' : a ∈ (cech L).Z (d : ℤ) := hL'.symm ▸ ha
      have hb' : edge1 a ∈ (mixedCech (fun I J => omB k Y.functionField
          (R (lft (uni I J)) (rgt (uni I J))) d)).B ((d : ℤ) + 2) := by
        have he : (fun I J => omB k Y.functionField (R (lft (uni I J)) (rgt (uni I J))) d) =
            fun I J => omB k Y.functionField (R I J) d := by
          funext I J
          rw [lft_uni, rgt_uni]
        rwa [he]
      have key : a ∈ (cech L).B (d : ℤ) := hG.leftBoundary_of_mixedEdge hV₂.cover d d ha' hb'
      exact hL' ▸ key
    exact IsFinCover.alternatingTrace_eq_fixedOrigin j₂ hE hL hqp hfinite hchart
      hgraph horigin A hrow hdet u hlift hedge
  · have hgt : d < p := lt_of_not_ge hp'
    have he (m : ℕ) : LinearMap.trace k _ (u m) = 0 :=
      hE.trace_rationalCech_eq_zero_of_dim_lt hgt (m : ℤ) (u m)
    simp only [he, mul_zero, Finset.sum_const_zero, coeff_det_one_add_X_smul_eq_zero_of_dim_lt hgt,
      zero_div, ite_self, finsum_zero]

end GlobalTheory.SchemeCohomology
