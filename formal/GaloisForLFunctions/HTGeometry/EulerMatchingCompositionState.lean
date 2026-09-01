import GaloisForLFunctions.HTGeometry.DerivationAlgebraicStability
import GaloisForLFunctions.HTGeometry.AdjoinSingletonAlgebraicWitness
import GaloisForLFunctions.HTGeometry.EulerCompositionPolynomialRigidity
import GaloisForLFunctions.HTGeometry.CompositionJetTrdeg
import GaloisForLFunctions.HTGeometry.PrimeRadialRelativeJetRank
import GaloisForLFunctions.HTGeometry.StateFieldTrdeg
import GaloisForLFunctions.HTGeometry.TwoDefectDecomposition

/-!
# The Euler matching state of a composition

The observability determinant of a composition degenerates exactly when the outer derivative obeys
`x·∂_x A + A = 0`, i.e. when the product state `x·A = g·(f′∘g)` is annihilated by the coordinate
derivation along the inner function.  This file shows that the degeneration forces the outer factor
to be a polynomial.

The mechanism is a transcendence count.  The product state lies in the algebraic closure of
`ℂ(g, f∘g)`, which has transcendence degree two.  If it were transcendental over `ℂ(f∘g)`, the
inner state `g` — which the coordinate derivation moves, hence is transcendental over the field the
derivation kills — would add a third degree.  So the product state is algebraic over `ℂ[f∘g]`, and a
denominator-free witness for that algebraicity is exactly the Euler relation
`∑_k C_k(f)·(z f′)^k = 0`, which makes `f` a polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

variable {f g : ℂ → ℂ}

/-- A non-polynomial entire function is nonconstant. -/
theorem not_const_of_not_polynomial (h : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z) :
    ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c := by
  rintro ⟨c, hc⟩
  exact h ⟨Polynomial.C c, fun z => by rw [hc z, Polynomial.eval_C]⟩

/-- A composition whose outer factor is not a polynomial is nonconstant. -/
theorem not_const_comp_of_not_polynomial (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) :
    ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c := by
  rintro ⟨c, hc⟩
  refine not_const_of_not_polynomial hfnp ⟨c, fun w => ?_⟩
  by_contra hne
  have hFne : ∃ w : ℂ, (fun u : ℂ => f u - c) w ≠ 0 := ⟨w, sub_ne_zero.mpr hne⟩
  obtain ⟨z, hz⟩ := exists_ne_zero_comp (hf.sub (differentiable_const c)) hg hFne hncg
  exact hz (by simp [hc z])

/-- **The Euler matching equation forces the outer factor to be a polynomial.** -/
theorem exists_polynomial_of_euler_matching (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) (hncf : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c)
    (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c)
    (hyx : AlgebraicIndependent ℂ ![jetElem hcomp 0, jetElem hg 0])
    (hA : IsAlgebraic ↥(IntermediateField.adjoin ℂ
        (Set.range ![jetElem hcomp 0, jetElem hg 0])) (compJetElem hf hg 1))
    (Dx : Derivation ℂ (meroField (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ)))
    (hDxx : Dx (jetElem hg 0) = 1) (hDxy : Dx (jetElem hcomp 0) = 0)
    (hmatch : jetElem hg 0 * Dx (compJetElem hf hg 1) + compJetElem hf hg 1 = 0) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z := by
  classical
  set x : meroField (Set.univ : Set ℂ) := jetElem hg 0 with hxdef
  set y : meroField (Set.univ : Set ℂ) := jetElem hcomp 0 with hydef
  set A : meroField (Set.univ : Set ℂ) := compJetElem hf hg 1 with hAdef
  set K : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin ℂ (Set.range ![y, x]) with hKdef
  set u : meroField (Set.univ : Set ℂ) := x * A with hudef
  -- the coordinate derivation kills the product state
  have hDxu : Dx u = 0 := by
    rw [hudef, Dx.leibniz, smul_eq_mul, smul_eq_mul, hDxx, mul_one]
    exact hmatch
  -- the product state lies in the relative algebraic closure of `K`
  have hxK : x ∈ K := IntermediateField.subset_adjoin ℂ _ ⟨1, rfl⟩
  have hyK : y ∈ K := IntermediateField.subset_adjoin ℂ _ ⟨0, rfl⟩
  set MK : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    (algebraicClosure ↥K (meroField (Set.univ : Set ℂ))).restrictScalars ℂ with hMKdef
  have hxMK : x ∈ MK := mem_algebraicClosure_restrictScalars_of_mem K hxK
  have hyMK : y ∈ MK := mem_algebraicClosure_restrictScalars_of_mem K hyK
  have hAMK : A ∈ MK := by
    rw [hMKdef, IntermediateField.mem_restrictScalars]
    exact mem_algebraicClosure_iff.mpr hA
  have huMK : u ∈ MK := IntermediateField.mul_mem _ hxMK hAMK
  have htrdegMK : Algebra.trdeg ℂ ↥MK = Cardinal.mk (Fin 2) := by
    rw [hMKdef, trdeg_algebraicClosure_restrictScalars_eq, hKdef]
    exact trdeg_intermediateFieldAdjoin_range_eq_cardinalMk_of_algebraicIndependent _ hyx
  -- the product state is algebraic over `ℂ[f ∘ g]`
  have hAlg : IsAlgebraic ↥(Algebra.adjoin ℂ ({y} : Set L)) u := by
    by_contra hut
    have hpair : AlgebraicIndependent ℂ ![u, y] :=
      algebraicIndependent_pair_of_transcendental (R := ℂ) y u
        (transcendental_jetElem_zero hcomp hncomp) hut
    have hbase : Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (Set.range ![u, y]))
        = Cardinal.mk (Fin 2) :=
      trdeg_intermediateFieldAdjoin_range_eq_cardinalMk_of_algebraicIndependent _ hpair
    have hker : ∀ w ∈ Set.range ![u, y], Dx w = 0 := by
      rintro w ⟨j, rfl⟩
      fin_cases j
      · exact hDxu
      · exact hDxy
    have hxtr : ¬ IsAlgebraic ↥(IntermediateField.adjoin ℂ (Set.range ![u, y])) x := by
      intro halg
      have h0 := derivationBase_eq_zero_of_isAlgebraic_adjoin Dx hker halg
      rw [hDxx] at h0
      exact one_ne_zero h0
    have hins : Algebra.trdeg ℂ
        ↥(IntermediateField.adjoin ℂ (insert x (Set.range ![u, y])))
        = Cardinal.mk (Fin 2) + 1 :=
      (trdeg_adjoin_insert_eq_add_one hxtr).trans (congrArg (fun c : Cardinal => c + 1) hbase)
    have hle : IntermediateField.adjoin ℂ (insert x (Set.range ![u, y])) ≤ MK := by
      rw [IntermediateField.adjoin_le_iff]
      rintro w (rfl | ⟨j, rfl⟩)
      · exact hxMK
      · fin_cases j
        · exact huMK
        · exact hyMK
    have hmono : Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (insert x (Set.range ![u, y])))
        ≤ Algebra.trdeg ℂ ↥MK := by
      have heq := trdeg_add_relTrdeg hle
      calc Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (insert x (Set.range ![u, y])))
          ≤ Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (insert x (Set.range ![u, y])))
              + relTrdeg hle := le_self_add
        _ = Algebra.trdeg ℂ ↥MK := heq
    have hcard : Cardinal.mk (Fin 2) + 1 ≤ Cardinal.mk (Fin 2) := by
      rw [← hins, ← htrdegMK]; exact hmono
    rw [Cardinal.mk_fin] at hcard
    have hnat : ((3 : ℕ) : Cardinal) ≤ ((2 : ℕ) : Cardinal) := by push_cast; push_cast at hcard;
      exact hcard
    exact absurd (Cardinal.natCast_le.mp hnat) (by norm_num)
  -- a denominator-free witness is the Euler relation
  obtain ⟨m, C, hCm, hrelsum⟩ :=
    exists_polynomialCoeff_relation_of_isAlgebraic_adjoin_singleton hAlg
  have hCmne : C m ≠ 0 := by
    intro h0
    exact hCm (by rw [h0]; exact map_zero _)
  exact exists_polynomial_of_euler_mero_relation hf hg hcomp hncg hncf
    ⟨m, Finset.self_mem_range_succ m, hCmne⟩ hrelsum

end

end GaloisForLFunctions.HTGeometry
