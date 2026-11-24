import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphOriginComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphOriginNumerator
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphResidueTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalAppendedClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LaurentOriginResidue

/-! The diagonal action and graph residue identify the alternating
trace of a finite étale correspondence with its fixed origin values. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E L : Type} [Field k] [CharZero k] [IsAlgClosed k]
  [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  [Module.Finite E L] [Algebra.Etale E L] {d p q : ℕ} {x : Fin (d + 1) → F}
  (j₂ : E →ₐ[k] L)

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "ι" => Fin (d + 1)
local notation "B₀" => rB k L x {0}
local notation "R" => fun I J => RY x j₂ I J
local notation "C" => cech (fun I => omB k E (rB k E x I) p)
local notation "P" => cech (fun I : Finset (ChartPair d) => omB k L ((R) (lft I) (rgt I)) p)
local notation "Fixed" => fun f : OriginFibrePoint k L x => IsFix B₀ (Subtype.val f) j₂ (rB k E x {0})
local notation "j₁" => IsScalarTower.toAlgHom k E L

open Classical in
/-- With the fixed points on the reduced origin fibre, the column
residue is the cotangent characteristic coefficient divided by the
determinant of the graph intersection. -/
theorem IsFinCover.alternatingTrace_eq_fixedOrigin
    (hE : IsFinCover k E x) (hL : IsFinCover k L x) (hqp : q + p = d)
    [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)] [IsReduced (B₀ ⧸ originIdeal k L x)]
    (hfinite : ∀ I J : Finset ι, I.Nonempty → J.Nonempty → Algebra.FiniteType k ((R) I J))
    (hchart : ∀ A B : Finset (ChartPair d), A.Nonempty → A ⊆ B →
      (R) (lft A) (rgt A) ≤ (R) (lft B) (rgt B))
    (hgraph : ∀ {m : ℕ} {n : Fin m → ℕ × ℕ} {z : Fin m → E ⊗[k] E}
      (hz : NormalizedDiagonalEquations hE.pd n z)
      (I J : Finset ι) {i j : ι} (hi : i ∈ I) (hj : j ∈ J) (e : (R) I J →ₐ[k] k),
      (∀ l, e ⟨_, graphAffineWeight_mem hE.pd j₂ hz hi hj l⟩ = 0) →
      I = {0} ∧ J = {0} ∧
        ∃ f : OriginFibrePoint k L x, (Fixed) f ∧
          ∀ a b, Val ((R) I J) e a b ↔ Val B₀ f.1 a b)
    (horigin : ∀ (I J : Finset ι) {i j : ι} (hi : i ∈ I) (hj : j ∈ J) (e : (R) I J →ₐ[k] k),
      (∀ l, e ⟨_, originAffineWeight_mem hE.pd j₂ hi hj l⟩ = 0) →
      I = {0} ∧ ∃ f : OriginFibrePoint k L x, ∀ a b, Val ((R) I J) e a b ↔ Val B₀ f.1 a b)
    (A : OriginFibrePoint k L x → Matrix (Fin d) (Fin d) k)
    (hrow : ∀ f, (Fixed) f → ∀ m, ∃ (c : B₀) (g : Fin d → B₀), f.1 c ≠ 0 ∧
      (c : L) * j₂ (algebraMap F E (x m.succ / x 0)) =
        ∑ l, (g l : L) * algebraMap F L (x l.succ / x 0) ∧
      ∀ l, f.1 (g l) = f.1 c * A f m l)
    (hdet : ∀ f, (Fixed) f → (1 - A f).det ≠ 0)
    [∀ m : ℕ, Module.Finite k ((C).H (m : ℤ))]
    (u : ∀ m : ℕ, (C).H (m : ℤ) →ₗ[k] (C).H (m : ℤ))
    (hlift : ∀ m : ℕ, ∀ a : (C).Z (m : ℤ), ∃ b ∈ (P).Z (m : ℤ),
      (∀ J, b (uni ∅ J) = pullbackDR j₂ (a.val J)) ∧
      ∃ a' : (C).Z (m : ℤ), (∀ I, a'.val I = traceDR k E L (b (uni I ∅))) ∧
        u m (Submodule.Quotient.mk a) = Submodule.Quotient.mk a')
    (hedge : ∀ a' ∈ (cech (fun I => omB k L (rB k L x I) d)).Z (d : ℤ),
      edge1 a' ∈ (mixedCech (fun I J => omB k L ((R) I J) d)).B ((d : ℤ) + 2) →
        a' ∈ (cech (fun I => omB k L (rB k L x I) d)).B (d : ℤ)) :
    ∑ m ∈ Finset.range (d + 1), (-1 : k) ^ m * LinearMap.trace k _ (u m) =
      ∑ᶠ f : OriginFibrePoint k L x,
        if (Fixed) f then
          (1 + (Polynomial.X : Polynomial k) • (A f).map Polynomial.C).det.coeff p / (1 - A f).det
        else 0 := by
  classical
  obtain ⟨τ, hτ⟩ := hE.topDegreeForms.1
  obtain ⟨ρ, hρ⟩ := hE.pd.exists_residue
  have hpq : p + q = d := (Nat.add_comm _ _).trans hqp
  obtain ⟨m, n, z, hz⟩ := hE.exists_normalizedDiagonalEquations
  obtain ⟨c, hc, hcol⟩ := hE.exists_appendedDiagonalCocycle τ hτ hpq hz
  let c₀ := restrictAppendedDiagonal q p c
  let T := diagonalChartSystem (E := E) hE.pd q p
  let U := graphChartSystem hE.pd j₂ q p
  let G := Fin m ⊕ₗ DiagonalIndex d
  let S := normalizedDiagonalSystem (E := E) hE.pd q p
  let N : G → ℕ × ℕ := appendedDiagonalDegrees n
  let Z := appendedDiagonalWeights hE.pd q p z
  let Z' := graphScalarMap (j₁) j₂ ∘ Z
  let f (a : Finset (ChartPair d ⊕ₗ G) →
      ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)
      (I : Finset (ChartPair d ⊕ₗ G)) : DR k L :=
    graphFormPullback (j₁) j₂ (a I)
  let g := f c
  have hg : g ∈ (U.complex N Z').Z ((d : ℤ) + 2) := by
    have hm := graphFormPullback_isMap hE.pd j₂ q p N Z ((d : ℤ) + 2) c hc.1
    refine ⟨hm.1, ?_⟩
    have hd : (S.complex N Z).D c = 0 := hc.2
    have hf₀ : f 0 = 0 := funext fun _ => map_zero (graphFormPullback (j₁) j₂)
    change (U.complex N Z').D (f c) = 0
    exact hm.2.symm.trans ((congrArg f hd).trans hf₀)
  have hc₀ := restrictAppendedDiagonal_mem_cycles hE.pd q p hc
  have hact := hE.diagonalCechPart_acts τ hτ ρ hρ hpq hc₀
    (T.lev_rightIndices_of_mem_complex_terms hc₀.1)
    (fun i j L hL v => by
      simpa only [c₀, restrictAppendedDiagonal, lft_uni, rgt_uni] using hcol i j L hL v)
  let coeff (f : OriginFibrePoint k L x) : k :=
    (1 + (Polynomial.X : Polynomial k) • (A f).map Polynomial.C).det.coeff p
  let a (f : OriginFibrePoint k L x) : k := if (Fixed) f then coeff f / (1 - A f).det else 0
  obtain ⟨b, hb⟩ := (trace_originFibre hL).2.1 a
  have hb₀ (f : OriginFibrePoint k L x) (hf : ¬ (Fixed) f) : f.1 b = 0 :=
    (congrFun hb f).trans (if_neg hf)
  let I := selectedIndices (diagonalIndexEmbedding (0 : ι))
  have hI : I.card = d := by simp [I, selectedIndices]
  have hS : selectedIndices (graphOriginSelection (κ := Fin m) (d := d)) = uni ∅ I := by
    have hmap : I.map (joinedRight : DiagonalIndex d ↪o G).toEmbedding = uni ∅ I :=
      map_joinedRight I
    rw [← hmap]
    simp only [I, selectedIndices, Finset.map_map] <;> rfl
  let b₀ (K : Finset G) := c (uni (uni {0} {0}) K)
  have ht : (fun K => b₀ (uni ∅ K)) ∈
      (T.columnComplex (fun _ => (1, 1)) T.homogeneousMinor {0} {0}).C (d : ℤ) := by
    have hcol₀ : (fun K => b₀ (uni ∅ K)) =
        fun K : Finset (DiagonalIndex d) => c₀ (uni (uni {0} {0}) K) := by
      funext K
      simp only [c₀, b₀, restrictAppendedDiagonal, lft_uni, rgt_uni]
    rw [hcol₀]
    exact (T.singletonColumn_mem_cycles (n := fun _ : DiagonalIndex d => (1, 1))
      (z := T.homogeneousMinor) (c := c₀) hc₀ 0 0).1
  have hgCech := chartPart_graph_sub_origin_mem_boundary hE.pd j₂ hL hqp hz hfinite
    (hgraph hz) horigin A hrow hdet b hb₀ hg (fun a₀ ha₀ => by
      obtain ⟨s, hs, hv⟩ := hE.graphOriginValue_of_diagonalColumn hL j₂ a₀ ha₀
        (A a₀) (hrow a₀ ha₀) τ hτ hqp ρ hρ n b₀ ht (hcol 0 0 I hI)
      refine ⟨s, ?_, ?_⟩
      · simpa only [hS, g, f, b₀] using hs
      · have hb' : a₀.1 b = coeff a₀ / (1 - A a₀).det :=
          (congrFun hb a₀).trans (if_pos ha₀)
        rw [hb', mul_comm ((1 - A a₀).det), div_mul_cancel₀ _ (hdet a₀ ha₀)]
        exact hv)
  have hG : (fun I => graphDRPullback (j₁) j₂ (diagonalCechPart c₀ I)) = chartPart g := by
    funext I
    rw [show diagonalCechPart c₀ = diagonalCechPart c from
      diagonalCechPart_restrictAppendedDiagonal c]
    exact graphDRPullback_diagonalCechPart j₂ c I
  have hM : U.M = fun I J => omB k L ((R) I J) d :=
    funext fun I => funext fun J => congrArg (omB k L ((R) I J)) hqp
  change _ ∈ (mixedCech U.M).B ((d : ℤ) + 2) at hgCech
  rw [hM] at hgCech
  have htrace := IsFinCover.alternatingTrace_eq_residue_of_graph j₂ hE hL hqp hchart
    τ hτ ρ hρ u hlift hedge hact.1 (fun m _ => hact.2 m) b (hG.symm ▸ hgCech)
  rw [htrace, hL.residue_trace_origin ρ hρ]
  exact congrArg finsum hb

end GlobalTheory.PD
