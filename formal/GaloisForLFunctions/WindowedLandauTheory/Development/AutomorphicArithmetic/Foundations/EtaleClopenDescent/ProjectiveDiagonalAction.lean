import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.DiagonalTraceCup
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicTheta
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicColumnComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicResidue
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedEdgeRelation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechLeftCupBoundary

/-! The logarithmic cup with the diagonal and the determinant lift of
the input differ by a boundary. Their left residues therefore give
the identity on right Čech cohomology. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p q : ℕ}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "π" => (Algebra.TensorProduct.lmul' k : F ⊗[k] F →ₐ[k] F)
local notation "V₀" => ExteriorDifferentials k E p
local notation "W₀" => ExteriorDifferentials k E q
local notation "K₀" => ChartPair d ⊕ₗ DiagonalIndex d
local notation "A₀" => (fun J : Finset (Fin (d + 1)) => regularExteriorLattice (rB k E x J) p)

private theorem signedEdges_mem_boundary {k M : Type} [Field k]
    [AddCommGroup M] [Module k M] {d m : ℕ}
    (A : Finset (Fin (d + 1)) → Submodule k M)
    {a : Finset (Fin (d + 1)) → M} (ha : a ∈ (cech A).Z (m : ℤ)) :
    (-1 : ℤ) ^ (m * (d + 1) + d) • edge1 a - (-1 : ℤ) ^ ((m + 1) * d) • edge2 a ∈
      (mixedCech fun I J => A (I ∪ J)).B ((m : ℤ) + 2) := by
  let ε := (-1 : ℤ) ^ ((m + 1) * d)
  have he : (-1 : ℤ) ^ (m * (d + 1) + d) = ε * (-1 : ℤ) ^ m := by
    dsimp only [ε]
    rw [← pow_add]
    congr 1
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
  have h : (ε * (-1 : ℤ) ^ m) • edge1 a - ε • edge2 a =
      -ε • (edge2 a - (-1 : ℤ) ^ m • edge1 a) := by
    rw [mul_smul, neg_smul, smul_sub, neg_sub]
  rw [he, h]
  exact zsmul_mem (edge2_sub_edge1_mem_boundary A ha) _

private theorem diagonalTraceCup_top (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) {m : ℕ}
    {c : Finset K₀ → W₀ ⊗[k] V₀} {a : Finset (Fin (d + 1)) → V₀}
    (hc : let T := diagonalChartSystem (E := E) h.pd q p
      c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).C ((d : ℤ) + 2))
    (hs : let T := diagonalChartSystem (E := E) h.pd q p
      ∀ (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)), L.card = d → ∀ b : V₀,
        tensorContraction ((traceWedgeLeftDual (F := F) τ).flip b) (c (uni (uni {i} {j}) L)) =
          (-1 : ℤ) ^ d • (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) • b))
    (ha₀ : a ∅ = 0) (B : Finset (ChartPair d)) (L : Finset (DiagonalIndex d)) (hL : L.card = d) :
    let T := logarithmicChartSystem (E := E) h.pd p
    collapseLogarithmicTensor (k := k) (F := F) p
      (weightedLeftCup (traceWedgeTensorCoefficient (F := F) τ) m c a (uni B L)) =
      (-1 : ℤ) ^ (m * (d + 1) + d) •
        (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) • edge1 a B) := by
  intro T
  let Td := diagonalChartSystem (E := E) h.pd q p
  let kap (L : Finset (DiagonalIndex d)) :=
    π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L))
  have hs' : ∀ (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)), L.card = d → ∀ b : V₀,
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip b) (c (uni (uni {i} {j}) L)) =
        (-1 : ℤ) ^ d • (kap L • b) := hs
  have hzero : ∀ I J L, L.card = d → ¬ (I.card = 1 ∧ J.card = 1) → c (uni (uni I J) L) = 0 :=
    weightedColumn_top_zero Td (fun _ => (1, 1)) Td.homogeneousMinor (c := c) hc
  exact traceCup_collapse (F := F) (p := p) (q := q) (m := m) τ ha₀ kap hs' hzero B L hL

private theorem logarithmic_sub_boundary (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) {m : ℕ}
    {a : Finset (Fin (d + 1)) → V₀} (ha : a ∈ (cech A₀).Z (m : ℤ))
    {v θ : Finset K₀ → F ⊗[k] V₀}
    (hv : let T := logarithmicChartSystem (E := E) h.pd p
      v ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + m + 2))
    (hθ : let T := logarithmicChartSystem (E := E) h.pd p
      θ ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + m + 2))
    (hvL : Lev rightIndices (· ≤ (d : ℤ)) v) (hθL : Lev rightIndices (· ≤ (d : ℤ)) θ)
    (hvTop : let T := logarithmicChartSystem (E := E) h.pd p
      ∀ (B : Finset (ChartPair d)) (L : Finset (DiagonalIndex d)), L.card = d →
        collapseLogarithmicTensor (k := k) (F := F) p (v (uni B L)) =
          (-1 : ℤ) ^ (m * (d + 1) + d) •
            (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) • edge1 a B))
    (hθTop : let T := logarithmicChartSystem (E := E) h.pd p
      ∀ (I J : Finset (Fin (d + 1))) (L : Finset (DiagonalIndex d)), L.card = d →
        collapseLogarithmicTensor (k := k) (F := F) p (θ (uni (uni I J) L)) =
          (-1 : ℤ) ^ ((m + 1) * d) •
            (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) •
              (if I.card = 1 then a J else 0))) :
    let T := logarithmicChartSystem (E := E) h.pd p
    v - θ ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).B ((d : ℤ) + m + 2) := by
  intro T
  let γ := (-1 : ℤ) ^ (m * (d + 1) + d) • edge1 a - (-1 : ℤ) ^ ((m + 1) * d) • edge2 a
  have hγ : γ ∈ (mixedCech fun I J => A₀ (I ∪ J)).B ((d : ℤ) + m + 2 - d) := by
    rw [show (d : ℤ) + m + 2 - d = m + 2 by omega]
    exact signedEdges_mem_boundary A₀ ha
  have hbZ : v - θ ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + m + 2) :=
    sub_mem hv hθ
  have hbL : Lev rightIndices (· ≤ (d : ℤ)) (v - θ) := fun s hs =>
    sub_eq_zero.mpr ((hvL s hs).trans (hθL s hs).symm)
  refine h.logarithmic_boundary_of_collapse_boundary (p := p) τ hτ hγ hbZ hbL ?_
  intro U B L hL
  obtain ⟨I, J, rfl⟩ : ∃ I J, B = uni I J := ⟨lft B, rgt B, (uni_lft_rgt B).symm⟩
  simp only [Pi.sub_apply, γ, Pi.smul_apply, smul_sub, map_sub,
    hvTop (uni I J) L hL, hθTop I J L hL, edge2, lft_uni, rgt_uni]
  rw [smul_comm ((-1 : ℤ) ^ (m * (d + 1) + d)), smul_comm ((-1 : ℤ) ^ ((m + 1) * d))]

private theorem exists_traceCup_sub_boundary (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ)
    (hpq : p + q = d)
    {c : Finset K₀ → W₀ ⊗[k] V₀}
    (hc : let T := diagonalChartSystem (E := E) h.pd q p
      c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + 2))
    (hL : Lev rightIndices (· ≤ (d : ℤ)) c)
    (hs : let T := diagonalChartSystem (E := E) h.pd q p
      ∀ (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)), L.card = d → ∀ b : V₀,
        tensorContraction ((traceWedgeLeftDual (F := F) τ).flip b) (c (uni (uni {i} {j}) L)) =
          (-1 : ℤ) ^ d • (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) • b))
    {m : ℕ} {a : Finset (Fin (d + 1)) → V₀} (ha : a ∈ (cech A₀).Z (m : ℤ)) :
    let T := logarithmicChartSystem (E := E) h.pd p
    ∃ θ : Finset K₀ → F ⊗[k] V₀,
      weightedLeftCup (traceWedgeTensorCoefficient (F := F) τ) m c a - θ ∈
        (T.complex (fun _ => (1, 1)) T.homogeneousMinor).B ((d : ℤ) + m + 2) ∧
      ∀ J, θ (uni (uni Finset.univ J) ∅) = (1 : F) ⊗ₜ[k] a J := by
  intro T
  let μ := traceWedgeTensorCoefficient (F := F) (p := p) (q := q) τ
  let v := weightedLeftCup μ m c a
  have hv : v ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + m + 2) :=
    h.traceCup_diagonal_mem_cycles (p := p) (q := q) (m := m) τ hτ hpq hc ha
  have hvL := weightedLeftCup_level (E := W₀ ⊗[k] V₀) (M := V₀) (N := F ⊗[k] V₀)
    (d := d) (m := m) μ c a hL
  have hvTop := diagonalTraceCup_top (p := p) (q := q) (m := m) h τ hc.1 hs (cechC_apply_empty ha.1)
  obtain ⟨θ, hθ, hθL, hθTop, hθ₀⟩ := h.pd.exists_logarithmicTheta (E := E) (p := p) m ha
  refine ⟨θ, ?_, hθ₀⟩
  exact logarithmic_sub_boundary (p := p) (m := m) h τ hτ ha
    (v := v) (θ := θ) hv hθ hvL hθL hvTop hθTop

private theorem boundary_of_projected_difference {k ι S M N : Type}
    [Field k] [LinearOrder ι] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (A : Finset ι → Submodule k M) {m : ℤ}
    (r : N →ₗ[k] M) (s : Finset ι → S) {v θ : S → N}
    {z a : Finset ι → M}
    (hb : (fun J => r ((v - θ) (s J))) ∈ (cech A).B m)
    (hv : ∀ J, r (v (s J)) = z J) (hθ : ∀ J, r (θ (s J)) = a J) :
    a - z ∈ (cech A).B m := by
  have he : (fun J => r ((v - θ) (s J))) = z - a := by
    funext J
    change r (v (s J) - θ (s J)) = z J - a J
    rw [map_sub, hv, hθ]
  rw [he] at hb
  exact neg_sub z a ▸ neg_mem hb

private theorem traceCup_chartPart_univ (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) {m : ℕ}
    {c : Finset K₀ → W₀ ⊗[k] V₀} {a : Finset (Fin (d + 1)) → V₀}
    (hc : let T := diagonalChartSystem (E := E) h.pd q p
      c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).C ((d : ℤ) + 2))
    (ha : a ∈ (cech A₀).C (m : ℤ)) (J : Finset (Fin (d + 1))) :
    let μ := traceWedgeTensorCoefficient (F := F) (p := p) (q := q) τ
    chartPart (weightedLeftCup μ m c a) (uni Finset.univ J) =
      cupAlongLeft μ a (chartPart c) J := by
  intro μ
  rw [chartPart, weightedLeftCup_apply, Finset.card_empty, Nat.add_zero]
  change (-1 : ℤ) ^ (m * J.card) • cupAlongLeft μ a (chartPart c) J = _
  by_cases hJ : J.card = m + 1
  · rw [hJ, (Nat.even_mul_succ_self m).neg_one_pow, one_smul]
  · have h0 : cupAlongLeft μ a (chartPart c) J = 0 := by
      rw [cupAlongLeft, cechCup_apply]
      refine Finset.sum_eq_zero fun i hi => ?_
      let I := Finset.univ.filter (· ≤ i)
      let K := Finset.univ.filter (i ≤ ·)
      by_cases hK : K.card = m + 1
      · have he := card_filter_le_add_card_filter_ge (Finset.univ : Finset (Fin (d + 1))) i hi
        simp only [Finset.card_univ, Fintype.card_fin] at he
        have hdeg : ((uni (uni I J) (∅ : Finset (DiagonalIndex d))).card : ℤ) ≠ (d : ℤ) + 2 := by
          rw [card_uni, card_uni, Finset.card_empty, add_zero]
          change I.card + K.card = d + 1 + 1 at he
          omega
        have hc0 : chartPart c (uni I J) = 0 := (Submodule.mem_bot k).mp (by
          simpa only [chartPart, if_neg hdeg] using
            acx_mem_terms_iff.mp hc (uni (uni I J) (∅ : Finset (DiagonalIndex d))))
        rw [hc0, map_zero, LinearMap.zero_apply]
      · have haK : a K = 0 := (Submodule.mem_bot k).mp (by
          simpa only [if_neg (fun he : K.Nonempty ∧ (K.card : ℤ) = (m : ℤ) + 1 =>
            hK (by omega))] using Submodule.mem_pi.mp ha K (Set.mem_univ K))
        rw [haK, map_zero]
    rw [h0, smul_zero]

private theorem residue_identity_of_logarithmic_comparison (h : IsPd k x)
    (ρ : F →ₗ[k] k) (hρ : IsRes x ρ) {m : ℕ}
    {v θ : Finset K₀ → F ⊗[k] V₀} {a : Finset (Fin (d + 1)) → V₀}
    {z : Finset (Fin (d + 1)) → F ⊗[k] V₀}
    (hb : let T := logarithmicChartSystem (E := E) h p
      v - θ ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).B ((d : ℤ) + m + 2))
    (hv : ∀ J, chartPart v (uni Finset.univ J) = z J)
    (hθ : ∀ J, θ (uni (uni Finset.univ J) ∅) = (1 : F) ⊗ₜ[k] a J) :
    a - (fun J => logarithmicResidueTensor (E := E) (p := p) ρ (z J)) ∈ (cech A₀).B (m : ℤ) := by
  let T := logarithmicChartSystem (E := E) h p
  let n : DiagonalIndex d → ℕ × ℕ := fun _ => (1, 1)
  let r : F ⊗[k] V₀ →ₗ[k] V₀ := logarithmicResidueTensor ρ
  let s (J : Finset (Fin (d + 1))) : Finset K₀ :=
    uni (uni (Finset.univ : Finset (Fin (d + 1))) J) ∅
  have hchart : chartPart (v - θ) ∈ (mixedCech T.M).B ((d : ℤ) + m + 2) :=
    T.chartPart_mem_boundaries (n := n) (z := T.homogeneousMinor) (a := v - θ) hb
  have hRes : (fun J => r ((v - θ) (s J))) ∈ (cech A₀).B (m : ℤ) :=
    h.logarithmicResidueTensor_mem_boundary (E := E) (p := p) (m := m)
      ρ hρ (c := chartPart (v - θ)) hchart
  refine boundary_of_projected_difference A₀ r s (v := v) (θ := θ) hRes ?_ ?_
  · intro J
    exact congrArg r (hv J)
  · intro J
    calc
      r (θ (s J)) = r ((1 : F) ⊗ₜ[k] a J) := congrArg r (hθ J)
      _ = a J := by
        change logarithmicResidueTensor ρ ((1 : F) ⊗ₜ[k] a J) = a J
        rw [logarithmicResidueTensor_tmul, hρ.1, one_smul]

/-- The chart projection of the diagonal cocycle acts as the identity
on regular right cohomology by traced residue and left cup product. -/
theorem IsFinCover.diagonal_action_eq_identity (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    (hpq : p + q = d)
    {c : Finset K₀ → W₀ ⊗[k] V₀}
    (hc : let T := diagonalChartSystem (E := E) h.pd q p
      c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + 2))
    (hL : Lev rightIndices (· ≤ (d : ℤ)) c)
    (hs : let T := diagonalChartSystem (E := E) h.pd q p
      ∀ (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)), L.card = d → ∀ b : V₀,
        tensorContraction ((traceWedgeLeftDual (F := F) τ).flip b) (c (uni (uni {i} {j}) L)) =
          (-1 : ℤ) ^ d • (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) • b))
    {m : ℕ} {a : Finset (Fin (d + 1)) → V₀} (ha : a ∈ (cech A₀).Z (m : ℤ)) :
    a - (fun J => logarithmicResidueTensor (E := E) (p := p) ρ
      (cupAlongLeft (traceWedgeTensorCoefficient (F := F) (p := p) (q := q) τ) a (chartPart c) J)) ∈
      (cech A₀).B (m : ℤ) := by
  let μ := traceWedgeTensorCoefficient (F := F) (p := p) (q := q) τ
  let v := weightedLeftCup μ m c a
  let z (J : Finset (Fin (d + 1))) := cupAlongLeft μ a (chartPart c) J
  obtain ⟨θ, hb, hθ⟩ := exists_traceCup_sub_boundary (p := p) (q := q) (m := m)
    h τ hτ hpq hc hL hs ha
  exact residue_identity_of_logarithmic_comparison (p := p) (m := m)
    h.pd ρ hρ (v := v) (θ := θ) (a := a) (z := z) hb
    (traceCup_chartPart_univ (p := p) (q := q) (m := m) h τ hc.1 ha.1) hθ

end GlobalTheory.PD
