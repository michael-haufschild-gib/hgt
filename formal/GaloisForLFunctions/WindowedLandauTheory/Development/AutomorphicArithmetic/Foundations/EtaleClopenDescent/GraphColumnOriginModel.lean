import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginModelKoszul
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphChartSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartColumnScaling

/-! Normalization transfers the local boundary criterion and lower
exactness to homogeneous graph columns. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k F E L ι : Type} [Field k]
  [Field F] [Field E] [Field L] [LinearOrder ι]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] L)
  {q p : ℕ} (hqp : q + p = d)

local notation "T" => graphChartSystem h j₂ q p
local notation "B₀" => rB k L x {0}

variable {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
  {n : ι → ℕ × ℕ} {z : ι → L} (hz : (graphChartSystem h j₂ q p).Admitted n z)

local notation "B" => RY x j₂ I J

/-- The normalized weights belong to the joined chart ring. -/
def graphColumnWeights (l : ι) : B :=
  ⟨(T).normalizedWeight n z i j l,
    (T).normalizedWeight_mem (graphChartSystem_good h j₂ q p) hz hi hj l⟩

include hqp in
/-- Normalization identifies graph column cycles with the scalar
Koszul cycles on regular top forms. -/
theorem graphColumn_scale_mem_cycles_iff (m : ℤ) (a : Finset ι → DR k L) :
    let r := graphColumnWeights h j₂ (q := q) (p := p) hi hj hz
    let w := fun l => Algebra.lsmul k k (DR k L) (r l : L)
    (T).scaleColumn n i j a ∈ ((T).columnComplex n z I J).Z m ↔
      a ∈ (acx (fun _ => omB k L B d) w).Z m := by
  intro r w
  have hM : (T).M I J = omB k L B (q + p) := rfl
  have hMd : (T).M I J = omB k L B d :=
    hM.trans (congrArg (omB k L (RY x j₂ I J)) hqp)
  rw [← hMd]
  exact (T).scaleColumn_mem_cycles_iff (graphChartSystem_good h j₂ q p) n z hi hj m a

variable [CharZero k] [IsAlgClosed k] [Fintype ι]

include hqp in
/-- The homogeneous top boundary is tested on the normalized selected
value at each common zero of the normalized graph weights. -/
theorem graphColumn_exact_and_boundary_of_originModel
    [Algebra.FiniteType k B] (sel : Fin d ↪o ι)
    (hL : IsFinCover k L x) [IsReduced ((B₀) ⧸ originIdeal k L x)] :
    let r := graphColumnWeights h j₂ (q := q) (p := p) hi hj hz
    let C := (T).columnComplex n z I J
    let w := fun l => Algebra.lsmul k k (DR k L) (r l : L)
    (∀ e : B →ₐ[k] k, (∀ l, e (r l) = 0) →
      ∃ f : OriginFibrePoint k L x, loc B e = loc (B₀) f.1 ∧
        ∃ u : ι → loc (B₀) f.1, (∀ l, (u l : L) = (r l : L)) ∧
          Ideal.span (Set.range fun j => u (sel j)) =
            RingHom.ker (locEval (B₀) f.1).toRingHom) →
    (∀ m < (d : ℤ), C.Z m ≤ C.B m) ∧
      ∀ a ∈ C.Z (d : ℤ),
        (∀ e : B →ₐ[k] k, (∀ l, e (r l) = 0) →
          ((T).scaleColumn n i j).symm a (selectedIndices sel) ∈
            selectedBoundaryValues (omB k L (loc B e) d) w sel) →
        a ∈ C.B (d : ℤ) := by
  intro r C w H
  let C₀ := acx (fun _ => omB k L B d) w
  have hC₀ : C₀ = acx (fun _ => (T).M I J)
      (fun l => (T).act ((T).normalizedWeight n z i j l)) := by
    let P := RY x j₂ I J
    have hM : (T).M I J = omB k L P (q + p) := rfl
    have hMd : (T).M I J = omB k L P d :=
      hM.trans (congrArg (omB k L P) hqp)
    rw [hMd]
    rfl
  obtain ⟨he, hb⟩ := chartKoszul_exact_and_boundary_of_originModel B r sel hL H
  have hT := graphChartSystem_good h j₂ q p
  refine ⟨?_, ?_⟩
  · intro m hm
    exact (T).columnExact_of_normalized hT n z hi hj m (hC₀ ▸ he m hm)
  · intro a ha hh
    let c := ((T).scaleColumn n i j).symm a
    have hc : (T).scaleColumn n i j c = a := ((T).scaleColumn n i j).apply_symm_apply a
    have hcz : c ∈ C₀.Z (d : ℤ) :=
      (graphColumn_scale_mem_cycles_iff h j₂ hqp hi hj hz d c).mp (hc.symm ▸ ha)
    have hcb : c ∈ C₀.B (d : ℤ) := hb c hcz hh
    exact hc ▸ ((T).scaleColumn_mem_boundaries_iff hT n z hi hj d c).mpr (hC₀ ▸ hcb)

end GlobalTheory.WH
