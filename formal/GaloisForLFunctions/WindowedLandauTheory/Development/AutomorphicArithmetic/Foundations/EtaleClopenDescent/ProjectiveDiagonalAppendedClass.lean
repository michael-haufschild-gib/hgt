import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalAppendedColumns
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalAppendRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SingletonChartColumns

/-! The weighted diagonal class extends to the extra scalar equations
from the normalized charts. Its restriction retains the identity action. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E κ : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [LinearOrder κ] [Fintype κ] {d : ℕ} {x : Fin (d + 1) → F} {p q : ℕ}
  {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "π" => (Algebra.TensorProduct.lmul' k : F ⊗[k] F →ₐ[k] F)
local notation "V" => ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p

/-- The enlarged diagonal cocycle preserves the identity contractions
on singleton chart pairs under restriction to the base indices. -/
theorem IsFinCover.exists_appendedDiagonalCocycle (H : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d)
    (hz : NormalizedDiagonalEquations H.pd n z) :
    let T := diagonalChartSystem (E := E) H.pd q p
    let W := normalizedDiagonalSystem (E := E) H.pd q p
    ∃ c ∈ (W.complex (appendedDiagonalDegrees n) (appendedDiagonalWeights H.pd q p z)).Z ((d : ℤ) + 2),
      ∀ (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)), L.card = d →
        ∀ b : ExteriorDifferentials k E p,
          tensorContraction ((traceWedgeLeftDual (F := F) τ).flip b) (c (uni (uni {i} {j}) (uni ∅ L))) =
            (-1 : ℤ) ^ d • (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) • b) := by
  let T := diagonalChartSystem (E := E) H.pd q p
  let W := normalizedDiagonalSystem (E := E) H.pd q p
  let N : κ ⊕ₗ DiagonalIndex d → ℕ × ℕ := appendedDiagonalDegrees n
  let Z := appendedDiagonalWeights H.pd q p z
  let kap (L : Finset (DiagonalIndex d)) := π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L))
  have hcols (i j : Fin (d + 1)) :
      ∃ v ∈ (W.columnComplex N Z {i} {j}).Z (d : ℤ),
        ∀ L (a : ExteriorDifferentials k E p),
          tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) (v (uni ∅ L)) = kap L • a := by
    obtain ⟨b, hb, hbid⟩ := H.exists_diagonalColumn τ hτ hpq i j
    obtain ⟨v, hv, he⟩ := (H.appendedDiagonalColumn τ hτ hpq hz
      (Finset.mem_singleton_self i) (Finset.mem_singleton_self j)).2.2 b hb
        (fun L => ⟨kap L, hbid L⟩)
    exact ⟨v, hv, fun L a => (congrArg (tensorContraction
      ((traceWedgeLeftDual (F := F) τ).flip a)) (he L)).trans (hbid L a)⟩
  choose v hv hvid using hcols
  let e : ℤ := (-1 : ℤ) ^ d
  let u (i j : Fin (d + 1)) : Finset (κ ⊕ₗ DiagonalIndex d) → V := (e : k) • v i j
  have hu (i j : Fin (d + 1)) : u i j ∈ (W.columnComplex N Z {i} {j}).Z (d : ℤ) :=
    Submodule.smul_mem ((W.columnComplex N Z {i} {j}).Z (d : ℤ)) (e : k) (hv i j)
  have huid (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)) (a : ExteriorDifferentials k E p) :
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) (u i j (uni ∅ L)) =
        e • (kap L • a) := by
    let f : (V) →ₗ[k] ExteriorDifferentials k E p :=
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a)
    calc
      f (u i j (uni ∅ L)) = (e : k) • f (v i j (uni ∅ L)) := f.map_smul (e : k) _
      _ = (e : k) • (kap L • a) := congrArg (fun b => (e : k) • b) (hvid i j L a)
      _ = _ := Int.cast_smul_eq_zsmul k e (kap L • a)
  have hex (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) (m : ℤ)
      (hm : m < (d : ℤ)) : (W.columnComplex N Z I J).Z m ≤ (W.columnComplex N Z I J).B m :=
    (H.appendedDiagonalColumn τ hτ hpq hz (chartIndex_mem hI) (chartIndex_mem hJ)).1 m hm
  have hzero (B : Finset (ChartPair d)) (_ : B.card = 3)
      (hI : (lft B).Nonempty) (hJ : (rgt B).Nonempty)
      (b : Finset (κ ⊕ₗ DiagonalIndex d) → V)
      (hb : b ∈ (W.columnComplex N Z (lft B) (rgt B)).Z (d : ℤ))
      (hB : ∀ L, b L = deltaL k (ChartPair d) (V)
        (fun C => singletonChartColumns u (uni C L)) B) :
      b ∈ (W.columnComplex N Z (lft B) (rgt B)).B (d : ℤ) := by
    apply (H.appendedDiagonalColumn τ hτ hpq hz (chartIndex_mem hI) (chartIndex_mem hJ)).2.1 b hb
    intro f
    have hs : Function.Surjective ((traceWedgeLeftDual (F := F) (p := p) (q := q) τ).flip) := by
      change Function.Surjective (traceWedgeDual (F := F) (p := q) (q := p) τ)
      exact (H.traceWedgeDual_bijective τ hτ (by simpa only [Nat.add_comm q p] using hpq : q + p = d)).2
    obtain ⟨a, rfl⟩ := hs f
    let L := selectedIndices (diagonalIndexEmbedding (chartIndex (rgt B)))
    change tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) (b (uni ∅ L)) = 0
    rw [hB]
    exact map_deltaL_singletonChartColumns_eq_zero _ u (uni ∅ L) _ (fun i j => huid i j L a) B
  obtain ⟨c, hc, hcl⟩ := W.exists_cocycle_of_singletonChartColumns
    (normalizedDiagonalSystem_good (E := E) H.pd q p) (appendedDiagonal_admitted H.pd q p hz)
    hu hex hzero
  refine ⟨c, hc, fun i j L hL a => ?_⟩
  let L' : Finset (κ ⊕ₗ DiagonalIndex d) := uni ∅ L
  have hL' : L'.card = d := by
    simpa only [L', card_uni, Finset.card_empty, zero_add] using hL
  have he : (((uni (uni {i} {j}) L' ∩ rightIndices).card : ℕ) : ℤ) = (d : ℤ) :=
    congrArg (fun b : ℕ => (b : ℤ)) ((card_inter_rightIndices (uni {i} {j}) L').trans hL')
  have hs := hcl (uni (uni {i} {j}) L') (fun ht => (not_lt_of_ge (le_of_eq he.symm)) ht)
  change c (uni (uni {i} {j}) L') - singletonChartColumns u (uni (uni {i} {j}) L') = 0 at hs
  rw [sub_eq_zero.mp hs, singletonChartColumns_apply]
  exact huid i j L a

end GlobalTheory.PD
