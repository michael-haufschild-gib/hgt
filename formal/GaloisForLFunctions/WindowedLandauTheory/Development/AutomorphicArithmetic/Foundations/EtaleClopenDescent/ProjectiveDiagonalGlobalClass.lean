import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalLocalClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalColumns
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SingletonChartColumns

/-! The contracted local diagonal determinants agree, so their
horizontal differences have regular Koszul primitives. The resulting
global diagonal cocycle has the prescribed top action on chart pairs. -/

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

/-- The regular homogeneous diagonal complex admits a global cocycle
with scalar identity contractions in its top Koszul degree. -/
theorem IsFinCover.exists_diagonalCocycle (H : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d) :
    let T := diagonalChartSystem (E := E) H.pd q p
    ∃ c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + 2),
      Lev rightIndices (· ≤ (d : ℤ)) c ∧
      ∀ (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)), L.card = d →
        ∀ a : ExteriorDifferentials k E p,
          tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) (c (uni (uni {i} {j}) L)) =
            (-1 : ℤ) ^ d • (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) • a) := by
  let T := diagonalChartSystem (E := E) H.pd q p
  let n : DiagonalIndex d → ℕ × ℕ := fun _ => (1, 1)
  let kap (L : Finset (DiagonalIndex d)) := π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L))
  let z := T.homogeneousMinor
  choose v hv hvid using fun i j => H.exists_diagonalColumn τ hτ hpq i j
  let e : ℤ := (-1 : ℤ) ^ d
  let u (i j : Fin (d + 1)) : Finset (DiagonalIndex d) → _ := (e : k) • v i j
  have hu (i j : Fin (d + 1)) : u i j ∈ (T.columnComplex n z {i} {j}).Z (d : ℤ) :=
    Submodule.smul_mem ((T.columnComplex n z {i} {j}).Z (d : ℤ)) (e : k) (hv i j)
  have huid (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)) (a : ExteriorDifferentials k E p) :
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) (u i j L) =
        (-1 : ℤ) ^ d • (kap L • a) := by
    let f : (ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p) →ₗ[k]
        ExteriorDifferentials k E p :=
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a)
    calc
      f (u i j L) = (e : k) • f (v i j L) := f.map_smul (e : k) (v i j L)
      _ = (e : k) • (kap L • a) := congrArg (fun b => (e : k) • b) (hvid i j L a)
      _ = _ := Int.cast_smul_eq_zsmul k e (kap L • a)
  have hex (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) (m : ℤ)
      (hm : m < (d : ℤ)) : (T.columnComplex n z I J).Z m ≤ (T.columnComplex n z I J).B m :=
    (H.diagonalColumn_exact_and_boundary q p (chartIndex_mem hI) (chartIndex_mem hJ)).1 m hm
  have hzero (B : Finset (ChartPair d)) (_ : B.card = 3)
      (hI : (lft B).Nonempty) (hJ : (rgt B).Nonempty)
      (b : Finset (DiagonalIndex d) → _)
      (hb : b ∈ (T.columnComplex n z (lft B) (rgt B)).Z (d : ℤ))
      (hB : ∀ L, b L = deltaL k (ChartPair d)
        (ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)
        (fun C => singletonChartColumns u (uni C L)) B) :
      b ∈ (T.columnComplex n z (lft B) (rgt B)).B (d : ℤ) := by
    apply (H.diagonalColumn_exact_and_boundary q p (chartIndex_mem hI) (chartIndex_mem hJ)).2 b hb
    intro f
    have hsurj : Function.Surjective ((traceWedgeLeftDual (F := F) (p := p) (q := q) τ).flip) := by
      change Function.Surjective (traceWedgeDual (F := F) (p := q) (q := p) τ)
      exact (H.traceWedgeDual_bijective τ hτ (by simpa only [Nat.add_comm q p] using hpq : q + p = d)).2
    obtain ⟨a, rfl⟩ := hsurj f
    let L := selectedIndices (diagonalIndexEmbedding (chartIndex (rgt B)))
    change tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) (b L) = 0
    rw [hB]
    exact map_deltaL_singletonChartColumns_eq_zero _ u L _ (fun i j => huid i j L a) B
  obtain ⟨c, hc, hcl⟩ := T.exists_cocycle_of_singletonChartColumns
    (diagonalChartSystem_good (E := E) H.pd q p) (diagonalChartSystem_admitted (E := E) H.pd q p)
    hu hex hzero
  refine ⟨c, hc, ?_, ?_⟩
  · intro s hs
    have h1 := hcl s (by omega)
    change c s - singletonChartColumns u s = 0 at h1
    rw [sub_eq_zero.mp h1, singletonChartColumns]
    split_ifs with h
    · have hcard : ((rgt s).card : ℤ) ≠ (d : ℤ) := by
        obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
        have he : (((uni B L ∩ rightIndices).card : ℕ) : ℤ) = L.card :=
          congrArg (fun a : ℕ => (a : ℤ)) (card_inter_rightIndices B L)
        intro hL
        rw [rgt_uni] at hL
        exact hs (le_of_eq (he.trans hL))
      exact (Submodule.mem_bot k).mp (by
        simpa only [if_neg hcard] using acx_mem_terms_iff.mp (hu _ _).1 (rgt s))
    · rfl
  · intro i j L hL a
    have he : (((uni (uni {i} {j}) L ∩ rightIndices).card : ℕ) : ℤ) = (d : ℤ) :=
      congrArg (fun b : ℕ => (b : ℤ)) ((card_inter_rightIndices (uni {i} {j}) L).trans hL)
    have hs := hcl (uni (uni {i} {j}) L) (fun ht => (not_lt_of_ge (le_of_eq he.symm)) ht)
    change c (uni (uni {i} {j}) L) - singletonChartColumns u (uni (uni {i} {j}) L) = 0 at hs
    rw [sub_eq_zero.mp hs, singletonChartColumns_apply]
    exact huid i j L a

end GlobalTheory.PD
