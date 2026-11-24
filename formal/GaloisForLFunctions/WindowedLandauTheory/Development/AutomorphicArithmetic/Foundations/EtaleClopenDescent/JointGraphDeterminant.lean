import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginSelectedDeterminant
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphOriginSelectedWeights

/-! In the combined graph and origin complex the graph component of
a top class multiplies its origin coefficient by the transverse
determinant. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR TensorProduct Matrix

namespace GlobalTheory.WH

private theorem exists_jointRowPresentation {R G : Type} [CommRing R] [LinearOrder G]
    {d : ℕ} (g : Fin d ↪o G) (r : G ⊕ₗ Fin d → R) (t : Fin d → R)
    (D : Matrix (Fin d) (Fin d) R)
    (ht : ∀ i, r (joinedRight i) = t i)
    (hr : ∀ i, r (joinedLeft i) ∈ Ideal.span (Set.range t))
    (hd : ∀ i, r (joinedLeft (g i)) = (D *ᵥ t) i) :
    ∃ ρ : (G ⊕ₗ Fin d) → Fin d → R,
      (∀ i, r i = ∑ j, ρ i j * r (joinedRight j)) ∧
      (Matrix.of fun i j => ρ (joinedRight i) j) = 1 ∧
      (Matrix.of fun i j => ρ (joinedLeft (g i)) j) = D := by
  classical
  choose b hb using fun i => Ideal.mem_span_range_iff_exists_fun.mp (hr i)
  let ρ₀ (i : G) (j : Fin d) : R :=
    if hi : i ∈ Set.range g then D (Classical.choose hi) j else b i j
  let ρ : (G ⊕ₗ Fin d) → Fin d → R := fun i =>
    Sum.elim ρ₀ (fun j l => (1 : Matrix (Fin d) (Fin d) R) j l) (ofLex i)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro i
    simp only [ht]
    obtain ⟨l, rfl⟩ := (toLex : G ⊕ Fin d ≃ G ⊕ₗ Fin d).surjective i
    rcases l with l | l
    · change r (joinedLeft l) = ∑ j, ρ₀ l j * t j
      by_cases hl : l ∈ Set.range g
      · let i := Classical.choose hl
        have hi : g i = l := Classical.choose_spec hl
        simp only [ρ₀, dif_pos hl]
        exact (congrArg (fun l : G => r (joinedLeft l)) hi.symm).trans (hd i)
      · simpa only [ρ₀, dif_neg hl] using (hb l).symm
    · change r (joinedRight l) = ((1 : Matrix (Fin d) (Fin d) R) *ᵥ t) l
      rw [ht, Matrix.one_mulVec]
  · apply Matrix.ext
    intro i j
    rfl
  · apply Matrix.ext
    intro i j
    change ρ₀ (g i) j = D i j
    have hi : g i ∈ Set.range g := Set.mem_range_self i
    simp only [ρ₀, dif_pos hi]
    rw [g.injective (Classical.choose_spec hi)]

private theorem map_det_one_sub {R S : Type} [CommRing R] [CommRing S] {d : ℕ}
    (e : R →+* S) (A : Matrix (Fin d) (Fin d) R) :
    e (1 - A).det = (1 - A.map e).det := by
  rw [e.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp [Matrix.one_apply, apply_ite]

section OriginBoundary

variable {k F L ι : Type} [Field k] [CharZero k] [Field F] [Field L]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  [LinearOrder ι] [Fintype ι] {d : ℕ} {x : Fin (d + 1) → F}
  (hL : IsFinCover k L x) [IsReduced ((rB k L x {0}) ⧸ originIdeal k L x)]
  (f : OriginFibrePoint k L x)

local notation "R" => loc (rB k L x {0}) (Subtype.val f)
local notation "ε" => locEval (rB k L x {0}) (Subtype.val f)
local notation "ω" => originAffineVolume k L x

include hL in
private theorem sub_mem_originSelectedBoundary_of_residue (e g : Fin d ↪o ι)
    (r : ι → R) (ρ : ι → Fin d → R)
    (he : Ideal.span (Set.range fun j => r (e j)) = RingHom.ker (ε).toRingHom)
    (hg : Ideal.span (Set.range fun j => r (g j)) = RingHom.ker (ε).toRingHom)
    (hr : ∀ i, r i = ∑ j, ρ i j * r (e j))
    (hρ : (Matrix.of fun i j => ρ (e i) j) = 1)
    {c : Finset ι → DR k L}
    (hc : c ∈ (acx (fun _ => omB k L R d) fun i => Algebra.lsmul k k (DR k L) (r i : L)).Z (d : ℤ))
    (a s : R) (ha : c (selectedIndices e) = (a : L) • (ω))
    (hs : ε s = ε ((Matrix.of fun i j => ρ (g i) j).det) * ε a) :
    (s : L) • (ω) - c (selectedIndices g) ∈ selectedBoundaryValues (omB k L R d)
      (fun i => Algebra.lsmul k k (DR k L) (r i : L)) g := by
  obtain ⟨b, hb, hres⟩ := hL.exists_topCoefficient_of_selectedDeterminant f e g r ρ he hg hr hρ hc a ha
  have hzero : ε (s - b) = 0 := by rw [map_sub, hs, hres, sub_self]
  have hB := (hL.mem_selectedBoundaryValues_iff_residue f r g hg (s - b)).mpr hzero
  rwa [Subalgebra.coe_sub, sub_smul, ← hb] at hB

end OriginBoundary

variable {k F E L κ : Type} [Field k] [CharZero k] [Field F] [Field E] [Field L]
  [LinearOrder κ] [Fintype κ]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] L)
  {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E}

local notation "G" => κ ⊕ₗ DiagonalIndex d
local notation "Q" => (κ ⊕ₗ DiagonalIndex d) ⊕ₗ Fin d

abbrev jointOriginSelection : Fin d ↪o Q := joinedRight

abbrev jointGraphSelection : Fin d ↪o Q :=
  (graphOriginSelection (κ := κ)).trans joinedLeft

variable (hL : IsFinCover k L x) [IsReduced ((rB k L x {0}) ⧸ originIdeal k L x)]
  (f : OriginFibrePoint k L x)

local notation "B" => rB k L x {0}
local notation "R" => loc B (Subtype.val f)
local notation "ε" => locEval B (Subtype.val f)

include hL

omit [CharZero k] [Fintype κ] in
private theorem exists_jointGraphPresentation (hz : NormalizedDiagonalEquations h n z)
    (hf : IsFix B f.1 j₂ (rB k E x {0})) (M : Matrix (Fin d) (Fin d) k)
    (hrow : ∀ m, ∃ (c : B) (g : Fin d → B), f.1 c ≠ 0 ∧
      (c : L) * j₂ (algebraMap F E (x m.succ / x 0)) =
        ∑ l, (g l : L) * algebraMap F L (x l.succ / x 0) ∧
      ∀ l, f.1 (g l) = f.1 c * M m l)
    (hdet : (1 - M).det ≠ 0)
    (r : Q → R)
    (hG : ∀ i : G, (r (joinedLeft i) : L) =
      graphAffineWeight h j₂ (n := n) (z := z) (i := 0) (j := 0) i)
    (hO : ∀ j, r (jointOriginSelection j) = localOriginCoordinate f j) :
    (Ideal.span (Set.range fun j => r (jointGraphSelection j)) =
      RingHom.ker (ε).toRingHom) ∧
      ∃ ρ : Q → Fin d → R,
        (∀ i, r i = ∑ j, ρ i j * r (jointOriginSelection j)) ∧
        (Matrix.of fun i j => ρ (jointOriginSelection i) j) = 1 ∧
        ε ((Matrix.of fun i j => ρ (jointGraphSelection i) j).det) = (1 - M).det := by
  let v (i : Fin d) := j₂ (algebraMap F E (x i.succ / x 0))
  obtain ⟨A, hA, hrowA⟩ := exists_localRows_of_cleared f v M hrow
  let t := localOriginCoordinate f
  let D := 1 - A
  have hr (i : G) : r (joinedLeft i) ∈ Ideal.span (Set.range t) := by
    rw [hL.span_localOriginCoordinates f]
    change ε (r (joinedLeft i)) = 0
    have hv : Val B f.1 (r (joinedLeft i) : L) 0 :=
      (hG i).symm ▸ val_graphAffineWeight_at_fixedOrigin h j₂ hz f hf i
    exact ((val_iff_loc B f.1 _ _).mp hv).choose_spec
  let g := graphOriginSelection (κ := κ) (d := d)
  have hrowD (i : Fin d) : r (joinedLeft (g i)) = (D *ᵥ t) i := by
    apply Subtype.ext
    have hg := graphAffineWeight_at_origin_selected h j₂ (n := n) (z := z) i
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Subalgebra.coe_sub]
    exact (hG (g i)).trans (hg.trans (congrArg ((t i : L) - ·) (hrowA i).symm))
  have heval : ε D.det = (1 - M).det := (map_det_one_sub (ε).toRingHom A).trans
    (congrArg (fun M' => (1 - M').det) hA)
  have hu : IsUnit D.det := isUnit_loc_of_eval_ne_zero B f.1 _ (heval.symm ▸ hdet)
  have hS : Ideal.span (Set.range fun j => r (jointGraphSelection j)) =
      RingHom.ker (ε).toRingHom := by
    have he : (fun j => r (jointGraphSelection j)) = D *ᵥ t := funext hrowD
    rw [he, span_range_mulVec_eq D hu, hL.span_localOriginCoordinates f]
  obtain ⟨ρ, hρ, hId, hD⟩ := exists_jointRowPresentation g r t D hO hr hrowD
  refine ⟨hS, ρ, hρ, hId, ?_⟩
  rw [show (Matrix.of fun i j => ρ (jointGraphSelection i) j) = D from hD]
  exact heval

/-- Matching the graph coefficient to the determinant times the
origin coefficient gives a selected boundary in the graph column. -/
theorem sub_mem_selectedGraphBoundary_of_residue (hz : NormalizedDiagonalEquations h n z)
    (hf : IsFix B f.1 j₂ (rB k E x {0})) (M : Matrix (Fin d) (Fin d) k)
    (hrow : ∀ m, ∃ (c : B) (g : Fin d → B), f.1 c ≠ 0 ∧
      (c : L) * j₂ (algebraMap F E (x m.succ / x 0)) =
        ∑ l, (g l : L) * algebraMap F L (x l.succ / x 0) ∧
      ∀ l, f.1 (g l) = f.1 c * M m l)
    (hdet : (1 - M).det ≠ 0) (r : Q → R)
    (hG : ∀ i : G, (r (joinedLeft i) : L) =
      graphAffineWeight h j₂ (n := n) (z := z) (i := 0) (j := 0) i)
    (hO : ∀ j, r (jointOriginSelection j) = localOriginCoordinate f j)
    {c : Finset Q → DR k L}
    (hc : c ∈ (acx (fun _ => omB k L R d) fun i => Algebra.lsmul k k (DR k L) (r i : L)).Z (d : ℤ))
    (a s : R) (ha : c (selectedIndices jointOriginSelection) = (a : L) • originAffineVolume k L x)
    (hs : ε s = (1 - M).det * ε a) :
    (s : L) • originAffineVolume k L x - c (selectedIndices jointGraphSelection) ∈
      selectedBoundaryValues (omB k L R d)
        (fun i : G => Algebra.lsmul k k (DR k L) (r (joinedLeft i) : L)) graphOriginSelection := by
  obtain ⟨hS, ρ, hρ, hId, heval⟩ :=
    exists_jointGraphPresentation (κ := κ) (x := x) (n := n) (z := z) h j₂ hL f hz hf M hrow hdet r hG hO
  have hT : Ideal.span (Set.range fun j => r (jointOriginSelection j)) =
      RingHom.ker (ε).toRingHom :=
    (congrArg (fun t : Fin d → R => Ideal.span (Set.range t)) (funext hO)).trans
      (hL.span_localOriginCoordinates f)
  have hs' : ε s = ε ((Matrix.of fun i j => ρ (jointGraphSelection i) j).det) * ε a :=
    hs.trans (congrArg (fun v : k => v * ε a) heval.symm)
  exact sub_mem_originSelectedBoundary_of_residue (ι := Q) (x := x) hL f jointOriginSelection
    jointGraphSelection r ρ hT hS hρ hId (c := c) hc a s ha hs'

end GlobalTheory.WH
