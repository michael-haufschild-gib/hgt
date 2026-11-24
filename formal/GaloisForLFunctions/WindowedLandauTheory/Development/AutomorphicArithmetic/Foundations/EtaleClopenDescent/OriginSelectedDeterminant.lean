import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginTopFormLattice
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulSelectedDeterminant

/-! A change of selected Koszul parameters multiplies the affine
volume coefficient of the top class by its residue determinant. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.WH
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k F E ι : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [LinearOrder ι] [Fintype ι] {d : ℕ} {x : Fin (d + 1) → F}
  (h : IsFinCover k E x) [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)]
  (e : OriginFibrePoint k E x)

local notation "B" => rB k E x {0}
local notation "R" => loc B (Subtype.val e)
local notation "P" => omB k E R d
local notation "ε" => locEval B (Subtype.val e)
local notation "ω" => originAffineVolume k E x

include h in
/-- Compare two top Koszul components in the point-local ring. -/
theorem IsFinCover.exists_topCoefficient_of_selectedDeterminant
    (a b : Fin d ↪o ι) (r : ι → R) (ρ : ι → Fin d → R)
    (ha : Ideal.span (Set.range fun j => r (a j)) = RingHom.ker (ε).toRingHom)
    (hb : Ideal.span (Set.range fun j => r (b j)) = RingHom.ker (ε).toRingHom)
    (hr : ∀ i, r i = ∑ j, ρ i j * r (a j))
    (hρ : (Matrix.of fun i j => ρ (a i) j) = 1)
    {c : Finset ι → DR k E}
    (hc : c ∈ (acx (fun _ => P) fun i => Algebra.lsmul k k (DR k E) (r i : E)).Z (d : ℤ))
    (v : R) (hv : c (selectedIndices a) = (v : E) • (ω)) :
    ∃ u : R, c (selectedIndices b) = (u : E) • (ω) ∧
      ε u = ε ((Matrix.of fun i j => ρ (b i) j).det) * ε v := by
  let act : R →ₐ[k] Module.End k (DR k E) :=
    (Algebra.lsmul k k (DR k E)).comp (R).val
  have hs : Ideal.span (Set.range (localOriginCoordinate e)) ≤
      Ideal.span (Set.range fun j => r (a j)) :=
    ((h.span_localOriginCoordinates e).trans ha.symm).le
  have hex (m : ℤ) (hm : m < (d : ℤ)) :
      (acx (fun _ => P) fun i => act (r (a i))).Z m ≤
        (acx (fun _ => P) fun i => act (r (a i))).B m :=
    h.localOriginKoszul_exact e (r ∘ a) hs m hm
  have hD := sub_selectedDeterminant_mem_boundaryValues act (P)
    (fun s _ hw => smul_mem_omB s.property hw) a b r ρ hr hρ hex hc
  have ht : c (selectedIndices b) ∈ (P) := by
    have he : ((selectedIndices b).card : ℤ) = d := by simp [selectedIndices]
    simpa only [he, if_true] using acx_mem_terms_iff.mp hc.1 (selectedIndices b)
  obtain ⟨u, hu⟩ := h.exists_localOriginVolumeCoefficient e _ ht
  refine ⟨u, hu, ?_⟩
  let D := (Matrix.of fun i j => ρ (b i) j).det
  rw [hu, hv] at hD
  change (u : E) • (ω) - (D : E) • ((v : E) • (ω)) ∈ _ at hD
  rw [smul_smul, ← sub_smul] at hD
  have htest := (h.mem_selectedBoundaryValues_iff_residue e r b hb (u - D * v)).mp hD
  rw [map_sub, map_mul] at htest
  exact sub_eq_zero.mp htest

end GlobalTheory.PD
