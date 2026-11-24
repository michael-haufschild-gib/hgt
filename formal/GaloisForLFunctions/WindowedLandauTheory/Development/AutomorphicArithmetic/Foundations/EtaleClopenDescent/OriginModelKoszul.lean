import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ChartKoszulUnit
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginTopFormLattice

/-! On a chart, the only local computations required for Koszul
exactness are at the common zeros of the weights. At these points an
origin-ideal model supplies the selected boundary test. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD
open scoped GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k F L ι : Type} [Field k] [CharZero k] [IsAlgClosed k] [Field F] [Field L]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  [LinearOrder ι] [Fintype ι] {d : ℕ} {x : Fin (d + 1) → F}
  (B : Subalgebra k L) [Algebra.FiniteType k B] (r : ι → B) (sel : Fin d ↪o ι)
  (hL : IsFinCover k L x) [IsReduced ((rB k L x {0}) ⧸ originIdeal k L x)]

local notation "w" => fun i => Algebra.lsmul k k (DR k L) (r i : L)
local notation "B₀" => rB k L x {0}
local notation "C" => acx (fun _ => omB k L B d) (w)

include hL in
/-- Off the common zero locus the complex has a unit weight.
At a common zero the selected weights may be tested in a local
origin-ideal model. -/
theorem chartKoszul_exact_and_boundary_of_originModel
    (hmodel : ∀ e : B →ₐ[k] k, (∀ i, e (r i) = 0) →
      ∃ f : OriginFibrePoint k L x, loc B e = loc B₀ f.1 ∧
        ∃ u : ι → loc B₀ f.1, (∀ i, (u i : L) = (r i : L)) ∧
          Ideal.span (Set.range fun j => u (sel j)) =
            RingHom.ker (locEval B₀ f.1).toRingHom) :
    (∀ m < (d : ℤ), (C).Z m ≤ (C).B m) ∧
      ∀ a ∈ (C).Z (d : ℤ),
        (∀ e : B →ₐ[k] k, (∀ i, e (r i) = 0) → a (selectedIndices sel) ∈
          selectedBoundaryValues (omB k L (loc B e) d) (w) sel) →
        a ∈ (C).B (d : ℤ) := by
  classical
  have hu (e : B →ₐ[k] k) (j : ι) (hj : e (r j) ≠ 0) (m : ℤ) :
      (acx (fun _ => omB k L (loc B e) d) (w)).Z m ≤
        (acx (fun _ => omB k L (loc B e) d) (w)).B m := by
    let r' := (Subalgebra.inclusion (le_loc B e)) ∘ r
    have he : locEval B e (r' j) = e (r j) := locEval_inclusion B e (r j)
    exact chartKoszul_exact_of_unit (loc B e) d r' (j := j)
      (isUnit_loc_of_eval_ne_zero B e _ (he.symm ▸ hj)) m
  have he (e : B →ₐ[k] k) (hzero : ∀ i, e (r i) = 0) :
      (∀ m < (d : ℤ), (acx (fun _ => omB k L (loc B e) d) (w)).Z m ≤
        (acx (fun _ => omB k L (loc B e) d) (w)).B m) ∧
      (∀ m < (d : ℤ), (acx (fun _ => omB k L (loc B e) d) fun j => (w) (sel j)).Z m ≤
        (acx (fun _ => omB k L (loc B e) d) fun j => (w) (sel j)).B m) := by
    obtain ⟨f, hf, u, hru, hspan⟩ := hmodel e hzero
    have hspan' : Ideal.span (Set.range (localOriginCoordinate f)) =
        Ideal.span (Set.range fun j => u (sel j)) :=
      (hL.span_localOriginCoordinates f).trans hspan.symm
    rw [hf]
    have huw : (fun j => Algebra.lsmul k k (DR k L) (u j : L)) = (w) :=
      funext fun j => congrArg (Algebra.lsmul k k (DR k L)) (hru j)
    constructor
    · intro m hm
      have hr : Ideal.span (Set.range (localOriginCoordinate f)) ≤ Ideal.span (Set.range u) := by
        rw [hspan']
        exact Ideal.span_mono (Set.range_comp_subset_range sel u)
      have h := hL.localOriginKoszul_exact f u hr m hm
      rwa [huw] at h
    · intro m hm
      have h := hL.localOriginKoszul_exact f (u ∘ sel) hspan'.le m hm
      change (acx (fun _ => omB k L (loc B₀ f.1) d)
        (fun j => (fun l => Algebra.lsmul k k (DR k L) (u l : L)) (sel j))).Z m ≤
        (acx (fun _ => omB k L (loc B₀ f.1) d)
          (fun j => (fun l => Algebra.lsmul k k (DR k L) (u l : L)) (sel j))).B m at h
      rwa [huw] at h
  refine ⟨?_, ?_⟩
  · intro m hm
    apply chartKoszul_exact_of_local B d r m
    intro e
    by_cases hzero : ∀ i, e (r i) = 0
    · exact (he e hzero).1 m hm
    · push Not at hzero
      obtain ⟨j, hj⟩ := hzero
      exact hu e j hj m
  · intro a ha hTop
    apply chartKoszul_mem_boundaries_of_local B d r a ha.1
    intro e
    have hza := chartKoszul_cycles_le_localCycles B d r e d ha
    by_cases hzero : ∀ i, e (r i) = 0
    · exact boundary_of_selected_component sel
        (fun i j => (Commute.all (r i : L) (r j : L)).map (Algebra.lsmul k k (DR k L)))
        (fun j _ hv => smul_mem_omB ((le_loc B e) (r j).property) hv)
        (he e hzero).2 hza (hTop e hzero)
    · push Not at hzero
      obtain ⟨j, hj⟩ := hzero
      exact hu e j hj d hza

end GlobalTheory.WH
