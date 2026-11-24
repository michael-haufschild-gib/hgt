import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ChartKoszulDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SelectedKoszulComponent

/-! A unit weight gives a primitive in every degree, and a selected
unit weight makes every regular coefficient a boundary value. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD
open scoped GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k L ι : Type} [Field k] [Field L] [Algebra k L]
  [LinearOrder ι] (B : Subalgebra k L) (p : ℕ) (r : ι → B)

local notation "w" => fun i => Algebra.lsmul k k (DR k L) (r i : L)

theorem chartKoszul_exact_of_unit {j : ι} (hu : IsUnit (r j)) (m : ℤ) :
    (acx (fun _ => omB k L B p) w).Z m ≤ (acx (fun _ => omB k L B p) w).B m := by
  apply acx_lattice_exact (k := k) (chartFormLattice B p) r m
  intro a ha hz
  have htop : Ideal.span (Set.range r) = ⊤ :=
    (Ideal.span (Set.range r)).eq_top_of_isUnit_mem (Ideal.subset_span (Set.mem_range_self j)) hu
  obtain ⟨b, hb, hdb⟩ := exists_koszul_primitive_smul r ha hz
    (g := (1 : B)) (htop.symm ▸ Submodule.mem_top)
  exact ⟨b, hb, hdb.trans (one_smul B a)⟩

theorem le_selectedBoundaryValues_of_unit {d : ℕ} (sel : Fin d ↪o ι) {j : Fin d}
    (hu : IsUnit (r (sel j))) :
    omB k L B p ≤ selectedBoundaryValues (omB k L B p) w sel := by
  rw [selectedBoundaryValues_eq_iSup]
  intro v hv
  obtain ⟨u, hu⟩ := hu
  apply le_iSup (fun j => (omB k L B p).map (Algebra.lsmul k k (DR k L) (r (sel j) : L))) j
  let b : B := ↑u⁻¹
  refine ⟨(b : L) • v, smul_mem_omB b.property hv, ?_⟩
  change (r (sel j) : L) • ((b : L) • v) = v
  have hmul : (r (sel j) : L) * (b : L) = 1 := by
    change B.val (r (sel j) * b) = 1
    rw [← hu, show (u : B) * b = 1 from Units.mul_inv u, map_one]
  rw [smul_smul, hmul, one_smul]

theorem chartKoszul_cycles_le_localCycles (e : B →ₐ[k] k) (m : ℤ) :
    (acx (fun _ => omB k L B p) w).Z m ≤ (acx (fun _ => omB k L (loc B e) p) w).Z m := by
  intro a ha
  refine ⟨acx_mem_terms_iff.mpr fun I => ?_, ha.2⟩
  by_cases hI : (I.card : ℤ) = m
  · rw [if_pos hI]
    exact omB_mono (le_loc B e) p (by simpa only [if_pos hI] using acx_mem_terms_iff.mp ha.1 I)
  · simpa only [if_neg hI] using acx_mem_terms_iff.mp ha.1 I

variable [IsAlgClosed k] [Fintype ι] [Algebra.FiniteType k B]

/-- Lower exactness on each point-local chart implies lower
exactness on the original chart. -/
theorem chartKoszul_exact_of_local (m : ℤ)
    (hex : ∀ e : B →ₐ[k] k, (acx (fun _ => omB k L (loc B e) p) w).Z m ≤
      (acx (fun _ => omB k L (loc B e) p) w).B m) :
    (acx (fun _ => omB k L B p) w).Z m ≤ (acx (fun _ => omB k L B p) w).B m := by
  intro a ha
  apply chartKoszul_mem_boundaries_of_local B p r a ha.1
  intro e
  apply hex e
  exact chartKoszul_cycles_le_localCycles B p r e m ha

/-- If the weights have no common zero, the column is exact in
every degree. -/
theorem chartKoszul_exact_of_no_common_zero
    (h : ∀ e : B →ₐ[k] k, ∃ j, e (r j) ≠ 0) (m : ℤ) :
    (acx (fun _ => omB k L B p) w).Z m ≤ (acx (fun _ => omB k L B p) w).B m := by
  apply chartKoszul_exact_of_local B p r m
  intro e
  obtain ⟨j, hj⟩ := h e
  let r' := (Subalgebra.inclusion (le_loc B e)) ∘ r
  have he : locEval B e (r' j) = e (r j) := locEval_inclusion B e (r j)
  exact chartKoszul_exact_of_unit (loc B e) p r' (j := j)
    (isUnit_loc_of_eval_ne_zero B e _ (he.symm ▸ hj)) m

end GlobalTheory.WH
