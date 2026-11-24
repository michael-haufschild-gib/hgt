import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ChartKoszulDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SelectedKoszulComponent

/-! The boundary values of a selected Koszul cube descend from
its point-local chart lattices. -/

noncomputable section

open GlobalTheory.CechDR
open scoped GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k L ι : Type} [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
  [LinearOrder ι] (B : Subalgebra k L) [Algebra.FiniteType k B]
  (p : ℕ) (r : ι → B) {d : ℕ} (e : Fin d ↪o ι)

local notation "w" => fun i => Algebra.lsmul k k (DR k L) (r i : L)

/-- A regular form with a selected boundary value at every point
is itself a selected boundary value over the chart. -/
theorem selectedBoundaryValues_mem_of_local {v : DR k L} (hv : v ∈ omB k L B p)
    (h : ∀ f : B →ₐ[k] k, v ∈ selectedBoundaryValues (omB k L (loc B f) p) (w) e) :
    v ∈ selectedBoundaryValues (omB k L B p) (w) e := by
  let N : Finset (Fin d) := Finset.univ
  let a (I : Finset (Fin d)) := if I = N then v else 0
  let C := acx (fun _ => omB k L B p) fun j => (w) (e j)
  have hcard : (N.card : ℤ) = d := by simp [N]
  have ha : a ∈ C.C (d : ℤ) := by
    apply acx_mem_terms_iff.mpr
    intro I
    by_cases he : I = N
    · subst I
      exact show a N ∈ _ from by rw [a, if_pos rfl, if_pos hcard]; exact hv
    · rw [a, if_neg he]
      exact zero_mem _
  have hl (f : B →ₐ[k] k) :
      a ∈ (acx (fun _ => omB k L (loc B f) p) fun j => (w) (e j)).B (d : ℤ) := by
    obtain ⟨b, hb, hbe⟩ := h f
    have haeq : b = a := by
      funext I
      by_cases hI : I = N
      · subst I
        exact hbe.trans (if_pos rfl).symm
      · have hn : (I.card : ℤ) ≠ d := by
          intro he
          apply hI
          exact Finset.eq_univ_of_card (by exact_mod_cast he)
        have ht := acx_mem_terms_iff.mp (Cx.boundaries_le_cycles
          (acx_isCx _ _ (fun i j => (Commute.all (r (e i) : L) (r (e j) : L)).map
            (Algebra.lsmul k k (DR k L)))
            (fun _ i _ _ hx => GlobalTheory.PD.smul_mem_omB ((le_loc B f) (r (e i)).property) hx))
          d hb).1 I
        rw [if_neg hn] at ht
        rw [(Submodule.mem_bot k).mp ht, a, if_neg hI]
    exact haeq ▸ hb
  have hba : a ∈ C.B (d : ℤ) :=
    chartKoszul_mem_boundaries_of_local B p (r ∘ e) a ha hl
  exact ⟨a, hba, if_pos rfl⟩

end GlobalTheory.WH
