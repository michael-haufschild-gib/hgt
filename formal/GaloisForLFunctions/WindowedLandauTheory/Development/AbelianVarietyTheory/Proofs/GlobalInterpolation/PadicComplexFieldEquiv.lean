import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Sequences

/-! The algebraic closure of the p-adic field and the complex field have the
same cardinality and characteristic, so they are isomorphic as fields. -/

noncomputable section

open Cardinal Filter Topology

namespace GlobalTheory.TeichPlace

theorem cardinalMk_padic_eq_continuum (p : ℕ) [Fact p.Prime] : #ℚ_[p] = 𝔠 := by
  apply le_antisymm
  · have hd := Padic.denseRange_ratCast p
    have h : ∀ x : ℚ_[p], ∃ u : ℕ → ℚ,
        Tendsto (fun n => (u n : ℚ_[p])) atTop (𝓝 x) := by
      intro x
      obtain ⟨v, hv, hx⟩ := mem_closure_iff_seq_limit.mp (hd x)
      choose u hu using hv
      exact ⟨u, by simpa only [hu] using hx⟩
    choose u hu using h
    have hi : Function.Injective u := by
      intro x y hxy
      have hy := hu y
      rw [← hxy] at hy
      exact tendsto_nhds_unique (hu x) hy
    refine (Cardinal.mk_le_of_injective hi).trans ?_
    simp
  · exact continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p]

theorem cardinalMk_padicAlgCl_eq_continuum (p : ℕ) [Fact p.Prime] : #(PadicAlgCl p) = 𝔠 := by
  apply le_antisymm
  · exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans
      (max_le (cardinalMk_padic_eq_continuum p).le Cardinal.aleph0_le_continuum)
  · rw [← cardinalMk_padic_eq_continuum p]
    exact Cardinal.mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective

/-- An abstract field equivalence transports the p-adic valuation to the complex field. -/
theorem nonempty_padicAlgCl_ringEquiv_complex (p : ℕ) [Fact p.Prime] :
    Nonempty (PadicAlgCl p ≃+* ℂ) :=
  IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [cardinalMk_padicAlgCl_eq_continuum]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [cardinalMk_padicAlgCl_eq_continuum, Cardinal.mk_complex]))

end GlobalTheory.TeichPlace
