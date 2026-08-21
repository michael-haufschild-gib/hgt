import GaloisForLFunctions.HTGeometry.KaehlerConnection
import GaloisForLFunctions.HTGeometry.KaehlerAlgebraicIndependence

/-!
# Differentially independent elements have independent differentials over the operator ring

The connection sends `d y` to `d (δ y)`, so an operator relation `∑ Lᵢ · d yᵢ = 0` is exactly a
field-linear relation among the differentials of the jets `δⁿ yᵢ`.  When the `yᵢ` are
differentially independent those jets are algebraically independent, and over a characteristic-zero
base algebraic independence is the same as linear independence of the universal differentials.  So
the `d yᵢ` are linearly independent over `K[∂;δ]`.

This is the lower bound for the rank of the Kähler module: it is at least the differential
transcendence degree.

* `kaehlerConnection_iterate_D` — `∇ⁿ (d y) = d (δⁿ y)`;
* `linearIndependent_diffOp_D_of_differentialIndependent` — **the independence theorem**;
* `linearIndependent_mkQ_of_torsion` — independence survives the quotient by a torsion submodule.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]

theorem kaehlerConnection_iterate_D (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (y : K) (n : ℕ) :
    (kaehlerConnection hC : Ω[K⁄C] → Ω[K⁄C])^[n] (KaehlerDifferential.D C K y)
      = KaehlerDifferential.D C K (differentialJet n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, kaehlerConnection_D, differentialJet_succ]

/-- **Differentially independent elements have `K[∂;δ]`-independent differentials.** -/
theorem linearIndependent_diffOp_D_of_differentialIndependent [IsConstantBase C K] [CharZero C]
    {r : ℕ} {y : Fin r → K}
    (hy : AlgebraicIndependent C (fun p : Fin r × ℕ => differentialJet p.2 (y p.1))) :
    LinearIndependent (DiffOp K) (fun i => KaehlerDifferential.D C K (y i)) := by
  classical
  have hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0 :=
    IsConstantBase.deriv_algebraMap
  have hK : LinearIndependent K
      (fun p : Fin r × ℕ => KaehlerDifferential.D C K (differentialJet p.2 (y p.1))) :=
    (algebraicIndependent_iff_kaehlerD_linearIndependent
      (fun p : Fin r × ℕ => differentialJet p.2 (y p.1))).mp hy
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set N : ℕ := (Finset.univ.sup fun i => DiffOp.degree (g i)) + 1 with hN
  set T : Finset ℕ := Finset.range N with hT
  have hzero : ∀ (i : Fin r) (n : ℕ), n ∉ T → DiffOp.coeff (g i) n = 0 := by
    intro i n hn
    have hdeg : DiffOp.degree (g i) ≤ Finset.univ.sup fun i => DiffOp.degree (g i) :=
      Finset.le_sup (f := fun i => DiffOp.degree (g i)) (Finset.mem_univ i)
    have hlt : Finset.univ.sup (fun i => DiffOp.degree (g i)) < n := by
      rw [hT, Finset.mem_range] at hn
      omega
    exact DiffOp.degree_le_iff.mp le_rfl n (lt_of_le_of_lt hdeg hlt)
  have hexp : ∀ i : Fin r, g i • (KaehlerDifferential.D C K (y i))
      = ∑ n ∈ T, (DiffOp.coeff (g i) n) •
          KaehlerDifferential.D C K (differentialJet n (y i)) := by
    intro i
    rw [diffOp_smul_def, diffOpSMul_eq_sum hC _ _ T (hzero i)]
    exact Finset.sum_congr rfl fun n _ => by rw [kaehlerConnection_iterate_D]
  have hrel : ∑ p ∈ (Finset.univ ×ˢ T : Finset (Fin r × ℕ)),
      (DiffOp.coeff (g p.1) p.2) •
        KaehlerDifferential.D C K (differentialJet p.2 (y p.1)) = 0 := by
    rw [Finset.sum_product]
    rw [← hg]
    exact (Finset.sum_congr rfl fun i _ => hexp i).symm
  have hall := linearIndependent_iff'.mp hK (Finset.univ ×ˢ T)
    (fun p => DiffOp.coeff (g p.1) p.2) hrel
  intro i
  refine DiffOp.ext fun n => ?_
  rw [DiffOp.coeff_zero]
  by_cases hn : n ∈ T
  · exact hall (i, n) (Finset.mem_product.mpr ⟨Finset.mem_univ i, hn⟩)
  · exact hzero i n hn

/-- **Independence survives the quotient by a torsion submodule.** -/
theorem linearIndependent_mkQ_of_torsion {M : Type*} [AddCommGroup M] [Module (DiffOp K) M]
    (N : Submodule (DiffOp K) M) (hN : ∀ ω ∈ N, ∃ p : DiffOp K, p ≠ 0 ∧ p • ω = 0)
    {r : ℕ} {v : Fin r → M} (hv : LinearIndependent (DiffOp K) v) :
    LinearIndependent (DiffOp K) (fun i => N.mkQ (v i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmem : (∑ i, g i • v i) ∈ N := by
    rw [← Submodule.Quotient.mk_eq_zero]
    have hpush : (Submodule.Quotient.mk (∑ i, g i • v i) : M ⧸ N) = ∑ i, g i • N.mkQ (v i) := by
      show N.mkQ (∑ i, g i • v i) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    rw [hpush, hg]
  obtain ⟨p, hp0, hp⟩ := hN _ hmem
  have hsum : ∑ i, (p * g i) • v i = 0 := by
    rw [← hp, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_smul p (g i) (v i)
  have hzero := (Fintype.linearIndependent_iff.mp hv) (fun i => p * g i) hsum
  intro i
  exact (mul_eq_zero.mp (hzero i)).resolve_left hp0


end

end GaloisForLFunctions.HTGeometry
