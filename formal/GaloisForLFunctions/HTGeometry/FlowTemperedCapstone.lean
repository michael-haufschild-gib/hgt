import GaloisForLFunctions.HTGeometry.TestFunctionModulation

/-!
# Temperedness of the spectral multiplicity measure

Composing the chain: trace class makes the truncated traces pointwise bounded, barrelledness of
the test space turns that into a `C^k` bound on the trace, the Leibniz estimate turns the `C^k`
bound into polynomial growth in the modulation frequency, and the spectral counting bound turns
that into polynomial growth of the multiplicity measure.

* `deningerTest_multiplicityMeasure_polynomial_growth` : the composed statement.
-/

namespace GaloisForLFunctions.HTGeometry

open TopologicalSpace

section Capstone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedSpace ℝ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]

omit [CompleteSpace H] in
/-- **Temperedness of the multiplicity measure.**  If the truncated traces of the smoothing are
pointwise bounded — the trace-class hypothesis — and dominate the trace functional, and if the
weight symbol stays above `c` on the window of radius `ε` around the modulation frequency, then
the multiplicity measure of that window grows at most polynomially. -/
theorem deningerTest_multiplicityMeasure_polynomial_growth
    (U : UnitaryFlow ℂ H) (J : Compacts ℝ) {iota : Type*} (b : iota → H)
    (T : DeningerTest J → ℝ)
    (hbdd : ∀ phi : DeningerTest J,
      BddAbove (Set.range fun s : Finset iota => ‖deningerTruncTrace U J b s phi‖))
    (hdom : ∀ phi : DeningerTest J,
      ‖T phi‖ ≤ ⨆ s : Finset iota, ‖deningerTruncTrace U J b s phi‖)
    (phi0 : DeningerTest J)
    {kappa : Type*} (lam : kappa → ℝ) {g : ℝ → ℝ → ℝ} {eps c : ℝ} (hc : 0 < c)
    (hlow : ∀ x lambda : ℝ, |lambda - x| ≤ eps → c ≤ g x lambda)
    (htrace : ∀ (x : ℝ) (u : Finset kappa), ∑ i ∈ u, g x (lam i)
      ≤ T ⟨complexModulatedWeight ((phi0 : ℝ → ℂ)) x,
          complexModulatedWeight_mem_deningerTestSpace phi0.2 x⟩) :
    ∃ (k : ℕ) (Cb : ℝ), ∀ x : ℝ,
      multiplicityMeasure lam (Set.Icc (x - eps) (x + eps))
        ≤ ENNReal.ofReal (Cb * (1 + |x|) ^ k / c) := by
  obtain ⟨k, C, hbound⟩ := deningerTruncTrace_exists_order_bound U J b T hbdd hdom
  set M : ℝ := ((Finset.range (k + 1)).sup (deningerTestFamily J)) phi0 with hMdef
  have hM0 : ∀ m ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ m ((phi0 : ℝ → ℂ)) t‖ ≤ M :=
    forall_norm_iteratedFDeriv_le_of_sup_le (le_of_eq hMdef.symm)
  refine ⟨k, (C : ℝ) * M, fun x => ?_⟩
  refine multiplicityMeasure_polynomial_growth lam hc hlow ?_ x
  intro y u
  have hmod : ∀ n ≤ k, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n (complexModulatedWeight ((phi0 : ℝ → ℂ)) y) t‖ ≤ (1 + |y|) ^ k * M :=
    norm_iteratedFDeriv_modulatedWeight_le_pow phi0.2.1 hM0 y
  have hsup : ((Finset.range (k + 1)).sup (deningerTestFamily J))
      ⟨complexModulatedWeight ((phi0 : ℝ → ℂ)) y,
        complexModulatedWeight_mem_deningerTestSpace phi0.2 y⟩
      ≤ (1 + |y|) ^ k * M :=
    sup_le_of_forall_norm_iteratedFDeriv_le hmod
  have hTle : T ⟨complexModulatedWeight ((phi0 : ℝ → ℂ)) y,
      complexModulatedWeight_mem_deningerTestSpace phi0.2 y⟩ ≤ (C : ℝ) * ((1 + |y|) ^ k * M) := by
    refine le_trans (le_abs_self _) ?_
    refine le_trans (hbound _) ?_
    exact mul_le_mul_of_nonneg_left hsup (NNReal.coe_nonneg C)
  refine le_trans (htrace y u) ?_
  refine le_trans hTle (le_of_eq ?_)
  ring

end Capstone

end GaloisForLFunctions.HTGeometry
