import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.SpectralBasis
import GaloisForLFunctions.HTGeometry.CfcEigenvectorRankOneAssembly

/-! # Fractional heat moments on the surviving Hilbert space -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap
open scoped InnerProductSpace

/-- Fractional power of the physical squared propagator, formed on the gas itself by continuous functional calculus. -/
def momentOperator (P : Projection) (q : ℝ) : GasOp := cfc (fun x : ℝ => x^q) (projected P^2)

private theorem moment_on_basis {P : Projection} {b : ℕ → ℝ} (e : HilbertBasis ℕ ℂ Gas)
    (he : ∀ n, (projected P^2) (e n) = (b n:ℂ) • e n) {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    momentOperator P q (e n) = ((b n^q:ℝ):ℂ) • e n :=
  HTGeometry.cfc_apply_eigenvector_rankOne _ (projected_square_positive P).isSelfAdjoint (he n) (Real.continuous_rpow_const hq).continuousOn

private theorem moment_diagonal {P : Projection} {b : ℕ → ℝ} (e : HilbertBasis ℕ ℂ Gas)
    (he : ∀ n, (projected P^2) (e n) = (b n:ℂ) • e n) {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    inner ℂ (e n) (momentOperator P q (e n)) = ((b n^q:ℝ):ℂ) := by
  rw [moment_on_basis e he hq n,inner_smul_right,inner_self_eq_norm_sq_to_K,e.orthonormal.1 n]
  norm_num

/-- The fractional moment observable is Hilbert–Schmidt precisely above half order. -/
theorem momentOperator_hilbertSchmidt_iff (P : Projection) {r : ℕ} (dim : MissingDimension P r)
    (hc : Conserving (projected P)) (q : GibbsExponent) : (momentOperator P q.val).IsHilbertSchmidt ↔ 1/2 < q.val := by
  let b := physicalSpectrum P dim hc
  obtain ⟨e,he⟩ := exists_physical_heat_basis P dim hc
  have hn (n : ℕ) : ‖momentOperator P q.val (e n)‖^2 = (b n).val^(2*q.val) := by
    rw [moment_on_basis e he q.property.le n,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (band_pos b n).le _),e.orthonormal.1 n,mul_one,
      mul_comm (2:ℝ),Real.rpow_mul (band_pos b n).le,Real.rpow_two]
  rw [isHilbertSchmidt_iff_summable e]
  simp only [hn,summable_band_rpow_iff]
  constructor <;> intro h <;> linarith only [h]

/-- Composition of equal half powers gives the full power, including at orders where the separate traces diverge. -/
theorem momentOperator_half_product (P : Projection) {r : ℕ} (dim : MissingDimension P r)
    (hc : Conserving (projected P)) (q : GibbsExponent) :
    momentOperator P q.val = momentOperator P (q.val/2) ∘L momentOperator P (q.val/2) := by
  let b := physicalSpectrum P dim hc
  obtain ⟨e,he⟩ := exists_physical_heat_basis P dim hc
  have hq : 0 < q.val := q.property
  refine ContinuousLinearMap.ext_on (s := Set.range e) (Submodule.dense_iff_topologicalClosure_eq_top.2 e.dense_span) ?_
  rintro _ ⟨n,rfl⟩
  rw [comp_apply,moment_on_basis e he (half_pos hq).le,map_smul,moment_on_basis e he (half_pos hq).le,
    smul_smul,← Complex.ofReal_mul,← Real.rpow_add (band_pos b n),add_halves,moment_on_basis e he hq.le]

private theorem half_isHS (P : Projection) {r : ℕ} (dim : MissingDimension P r)
    (hc : Conserving (projected P)) (q : GibbsExponent) (hq : 1 < q.val) :
    (momentOperator P (q.val/2)).IsHilbertSchmidt :=
  (momentOperator_hilbertSchmidt_iff P dim hc ⟨q.val/2,half_pos q.property⟩).mpr (by
    change (1:ℝ)/2 < q.val/2
    linarith only [hq])

/-- The exact ordinary trace domain of every projected moment operator is q > 1. -/
theorem momentOperator_traceClass_iff (P : Projection) {r : ℕ} (dim : MissingDimension P r)
    (hc : Conserving (projected P)) (q : GibbsExponent) : (momentOperator P q.val).IsTraceClass ↔ 1 < q.val := by
  constructor
  · rintro ⟨A,B,hA,hB,hprod⟩
    obtain ⟨e,he⟩ := exists_physical_heat_basis P dim hc
    have hsum := (summable_inner_diag_comp hA hB e).norm
    rw [← hprod] at hsum
    apply (summable_band_rpow_iff (physicalSpectrum P dim hc) q.val).mp
    exact hsum.congr (fun n => by
      rw [moment_diagonal e he q.property.le,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (band_pos _ n).le _)])
  · intro hq
    exact ⟨_,_,half_isHS P dim hc q hq,half_isHS P dim hc q hq,momentOperator_half_product P dim hc q⟩

/-- The trace of the fractional power on the gas is the ordinary moment of its interlacing levels. -/
theorem momentOperator_trace (P : Projection) {r : ℕ} (dim : MissingDimension P r)
    (hc : Conserving (projected P)) (q : GibbsExponent) (hq : 1 < q.val) :
    opTrace (momentOperator P q.val) = ((∑' n, (physicalSpectrum P dim hc n).val^q.val : ℝ) : ℂ) := by
  obtain ⟨e,he⟩ := exists_physical_heat_basis P dim hc
  have hhs := half_isHS P dim hc q hq
  have htrace := opTrace_comp_eq_tsum_basis hhs hhs e
  rw [← momentOperator_half_product P dim hc q] at htrace
  simp only [moment_diagonal e he q.property.le] at htrace
  rwa [← Complex.ofReal_tsum] at htrace

/-- Real spectral loss equals the difference of the zeta trace and the fractional operator trace on the original gas. -/
theorem momentLoss_eq_fractional_trace (P : Projection) {r : ℕ} (dim : MissingDimension P r)
    (hc : Conserving (projected P)) (q : GibbsExponent) (hq : 1 < q.val) :
    momentLoss q (physicalSpectrum P dim hc) = (riemannZeta (q.val:ℂ)).re - (opTrace (momentOperator P q.val)).re := by
  rw [momentLoss_eq_trace_difference q hq,momentOperator_trace P dim hc q hq,Complex.ofReal_re]

#print axioms momentOperator_hilbertSchmidt_iff
#print axioms momentOperator_half_product
#print axioms momentOperator_traceClass_iff
#print axioms momentOperator_trace
#print axioms momentLoss_eq_fractional_trace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
