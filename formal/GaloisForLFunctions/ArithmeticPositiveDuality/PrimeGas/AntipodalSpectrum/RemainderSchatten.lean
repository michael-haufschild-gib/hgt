import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RefinementOperators
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RemainderPartition
import GaloisForLFunctions.HTGeometry.LpDiagonalSchattenEnergy
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# Schatten law for the heat-weighted clock error

The absolute p-th power of a thermal coefficient is the real heat weight
at p times the real inverse temperature. This identifies the singular-value
sum of the concrete two-copy operator with a radial zeta partition.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture.Binary
open scoped Classical

private theorem word_norm_power (s : ℂ) (p : ℝ) (x : Word) :
    ‖wordHeat s x‖^p = ‖wordHeat ((p*s.re:ℝ):ℂ) x‖ := by
  rw [wordHeat_total,wordHeat_total,norm_heat,norm_heat,← Real.exp_mul,Complex.ofReal_re]
  congr 1
  ring

private theorem real_word (b : ℝ) (x : Word) :
    (wordHeat (b:ℂ) x).re = ‖wordHeat (b:ℂ) x‖ := by
  rw [wordHeat_total,norm_heat,Complex.ofReal_re,heat,← Complex.ofReal_neg,← Complex.ofReal_mul,← Complex.ofReal_exp,Complex.ofReal_re]

private theorem power_indicator (t : ExceptionalTime) (j : ℕ) (s : ℂ) (p : {r : ℝ // 0 < r}) :
    (fun x => ‖tailMultiplier t j s x‖^p.val) =
      {x | remainder t j x}.indicator (fun x => ‖wordHeat ((p.val*s.re:ℝ):ℂ) x‖) := by
  funext x
  by_cases hx : remainder t j x
  · simp only [tailMultiplier,if_pos hx,Set.indicator_of_mem (show x ∈ {y | remainder t j y} from hx),word_norm_power]
  · simp only [tailMultiplier,if_neg hx,Set.indicator_of_notMem (show x ∉ {y | remainder t j y} from hx),norm_zero,Real.zero_rpow p.property.ne']

/-- The entire Schatten scale, including the sublinear range of exponents. -/
theorem damped_schatten_iff (t : ExceptionalTime) (j : ℕ) (s : ClosedHeatPlane) (p : {r : ℝ // 0 < r}) :
    _root_.RHTower.MemSchattenClass p.val (dampedRemainder t j s) ↔ 1/2 < p.val*s.val.re := by
  rw [damped_diagonal,HTGeometry.memSchattenClass_lpDiagonalCLM_iff _ _ _ p.property,power_indicator t j s.val p,
    ← summable_subtype_iff_indicator]
  exact (sectorHeat_iff _ _).symm.trans (remainder_heat_iff t j ((p.val*s.val.re:ℝ):ℂ))

theorem damped_traceClass_iff (t : ExceptionalTime) (j : ℕ) (s : ClosedHeatPlane) :
    (dampedRemainder t j s).IsTraceClass ↔ 1/2 < s.val.re := by
  have h := damped_schatten_iff t j s ⟨1,zero_lt_one⟩
  change _root_.RHTower.MemSchattenClass 1 _ ↔ 1/2 < 1*s.val.re at h
  rw [one_mul] at h
  exact (Iff.intro _root_.RHTower.IsTraceClass.memSchattenClass_one _root_.RHTower.MemSchattenClass.one_isTraceClass).trans h

/-- Exact sum of powers of the singular values in the summable half-plane. -/
theorem damped_schatten_sum (t : ExceptionalTime) (j : ℕ) (s : ClosedHeatPlane)
    (p : {r : ℝ // 0 < r ∧ 1/2 < r*s.val.re}) :
    let u : ℂ := ((p.val*s.val.re:ℝ):ℂ)
    (∑' n, _root_.RHTower.approxNumber (dampedRemainder t j s) n ^ p.val) =
      (riemannZeta (2*u)*(2*windingWeight t j u/(1-windingWeight t j u))).re := by
  let b := p.val*s.val.re
  have hβ : 1/2 < (b:ℂ).re := p.property.2
  have hs := ((sectorHeat_iff _ _).mp ((remainder_heat_iff t j _).mpr hβ)).of_norm
  have hr := Complex.hasSum_re hs.hasSum
  change _ = (riemannZeta (2*(b:ℂ))*(2*windingWeight t j (b:ℂ)/(1-windingWeight t j (b:ℂ)))).re
  rw [damped_diagonal,HTGeometry.tsum_rpow_approxNumber_lpDiagonalCLM _ _ _ p.property.1,
    power_indicator t j s.val ⟨p.val,p.property.1⟩,← tsum_subtype,← remainder_partition t j ⟨(b:ℂ),hβ⟩]
  exact (tsum_congr fun x : {x // remainder t j x} => (real_word b x.val).symm).trans hr.tsum_eq

theorem damped_traceNorm (t : ExceptionalTime) (j : ℕ) (s : {s : ℂ // 1/2 < s.re}) :
    let u := (s.val.re : ℂ)
    _root_.RHTower.traceNorm (LabelSpace Word) (dampedRemainder t j ⟨s.val,by linarith only [s.property]⟩) =
      (riemannZeta (2*u)*(2*windingWeight t j u/(1-windingWeight t j u))).re := by
  let z : ClosedHeatPlane := ⟨s.val,by linarith only [s.property]⟩
  have h := damped_schatten_sum t j z ⟨1,zero_lt_one,by simpa only [one_mul] using s.property⟩
  simpa only [_root_.RHTower.traceNorm,Real.rpow_one,one_mul] using h

/-- The binary split is isometric precisely on the trace-class boundary of each operator error. -/
theorem split_iff_damped_trace_boundary (t : ExceptionalTime) (j : ℕ) (s : ClosedHeatPlane) :
    (∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split s.val f x) ↔
      ¬(dampedRemainder t j s).IsTraceClass ∧
        ∀ δ : {d : ℝ // 0 < d}, (dampedRemainder t j
          ⟨s.val+(δ.val:ℂ),show 0 ≤ s.val.re+δ.val from add_nonneg s.property δ.property.le⟩).IsTraceClass := by
  rw [split_isometric_iff]
  simp only [damped_traceClass_iff,not_lt,Complex.add_re,Complex.ofReal_re]
  constructor
  · intro he
    exact ⟨he.le,fun δ => by linarith only [he,δ.property]⟩
  · rintro ⟨hle,hδ⟩
    apply le_antisymm hle
    by_contra! h
    have h' := hδ ⟨1/2-s.val.re,sub_pos.mpr h⟩
    change 1/2 < s.val.re+(1/2-s.val.re) at h'
    linarith only [h']

#print axioms damped_schatten_iff
#print axioms damped_schatten_sum
#print axioms damped_traceClass_iff
#print axioms damped_traceNorm
#print axioms split_iff_damped_trace_boundary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
