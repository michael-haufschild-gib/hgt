import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEta
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Adjacent-shell interference in the two-copy gas

Pair the order-resolved channels at parameters 1 and s and take the difference
between successive odd and even shells. This diagonal is trace class throughout
the positive half-plane. Its trace detects exactly the zeta zeros in the open
strip, where the undifferenced Gibbs diagonal has no ordinary partition trace.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open scoped ComplexConjugate

def overlap (s : ℂ) (n : ℕ+) : ℂ :=
  ∑ d ∈ (n : ℕ).divisors, conj (channel 1 n d) * channel s n d

theorem overlap_eq_heat (s : ℂ) (n : ℕ+) : overlap s n = heat s n := by
  rw [overlap, shell_pairing, map_one, heat_add, ← mul_assoc, heat_eq_cpow,
    Complex.cpow_neg, Complex.cpow_one, mul_inv_cancel₀ (by exact_mod_cast n.ne_zero), one_mul]

def adjacentDifference (s : ℂ) (k : ℕ) : ℂ :=
  overlap s (2 * k).succPNat - overlap s (2 * k + 1).succPNat

theorem adjacentDifference_eq (s : ℂ) (k : ℕ) :
    adjacentDifference s k = RiemannGaussian.pairedEtaCoreSummand s k := by
  simp only [adjacentDifference, overlap_eq_heat, heat_eq_cpow]
  rfl

private def halfDifference (s : ℂ) (k : ℕ) : ℂ := adjacentDifference s k ^ (2⁻¹ : ℂ)

private theorem halfDifference_sq (s : ℂ) (k : ℕ) :
    halfDifference s k ^ 2 = adjacentDifference s k := by
  rw [halfDifference, ← Complex.cpow_mul_ofNat]
  norm_num

private theorem halfDifference_summable (s : {z : ℂ // 0 < z.re}) :
    Summable fun k => ‖halfDifference s.val k‖ ^ 2 := by
  have h := (RiemannGaussian.summable_pairedEtaCoreSummand s.2).norm
  refine h.congr fun k => ?_
  rw [← norm_pow, halfDifference_sq, adjacentDifference_eq]

/-- Diagonal adjacent-shell contrast factored into Hilbert–Schmidt operators. -/
def adjacentOperator (s : {z : ℂ // 0 < z.re}) :=
  let A := HilbertSchmidt.diagOp (halfDifference s.val) (halfDifference_summable s)
  A ∘L A

theorem adjacentOperator_apply (s : {z : ℂ // 0 < z.re}) (f : lp (fun _ : ℕ => ℂ) 2) (k : ℕ) :
    adjacentOperator s f k = adjacentDifference s.val k * f k := by
  rw [adjacentOperator, ContinuousLinearMap.comp_apply, HilbertSchmidt.diagOp_apply,
    HilbertSchmidt.diagOp_apply, ← mul_assoc, ← sq, halfDifference_sq]

/-- The trace is the convergent paired eta function at every positive real part. -/
theorem adjacentTrace_eq_eta (s : {z : ℂ // 0 < z.re}) :
    ContinuousLinearMap.opTrace (adjacentOperator s) = RiemannGaussian.pairedEtaCore s.val := by
  rw [adjacentOperator, HilbertSchmidt.opTrace_diagOp_comp]
  exact tsum_congr fun k => by rw [← sq, halfDifference_sq, adjacentDifference_eq]

abbrev OpenStrip := {s : ℂ // 0 < s.re ∧ s.re < 1}

theorem adjacentTrace_zero_iff (s : OpenStrip) :
    ContinuousLinearMap.opTrace (adjacentOperator ⟨s.val, s.2.1⟩) = 0 ↔ riemannZeta s.val = 0 := by
  have hne : s.val ≠ 1 := by
    intro h
    have := s.2.2
    rw [h, Complex.one_re] at this
    exact this.false
  rw [adjacentTrace_eq_eta,
    RiemannGaussian.pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one s.2.1 hne,
    mul_eq_zero]
  exact or_iff_right (RiemannGaussian.pairedEtaFactor_ne_zero_of_re_lt_one s.2.2)

/-- RH asks whether every vanishing interference trace forces the original two-copy split
to preserve all state norms. -/
theorem rh_iff_trace_zero_forces_isometry :
    RiemannHypothesis ↔ ∀ s : OpenStrip,
      ContinuousLinearMap.opTrace (adjacentOperator ⟨s.val, s.2.1⟩) = 0 →
        ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s.val f x := by
  constructor
  · intro rh s hz
    apply (split_isometric_iff _).2
    apply rh s.val ((adjacentTrace_zero_iff s).1 hz)
    · rintro ⟨n, hn⟩
      have h := s.2.1
      rw [hn] at h
      norm_num [Complex.mul_re] at h
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · intro h
      have ht := s.2.2
      rw [h, Complex.one_re] at ht
      exact ht.false
  · intro h
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.2
    intro s hhalf hone hz
    let z : OpenStrip := ⟨s, by linarith, hone⟩
    have he := (split_isometric_iff s).1 (h z ((adjacentTrace_zero_iff z).2 hz))
    exact hhalf.ne' he

#print axioms adjacentOperator_apply
#print axioms adjacentTrace_eq_eta
#print axioms adjacentTrace_zero_iff
#print axioms rh_iff_trace_zero_forces_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
