import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.ClockZeros
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdjacentShellTrace

/-! # Recovering the isometry line from genuine zeros at unbounded prime energies -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift

/-- Only convergent zeros enter the measurement, and all primes below N may be discarded. -/
def measuredZeros (N : ℕ) : Set ℂ := {s | ∃ p : Nat.Primes, N ≤ (p:ℕ) ∧
  finiteSplit (lacunaryOmission p) s ∧ compositionResponse (lacunaryOmission p) s = 0}

private theorem height_error (p : Nat.Primes) (t : ℝ) :
    |t-((⌊t/primeZeroSpacing p⌋:ℤ)+1/2:ℝ)*primeZeroSpacing p| ≤ primeZeroSpacing p/2 := by
  let h := primeZeroSpacing p
  let j : ℤ := ⌊t/h⌋
  have hp : 0 < h := primeZeroSpacing_pos p
  have hlo : (j:ℝ)*h ≤ t := (le_div_iff₀ hp).mp (Int.floor_le _)
  have hhi : t < ((j:ℝ)+1)*h := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one _)
  change |t-((j:ℝ)+1/2)*h| ≤ h/2
  rw [abs_le]
  constructor <;> linarith only [hlo,hhi]

/-- The midpoint zero in the target's clock interval gives a uniform half-spacing accuracy. -/
theorem prime_zero_approximation (p : Nat.Primes) {s : ℂ} (hs : s.re = 1/2) :
    ∃ z : ℂ, (finiteSplit (lacunaryOmission p) z ∧ compositionResponse (lacunaryOmission p) z = 0) ∧
      dist s z ≤ primeZeroSpacing p/2 := by
  let j : ℤ := ⌊s.im/primeZeroSpacing p⌋
  refine ⟨primeZeroPoint p j,(lacunary_zero_iff p _).mpr ⟨j,rfl⟩,?_⟩
  have he : s-primeZeroPoint p j = (((s.im-((j:ℝ)+1/2)*primeZeroSpacing p:ℝ):ℂ)*Complex.I) := by
    let y := ((j:ℝ)+1/2)*primeZeroSpacing p
    change s-(((1/2:ℝ):ℂ)+(y:ℂ)*Complex.I) = ((s.im-y:ℝ):ℂ)*Complex.I
    apply Complex.ext <;> simp [hs]
  rw [dist_eq_norm,he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact height_error p s.im

private theorem small_prime_spacing (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Nat.Primes, N ≤ (p:ℕ) ∧ primeZeroSpacing p/2 < ε := by
  obtain ⟨K,hK⟩ := exists_nat_gt (Real.exp (Real.pi/ε))
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (max N K)
  let p : Nat.Primes := ⟨q,hprime⟩
  have hKq : K ≤ q := (le_max_right _ _).trans hq
  have hlog : Real.pi/ε < energy (primePNat p) := by
    rw [← Real.log_exp (Real.pi/ε)]
    exact Real.log_lt_log (Real.exp_pos _) (hK.trans_le (by exact_mod_cast hKq))
  have hπ := (div_lt_iff₀ hε).mp hlog
  have hsmall : primeZeroSpacing p < ε := by
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) (prime_energy_pos p))).mpr
    nlinarith only [hπ,mul_pos hε (prime_energy_pos p)]
  exact ⟨p,(le_max_left _ _).trans hq,by linarith only [hsmall,hε]⟩

private theorem measured_on_line {N : ℕ} {s : ℂ} (hs : s ∈ measuredZeros N) : s.re = 1/2 := by
  obtain ⟨p,_,hp⟩ := hs
  obtain ⟨j,rfl⟩ := (lacunary_zero_iff p s).mp hp
  exact primeZeroPoint_re p j

/-- Removing every species up to any finite cutoff leaves the same closed set of observable zeros. -/
theorem closure_measuredZeros (N : ℕ) : closure (measuredZeros N) = {s : ℂ | s.re = 1/2} := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ hs => measured_on_line hs) (isClosed_eq Complex.continuous_re continuous_const)
  · intro s hs
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨p,hp,hh⟩ := small_prime_spacing N hε
    obtain ⟨z,hz,hd⟩ := prime_zero_approximation p hs
    exact ⟨z,⟨p,hp,hz⟩,hd.trans_lt hh⟩

/-- One half-spacing test for every sufficiently large prime is equivalent to global quantum isometry. -/
theorem prime_zero_test_iff_isometry (N : ℕ) (s : ℂ) :
    (∀ p : Nat.Primes, N ≤ (p:ℕ) → ∃ z : ℂ,
      (finiteSplit (lacunaryOmission p) z ∧ compositionResponse (lacunaryOmission p) z = 0) ∧
      dist s z ≤ primeZeroSpacing p/2) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  refine ⟨fun h => ?_,fun hs p _ => prime_zero_approximation p hs⟩
  have hm : s ∈ closure (measuredZeros N) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨p,hp,hh⟩ := small_prime_spacing N hε
    obtain ⟨z,hz,hd⟩ := h p hp
    exact ⟨z,⟨p,hp,hz⟩,hd.trans_lt hh⟩
  rw [closure_measuredZeros] at hm
  exact hm

/-- Equilibrium zeta zeros in the open strip admit approximation by measured response zeros precisely under RH. -/
theorem rh_iff_approximable_by_composition_zeros (N : ℕ) :
    RiemannHypothesis ↔ ∀ s : OpenStrip, riemannZeta s.val = 0 → s.val ∈ closure (measuredZeros N) := by
  rw [rh_iff_trace_zero_forces_isometry,closure_measuredZeros]
  constructor
  · intro h s hz
    exact (split_isometric_iff _).mp (h s ((adjacentTrace_zero_iff s).mpr hz))
  · intro h s hz
    exact (split_isometric_iff _).mpr (h s ((adjacentTrace_zero_iff s).mp hz))

#print axioms prime_zero_approximation
#print axioms closure_measuredZeros
#print axioms prime_zero_test_iff_isometry
#print axioms rh_iff_approximable_by_composition_zeros

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
