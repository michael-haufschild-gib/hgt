import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands.Arithmetic
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands.Products
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Rigidity

/-! # An unordered probability measurement fixes the Hamiltonian on every shell -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands

open Finset Real

variable {n : ℕ} [NeZero n]

def signal (P : Fin n ↪ Nat.Primes) (E : ℕ+ → ℝ) := reading (law (sample P E))

theorem signed_scale (P : Fin n ↪ Nat.Primes) (E : ℕ+ → ℝ) (s : ℂ) (iso : Isometric E s) :
    signal P energy=2*s.re*signal P E := by
  have eqn : sample P energy = fun i => (2*s.re)*sample P E i :=
    funext fun i => ((isometric_iff_energy E s).mp iso (mode (P i))).symm
  simp only [signal,gibbs_reading,eqn,edge_scale]

/-- The signed scale is the quotient of two finite statistics. -/
theorem thermometer (hn : 3 ≤ n) (P : Fin n ↪ Nat.Primes) (E : ℕ+ → ℝ) (s : ℂ)
    (iso : Isometric E s) : signal P E ≠ 0 ∧ signal P energy/signal P E=2*s.re := by
  have nz : signal P energy ≠ 0 := by
    rw [signal,gibbs_reading]
    exact prime_edge_ne_zero hn P
  have h := signed_scale P E s iso
  have obs : signal P E ≠ 0 := fun zero => nz (by simpa only [zero,mul_zero] using h)
  exact ⟨obs,(div_eq_iff obs).mpr h⟩

theorem calibration_iff (hn : 3 ≤ n) (P : Fin n ↪ Nat.Primes) (E : ℕ+ → ℝ) (s : ℂ) :
    Isometric E s ∧ exp (signal P E)=exp (signal P energy) ↔ E=energy ∧ s.re=1/2 := by
  rw [exp_eq_exp]
  constructor
  · rintro ⟨iso,obs⟩
    obtain ⟨nz,eqn⟩ := thermometer hn P E s iso
    rw [←obs,div_self nz] at eqn
    have terms := (isometric_iff_energy E s).mp iso
    rw [←eqn] at terms
    exact ⟨funext fun k => (one_mul (E k)).symm.trans (terms k),by linarith only [eqn]⟩
  · rintro ⟨rfl,re⟩
    exact ⟨(split_isometric_iff s).mpr re,rfl⟩

/-- The reference is specified by integer labels alone. -/
theorem prime_reference (P : Fin n ↪ Nat.Primes) :
    ∃ i j, (∀ a, (P i).val ≤ (P a).val ∧ (P a).val ≤ (P j).val) ∧
      exp (signal P energy)=(((P i).val*(P j).val:ℕ):ℝ)^n / ((∏ a,(P a).val:ℕ):ℝ)^2 := by
  obtain ⟨i,_,lo⟩ := exists_min_image univ (fun a => (P a).val) univ_nonempty
  obtain ⟨j,_,hi⟩ := exists_max_image univ (fun a => (P a).val) univ_nonempty
  refine ⟨i,j,fun a => ⟨lo a (mem_univ a),hi a (mem_univ a)⟩,?_⟩
  rw [signal,gibbs_reading]
  exact integer_product_at (fun a => mode (P a)) i j
    (fun a => lo a (mem_univ a)) (fun a => hi a (mem_univ a))

/-- The measured side of the calibration uses only products and extremal probabilities. -/
theorem odds_iff (hn : 3 ≤ n) (P : Fin n ↪ Nat.Primes) (E : ℕ+ → ℝ) (s : ℂ) :
    Isometric E s ∧ odds (law (sample P E))=exp (signal P energy) ↔ E=energy ∧ s.re=1/2 := by
  rw [odds_eq (law (sample P E)) (fun a => _root_.HTGeometry.finiteGibbsStateWeight_pos 1 (sample P E) a)]
  exact calibration_iff hn P E s

theorem full_partition (hn : 3 ≤ n) (P : Fin n ↪ Nat.Primes) (E : ℕ+ → ℝ) (s : ℂ) :
    Isometric E s ∧ exp (signal P E)=exp (signal P energy) ↔ Isometric E s ∧
      ∀ z : {w : ℂ // 1<w.re}, HasSum (fun k => Complex.exp (-z.val*(E k:ℂ))) (riemannZeta z.val) := by
  rw [←one_trace_iff_all (⟨2,by norm_num⟩ : TraceTemperature) E s,
    isometry_and_trace_iff,calibration_iff hn]

#print axioms thermometer
#print axioms prime_reference
#print axioms calibration_iff
#print axioms odds_iff
#print axioms full_partition

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands
