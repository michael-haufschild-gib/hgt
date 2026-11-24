import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.PrimeRay
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.LacunaryLaw
import Mathlib.Analysis.Meromorphic.Order

/-! # Simple torsion zeros of finite partitions extracted at one prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing
open _root_.RHTower.PrimeCoShift

def digitPartition (q : Nat.Primes) (A : Finset ℕ) (s : ℂ) : ℂ := ∑ a : A, heat s (primeRayLabel q a.val)

private theorem analytic_heat_at (n : ℕ+) (s : ℂ) : AnalyticAt ℂ (fun w => heat w n) s :=
  (analyticAt_id.neg.mul analyticAt_const).cexp

private theorem analytic_digitPartition (q : Nat.Primes) (A : Finset ℕ) (s : ℂ) : AnalyticAt ℂ (digitPartition q A) s :=
  Finset.analyticAt_fun_sum _ (fun a _ => analytic_heat_at (primeRayLabel q a.val) s)

/-- Multiplication by the finite complement and the elementary difference clears every zero. -/
theorem tile_heat_identity (q : Nat.Primes) {A T : Finset ℕ} {L : ℕ+} (h : tilesInterval A T L.val) (s : ℂ) :
    digitPartition q A s * digitPartition q T s * (heat s (primePNat q)-1) = heat s (primeRayLabel q L.val)-1 := by
  simp only [digitPartition,heat_primeRayLabel,interval_partition h,geom_sum_mul]

private theorem simple_at_root (q : Nat.Primes) {A T : Finset ℕ} {L : ℕ+} (h : tilesInterval A T L.val)
    {s : ℂ} (hz : digitPartition q A s = 0) :
    heat s (primeRayLabel q L.val) = 1 ∧ s.re = 0 ∧ meromorphicOrderAt (digitPartition q A) s = 1 := by
  let n := primeRayLabel q L.val
  have hE : 0 < energy n := by
    rw [show energy n = (L.val:ℝ)*energy (primePNat q) from energy_primeRayLabel q L.val]
    exact mul_pos (Nat.cast_pos.mpr L.pos) (prime_energy_pos q)
  have he := tile_heat_identity q h s
  rw [hz,zero_mul,zero_mul] at he
  have h1 : heat s n = 1 := sub_eq_zero.mp he.symm
  have hr := congrArg norm h1
  rw [norm_heat,norm_one,Real.exp_eq_one_iff] at hr
  have ha := analytic_digitPartition q A s
  refine ⟨h1,neg_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right hE.ne'),?_⟩
  have hd : deriv (digitPartition q A) s ≠ 0 := by
    intro hd₀
    have hA : HasDerivAt (digitPartition q A) 0 s := hd₀ ▸ ha.differentiableAt.hasDerivAt
    have hT := (analytic_digitPartition q T s).differentiableAt.hasDerivAt
    have hU := (analytic_heat_at (primePNat q) s).differentiableAt.hasDerivAt.sub_const 1
    have hm : HasDerivAt (fun w => digitPartition q A w * digitPartition q T w * (heat w (primePNat q)-1)) 0 s := by
      have hp := (hA.mul hT).mul hU
      simp only [Pi.mul_apply,hz,zero_mul,add_zero] at hp
      exact hp
    have hf : (fun w => digitPartition q A w * digitPartition q T w * (heat w (primePNat q)-1)) =
        (fun w => heat w n - 1) := funext (tile_heat_identity q h)
    rw [hf] at hm
    have hn := ((Complex.hasDerivAt_exp _).comp s ((hasDerivAt_id s).neg.mul_const (energy n:ℂ))).sub_const 1
    have hder : (0:ℂ) = heat s n * (-1 * (energy n:ℂ)) := hm.unique hn
    exact (mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (neg_ne_zero.mpr one_ne_zero)
      (Complex.ofReal_ne_zero.mpr hE.ne'))) hder.symm
  rw [ha.meromorphicOrderAt_eq,ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hd]
  rfl

/-- A single bounded period pins all zeros to the imaginary torsion grid and fixes their multiplicity. -/
theorem extractable_partition_zeros (q : Nat.Primes) {A : Finset ℕ} (hA : A.Nonempty) (h : extractable q A) :
    ∃ L : ℕ+, L.val ≤ 2^(A.max' hA) ∧ ∀ s : ℂ, digitPartition q A s = 0 →
      heat s (primeRayLabel q L.val) = 1 ∧ s.re = 0 ∧ meromorphicOrderAt (digitPartition q A) s = 1 := by
  obtain ⟨L,hL,T,hT⟩ := (extractable_iff_interval q A hA).mp h
  exact ⟨L,hL,fun _ hz => simple_at_root q hT hz⟩

#print axioms tile_heat_identity
#print axioms extractable_partition_zeros

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
