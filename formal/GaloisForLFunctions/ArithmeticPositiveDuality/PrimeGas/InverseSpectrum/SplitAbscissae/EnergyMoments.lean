import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.SplitAbscissae.PrimeTower

/-! # Energy moments of the actual two-copy output -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift

/-- Finiteness of the m-th energy moment in the outgoing pair basis. -/
def splitEnergyMomentFinite (f : Gas) (s : ℂ) (m : ℕ) : Prop :=
  Summable (fun x : ℕ+ × ℕ+ => energy (x.1*x.2)^m*‖split s f x‖^2)

private theorem shellEnergy_nonneg (n : ℕ+) : 0 ≤ energy n :=
  Real.log_nonneg (show (1:ℝ) ≤ n.val by exact_mod_cast n.pos)

/-- Grouping the energy-weighted pair probabilities by total occupation gives the native shell series. -/
theorem splitEnergyMomentFinite_iff (f : Gas) (s : ℂ) (m : ℕ) :
    splitEnergyMomentFinite f s m ↔ Summable (fun n => energy n^m*shellMass s n*‖f n‖^2) := by
  let a (n : ℕ+) : ℂ := Real.sqrt (energy n^m)
  let g (n : ℕ+) := a n*f n
  have ha (n : ℕ+) : ‖a n‖^2 = energy n^m := by
    change ‖(Real.sqrt (energy n^m):ℂ)‖^2 = _
    rw [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (pow_nonneg (shellEnergy_nonneg n) _)]
  have hpair (x : ℕ+ × ℕ+) : ‖split s g x‖^2 = energy (x.1*x.2)^m*‖split s f x‖^2 := by
    have he : split s g x = a (x.1*x.2)*split s f x := by unfold split g; ring
    rw [he,norm_mul,mul_pow,ha]
  have hsingle (n : ℕ+) : shellMass s n*‖g n‖^2 = energy n^m*shellMass s n*‖f n‖^2 := by
    change shellMass s n*‖a n*f n‖^2 = _
    rw [norm_mul,mul_pow,ha]
    ring
  have h : Summable (fun x => ‖split s g x‖^2) ↔ Summable (fun n => shellMass s n*‖g n‖^2) :=
    exists_congr (fun r => split_hasSum_iff s g r)
  exact (congrArg Summable (funext hpair)).to_iff.symm.trans (h.trans (congrArg Summable (funext hsingle)).to_iff)

theorem zeroth_energyMoment_iff (v : MissingWave) (s : ℂ) :
    splitEnergyMomentFinite v.val s 0 ↔ finiteSplit v s := by
  simp only [splitEnergyMomentFinite,finiteSplit,pow_zero,one_mul]

/-- At zero, square summability of the pair output is precisely existence of a critical-heat preimage. -/
theorem heatRange_iff_split_at_zero (f : Gas) :
    f ∈ LinearMap.range criticalOperator.toLinearMap ↔ splitEnergyMomentFinite f 0 0 := by
  rw [heat_range_iff_summable,splitEnergyMomentFinite_iff,← Equiv.pnatEquivNat.symm.summable_iff
    (f := fun n => energy n^0*shellMass 0 n*‖f n‖^2)]
  change Summable (fun k => ‖f (number k)‖^2/occupationWeight k) ↔
    Summable (fun k => energy (number k)^0*shellMass 0 (number k)*‖f (number k)‖^2)
  simp only [pow_zero,one_mul,shellMass_zero_eq_inv_occupationWeight,div_eq_inv_mul]

/-- Each prime quantum contributes the same squared shell multiplier. -/
theorem shellMass_primeRayLabel (p : Nat.Primes) (s : ℂ) (k : ℕ) :
    shellMass s (primeRayLabel p k) = Real.exp ((1-2*s.re)*energy (primePNat p))^k := by
  rw [shellMass,energy_primeRayLabel,← Real.exp_nat_mul]
  congr 1
  ring

theorem primeRayWave_energyMoment (p : Nat.Primes) (w : ℕ → ℝ) (hw hs) (s : ℂ) (m : ℕ) :
    splitEnergyMomentFinite (primeRayWave p w hw hs) s m ↔
      Summable (fun k : ℕ => (k:ℝ)^m*Real.exp ((1-2*s.re)*energy (primePNat p))^k*w k) := by
  rw [splitEnergyMomentFinite_iff,primeRayWave_weighted]
  let r := Real.exp ((1-2*s.re)*energy (primePNat p))
  have he (k : ℕ) : energy (primeRayLabel p k)^m*shellMass s (primeRayLabel p k)*w k =
      energy (primePNat p)^m*((k:ℝ)^m*r^k*w k) := by
    rw [energy_primeRayLabel,mul_pow,shellMass_primeRayLabel]
    dsimp only [r]
    ring
  rw [funext he,summable_mul_left_iff (pow_ne_zero m (prime_energy_pos p).ne')]

#print axioms splitEnergyMomentFinite_iff
#print axioms zeroth_energyMoment_iff
#print axioms heatRange_iff_split_at_zero
#print axioms shellMass_primeRayLabel
#print axioms primeRayWave_energyMoment

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
