import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.SplitAbscissae.EnergyMoments
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.SplitAbscissae.Convergence

/-! # Sharp energy-moment profiles on one elementary prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift

/-- Proposed finite moments at a split threshold, with polynomial damping of degree d. -/
def momentAdmitted (θ : ℝ) (d : ℕ) (σ : ℝ) (m : ℕ) : Prop := θ < σ ∨ θ = σ ∧ m+1 < d

private def rayRatio (p : Nat.Primes) (θ σ : ℝ) := Real.exp (2*(θ-σ)*energy (primePNat p))

private theorem ratio_summable (p : Nat.Primes) (θ σ : ℝ) (m d : ℕ) :
    Summable (towerTerm (rayRatio p θ σ) m d) ↔ momentAdmitted θ d σ m := by
  have hlt : rayRatio p θ σ < 1 ↔ θ < σ := by
    rw [rayRatio,Real.exp_lt_one_iff]
    constructor
    · intro h
      by_contra! hh
      exact h.not_ge (mul_nonneg (by linarith only [hh]) (prime_energy_pos p).le)
    · intro h
      exact mul_neg_of_neg_of_pos (by linarith only [h]) (prime_energy_pos p)
  have he : rayRatio p θ σ = 1 ↔ θ = σ := by
    constructor
    · intro h
      have h0 := (Real.exp_eq_one_iff _).mp h
      have hh := (mul_eq_zero.mp h0).resolve_right (prime_energy_pos p).ne'
      linarith only [hh]
    · rintro rfl
      simp [rayRatio]
  rw [summable_towerTerm_iff (show 0 < rayRatio p θ σ from Real.exp_pos _) m d,hlt,he,momentAdmitted]

private theorem profile_wave_moment (p : Nat.Primes) (θ : ℝ) (d : ℕ)
    (hw : ∀ k, 0 ≤ towerTerm (rayRatio p θ (1/2)) 0 d k) (hs) (s : ℂ) (m : ℕ) :
    splitEnergyMomentFinite (primeRayWave p _ hw hs) s m ↔ momentAdmitted θ d s.re m := by
  let q := Real.exp ((1-2*s.re)*energy (primePNat p))
  have hr : q*rayRatio p θ (1/2) = rayRatio p θ s.re := by
    dsimp only [q,rayRatio]
    rw [← Real.exp_add]
    congr 1
    ring
  have he (k : ℕ) : (k:ℝ)^m*q^k*towerTerm (rayRatio p θ (1/2)) 0 d k = towerTerm (rayRatio p θ s.re) m d k := by
    rw [towerTerm,towerTerm,pow_zero,one_mul,← hr,mul_pow]
    ring
  rw [primeRayWave_energyMoment]
  exact (congrArg Summable (funext he)).to_iff.trans (ratio_summable p θ s.re m d)

/-- For every specified prime, convergence at the isometry line and divergence at zero are the only restrictions on these complete moment profiles. -/
theorem prime_moment_profile_iff (p : Nat.Primes) (θ : ℝ) (d : ℕ) :
    (∃ v : MissingWave, onPrimeRay p v.val ∧ ∀ (s : ℂ) (m : ℕ),
      splitEnergyMomentFinite v.val s m ↔ momentAdmitted θ d s.re m) ↔
      momentAdmitted θ d (1/2) 0 ∧ ¬ momentAdmitted θ d 0 0 := by
  constructor
  · rintro ⟨v,_,h⟩
    have hh := (forall_finiteSplit_iff ((1/2:ℝ):ℂ)).mpr le_rfl v
    exact ⟨(h _ 0).mp ((zeroth_energyMoment_iff v _).mpr hh),
      fun h0 => v.property ((heatRange_iff_split_at_zero v.val).mpr ((h 0 0).mpr h0))⟩
  · rintro ⟨hn,ho⟩
    have hw (k : ℕ) : 0 ≤ towerTerm (rayRatio p θ (1/2)) 0 d k :=
      div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Real.exp_pos _).le _)) (pow_nonneg (Nat.cast_nonneg _) _)
    have hs := (ratio_summable p θ (1/2) 0 d).mpr hn
    let f := primeRayWave p _ hw hs
    have hf : f ∉ LinearMap.range criticalOperator.toLinearMap := fun hin =>
      ho ((profile_wave_moment p θ d hw hs 0 0).mp ((heatRange_iff_split_at_zero f).mp hin))
    exact ⟨⟨f,hf⟩,primeRayWave_support p _ hw hs,profile_wave_moment p θ d hw hs⟩

#print axioms prime_moment_profile_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
