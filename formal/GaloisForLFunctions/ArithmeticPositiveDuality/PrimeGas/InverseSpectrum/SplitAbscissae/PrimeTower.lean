import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.SplitDomain

/-! # Realizing positive intensities on the powers of one elementary prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift GaloisForLFunctions.HTGeometry

/-- The occupation with k identical quanta of one prime. -/
def primeRayLabel (p : Nat.Primes) (k : ℕ) : ℕ+ := primePNat p ^ k

theorem primeRayLabel_injective (p : Nat.Primes) : Function.Injective (primeRayLabel p) := by
  intro j k h
  have he := congrArg PNat.val h
  change (p:ℕ)^j = (p:ℕ)^k at he
  exact (pow_right_strictMono₀ p.property.one_lt).injective he

theorem energy_primeRayLabel (p : Nat.Primes) (k : ℕ) :
    energy (primeRayLabel p k) = (k:ℝ)*energy (primePNat p) := by
  simp only [primeRayLabel,energy,PNat.pow_coe,Nat.cast_pow,Real.log_pow]

theorem prime_energy_pos (p : Nat.Primes) : 0 < energy (primePNat p) :=
  Real.log_pos (show (1:ℝ) < (primePNat p).val by exact_mod_cast p.property.one_lt)

/-- A wave with no labels outside a single prime-power ray. -/
def onPrimeRay (p : Nat.Primes) (f : Gas) : Prop := ∀ n ∉ Set.range (primeRayLabel p), f n = 0

private def rayAmplitude (p : Nat.Primes) (w : ℕ → ℝ) :=
  Function.extend (primeRayLabel p) (fun k => (Real.sqrt (w k):ℂ)) (fun _ => 0)

private theorem ray_sq (p : Nat.Primes) {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (k : ℕ) :
    ‖rayAmplitude p w (primeRayLabel p k)‖^2 = w k := by
  rw [rayAmplitude,(primeRayLabel_injective p).extend_apply,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw k)]

private theorem ray_off (p : Nat.Primes) (w : ℕ → ℝ) {n : ℕ+} (hn : n ∉ Set.range (primeRayLabel p)) :
    rayAmplitude p w n = 0 := Function.extend_apply' _ _ _ hn

/-- The nonnegative-amplitude state with specified summable shell intensities. -/
def primeRayWave (p : Nat.Primes) (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : Summable w) : Gas := by
  refine ⟨rayAmplitude p w,HilbertSchmidt.memℓp_of_sq ?_⟩
  have hz (n : ℕ+) (hn : n ∉ Set.range (primeRayLabel p)) : ‖rayAmplitude p w n‖^2 = 0 := by
    rw [ray_off p w hn,norm_zero,zero_pow two_ne_zero]
  apply ((primeRayLabel_injective p).summable_iff hz).mp
  exact hs.congr (fun k => (ray_sq p hw k).symm)

theorem primeRayWave_support (p : Nat.Primes) (w : ℕ → ℝ) (hw hs) : onPrimeRay p (primeRayWave p w hw hs) :=
  fun _ hn => ray_off p w hn

/-- Every shell-diagonal moment reduces to a one-variable series on this state. -/
theorem primeRayWave_weighted (p : Nat.Primes) (w : ℕ → ℝ) (hw hs) (F : ℕ+ → ℝ) :
    Summable (fun n => F n*‖primeRayWave p w hw hs n‖^2) ↔ Summable (fun k => F (primeRayLabel p k)*w k) := by
  let f (n : ℕ+) := F n*‖rayAmplitude p w n‖^2
  have hoff (n : ℕ+) (hn : n ∉ Set.range (primeRayLabel p)) : f n = 0 := by
    simp only [f,ray_off p w hn,norm_zero,zero_pow two_ne_zero,mul_zero]
  change Summable f ↔ _
  rw [← (primeRayLabel_injective p).summable_iff hoff]
  have he (k : ℕ) : (f ∘ primeRayLabel p) k = F (primeRayLabel p k)*w k := by
    simp only [Function.comp_apply,f,ray_sq p hw]
  exact (congrArg Summable (funext he)).to_iff

#print axioms primeRayLabel_injective
#print axioms energy_primeRayLabel
#print axioms prime_energy_pos
#print axioms primeRayWave_support
#print axioms primeRayWave_weighted

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
