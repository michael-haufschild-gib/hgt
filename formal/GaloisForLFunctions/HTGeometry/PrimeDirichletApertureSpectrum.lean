import GaloisForLFunctions.HTGeometry.GammaProjectivePrimeTorusCarrier
import GaloisForLFunctions.HTGeometry.BohrProductUniformLimit

/-!
# The aperture lattice is a Bohr spectrum

The finite prime Dirichlet polynomial

`D_{N,σ}(t) = ∑_{p ≤ N} p^{-σ-it}`

is a trigonometric polynomial on the vertical line whose frequencies are exactly the prime
logarithms `−log p`, `p ≤ N`, each with the nonzero coefficient `p^{-σ}`.  Its Bohr frequency module
is therefore exactly the aperture-`N` character module `span_ℚ {log p : p ≤ N}`, of rational rank
`π(N)`.

This grounds the abstract aperture lattice: it is not merely a lattice one may inject into a
carrier, it *is* the frequency module of a concrete analytic observable on the line, so the carrier
covering-dimension bound applies to that observable.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- The vertical frequency carried by the prime `p`. -/
noncomputable def primeLineFrequency (p : Nat.Primes) : ℝ := -Real.log ((p : ℕ) : ℝ)

/-- The finite prime Dirichlet polynomial on the vertical line `Re s = σ`. -/
noncomputable def primeDirichletLine (N : ℕ) (σ t : ℝ) : ℂ :=
  ∑ p ∈ primesLE N, (((((p : ℕ) : ℝ)) ^ (-σ) : ℝ) : ℂ) * expChar (primeLineFrequency p) t

theorem primeLineFrequency_injective : Function.Injective primeLineFrequency := by
  intro p q h
  rw [primeLineFrequency, primeLineFrequency, neg_inj] at h
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by
    exact_mod_cast (Nat.Prime.pos p.2)
  have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.Prime.pos q.2)
  have hcast : ((p : ℕ) : ℝ) = ((q : ℕ) : ℝ) := Real.log_injOn_pos hp hq h
  have : (p : ℕ) = (q : ℕ) := by exact_mod_cast hcast
  exact Subtype.ext this

theorem primeDirichletLine_coeff_pos (p : Nat.Primes) (σ : ℝ) :
    (0 : ℝ) < (((p : ℕ) : ℝ)) ^ (-σ) := by
  refine Real.rpow_pos_of_pos ?_ _
  exact_mod_cast (Nat.Prime.pos p.2)

theorem continuous_primeDirichletLine (N : ℕ) (σ : ℝ) : Continuous (primeDirichletLine N σ) := by
  unfold primeDirichletLine
  exact continuous_finsetSum _ (fun p _ => continuous_const.mul (continuous_expChar _))

theorem isBohrAlmostPeriodic_primeDirichletLine (N : ℕ) (σ : ℝ) :
    HTGeometry.IsBohrAlmostPeriodic (primeDirichletLine N σ) := by
  unfold primeDirichletLine
  exact isBohrAlmostPeriodic_sum (primesLE N)
    (fun p _ => continuous_const.mul (continuous_expChar _))
    (fun p _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))

/-- The Bohr coefficients of the prime Dirichlet polynomial. -/
theorem bohrCoefficient_primeDirichletLine (N : ℕ) (σ lam : ℝ) :
    bohrCoefficient (primeDirichletLine N σ) lam
      = ∑ p ∈ primesLE N, if primeLineFrequency p = lam then
          (((((p : ℕ) : ℝ)) ^ (-σ) : ℝ) : ℂ) else 0 := by
  classical
  have hfun : primeDirichletLine N σ
      = fun t : ℝ => ∑ p ∈ primesLE N,
        (((((p : ℕ) : ℝ)) ^ (-σ) : ℝ) : ℂ) * bohrExp (primeLineFrequency p) t := by
    funext t
    exact Finset.sum_congr rfl fun p _ => by rw [expChar_eq_bohrExp]
  rw [hfun, bohrCoefficient_trigPoly]

/-- Each aperture prime really is a frequency, with its Dirichlet coefficient. -/
theorem bohrCoefficient_primeDirichletLine_prime {N : ℕ} (σ : ℝ) {p : Nat.Primes}
    (hp : p ∈ primesLE N) :
    bohrCoefficient (primeDirichletLine N σ) (primeLineFrequency p)
      = (((((p : ℕ) : ℝ)) ^ (-σ) : ℝ) : ℂ) := by
  classical
  rw [bohrCoefficient_primeDirichletLine]
  have hterm : ∀ q ∈ primesLE N,
      (if primeLineFrequency q = primeLineFrequency p then
        (((((q : ℕ) : ℝ)) ^ (-σ) : ℝ) : ℂ) else 0)
        = if q = p then (((((q : ℕ) : ℝ)) ^ (-σ) : ℝ) : ℂ) else 0 := by
    intro q _
    by_cases hqp : q = p
    · simp [hqp]
    · have : primeLineFrequency q ≠ primeLineFrequency p :=
        fun h => hqp (primeLineFrequency_injective h)
      simp [this, hqp]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' (primesLE N) p (fun q => (((((q : ℕ) : ℝ)) ^ (-σ) : ℝ) : ℂ)), if_pos hp]

theorem primeLineFrequency_mem_bohrSpectrum {N : ℕ} (σ : ℝ) {p : Nat.Primes}
    (hp : p ∈ primesLE N) :
    primeLineFrequency p ∈ bohrSpectrum (primeDirichletLine N σ) := by
  show bohrCoefficient (primeDirichletLine N σ) (primeLineFrequency p) ≠ 0
  rw [bohrCoefficient_primeDirichletLine_prime σ hp]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (primeDirichletLine_coeff_pos p σ)

theorem bohrSpectrum_primeDirichletLine_subset (N : ℕ) (σ : ℝ) :
    bohrSpectrum (primeDirichletLine N σ)
      ⊆ primeLineFrequency '' (primesLE N : Set Nat.Primes) := by
  classical
  intro lam hlam
  by_contra hnot
  refine hlam ?_
  rw [bohrCoefficient_primeDirichletLine]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hne : primeLineFrequency p ≠ lam := by
    intro h
    exact hnot ⟨p, by simpa using hp, h⟩
  simp [hne]

/-- **The frequency module of the prime Dirichlet polynomial is the aperture module.** -/
theorem bohrFrequencyModule_primeDirichletLine (N : ℕ) (σ : ℝ) :
    bohrFrequencyModule (primeDirichletLine N σ) = primeApertureCharacterModule N := by
  classical
  refine le_antisymm ?_ ?_
  · rw [bohrFrequencyModule]
    refine Submodule.span_le.mpr ?_
    intro lam hlam
    obtain ⟨p, hp, rfl⟩ := bohrSpectrum_primeDirichletLine_subset N σ hlam
    have hbase : Real.log ((p : Nat.Primes) : ℕ) ∈ primeApertureCharacterModule N := by
      unfold primeApertureCharacterModule primeLogSpan
      exact Submodule.subset_span ⟨⟨p, by simpa using hp⟩, rfl⟩
    have hneg := Submodule.neg_mem (primeApertureCharacterModule N) hbase
    rw [SetLike.mem_coe, primeLineFrequency]
    exact hneg
  · unfold primeApertureCharacterModule primeLogSpan
    refine Submodule.span_le.mpr ?_
    rintro x ⟨p, rfl⟩
    have hp : (p : Nat.Primes) ∈ primesLE N := p.2
    have hmem := primeLineFrequency_mem_bohrSpectrum σ hp
    have hneg := Submodule.neg_mem (bohrFrequencyModule (primeDirichletLine N σ))
      (Submodule.subset_span hmem)
    rw [SetLike.mem_coe]
    rw [primeLineFrequency, neg_neg] at hneg
    exact hneg

/-- The rational Bohr frequency rank of the prime Dirichlet polynomial is exactly `π(N)`. -/
theorem finrank_bohrFrequencyModule_primeDirichletLine (N : ℕ) (σ : ℝ) :
    Module.finrank ℚ (bohrFrequencyModule (primeDirichletLine N σ)) = Nat.primeCounting N := by
  rw [bohrFrequencyModule_primeDirichletLine, primeApertureCharacterModule_finrank]

/-- **The carrier bound, on a concrete observable.**  Any finite rational character space receiving
an injection of the frequency module of the aperture-`N` prime Dirichlet polynomial has dimension at
least `π(N)`. -/
theorem primeDirichlet_carrier_covering_dim_ge {A : Type*} [AddCommGroup A] [Module ℚ A]
    [Module.Finite ℚ A] (N : ℕ) (σ : ℝ)
    (j : bohrFrequencyModule (primeDirichletLine N σ) →ₗ[ℚ] A) (hj : Function.Injective j) :
    Nat.primeCounting N ≤ Module.finrank ℚ A := by
  have h := bohrFrequencyModule_primeDirichletLine N σ
  refine primeAperture_carrier_covering_dim_ge N
    (j.comp (LinearEquiv.ofEq _ _ h.symm).toLinearMap) ?_
  exact hj.comp (LinearEquiv.ofEq _ _ h.symm).injective

end

end GaloisForLFunctions
