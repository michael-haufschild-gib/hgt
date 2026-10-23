import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHeckeTowerOfAPrimeIsThePeriodQuotient

/-!
# Almost every prime sees every right zero

A single prime tower `g(· − k log p)` is the period quotient of the scaling surface: two zeros share
the Frobenius eigenvalue `p^{ρ − ½}` exactly when they have the same real part and their ordinates
differ by a multiple of `2π/log p` (`frobEig_eq_frobEig_iff`). Over `𝔽_q` the commensurable prime
`q` identifies every zero with its vertical translates, which is why the Frobenius span counts each
outer eigenvalue once.

Over `ℚ` such a coincidence is rare. For two distinct zeros `ρ ≠ ρ'` at most **one** prime makes
them collide: if `p` and `q` both did, `log q / log p` would be the rational number `m/k`, against
the independence of prime logarithms (`subsingleton_resonantPrimes`). Hence, for a configuration
with finitely many right zeros, only finitely many **resonant primes** fail to separate the right
zeros (`finite_resonantPrimes`). At every other prime the eigenvalue classes are singletons, the
Frobenius weight of each class is `X_ρ(g) conj X_{1−ρ̄}(g) ≠ 0` for a spectrally generic test
(`frobWeight_ne_zero_of_injOn`), and the tower Pontryagin law becomes the full law
(`tower_pontryagin_law_of_injOn`):

  **one prime tower of one generic test carries the whole Hodge defect, for all but finitely many
  primes** (`almost_every_prime_tower_sees_every_right_zero`).

The rank-two Hecke orbit of `TheHodgeDefectIsCyclic` is needed only at the resonant primes, or when
the right zeros are infinite and their eigenvalues may accumulate.
-/

open Complex
open scoped ComplexConjugate Classical
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- **Coincidence of Frobenius eigenvalues.** At a positive scale `ℓ`, two points share an
eigenvalue iff they have the same real part and `ℓ (Im ρ − Im ρ') ∈ 2πℤ`. -/
theorem frobEig_eq_frobEig_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (ρ ρ' : ℂ) :
    frobEig ℓ ρ = frobEig ℓ ρ' ↔
      ρ.re = ρ'.re ∧ ∃ k : ℤ, ℓ * (ρ.im - ρ'.im) = 2 * Real.pi * k := by
  rw [frobEig, frobEig, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    have hre := congrArg Complex.re hk
    have him := congrArg Complex.im hk
    simp [Complex.mul_re, Complex.mul_im] at hre him
    rcases hre with h | h
    · exact ⟨h, k, by linarith⟩
    · exact absurd h hℓ.ne'
  · rintro ⟨hre, k, hk⟩
    refine ⟨k, Complex.ext ?_ ?_⟩
    · simp [Complex.mul_re, hre]
    · simp [Complex.mul_im]; linarith

/-- **At most one resonant prime per pair.** Two distinct points share a Frobenius eigenvalue at no
more than one prime: two primes would make `log q / log p` rational. -/
theorem subsingleton_resonantPrimes {ρ ρ' : ℂ} (hne : ρ ≠ ρ') :
    {p : ℕ | p.Prime ∧ frobEig (Real.log p) ρ = frobEig (Real.log p) ρ'}.Subsingleton := by
  have key : ∀ {r : ℕ}, r.Prime → frobEig (Real.log r) ρ = frobEig (Real.log r) ρ' →
      ∃ k : ℤ, k ≠ 0 ∧ Real.log r * (ρ.im - ρ'.im) = 2 * Real.pi * k := by
    intro r hr he
    have hlog : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
    obtain ⟨hre, k, hk⟩ := (frobEig_eq_frobEig_iff hlog ρ ρ').mp he
    refine ⟨k, fun hk0 => hne (Complex.ext hre ?_), hk⟩
    rw [hk0, Int.cast_zero, mul_zero] at hk
    rcases mul_eq_zero.mp hk with h | h
    · linarith
    · linarith
  rintro p ⟨hp, hpe⟩ q ⟨hq, hqe⟩
  by_contra hpq
  obtain ⟨k, hk0, hk⟩ := key hp hpe
  obtain ⟨m, hm0, hm⟩ := key hq hqe
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hk0' : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hΔ : ρ.im - ρ'.im ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hk
    exact hk0' (by nlinarith [Real.pi_pos])
  apply RHTower.irrational_log_ratio hp hq hpq
  refine ⟨(m : ℚ) / k, ?_⟩
  push_cast
  rw [div_eq_div_iff hk0' hlp.ne']
  apply mul_right_cancel₀ hΔ
  linear_combination (m : ℝ) * hk - (k : ℝ) * hm

/-- **Finitely many resonant primes.** If a configuration has finitely many right zeros, all but
finitely many primes separate them by their Frobenius eigenvalues. -/
theorem finite_resonantPrimes (Z : ZeroConfig) (hR : (rightZeros Z).Finite) :
    {p : ℕ | p.Prime ∧ ¬ Set.InjOn (frobEig (Real.log p)) (rightZeros Z)}.Finite := by
  have hsub : {p : ℕ | p.Prime ∧ ¬ Set.InjOn (frobEig (Real.log p)) (rightZeros Z)} ⊆
      ⋃ ρ ∈ rightZeros Z, ⋃ ρ' ∈ rightZeros Z,
        {p : ℕ | ρ ≠ ρ' ∧ p.Prime ∧ frobEig (Real.log p) ρ = frobEig (Real.log p) ρ'} := by
    rintro p ⟨hp, hinj⟩
    simp only [Set.InjOn, not_forall, exists_prop] at hinj
    obtain ⟨ρ, hρ, ρ', hρ', he, hne⟩ := hinj
    simp only [Set.mem_iUnion]
    exact ⟨ρ, hρ, ρ', hρ', hne, hp, he⟩
  refine Set.Finite.subset (hR.biUnion fun ρ _ => hR.biUnion fun ρ' _ => ?_) hsub
  by_cases hne : ρ = ρ'
  · simp [hne]
  · refine (subsingleton_resonantPrimes hne).finite.subset ?_
    rintro p ⟨-, hp, he⟩
    exact ⟨hp, he⟩

/-- At a separating scale, the Frobenius weight of the eigenvalue of a right zero is the single term
`X_ρ(g) conj X_{1−ρ̄}(g)`, nonzero for a spectrally generic test. -/
theorem frobWeight_ne_zero_of_injOn (Z : ZeroConfig) {g : ℝ → ℂ} (hgen : SpectrallyGeneric Z g)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hinj : Set.InjOn (frobEig ℓ) (rightZeros Z)) {ρ : ℂ}
    (hρ : ρ ∈ rightZeros Z) : frobWeight Z g ℓ (frobEig ℓ ρ) ≠ 0 := by
  rw [frobWeight, tsum_eq_single (⟨ρ, hρ.1⟩ : Z.carrier) (fun τ hτ => ?_)]
  · rw [if_pos rfl]
    exact mul_ne_zero (zeroCoord_ne_zero hgen _) ((map_ne_zero _).mpr (zeroCoord_ne_zero hgen _))
  · rw [if_neg]
    intro he
    have h1 : 1 < ‖frobEig ℓ τ‖ := by
      rw [he]; exact (one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2
    exact hτ (Subtype.ext (hinj ⟨τ.2, (one_lt_norm_frobEig_iff hℓ _).mp h1⟩ hρ he))

/-- At a separating scale every outer eigenvalue is visible. -/
theorem visibleEig_eq_of_injOn (Z : ZeroConfig) {g : ℝ → ℂ} (hgen : SpectrallyGeneric Z g)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hinj : Set.InjOn (frobEig ℓ) (rightZeros Z))
    (hO : (outerEig Z ℓ).Finite) : visibleEig Z g ℓ hO = hO.toFinset := by
  refine Finset.filter_true_of_mem fun b hb => ?_
  obtain ⟨ρ, hρ, rfl⟩ := hO.mem_toFinset.mp hb
  exact frobWeight_ne_zero_of_injOn Z hgen hℓ hinj hρ

/-- **The tower Pontryagin law at a separating scale.** If a tempered configuration has finitely many
right zeros and `frobEig ℓ` separates them, the Weil form has `n` negative squares on some window of
the tower of a spectrally generic test iff there are at least `n` zeros right of the line. -/
theorem tower_pontryagin_law_of_injOn (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hR : (rightZeros Z).Finite) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgen : SpectrallyGeneric Z g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hinj : Set.InjOn (frobEig ℓ) (rightZeros Z)) (n : ℕ) :
    (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
      (n : ℕ∞) ≤ (rightZeros Z).encard := by
  have hO : (outerEig Z ℓ).Finite := hR.image _
  rw [tower_pontryagin_law Z hZ hg hgc hℓ hO n, visibleEig_eq_of_injOn Z hgen hℓ hinj hO,
    ← hinj.encard_image, show frobEig ℓ '' rightZeros Z = outerEig Z ℓ from rfl,
    hO.encard_eq_coe_toFinset_card, ENat.coe_le_coe]

/-- **Almost every prime sees every right zero.** For a tempered configuration with finitely many
right zeros, all primes except finitely many resonant ones separate the right zeros by their
Frobenius eigenvalues, and at each such prime `p` the tower `g(· − k log p)` of any spectrally
generic test carries the whole Hodge defect. -/
theorem almost_every_prime_tower_sees_every_right_zero (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hR : (rightZeros Z).Finite) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgen : SpectrallyGeneric Z g) :
    {p : ℕ | p.Prime ∧ ¬ Set.InjOn (frobEig (Real.log p)) (rightZeros Z)}.Finite ∧
      ∀ p : ℕ, p.Prime → Set.InjOn (frobEig (Real.log p)) (rightZeros Z) → ∀ n : ℕ,
        (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g (Real.log p) K)) ↔
          (n : ℕ∞) ≤ (rightZeros Z).encard :=
  ⟨finite_resonantPrimes Z hR, fun p hp hinj n =>
    tower_pontryagin_law_of_injOn Z hZ hR hg hgc hgen
      (Real.log_pos (by exact_mod_cast hp.one_lt)) hinj n⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
