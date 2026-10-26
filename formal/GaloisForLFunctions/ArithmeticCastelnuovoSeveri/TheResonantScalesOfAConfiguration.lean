import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OneTestCarriesTheDefectOfZetaAtEachPrime
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTowersOfACurveAreItsBaseChanges

/-!
# The resonant scales of a configuration

A tower at scale `ℓ` merges two right zeros when they share the eigenvalue `e^{ℓ(ρ − ½)}`: equal
real parts and `ℓ (Im ρ − Im ρ') ∈ 2πℤ` (`frobEig_eq_frobEig_iff`). Such scales are *resonant*
(`resonantScales`); off them the tower defect counts right zeros, not eigenvalue classes.

* **Resonant scales are countable** (`countable_resonantScales`): each pair resonates on the
  lattice `2πℤ/(Im ρ − Im ρ')`.
* **Off resonance one tower carries the Hodge defect** (`deepSparse_tower_law_of_injOn`,
  `deepSparse_tower_law_off_resonance`): for a deep-sparse configuration, at every non-resonant
  scale one test's tower has `n` negative squares on some window iff there are at least `n` right
  zeros.
* **Primes are almost never resonant** (`finite_primes_encard_outerEig_ne`). At all but finitely
  many primes there are as many outer eigenvalues as right zeros: for finitely many right zeros
  each pair resonates at one prime at most; for infinitely many, an infinite class at `p` is
  separated at every `q ≠ p`, so at most one prime has finitely many outer eigenvalues
  (`subsingleton_primes_outerEig_finite`).
* **For `ζ`** (`zeta_tower_law_at_almost_every_prime`): at all but finitely many primes one test's
  `p`-tower carries the whole Hodge defect `#{Re ρ > ½}`.
* **Curves resonate at their arithmetic scales** (`CurveDatum.mem_resonantScales_of_rat`): for a
  datum off the unit circle every `ℓ` with `ℓ/log q` rational is resonant, since there finitely
  many eigenvalues fold infinitely many right zeros.

The period quotient of a curve is resonance at its arithmetic scales; the primes of `ℚ` are
resonant for `ζ` at most finitely often.
-/

open Complex Set
open scoped ComplexConjugate Classical
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The scales at which a tower merges two right zeros. -/
def resonantScales (Z : ZeroConfig) : Set ℝ :=
  {ℓ | 0 < ℓ ∧ ¬ Set.InjOn (frobEig ℓ) (rightZeros Z)}

/-- **Resonant scales are countable.** -/
theorem countable_resonantScales (Z : ZeroConfig) : (resonantScales Z).Countable := by
  have hR : (rightZeros Z).Countable :=
    (SquareRootThreshold.countable_carrier Z).mono fun _ h => h.1
  have hsub : resonantScales Z ⊆ ⋃ ρ ∈ rightZeros Z, ⋃ ρ' ∈ rightZeros Z,
      Set.range fun k : ℤ => 2 * Real.pi * k / (ρ.im - ρ'.im) := by
    rintro ℓ ⟨hℓ, hinj⟩
    simp only [Set.InjOn, not_forall, exists_prop] at hinj
    obtain ⟨ρ, hρ, ρ', hρ', he, hne⟩ := hinj
    obtain ⟨hre, k, hk⟩ := (frobEig_eq_frobEig_iff hℓ ρ ρ').mp he
    have hΔ : ρ.im - ρ'.im ≠ 0 := fun h0 => hne (Complex.ext hre (by linarith))
    simp only [Set.mem_iUnion]
    refine ⟨ρ, hρ, ρ', hρ', k, ?_⟩
    show 2 * Real.pi * k / (ρ.im - ρ'.im) = ℓ
    rw [← hk, mul_div_cancel_right₀ _ hΔ]
  exact (hR.biUnion fun ρ _ => hR.biUnion fun ρ' _ => Set.countable_range _).mono hsub

/-- At a non-resonant scale the outer eigenvalues are as many as the right zeros. -/
theorem encard_outerEig_eq_of_injOn (Z : ZeroConfig) {ℓ : ℝ}
    (hinj : Set.InjOn (frobEig ℓ) (rightZeros Z)) :
    (outerEig Z ℓ).encard = (rightZeros Z).encard :=
  hinj.encard_image

/-- **Off resonance one tower carries the Hodge defect.** -/
theorem deepSparse_tower_law_of_injOn (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) {ℓ : ℝ} (hℓ : 0 < ℓ) (hinj : Set.InjOn (frobEig ℓ) (rightZeros Z)) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
      (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
        (n : ℕ∞) ≤ (rightZeros Z).encard := by
  obtain ⟨g, hg, hgc, hlaw⟩ := deepSparse_exists_test_tower_law Z hZ hsp hℓ
  exact ⟨g, hg, hgc, fun n => (hlaw n).trans (by rw [encard_outerEig_eq_of_injOn Z hinj])⟩

/-- **The Hodge defect lives on one tower at all but countably many scales.** -/
theorem deepSparse_tower_law_off_resonance (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) :
    (resonantScales Z).Countable ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ∉ resonantScales Z →
      ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
        (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
          (n : ℕ∞) ≤ (rightZeros Z).encard :=
  ⟨countable_resonantScales Z, fun ℓ hℓ hres => deepSparse_tower_law_of_injOn Z hZ hsp hℓ (by
    by_contra h
    exact hres ⟨hℓ, h⟩)⟩

/-! ### Primes -/

/-- **An infinite class at one prime is separated at every other.** With infinitely many right
zeros, at most one prime has finitely many outer eigenvalues. -/
theorem subsingleton_primes_outerEig_finite (Z : ZeroConfig) (hR : (rightZeros Z).Infinite) :
    {p : ℕ | p.Prime ∧ (outerEig Z (Real.log p)).Finite}.Subsingleton := by
  rintro p ⟨hp, hpf⟩ q ⟨hq, hqf⟩
  by_contra hpq
  -- some eigenvalue class at `p` is infinite
  obtain ⟨b, -, hb⟩ : ∃ b ∈ outerEig Z (Real.log p),
      {ρ ∈ rightZeros Z | frobEig (Real.log p) ρ = b}.Infinite := by
    by_contra h
    push Not at h
    apply hR
    refine (hpf.biUnion fun b hb => h b hb).subset fun ρ hρ => ?_
    exact Set.mem_biUnion ⟨ρ, hρ, rfl⟩ ⟨hρ, rfl⟩
  -- at `q` its members have distinct eigenvalues
  have hinj : Set.InjOn (frobEig (Real.log q))
      {ρ ∈ rightZeros Z | frobEig (Real.log p) ρ = b} := by
    intro ρ hρ ρ' hρ' he
    by_contra hne
    exact hpq (subsingleton_resonantPrimes hne ⟨hp, hρ.2.trans hρ'.2.symm⟩ ⟨hq, he⟩)
  exact Set.Infinite.image hinj hb (hqf.subset (Set.image_mono fun ρ hρ => hρ.1))

/-- **Primes are almost never resonant.** At all but finitely many primes there are as many outer
eigenvalues as right zeros. -/
theorem finite_primes_encard_outerEig_ne (Z : ZeroConfig) :
    {p : ℕ | p.Prime ∧ (outerEig Z (Real.log p)).encard ≠ (rightZeros Z).encard}.Finite := by
  rcases (rightZeros Z).finite_or_infinite with hR | hR
  · refine (finite_resonantPrimes Z hR).subset ?_
    rintro p ⟨hp, hne⟩
    exact ⟨hp, fun hinj => hne (encard_outerEig_eq_of_injOn Z hinj)⟩
  · refine (subsingleton_primes_outerEig_finite Z hR).finite.subset ?_
    rintro p ⟨hp, hne⟩
    refine ⟨hp, ?_⟩
    by_contra hinf
    apply hne
    rw [Set.encard_eq_top_iff.mpr hinf, Set.encard_eq_top_iff.mpr hR]

/-- **One tower of `ζ` carries the Hodge defect at almost every prime.** At all primes outside a
finite set one test's `p`-tower has `n` negative squares on some window iff `ζ` has at least `n`
zeros right of the critical line. -/
theorem zeta_tower_law_at_almost_every_prime :
    {p : ℕ | p.Prime ∧ (outerEig zetaZeroConfig (Real.log p)).encard ≠
      (rightZeros zetaZeroConfig).encard}.Finite ∧
    ∀ p : ℕ, p.Prime → (outerEig zetaZeroConfig (Real.log p)).encard =
        (rightZeros zetaZeroConfig).encard →
      ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
        (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram zetaZeroConfig g (Real.log p) K)) ↔
          (n : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  refine ⟨finite_primes_encard_outerEig_ne _, fun p hp he => ?_⟩
  obtain ⟨g, hg, hgc, hlaw⟩ := zeta_exists_test_onePrime_tower_law hp
  exact ⟨g, hg, hgc, fun n => (hlaw n).trans (by rw [he])⟩

/-! ### Curves -/

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- **Curves resonate at their arithmetic scales.** For a datum with an eigenvalue off the unit
circle every scale `ℓ` with `ℓ/log q` rational is resonant: finitely many eigenvalues fold
infinitely many right zeros. -/
theorem mem_resonantScales_of_rat (hU : D.outerSpectrum.Nonempty) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hrat : ¬ Irrational (ℓ / Real.log D.q)) : ℓ ∈ resonantScales (D.curveConfig hD) :=
  ⟨hℓ, fun hinj => (D.curveConfig_rightZeros_infinite_iff hD).mpr hU
    (Set.Finite.of_finite_image (D.outerEig_curveConfig_finite hD hℓ hrat) hinj)⟩

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
