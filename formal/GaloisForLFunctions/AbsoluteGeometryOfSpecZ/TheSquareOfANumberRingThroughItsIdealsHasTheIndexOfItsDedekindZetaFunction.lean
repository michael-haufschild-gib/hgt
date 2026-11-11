import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIdealsOfANumberRingPairAsDegreePointsWithTheZerosOfItsHeckeFunctions
import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterRemovesTheModulusEulerFactors

/-!
# The square of a number ring through its ideals has the index of its Dedekind zeta function

Let `K` be any number field; nothing is assumed on `K` over `ℚ`. The ideals of its ring of
integers, counted by their norms, are the degree points of its square. A character of the ideal
class group is a ray class character of the unit modulus, and it is primitive
(`heckeFiniteConductor_trivialModulus`); the trivial one has the Dedekind zeta function as its
`L`-series.

* **The contacts** (`idealContact`, `heckeMangoldt_trivialModulus_one`). The norm `n` carries
  the contact order `Σ_{N𝔭^k = n} log N𝔭`, over the powers of the prime ideals of norm `n`.
* **The pairing** (`ringForm`, `tendsto_ringForm_add_idealContact`,
  `tendsto_ringForm_add_classContact`). `d` times the jets of the integers, minus the jets
  `1/(m + n)` once for each complex place, the counterterm with the discriminant, and twice the
  contacts of the ideals tend to `2 d₁ d₂ − Z_K(f)`, `Z_K` the sum over the zeros of the
  Dedekind zeta function. With the contacts twisted by a class character `ψ ≠ 1` there is no
  pole plane and the limit is `−Z_ψ(f)`.
* **The index** (`exists_le_negIndex_dedekindGram_iff`,
  `forall_negIndex_dedekindGram_eq_zero_iff`). Weil's form of the ring has `n` negative squares
  on some family of `n` tests iff the completed Dedekind zeta function has at least `n` distinct
  zeros to the right of the critical line; the inequality of Castelnuovo and Severi holds on the
  square of the ring iff all its zeros are on the line.
-/

noncomputable section

open Finset Filter Topology MeasureTheory NumberField
open Zeta23
open scoped Classical Real

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions ArtinMertens HTGeometry

variable (K : Type*) [Field K] [NumberField K]

/-! ### Class characters are primitive -/

/-- Every ray class character of the unit modulus is primitive. -/
theorem heckeFiniteConductor_trivialModulus (ψ : HeckeCharacter (trivialModulus K)) :
    heckeFiniteConductor (trivialModulus K) ψ = (trivialModulus K).fin := by
  have h := modulus_le_heckeFiniteConductor (trivialModulus K) ψ
  have htop : (trivialModulus K).fin = ⊤ := Ideal.one_eq_top
  rw [htop] at h ⊢
  exact top_le_iff.mp h

/-- The zeros of the `L`-function of a class character, with multiplicities. -/
def classZeros (ψ : HeckeCharacter (trivialModulus K)) : ZeroConfig :=
  heckeZeros (trivialModulus K) ψ (heckeFiniteConductor_trivialModulus K ψ)

/-- The zeros of the Dedekind zeta function of `K` in the critical strip, with
multiplicities. -/
def dedekindZeros : ZeroConfig := classZeros K 1

theorem temperedConfig_classZeros (ψ : HeckeCharacter (trivialModulus K)) :
    SquareRootThreshold.TemperedConfig (classZeros K ψ) :=
  temperedConfig_heckeZeros _ ψ _

/-! ### The data of the unit modulus -/

/-- A class character has no parity at a real place. -/
theorem heckeCoordinateParity_trivialModulus (ψ : HeckeCharacter (trivialModulus K))
    (v : {v : InfinitePlace K // v.IsReal}) :
    heckeCoordinateParity (trivialModulus K) ψ (Sum.inl v) = false := by
  rw [heckeCoordinateParity]
  exact dif_neg (Set.notMem_empty _)

/-- The factors `Γ_ℝ(s + 1)` of a class character are those of the complex places. -/
theorem heckeConjugatePlaces_trivialModulus (ψ : HeckeCharacter (trivialModulus K)) :
    heckeConjugatePlaces (trivialModulus K) ψ = InfinitePlace.nrComplexPlaces K := by
  rw [heckeConjugatePlaces]
  simp only [heckeCoordinateParity_trivialModulus, Bool.toNat_false, Finset.sum_const_zero,
    zero_add]

/-- The conductor scale of the unit modulus is the absolute discriminant. -/
theorem heckeCompletionNorm_trivialModulus :
    (heckeCompletionNorm (trivialModulus K) : ℝ) = |(NumberField.discr K : ℝ)| := by
  have h1 : Ideal.absNorm (trivialModulus K).fin = 1 := by
    show Ideal.absNorm (1 : Ideal (𝓞 K)) = 1
    rw [Ideal.one_eq_top, Ideal.absNorm_top]
  rw [heckeCompletionNorm, h1, mul_one, Nat.cast_natAbs, Int.cast_abs]

/-- The contact order of the norm `n` on the square of the ring: `Σ_{N𝔭^k = n} log N𝔭`. -/
def idealContact (n : ℕ) : ℝ :=
  ∑ pk ∈ (primePowersLe K n).filter (fun pk => Ideal.absNorm pk.1 ^ pk.2 = n),
    Real.log (Ideal.absNorm pk.1)

/-- The contacts of the trivial character are the contact orders of the norms. -/
theorem heckeMangoldt_trivialModulus_one (n : ℕ) :
    heckeMangoldt (trivialModulus K) 1 n = ((idealContact K n : ℝ) : ℂ) := by
  rw [heckeMangoldt, idealContact, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun pk hpk => ?_
  obtain ⟨P, k⟩ := pk
  obtain ⟨h1, -⟩ := Finset.mem_filter.mp hpk
  obtain ⟨-, hP0, -, -⟩ := mem_primePowersLe.mp h1
  rw [heckeValue_trivialModulus_one hP0, one_pow, one_mul]

theorem heckePole_trivialModulus_one : heckePole (trivialModulus K) 1 = 1 := by
  rw [heckePole, if_pos rfl]

/-! ### The pairing of the ideals -/

variable {f : ℝ → ℝ}

/-- The pairing of the ideals of the ring of integers of `K`, counted by their norms, without
the contacts: `d` times the jets and the counterterm of the integers, minus the jets `1/(m + n)`
of the complex places, minus `log |d_K|` times the mass. -/
def ringForm (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  (placeDegree K : ℝ) * degreeForm f L N -
    (InfinitePlace.nrComplexPlaces K : ℝ) * conjugateJet f L N -
    Real.log |(NumberField.discr K : ℝ)| *
      ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n

theorem heckeForm_trivialModulus (ψ : HeckeCharacter (trivialModulus K)) (f : ℝ → ℝ)
    (L N : ℕ) : heckeForm (trivialModulus K) ψ f L N = ringForm K f L N := by
  rw [heckeForm, ringForm, heckeConjugatePlaces_trivialModulus, heckeCompletionNorm_trivialModulus]

/-- **The pairing of the ideals twisted by a class character.** Jets, counterterm and twice the
contacts `Re Λ_ψ` tend to the pole plane, present for the trivial character alone, minus the sum
over the zeros of `L(s, ψ)`. -/
theorem tendsto_ringForm_add_classContact (ψ : HeckeCharacter (trivialModulus K))
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K₀ : ℕ} (hK : 1 ≤ K₀)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K₀ ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => ringForm K f (3 * K₀) N +
        2 * weightedContact (fun n => (heckeMangoldt (trivialModulus K) ψ n).re) f (3 * K₀) N)
      atTop
      (𝓝 ((heckePole (trivialModulus K) ψ).re *
          (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))) -
        heckeZeroSum (trivialModulus K) ψ (heckeFiniteConductor_trivialModulus K ψ) f)) := by
  have h := tendsto_heckeForm_add_idealContact (trivialModulus K) ψ
    (heckeFiniteConductor_trivialModulus K ψ) hf hfc hK hsupp
  refine h.congr fun N => ?_
  rw [heckeForm_trivialModulus]

/-- The sum over the zeros of the Dedekind zeta function of a packet. -/
def dedekindZeroSum (f : ℝ → ℝ) : ℝ :=
  heckeZeroSum (trivialModulus K) 1 (heckeFiniteConductor_trivialModulus K 1) f

/-- **The pairing of the square of a number ring through its ideals.** Jets, counterterm and
twice the contacts of the ideals tend to twice the product of the degrees minus the sum over the
zeros of the Dedekind zeta function. -/
theorem tendsto_ringForm_add_idealContact (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {K₀ : ℕ} (hK : 1 ≤ K₀) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K₀ ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => ringForm K f (3 * K₀) N +
        2 * weightedContact (idealContact K) f (3 * K₀) N) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        dedekindZeroSum K f)) := by
  have h := tendsto_ringForm_add_classContact K 1 hf hfc hK hsupp
  have hw : (fun n => (heckeMangoldt (trivialModulus K) 1 n).re) = idealContact K :=
    funext fun n => by rw [heckeMangoldt_trivialModulus_one, Complex.ofReal_re]
  rw [hw, heckePole_trivialModulus_one, Complex.one_re, one_mul] at h
  exact h

/-! ### The index -/

/-- **The Hodge index of the square of a number ring.** Weil's form of the ring has `n` negative
squares on some family of `n` tests iff the completed Dedekind zeta function has at least `n`
distinct zeros to the right of the critical line. -/
theorem exists_le_negIndex_dedekindGram_iff (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram (dedekindZeros K) f)) ↔
      (n : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros (dedekindZeros K)).encard :=
  exists_le_negIndex_heckeGram_iff _ 1 (heckeFiniteConductor_trivialModulus K 1) n

/-- **Castelnuovo and Severi on the square of a number ring.** Weil's form of the ring has no
negative square on any family of tests iff every zero of the completed Dedekind zeta function is
on the critical line. -/
theorem forall_negIndex_dedekindGram_eq_zero_iff :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
        (∀ i, HasCompactSupport (f i)) →
        hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram (dedekindZeros K) f) = 0) ↔
      ∀ ρ : ℂ, heckeXi (trivialModulus K) 1 ρ = 0 → ρ.re = 1 / 2 :=
  forall_negIndex_heckeGram_eq_zero_iff _ 1 (heckeFiniteConductor_trivialModulus K 1)

/-- The completed Dedekind zeta function right of `1`: the two poles cleared, the discriminant,
the Gamma factors of the places, and the Dedekind zeta function. -/
theorem heckeXi_trivialModulus_one {s : ℂ} (hs : 1 < s.re) :
    heckeXi (trivialModulus K) 1 s =
      s * (s - 1) * (heckeCompletionFactor (trivialModulus K) s *
        heckeGammaFactor (trivialModulus K) 1 s * dedekindZeta K s) := by
  rw [heckeXi_eq _ 1 hs, heckePoleFactor_of_eq_one rfl, heckeL_trivialModulus_one]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
