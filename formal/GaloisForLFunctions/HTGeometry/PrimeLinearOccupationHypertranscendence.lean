import GaloisForLFunctions.HTGeometry.PrimeNomePeriod
import GaloisForLFunctions.HTGeometry.PrimeOccupationPolarizedGammaPhaseSurvival
import GaloisForLFunctions.HTGeometry.ExponentialForwardSubstitution

/-!
# Finite prime occupation products at linear temperature

For a finite prime set `S` the two opposite occupation faces

`A_S(t) = ∏_{n ∈ M_S} (1 - t/n)`,  `B_S(t) = ∏_{n ∈ M_S} (1 + t/n)`

are the genus-zero canonical products over the `S`-smooth monoid.  They are entire, and as soon as
`S` has two elements they satisfy no algebraic differential equation.

The nomes of `A_S` are the reciprocal primes, which are the elliptic nomes of the periods
`i·log p/(2π)`; those periods are integrally independent, so the period-rank law makes the backward
all-order multiple elliptic Gamma product hypertranscendental in its *additive* variable.  That
product is `A_S` read in the multiplicative coordinate `exp (2πi z)`, so hypertranscendence descends
to `A_S` itself.  Reflection of the argument transfers the conclusion to `B_S`.

* `GaloisForLFunctions.primeOccupationFaceA`, `GaloisForLFunctions.primeOccupationFaceB`;
* `GaloisForLFunctions.multipleEllipticGammaBackwardProduct_eq_infiniteMultipleEllipticGamma`;
* `GaloisForLFunctions.hypertranscendental_primeOccupationFaceA`,
  `GaloisForLFunctions.hypertranscendental_primeOccupationFaceB`.
-/

open Complex Set
open scoped BigOperators

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-! ### The multiplicative coordinate -/

/-- **The backward all-order product is the genus-zero occupation product in the multiplicative
coordinate.**  Unique reindexing of the occupation lattice by finitely supported exponent vectors
identifies the two products factor by factor. -/
theorem multipleEllipticGammaBackwardProduct_eq_infiniteMultipleEllipticGamma
    {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaBackwardProduct τ z =
      HTGeometry.infiniteMultipleEllipticGamma 0 (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) := by
  classical
  set p : ι → ℂ := fun i => ellipticNome (τ i) with hp
  set x : ℂ := multipleEllipticGammaCoordinate z with hx
  have hL : multipleEllipticGammaBackwardProduct τ z
      = ∏' ν : ι →₀ ℕ, (1 - (∏ i, p i ^ ν i) * x) := by
    rw [multipleEllipticGammaBackwardProduct,
      ← (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)).tprod_eq
        (fun n : ι → ℕ => multipleEllipticGammaBackwardFactor τ n z)]
    exact tprod_congr fun ν => rfl
  have hR : HTGeometry.infiniteMultipleEllipticGamma 0 p x
      = ∏' ν : ι →₀ ℕ, (1 - x * (∏ i, p i ^ ν i)) := by
    rw [HTGeometry.infiniteMultipleEllipticGamma, HTGeometry.canonicalWeightProduct]
    refine tprod_congr fun ν => ?_
    rw [primaryFactor_zero_genus]
    congr 2
    exact Finsupp.prod_fintype ν (fun i n => p i ^ n) (fun i => pow_zero _)
  rw [hL, hR]
  exact tprod_congr fun ν => by ring

/-! ### The two occupation faces -/

/-- The forward occupation face of a finite prime source. -/
def primeOccupationFaceA (S : Finset Nat.Primes) (t : ℂ) : ℂ :=
  HTGeometry.infiniteMultipleEllipticGamma 0 (fun p : S => primeLinearNome p) t

/-- The reflected occupation face of a finite prime source. -/
def primeOccupationFaceB (S : Finset Nat.Primes) (t : ℂ) : ℂ :=
  primeOccupationFaceA S (-t)

theorem primeOccupationFaceA_eq_tprod (S : Finset Nat.Primes) (t : ℂ) :
    primeOccupationFaceA S t
      = ∏' ν : S →₀ ℕ, (1 - t * HTGeometry.nomeMonomial (fun p : S => primeLinearNome p) ν) := by
  rw [primeOccupationFaceA, HTGeometry.infiniteMultipleEllipticGamma,
    HTGeometry.canonicalWeightProduct]
  exact tprod_congr fun ν => primaryFactor_zero_genus _

theorem primeOccupationFaceB_eq_tprod (S : Finset Nat.Primes) (t : ℂ) :
    primeOccupationFaceB S t
      = ∏' ν : S →₀ ℕ, (1 + t * HTGeometry.nomeMonomial (fun p : S => primeLinearNome p) ν) := by
  rw [primeOccupationFaceB, primeOccupationFaceA_eq_tprod]
  exact tprod_congr fun ν => by ring

/-- **Both occupation faces are entire.** -/
theorem analyticOnNhd_primeOccupationFaceA (S : Finset Nat.Primes) :
    AnalyticOnNhd ℂ (primeOccupationFaceA S) Set.univ :=
  HTGeometry.infiniteMultipleEllipticGamma_analytic 0 (fun p : S => primeLinearNome p)
    (fun p => primeLinearNome_ne_zero p) (fun p => norm_primeLinearNome_lt_one p)
    Summable.of_finite

theorem differentiable_primeOccupationFaceA (S : Finset Nat.Primes) :
    Differentiable ℂ (primeOccupationFaceA S) :=
  (Complex.analyticOnNhd_univ_iff_differentiable).1 (analyticOnNhd_primeOccupationFaceA S)

theorem contDiff_primeOccupationFaceA (S : Finset Nat.Primes) :
    ContDiff ℂ (⊤ : ℕ∞) (primeOccupationFaceA S) :=
  contDiffOn_univ.1 ((analyticOnNhd_primeOccupationFaceA S).contDiffOn uniqueDiffOn_univ)

theorem differentiable_primeOccupationFaceB (S : Finset Nat.Primes) :
    Differentiable ℂ (primeOccupationFaceB S) :=
  (differentiable_primeOccupationFaceA S).comp differentiable_neg

/-! ### Hypertranscendence -/

theorem twoPiI_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
  exact_mod_cast Real.pi_ne_zero

/-- The backward multiple elliptic Gamma product at the reciprocal-prime periods is the forward
occupation face read in the multiplicative coordinate. -/
theorem multipleEllipticGammaBackwardProduct_primeNomePeriod (S : Finset Nat.Primes) :
    multipleEllipticGammaBackwardProduct
        (HTGeometry.primeNomePeriod (fun p : S => (p : Nat.Primes)))
      = fun z => primeOccupationFaceA S (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) := by
  classical
  funext z
  have hnome :
      (fun i : S => ellipticNome (HTGeometry.primeNomePeriod (fun p : S => (p : Nat.Primes)) i))
        = fun p : S => primeLinearNome p := by
    funext i
    rw [HTGeometry.ellipticNome_primeNomePeriod]
    rfl
  rw [multipleEllipticGammaBackwardProduct_eq_infiniteMultipleEllipticGamma, hnome]
  rfl

/-- **Every finite prime source with at least two primes has a hypertranscendental forward
occupation face.** -/
theorem hypertranscendental_primeOccupationFaceA (S : Finset Nat.Primes) (hS : 2 ≤ S.card) :
    Hypertranscendental (primeOccupationFaceA S) := by
  classical
  set q : S → Nat.Primes := fun p => (p : Nat.Primes) with hq
  set τ : S → ℂ := HTGeometry.primeNomePeriod q with hτ
  have hqinj : Function.Injective q := Subtype.val_injective
  have hcard : 2 ≤ Fintype.card S := by simpa using hS
  have hτim : ∀ i, 0 < (τ i).im := HTGeometry.primeNomePeriod_im_pos q
  have hminor : MultipleEllipticGammaHasRankThreeMinor τ :=
    multipleEllipticGammaHasRankThreeMinor_of_periodsIntegrallyIndependent τ
      (HTGeometry.periodsIntegrallyIndependent_primeNomePeriod hqinj) hcard
  have hBHT : Hypertranscendental (multipleEllipticGammaBackwardProduct τ) :=
    hypertranscendental_multipleEllipticGammaBackwardProduct_of_rankThreeMinor τ hτim hminor
  rw [hτ, hq, multipleEllipticGammaBackwardProduct_primeNomePeriod S] at hBHT
  exact HTGeometry.hypertranscendental_of_comp_exp (contDiff_primeOccupationFaceA S)
    twoPiI_ne_zero hBHT

/-- **The reflected occupation face is hypertranscendental as well.** -/
theorem hypertranscendental_primeOccupationFaceB (S : Finset Nat.Primes) (hS : 2 ≤ S.card) :
    Hypertranscendental (primeOccupationFaceB S) := by
  intro hDA
  have hback := hDA.comp_const_mul_uncond (by norm_num : (-1 : ℂ) ≠ 0)
  have hrw : (fun z : ℂ => primeOccupationFaceB S (-1 * z)) = primeOccupationFaceA S := by
    funext z
    rw [primeOccupationFaceB]
    congr 1
    ring
  rw [hrw] at hback
  exact hypertranscendental_primeOccupationFaceA S hS hback

end

end GaloisForLFunctions
