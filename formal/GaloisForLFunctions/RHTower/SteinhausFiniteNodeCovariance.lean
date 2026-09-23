import GaloisForLFunctions.RHTower.SmoothAFEZetaRightReflectedPrimalEnergyEvent
import GaloisForLFunctions.HTGeometry.ComplexGramPlucker

/-!
# Finite-node covariance of largest-prime Steinhaus channels

For finitely many coefficient systems, every complex linear combination of their
largest-prime channels is the largest-prime channel of the corresponding linear
combination of coefficients.  Complex Steinhaus Parseval therefore identifies:

* the covariance Rayleigh form over the independent large-prime phases, at each
  frozen small-prime configuration; and
* the expectation of that Rayleigh form over the small-prime phases

with explicit sums of squared arithmetic coefficient combinations.  The final
specialization uses the literal reflected-primal approximate-functional-equation
coefficients.  Thus joint nondegeneracy is reduced to one concrete arithmetic
Gram lower bound, rather than inferred from scalar channel energy.
-/

noncomputable section

namespace RHTower

open Complex Finset Nat MeasureTheory
open SteinhausModel
open GaloisForLFunctions.HTGeometry

/-- Complex linear combination of a finite family of arithmetic coefficient systems. -/
def steinhausFiniteNodeCoefficientCombination {J : ℕ}
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (n : ℕ) : ℂ :=
  ∑ j : Fin J, u j * a j n

/-- Complex linear combination of the corresponding largest-prime channels. -/
def steinhausFiniteNodeChannelCombination {J : ℕ}
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ)
    (X p : ℕ) (omega : Omega) : ℂ :=
  ∑ j : Fin J, u j * steinhausLargePrimeChannel (a j) X p omega

/-- Linear combination commutes exactly with largest-prime channel formation. -/
theorem steinhausFiniteNodeChannelCombination_eq_channel {J : ℕ}
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ)
    (X p : ℕ) (omega : Omega) :
    steinhausFiniteNodeChannelCombination a u X p omega =
      steinhausLargePrimeChannel
        (steinhausFiniteNodeCoefficientCombination a u) X p omega := by
  classical
  unfold steinhausFiniteNodeChannelCombination steinhausLargePrimeChannel
    steinhausFiniteNodeCoefficientCombination
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact expected energy of one finite-node channel combination. -/
theorem integral_normSq_steinhausFiniteNodeChannelCombination {J : ℕ}
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (X p : ℕ) :
    (∫ omega,
        ‖steinhausFiniteNodeChannelCombination a u X p omega‖ ^ (2 : ℕ)
          ∂steinhausMeasure) =
      ∑ m ∈ Finset.Icc 1 (X / p),
        ‖steinhausFiniteNodeCoefficientCombination a u (p * m)‖ ^ (2 : ℕ) := by
  simpa only [steinhausFiniteNodeChannelCombination_eq_channel] using
    integral_normSq_steinhausLargePrimeChannel
      (steinhausFiniteNodeCoefficientCombination a u) X p

/-- Arithmetic Gram energy controlling one complex Rayleigh direction across a prime family. -/
def steinhausFiniteNodeArithmeticGramEnergy {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (X : ℕ) : ℝ :=
  ∑ p ∈ P, ∑ m ∈ Finset.Icc 1 (X / p),
    ‖steinhausFiniteNodeCoefficientCombination a u (p * m)‖ ^ (2 : ℕ)

/-- The mean small-prime Rayleigh energy is the explicit arithmetic Gram energy. -/
theorem sum_integral_normSq_steinhausFiniteNodeChannelCombination {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (X : ℕ) :
    (∑ p ∈ P, ∫ omega,
        ‖steinhausFiniteNodeChannelCombination a u X p omega‖ ^ (2 : ℕ)
          ∂steinhausMeasure) =
      steinhausFiniteNodeArithmeticGramEnergy P a u X := by
  unfold steinhausFiniteNodeArithmeticGramEnergy
  exact Finset.sum_congr rfl fun p hp =>
    integral_normSq_steinhausFiniteNodeChannelCombination a u X p

/-- Coordinate set of all prime--cofactor samples entering a finite-node Gram form. -/
abbrev steinhausFiniteNodeFeatureIndex (P : Finset ℕ) (X : ℕ) :=
  ↥(P.sigma fun p => Finset.Icc 1 (X / p))

/-- Product first, then an arbitrary injective finite tie-breaker. -/
noncomputable def steinhausFiniteNodeFeatureIndexOrderKey
    (P : Finset ℕ) (X : ℕ) (q : steinhausFiniteNodeFeatureIndex P X) :=
  toLex (q.1.1 * q.1.2, Fintype.equivFin _ q)

theorem steinhausFiniteNodeFeatureIndexOrderKey_injective (P : Finset ℕ) (X : ℕ) :
    Function.Injective (steinhausFiniteNodeFeatureIndexOrderKey P X) := by
  intro q r h
  exact (Fintype.equivFin _).injective (congrArg (fun z => (ofLex z).2) h)

noncomputable instance steinhausFiniteNodeFeatureIndexLinearOrder
    (P : Finset ℕ) (X : ℕ) : LinearOrder (steinhausFiniteNodeFeatureIndex P X) :=
  LinearOrder.lift' (steinhausFiniteNodeFeatureIndexOrderKey P X)
    (steinhausFiniteNodeFeatureIndexOrderKey_injective P X)

noncomputable instance (priority := 10000) steinhausFiniteNodeFeatureIndexLE
    (P : Finset ℕ) (X : ℕ) : LE (steinhausFiniteNodeFeatureIndex P X) :=
  (steinhausFiniteNodeFeatureIndexLinearOrder P X).toLE

noncomputable instance (priority := 10000) steinhausFiniteNodeFeatureIndexLT
    (P : Finset ℕ) (X : ℕ) : LT (steinhausFiniteNodeFeatureIndex P X) :=
  (steinhausFiniteNodeFeatureIndexLinearOrder P X).toLT

theorem steinhausFiniteNodeFeatureIndex_lt_iff_key_lt
    {P : Finset ℕ} {X : ℕ} {q r : steinhausFiniteNodeFeatureIndex P X} :
    q < r ↔ steinhausFiniteNodeFeatureIndexOrderKey P X q <
      steinhausFiniteNodeFeatureIndexOrderKey P X r := by
  change (LinearOrder.lift' (steinhausFiniteNodeFeatureIndexOrderKey P X)
    (steinhausFiniteNodeFeatureIndexOrderKey_injective P X)).lt q r ↔ _
  rfl

/-- Product-first ordering: a smaller represented integer gives a smaller prime--cofactor feature
index, independently of tie-breaking by the prime and cofactor. -/
theorem steinhausFiniteNodeFeatureIndex_lt_of_product_lt
    {P : Finset ℕ} {X : ℕ} {q r : steinhausFiniteNodeFeatureIndex P X}
    (h : q.1.1 * q.1.2 < r.1.1 * r.1.2) : q < r := by
  apply steinhausFiniteNodeFeatureIndex_lt_iff_key_lt.mpr
  unfold steinhausFiniteNodeFeatureIndexOrderKey
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- Finite coefficient feature rows over the prime--cofactor sample set. -/
def steinhausFiniteNodeFeature {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (X : ℕ) :
    Fin J → steinhausFiniteNodeFeatureIndex P X → ℂ :=
  fun j q => a j (q.1.1 * q.1.2)

/-- Hermitian Gram matrix of the finite-node arithmetic coefficient rows. -/
def steinhausFiniteNodeArithmeticGram {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (X : ℕ) :
    Matrix (Fin J) (Fin J) ℂ :=
  hermFeatureGram (steinhausFiniteNodeFeature P a X)

/-- The explicit nested arithmetic energy is the coordinate-space squared norm of the
corresponding finite-node coefficient combination. -/
theorem steinhausFiniteNodeArithmeticGramEnergy_eq_feature_sum {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (X : ℕ) :
    steinhausFiniteNodeArithmeticGramEnergy P a u X =
      ∑ q : steinhausFiniteNodeFeatureIndex P X,
        ‖∑ j : Fin J, u j * steinhausFiniteNodeFeature P a X j q‖ ^ (2 : ℕ) := by
  classical
  unfold steinhausFiniteNodeArithmeticGramEnergy
    steinhausFiniteNodeCoefficientCombination steinhausFiniteNodeFeature
  calc
    (∑ p ∈ P, ∑ m ∈ Finset.Icc 1 (X / p),
        ‖∑ j : Fin J, u j * a j (p * m)‖ ^ (2 : ℕ)) =
        ∑ q ∈ P.sigma (fun p => Finset.Icc 1 (X / p)),
          ‖∑ j : Fin J, u j * a j (q.1 * q.2)‖ ^ (2 : ℕ) :=
      Finset.sum_sigma' _ _ _
    _ = ∑ q : ↥(P.sigma fun p => Finset.Icc 1 (X / p)),
          ‖∑ j : Fin J, u j * a j (q.1.1 * q.1.2)‖ ^ (2 : ℕ) := by
      rw [Finset.sum_subtype _ (fun _ => Iff.rfl)]

/-- Complex Cauchy--Binet identifies the finite-node arithmetic Gram determinant with
the sum of squared maximal coefficient minors. -/
theorem det_steinhausFiniteNodeArithmeticGram_eq_pluckerNormSq {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (X : ℕ) :
    (steinhausFiniteNodeArithmeticGram P a X).det =
      (hermPluckerNormSq (steinhausFiniteNodeFeature P a X) : ℂ) :=
  det_hermFeatureGram_eq_pluckerNormSq (steinhausFiniteNodeFeature P a X)

/-- Any single nonzero maximal terminal coefficient minor gives a quantitative lower bound
for the real arithmetic Gram determinant. -/
theorem norm_sq_steinhausFiniteNodeFeatureMinor_le_gram_det_re {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (X : ℕ)
    (s : Set.powersetCard (steinhausFiniteNodeFeatureIndex P X) J) :
    ‖hermFeatureMinor (steinhausFiniteNodeFeature P a X) s‖ ^ (2 : ℕ) ≤
      (steinhausFiniteNodeArithmeticGram P a X).det.re := by
  rw [det_steinhausFiniteNodeArithmeticGram_eq_pluckerNormSq]
  simp only [Complex.ofReal_re]
  unfold hermPluckerNormSq
  refine Finset.single_le_sum
    (s := Finset.univ)
    (f := fun q : Set.powersetCard (steinhausFiniteNodeFeatureIndex P X) J =>
      ‖hermFeatureMinor (steinhausFiniteNodeFeature P a X) q‖ ^ (2 : ℕ))
    ?_ (Finset.mem_univ s)
  intro q hq
  exact sq_nonneg _

/-- A frozen family of channel coefficients sampled by independent prime phases. -/
def steinhausFiniteNodeLargePrimePacket {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ)
    (M : ℕ) (omegaSmall omegaLarge : Omega) : ℂ :=
  ∑ p ∈ P,
    steinhausFiniteNodeChannelCombination a u M p omegaSmall * X p omegaLarge

/-- **Exact conditional covariance Rayleigh form.**  After freezing the channel
coefficients, integration over independent large-prime phases gives their squared
Gram energy. -/
theorem integral_normSq_steinhausFiniteNodeLargePrimePacket {J : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p ≠ 0)
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ)
    (M : ℕ) (omegaSmall : Omega) :
    (∫ omegaLarge,
        ‖steinhausFiniteNodeLargePrimePacket P a u M omegaSmall omegaLarge‖ ^ (2 : ℕ)
          ∂steinhausMeasure) =
      ∑ p ∈ P,
        ‖steinhausFiniteNodeChannelCombination a u M p omegaSmall‖ ^ (2 : ℕ) := by
  unfold steinhausFiniteNodeLargePrimePacket
  exact integral_normSq_dpoly_complex
    (fun p => steinhausFiniteNodeChannelCombination a u M p omegaSmall) P hP

/-- Literal reflected-primal AFE coefficient family at finitely many right-line nodes. -/
def smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient {J : ℕ}
    (d tau : Fin J → ℝ) (r : ℝ) (N : ℕ) (j : Fin J) (n : ℕ) : ℂ :=
  smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau j) r N n

/-- The mean finite-node covariance form for the literal reflected-primal AFE channels
is exactly the displayed arithmetic Gram sum. -/
theorem sum_integral_normSq_reflectedPrimalFiniteNodeChannelCombination {J : ℕ}
    (P : Finset ℕ) (d tau : Fin J → ℝ) (r : ℝ)
    (N : ℕ) (u : Fin J → ℂ) :
    (∑ p ∈ P, ∫ omega,
        ‖steinhausFiniteNodeChannelCombination
          (smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient d tau r N)
          u N p omega‖ ^ (2 : ℕ) ∂steinhausMeasure) =
      steinhausFiniteNodeArithmeticGramEnergy P
        (smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient d tau r N) u N :=
  sum_integral_normSq_steinhausFiniteNodeChannelCombination P
    (smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient d tau r N) u N

end RHTower

end
