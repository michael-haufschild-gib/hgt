import GaloisForLFunctions.HTGeometry.LBitTemporalDimensionLaw

/-!
# A summable infinite l-bit field with maximal rank in every finite window

This file constructs one coefficient field on every finite support of the countable chain.  Its
nonconstant coefficients are rationally independent, every finite restriction has the largest
possible temporal rank, and the complete infinite coefficient field is absolutely summable.

The construction separates arithmetic independence from spatial size.  Each support receives a
distinct prime logarithm, multiplied by a nonzero rational factor.  The factor contains an
explicit dyadic penalty for support encoding, cardinality, rightmost extent, and pairwise
diameter.  Rational rescaling preserves independence, while the injective encoding supplies one
summable geometric majorant for the entire countable family.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rightmost site of a finite support, with value zero on the empty support. -/
def finiteLBitSupportExtent (S : Finset ℕ) : ℕ :=
  S.sup fun i => i

/-- Largest pairwise lattice distance inside a finite support, with value zero on the empty
support. -/
def finiteLBitSupportDiameter (S : Finset ℕ) : ℕ :=
  S.sup fun i => S.sup fun j => Nat.dist i j

/-- Complexity controlling the coefficient assigned to a finite support.

Besides physical size (`card`, extent, and diameter), it contains Lean's injective countable
encoding.  The latter makes the global absolute-summability estimate immediate without changing
any finite-window rank. -/
def quasiLocalLBitSupportComplexity (S : Finset ℕ) : ℕ :=
  Encodable.encode S + S.card +
    finiteLBitSupportExtent S + finiteLBitSupportDiameter S

/-- Nonzero rational scale attached to a nonempty finite support. -/
noncomputable def quasiLocalLBitRationalScale
    (S : {S : Finset ℕ // S.Nonempty}) : ℚ :=
  1 /
    ((nonemptyFiniteSupportPrimeEmbedding S : ℕ) *
      2 ^ quasiLocalLBitSupportComplexity S.1)

theorem quasiLocalLBitRationalScale_ne_zero
    (S : {S : Finset ℕ // S.Nonempty}) :
    quasiLocalLBitRationalScale S ≠ 0 := by
  apply div_ne_zero one_ne_zero
  norm_cast
  exact mul_ne_zero
    (Nat.Prime.ne_zero
      (nonemptyFiniteSupportPrimeEmbedding S).2)
    (pow_ne_zero _ (by norm_num))

/-- The rational scale as a unit, used to transport linear independence. -/
noncomputable def quasiLocalLBitScaleUnit
    (S : {S : Finset ℕ // S.Nonempty}) : ℚˣ :=
  Units.mk0
    (quasiLocalLBitRationalScale S)
    (quasiLocalLBitRationalScale_ne_zero S)

/-- One exponentially quasi-local coefficient assignment on all finite supports of `ℕ`. -/
noncomputable def quasiLocalInfiniteLBitCoefficient
    (S : Finset ℕ) : ℝ :=
  if hS : S.Nonempty then
    quasiLocalLBitRationalScale ⟨S, hS⟩ •
      primeLogSupport
        (nonemptyFiniteSupportPrimeEmbedding ⟨S, hS⟩)
  else 0

/-- Every nonconstant coefficient of the quasi-local infinite assignment is rationally
independent. -/
theorem quasiLocalInfiniteLBitCoefficient_linearIndependent :
    LinearIndependent ℚ
      (fun S : {S : Finset ℕ // S.Nonempty} =>
        quasiLocalInfiniteLBitCoefficient S.1) := by
  have hprime :
      LinearIndependent ℚ
        (fun S : {S : Finset ℕ // S.Nonempty} =>
          primeLogSupport
            (nonemptyFiniteSupportPrimeEmbedding S)) :=
    primeLogSupport_linearIndependent.comp
      nonemptyFiniteSupportPrimeEmbedding
      nonemptyFiniteSupportPrimeEmbedding.injective
  have hscaled :=
    hprime.units_smul quasiLocalLBitScaleUnit
  have heq :
      (fun S : {S : Finset ℕ // S.Nonempty} =>
        quasiLocalInfiniteLBitCoefficient S.1) =
      (fun S : {S : Finset ℕ // S.Nonempty} =>
        quasiLocalLBitRationalScale S •
          primeLogSupport
            (nonemptyFiniteSupportPrimeEmbedding S)) := by
    funext S
    simp [quasiLocalInfiniteLBitCoefficient, S.2]
  rw [heq]
  change LinearIndependent ℚ
    (fun S : {S : Finset ℕ // S.Nonempty} =>
      (quasiLocalLBitScaleUnit S : ℚ) •
        primeLogSupport
          (nonemptyFiniteSupportPrimeEmbedding S)) at hscaled
  simpa only [quasiLocalLBitScaleUnit, Units.val_mk0] using hscaled

/-- Exact dyadic quasi-local envelope.  The exponent simultaneously penalizes support
cardinality, rightmost extent, pairwise diameter, and an injective support encoding. -/
theorem abs_quasiLocalInfiniteLBitCoefficient_le
    (S : Finset ℕ) :
    |quasiLocalInfiniteLBitCoefficient S| ≤
      ((1 : ℝ) / 2) ^ quasiLocalLBitSupportComplexity S := by
  classical
  by_cases hS : S.Nonempty
  · let p : Nat.Primes :=
      nonemptyFiniteSupportPrimeEmbedding ⟨S, hS⟩
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast p.2.pos
    have hlog :
        primeLogSupport p ≤ (p : ℝ) := by
      exact Real.log_le_self hp0.le
    have hscaleQ :
        (0 : ℚ) <
          quasiLocalLBitRationalScale ⟨S, hS⟩ := by
      change
        (0 : ℚ) <
          1 /
            (((p : ℕ) : ℚ) *
              2 ^ quasiLocalLBitSupportComplexity S)
      exact one_div_pos.mpr
        (mul_pos
          (by exact_mod_cast p.2.pos)
          (pow_pos (by norm_num) _))
    have hscale :
        (0 : ℝ) ≤
          (quasiLocalLBitRationalScale ⟨S, hS⟩ : ℚ) := by
      exact_mod_cast hscaleQ.le
    rw [quasiLocalInfiniteLBitCoefficient, dif_pos hS]
    change
      |quasiLocalLBitRationalScale ⟨S, hS⟩ •
          primeLogSupport p| ≤
        ((1 : ℝ) / 2) ^
          quasiLocalLBitSupportComplexity S
    rw [Rat.smul_def]
    rw [abs_of_nonneg
      (mul_nonneg hscale (primeLogSupport_pos p).le)]
    calc
      (quasiLocalLBitRationalScale ⟨S, hS⟩ : ℝ) *
            primeLogSupport p
          ≤ (quasiLocalLBitRationalScale ⟨S, hS⟩ : ℝ) *
            (p : ℝ) := by
              exact mul_le_mul_of_nonneg_left hlog hscale
      _ = ((1 : ℝ) / 2) ^
            quasiLocalLBitSupportComplexity S := by
              simp [quasiLocalLBitRationalScale, p]
              field_simp
              exact div_self hp0.ne'
  · rw [quasiLocalInfiniteLBitCoefficient, dif_neg hS, abs_zero]
    positivity

/-- The physical part of the envelope: decay is exponential in support cardinality, rightmost
extent, and pairwise diameter, independently of the auxiliary support encoding. -/
theorem abs_quasiLocalInfiniteLBitCoefficient_le_physical
    (S : Finset ℕ) :
    |quasiLocalInfiniteLBitCoefficient S| ≤
      ((1 : ℝ) / 2) ^
        (S.card + finiteLBitSupportExtent S +
          finiteLBitSupportDiameter S) := by
  refine (abs_quasiLocalInfiniteLBitCoefficient_le S).trans ?_
  apply pow_le_pow_of_le_one
  · norm_num
  · norm_num
  · simp only [quasiLocalLBitSupportComplexity]
    omega

/-- The entire countable coefficient field has finite absolute mass. -/
theorem summable_abs_quasiLocalInfiniteLBitCoefficient :
    Summable
      (fun S : Finset ℕ =>
        |quasiLocalInfiniteLBitCoefficient S|) := by
  apply Summable.of_nonneg_of_le
    (fun S => abs_nonneg _)
    (fun S => (abs_quasiLocalInfiniteLBitCoefficient_le S).trans ?_)
    (summable_geometric_two_encode :
      Summable
        (fun S : Finset ℕ =>
          ((1 : ℝ) / 2) ^ Encodable.encode S))
  apply pow_le_pow_of_le_one
  · norm_num
  · norm_num
  · simp only [quasiLocalLBitSupportComplexity]
    omega

/-- Restriction of the single infinite coefficient field along any finite site embedding. -/
noncomputable def quasiLocalInfiniteLBitRestriction
    (I : Type*) [Fintype I] [DecidableEq I]
    (e : I ↪ ℕ) (S : Finset I) : ℝ :=
  quasiLocalInfiniteLBitCoefficient (S.map e)

/-- Every finite restriction along every site embedding retains rational coefficient
independence. -/
theorem quasiLocalInfiniteLBitRestriction_linearIndependent
    (I : Type*) [Fintype I] [DecidableEq I]
    (e : I ↪ ℕ) :
    LinearIndependent ℚ
      (fun S : {S : Finset I // S.Nonempty} =>
        quasiLocalInfiniteLBitRestriction I e S.1) := by
  have hcomp :=
    quasiLocalInfiniteLBitCoefficient_linearIndependent.comp
      (mapNonemptyLBitSupport e)
      (mapNonemptyLBitSupport_injective e)
  have heq :
      (fun S : {S : Finset I // S.Nonempty} =>
        quasiLocalInfiniteLBitRestriction I e S.1) =
      (fun S : {S : Finset I // S.Nonempty} =>
        quasiLocalInfiniteLBitCoefficient
          (mapNonemptyLBitSupport e S).1) := by
    funext S
    rfl
  rw [heq]
  exact hcomp

/-- **Quasi-local infinite maximal-rank law.**  One absolutely summable coefficient assignment on
the countable chain has full temporal rank in every finite window, for every finite site type and
every embedding of that type into the chain. -/
theorem quasiLocalInfiniteLBitRestriction_fullRank
    (I : Type*) [Fintype I] [DecidableEq I]
    (e : I ↪ ℕ) :
    lbitTemporalRank (quasiLocalInfiniteLBitRestriction I e) =
      2 ^ Fintype.card I - 1 :=
  lbitTemporalRank_eq_card _
    (quasiLocalInfiniteLBitRestriction_linearIndependent I e)

end

end GaloisForLFunctions.HTGeometry
