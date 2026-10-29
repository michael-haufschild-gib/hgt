import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimeResidueWindowsControlEveryGramPacket
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheArithmeticCurvatureHasAnExactGramCompletion

/-!
# Actual prime-prefix forms dominate the cyclotomic Gram

Reduced-residue powers enumerate the primitive roots exactly. Consequently
the unit mean of a prefix packet is its complete cyclotomic Gram energy
divided by the totient. Positivity of the actual prime masses then gives one
lower operator bound for every packet, with arbitrary moving coefficients
and prefix lengths. The conductor and multiplicative window remain fixed.
-/

noncomputable section

open Finset Polynomial Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory

/-- The canonical root used to evaluate actual prime phases. -/
def arithmeticConductorRoot (q : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q)

theorem arithmeticConductorRoot_isPrimitive {q : ℕ} (hq : 0 < q) :
    IsPrimitiveRoot (arithmeticConductorRoot q) q :=
  Complex.isPrimitiveRoot_exp q hq.ne'

/-- Every function of the primitive phase has the same sum over units
as over primitive roots, with no averaging or asymptotic error. -/
theorem sum_units_primitiveRoot_values {q : ℕ} [NeZero q] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ q) (F : ℂ → ℝ) :
    (∑ u : (ZMod q)ˣ, F (ζ ^ (u : ZMod q).val)) =
      ∑ ξ ∈ primitiveRoots q ℂ, F ξ := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  refine sum_bij (fun u _ => ζ ^ (u : ZMod q).val) ?_ ?_ ?_ ?_
  · intro u _
    apply (mem_primitiveRoots hq).mpr
    apply hζ.pow_of_coprime
    apply (ZMod.isUnit_iff_coprime (u : ZMod q).val q).mp
    rw [ZMod.natCast_zmod_val]
    exact u.isUnit
  · intro u _ v _ huv
    have hv := hζ.pow_inj (ZMod.val_lt (u : ZMod q)) (ZMod.val_lt (v : ZMod q)) huv
    apply Units.ext
    exact (ZMod.natCast_zmod_val (u : ZMod q)).symm.trans
      ((congrArg (fun n : ℕ => (n : ZMod q)) hv).trans (ZMod.natCast_zmod_val (v : ZMod q)))
  · intro ξ hξ
    have hξp := (mem_primitiveRoots hq).mp hξ
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξp.pow_eq_one
    have hc : i.Coprime q := (hζ.pow_iff_coprime hq i).mp hξp
    have hu : IsUnit (i : ZMod q) := (ZMod.isUnit_iff_coprime i q).mpr hc
    refine ⟨hu.unit, mem_univ _, ?_⟩
    rw [IsUnit.unit_spec, ZMod.val_natCast_of_lt hi]
  · intro u _
    rfl

/-- The squared prefix packet as a literal function of the prime residue. -/
def arithmeticPrefixResidueEnergy {ι : Type*} (q : ℕ) (s : Finset ι)
    (a : ι → ℝ) (k : ι → ℕ) (r : ZMod q) : ℝ :=
  Complex.normSq (∑ i ∈ s,
    a i • primitivePrefixValue (arithmeticConductorRoot q ^ r.val) (k i))

/-- The actual von Mangoldt window of the primitive-phase packet. -/
def actualPrimePrefixGram {ι : Type*} (q : ℕ) (s : Finset ι)
    (a : ι → ℝ) (k : ι → ℕ) (A B N : ℕ) : ℝ :=
  ∑ n ∈ Ioc (A * N) (B * N),
    (ArithmeticFunction.vonMangoldt n : ℝ) / n *
      Complex.normSq (∑ i ∈ s,
        a i • primitivePrefixValue (arithmeticConductorRoot q ^ n) (k i))

theorem actualPrimePrefixGram_eq_residue {ι : Type*} {q : ℕ} [NeZero q]
    (s : Finset ι) (a : ι → ℝ) (k : ι → ℕ) (A B N : ℕ) :
    actualPrimePrefixGram q s a k A B N =
      residuePrimeWindow q (arithmeticPrefixResidueEnergy q s a k) A B N := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hp (n : ℕ) : arithmeticConductorRoot q ^ (n % q) = arithmeticConductorRoot q ^ n := by
    conv_rhs => rw [← Nat.mod_add_div n q]
    rw [pow_add, pow_mul, (arithmeticConductorRoot_isPrimitive hq).pow_eq_one,
      one_pow, mul_one]
  unfold actualPrimePrefixGram residuePrimeWindow arithmeticPrefixResidueEnergy
  refine sum_congr rfl fun n _ => ?_
  rw [ZMod.val_natCast, hp]
  ring

/-- The unit model is the full cyclotomic Gram, including all cross terms. -/
theorem primeClassKappa_arithmeticPrefixResidueEnergy {ι : Type*} {q : ℕ} [NeZero q]
    (s : Finset ι) (a : ι → ℝ) (k : ι → ℕ) :
    primeClassKappa q (arithmeticPrefixResidueEnergy q s a k) =
      (∑ i ∈ s, ∑ j ∈ s, a i * a j * primitivePrefixGram q (k i) (k j)) /
        (q.totient : ℝ) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  unfold primeClassKappa arithmeticPrefixResidueEnergy
  rw [sum_units_primitiveRoot_values (arithmeticConductorRoot_isPrimitive hq)
      (fun ζ => Complex.normSq (∑ i ∈ s, a i • primitivePrefixValue ζ (k i))),
    primitivePrefixGram_quadratic_eq s hq a k]
  simp only [Complex.sq_norm]

/-- Actual prime phases retain the entire cyclotomic Gram with one common
lower bound for all coefficients and all prefix lengths. -/
theorem eventually_actualPrimePrefixGram_dominates {ι : Type*} {q : ℕ} (hq : 0 < q)
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (s : Finset ι) (a : ι → ℝ) (k : ι → ℕ),
      ((Real.log B - Real.log A - ε) / (q.totient : ℝ)) *
          (∑ i ∈ s, ∑ j ∈ s, a i * a j * primitivePrefixGram q (k i) (k j)) ≤
        actualPrimePrefixGram q s a k A B N := by
  haveI : NeZero q := ⟨hq.ne'⟩
  filter_upwards [eventually_residuePrimeWindow_dominates_unitMean (q := q) hA hAB hε]
    with N hN
  intro s a k
  have h := hN (arithmeticPrefixResidueEnergy q s a k) (fun _ => Complex.normSq_nonneg _)
  rw [primeClassKappa_arithmeticPrefixResidueEnergy, ← actualPrimePrefixGram_eq_residue] at h
  convert h using 1
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primeClassKappa_arithmeticPrefixResidueEnergy
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_actualPrimePrefixGram_dominates
