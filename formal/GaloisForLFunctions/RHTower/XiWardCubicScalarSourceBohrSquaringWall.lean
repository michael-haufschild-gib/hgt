import GaloisForLFunctions.RHTower.XiWardCubicKreinOppositeRadialPairIncidence
import GaloisForLFunctions.HTGeometry.BohrTrigMeans

/-!
# Cubic Ward scalar-source Bohr squaring wall

The opposite-radial completed current has the correct signed divisor residues, but multiplying
two scalar Euler traces before ordinate dephasing changes the arithmetic coefficient type.
For every finite packet of distinct primitive cells, exact Bohr averaging removes all unequal
log-frequency pairs and leaves the square of each finite von Mangoldt weight.

The committed primitive cubic collision trace is instead linear in the resolved von Mangoldt
weight: its square root is placed on each of two common-index legs before contraction.  Therefore
a scalar product followed by Bohr dephasing cannot be that source trace.  A coefficient-faithful
continuation must retain the primitive index through a two-variable covariance/divided-difference
carrier and contract only after continuation.
-/

open scoped BigOperators
open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions

/-- Finite scalar Euler trace with the literal logarithmic primitive frequencies. -/
def xiWardCubicScalarEulerTrace {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (t : ℝ) : ℂ :=
  ∑ i : Fin N,
    finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe i)) *
      bohrExp (xiGammaEulerPrimitiveLogFrequency (pe i)) t

/-- Equal-frequency energy left by scalar Bohr dephasing. -/
def xiWardCubicScalarEulerBohrEnergy {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) : ℂ :=
  ∑ q ∈ (Finset.univ : Finset (Fin N)).product Finset.univ with
      xiGammaEulerPrimitiveLogFrequency (pe q.1) =
        xiGammaEulerPrimitiveLogFrequency (pe q.2),
    finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe q.1)) *
      star (finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe q.2)))

/-- Exact scalar dephasing law before primitive-frequency injectivity is used. -/
theorem bohrMean_xiWardCubicScalarEulerTrace_mul_star
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    bohrMean (fun t => xiWardCubicScalarEulerTrace pe t *
      star (xiWardCubicScalarEulerTrace pe t)) =
      xiWardCubicScalarEulerBohrEnergy pe := by
  classical
  unfold xiWardCubicScalarEulerTrace xiWardCubicScalarEulerBohrEnergy
  have hsplit :
      (fun t : ℝ =>
        (∑ i : Fin N,
          finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe i)) *
            bohrExp (xiGammaEulerPrimitiveLogFrequency (pe i)) t) *
        star (∑ i : Fin N,
          finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe i)) *
            bohrExp (xiGammaEulerPrimitiveLogFrequency (pe i)) t)) =
      fun t : ℝ =>
        ∑ q ∈ (Finset.univ : Finset (Fin N)).product Finset.univ,
          (finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe q.1)) *
            (starRingEnd ℂ)
              (finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe q.2)))) *
          bohrChar
            (xiGammaEulerPrimitiveLogFrequency (pe q.2) -
              xiGammaEulerPrimitiveLogFrequency (pe q.1)) t := by
    funext t
    change
      (∑ i : Fin N,
          finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe i)) *
            bohrExp (xiGammaEulerPrimitiveLogFrequency (pe i)) t) *
        (starRingEnd ℂ) (∑ i : Fin N,
          finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe i)) *
            bohrExp (xiGammaEulerPrimitiveLogFrequency (pe i)) t) = _
    rw [map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro q _hq
    rw [map_mul, conj_bohrExp]
    rw [show
      finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe q.1)) *
          bohrExp (xiGammaEulerPrimitiveLogFrequency (pe q.1)) t *
        ((starRingEnd ℂ) (finiteVonMangoldtWeight
            (xiGammaEulerValuationNat (pe q.2))) *
          bohrChar (xiGammaEulerPrimitiveLogFrequency (pe q.2)) t) =
        (finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe q.1)) *
          (starRingEnd ℂ)
            (finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe q.2)))) *
        (bohrExp (xiGammaEulerPrimitiveLogFrequency (pe q.1)) t *
          bohrChar (xiGammaEulerPrimitiveLogFrequency (pe q.2)) t) by ring,
      bohrExp_mul_bohrChar]
  rw [hsplit, bohrMean_sum (F := fun q : Fin N × Fin N => fun t : ℝ =>
      (finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe q.1)) *
        (starRingEnd ℂ)
          (finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe q.2)))) *
      bohrChar
        (xiGammaEulerPrimitiveLogFrequency (pe q.2) -
          xiGammaEulerPrimitiveLogFrequency (pe q.1)) t)
    ((Finset.univ : Finset (Fin N)).product Finset.univ)
    (fun q _ => continuous_const.mul (continuous_bohrChar _))
    (fun q _ => isBohrAlmostPeriodic_const_mul _
      (isBohrAlmostPeriodic_bohrChar _))]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [bohrMean_const_mul _ (continuous_bohrChar _)
    (isBohrAlmostPeriodic_bohrChar _), bohrMean_bohrChar]
  by_cases hfreq : xiGammaEulerPrimitiveLogFrequency (pe q.1) =
      xiGammaEulerPrimitiveLogFrequency (pe q.2)
  · rw [if_pos hfreq, if_pos (sub_eq_zero.mpr hfreq.symm), mul_one]
    rfl
  · rw [if_neg hfreq,
      if_neg (sub_ne_zero.mpr fun hrev => hfreq hrev.symm), mul_zero]

/-- Primitive logarithmic frequency labels are injective. -/
theorem xiGammaEulerPrimitiveLogFrequency_injective :
    Function.Injective xiGammaEulerPrimitiveLogFrequency := by
  intro pe tau h
  apply xiGammaEulerValuationNat_injective_commonTest
  have hnNat : 0 < xiGammaEulerValuationNat pe := by
    exact pow_pos pe.1.property.pos _
  have hmNat : 0 < xiGammaEulerValuationNat tau := by
    exact pow_pos tau.1.property.pos _
  have hn : (0 : ℝ) < xiGammaEulerValuationNat pe := by exact_mod_cast hnNat
  have hm : (0 : ℝ) < xiGammaEulerValuationNat tau := by exact_mod_cast hmNat
  have hexp := congrArg Real.exp h
  rw [xiGammaEulerPrimitiveLogFrequency,
    xiGammaEulerPrimitiveLogFrequency, Real.exp_log hn, Real.exp_log hm] at hexp
  exact_mod_cast hexp

/-- On a distinct primitive packet the surviving scalar energy is the sum of squared source
coefficients. -/
theorem xiWardCubicScalarEulerBohrEnergy_eq_sum_normSq
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (hpe : Function.Injective pe) :
    xiWardCubicScalarEulerBohrEnergy pe =
      ∑ i : Fin N,
        ((Complex.normSq
          (finiteVonMangoldtWeight (xiGammaEulerValuationNat (pe i))) : ℝ) : ℂ) := by
  classical
  rw [xiWardCubicScalarEulerBohrEnergy]
  let diag : Finset (Fin N × Fin N) :=
    Finset.univ.image fun i : Fin N => (i, i)
  have hset :
      ((Finset.univ : Finset (Fin N)).product Finset.univ).filter
          (fun q => xiGammaEulerPrimitiveLogFrequency (pe q.1) =
            xiGammaEulerPrimitiveLogFrequency (pe q.2)) = diag := by
    ext q
    simp only [Finset.mem_filter, diag, Finset.mem_image]
    constructor
    · rintro ⟨hqmem, hq⟩
      have hpet : pe q.1 = pe q.2 :=
        xiGammaEulerPrimitiveLogFrequency_injective hq
      have hqeq : q.1 = q.2 := hpe hpet
      exact ⟨q.1, Finset.mem_univ _, Prod.ext rfl hqeq⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩
  rw [hset]
  dsimp only [diag]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [Complex.normSq_eq_conj_mul_self]
    rw [Complex.star_def]
    ring
  · intro i _hi j _hj hij
    exact (Prod.mk.inj hij).1

/-- **W-H189 scalarization obstruction.**  Exact Bohr dephasing of a scalar primitive Euler
trace produces `sum (Lambda(n)/n)^(2 : ℕ)`, rather than the coefficient-linear primitive codiagonal. -/
theorem bohrMean_xiWardCubicScalarEulerTrace_eq_vonMangoldt_square
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (hpe : Function.Injective pe) :
    bohrMean (fun t => xiWardCubicScalarEulerTrace pe t *
      star (xiWardCubicScalarEulerTrace pe t)) =
      ∑ i : Fin N,
        ((((ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (pe i)) /
          xiGammaEulerValuationNat (pe i)) ^ (2 : ℕ) : ℝ)) : ℂ) := by
  rw [bohrMean_xiWardCubicScalarEulerTrace_mul_star,
    xiWardCubicScalarEulerBohrEnergy_eq_sum_normSq pe hpe]
  apply Finset.sum_congr rfl
  intro i _hi
  have hn : xiGammaEulerValuationNat (pe i) ≠ 0 := by
    unfold xiGammaEulerValuationNat
    exact pow_ne_zero _ (pe i).1.property.ne_zero
  rw [finiteVonMangoldtWeight_eq_ofReal hn]
  simp [Complex.normSq_apply]
  ring

end

end RHTower
