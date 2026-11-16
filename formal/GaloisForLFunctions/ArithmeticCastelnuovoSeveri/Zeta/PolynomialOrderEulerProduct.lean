import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialOrderClosedPointDegrees
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittGhost
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.Complex.Basic

/-!
# Formal Euler products over polynomial orders

The inverse Euler products over closed primes of bounded residue degree
stabilize coefficientwise. Their logarithmic ghost counts algebra points
over each finite constant extension. These are affine products: no points
at infinity are included.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolynomialOrderClosedPoints
open Polynomial IsDedekindDomain _root_.RHTower PowerSeries
open scoped PowerSeries.WithPiTopology Topology
variable (K B : Type*) [Field K] [Finite K] [CommRing B]
    [IsDedekindDomain B] [Infinite B] [Algebra K B] [Algebra K[X] B]
    [IsScalarTower K K[X] B] [Module.Free K[X] B] [Module.Finite K[X] B]
    (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The inverse local Euler factor `1 - T^deg(v)` of an actual closed prime. -/
def inverseEulerFactor (v : HeightOneSpectrum B) : PowerSeries ℂ :=
  deningerBigWittFactor 1 (placeDegree K B v)

omit [Finite K] [Infinite B] in
theorem inverseEulerFactor_constantCoeff (v : HeightOneSpectrum B) :
    constantCoeff (inverseEulerFactor K B v) = 1 :=
  deningerBigWittFactor_constantCoeff _ _ (placeDegree_pos K B v).ne'

/-- The inverse Euler product over all closed primes below a degree cutoff. -/
def inverseEulerPartial (N : ℕ) : PowerSeries ℂ :=
  ∏ v ∈ placesDegreeLe K B p N, inverseEulerFactor K B v

theorem inverseEulerPartial_constantCoeff (N : ℕ) :
    constantCoeff (inverseEulerPartial K B p N) = 1 := by
  simp only [inverseEulerPartial, map_prod, inverseEulerFactor_constantCoeff, Finset.prod_const_one]

omit [Finite K] [Infinite B] [Algebra K[X] B] [IsScalarTower K K[X] B]
    [Module.Free K[X] B] [Module.Finite K[X] B] [IsDedekindDomain B] in
private theorem coeff_mul_inverseEulerFactors_of_lt (f : PowerSeries ℂ)
    (S : Finset (HeightOneSpectrum B)) (k : ℕ)
    (hS : ∀ v ∈ S, k < placeDegree K B v) :
    coeff k (f * ∏ v ∈ S, inverseEulerFactor K B v) = coeff k f := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => simp only [Finset.prod_empty, mul_one]
  | @insert v S hv ih =>
    rw [Finset.prod_insert hv, ← mul_assoc]
    rw [ih (f * inverseEulerFactor K B v) (fun w hw => hS w (Finset.mem_insert_of_mem hw))]
    exact coeff_mul_deningerBigWittFactor_of_lt f 1 (hS v (Finset.mem_insert_self _ _))

/-- Coefficients stabilize as soon as the cutoff exceeds their degree. -/
theorem inverseEulerPartial_coeff_stable {k N M : ℕ} (hk : k ≤ N) (hNM : N ≤ M) :
    coeff k (inverseEulerPartial K B p M) = coeff k (inverseEulerPartial K B p N) := by
  classical
  have hsub := placesDegreeLe_mono K B p hNM
  have hprod : (∏ v ∈ placesDegreeLe K B p N, inverseEulerFactor K B v) *
      (∏ v ∈ placesDegreeLe K B p M \ placesDegreeLe K B p N, inverseEulerFactor K B v) =
      ∏ v ∈ placesDegreeLe K B p M, inverseEulerFactor K B v :=
    (mul_comm _ _).trans (Finset.prod_sdiff hsub)
  unfold inverseEulerPartial
  rw [← hprod]
  apply coeff_mul_inverseEulerFactors_of_lt
  intro v hv
  have hn : ¬ placeDegree K B v ≤ N := by
    simpa only [mem_placesDegreeLe] using (Finset.mem_sdiff.mp hv).2
  exact hk.trans_lt (lt_of_not_ge hn)

/-- The coefficientwise product of the inverse factors at every closed prime. -/
def inverseEulerProduct : PowerSeries ℂ :=
  PowerSeries.mk fun n => coeff n (inverseEulerPartial K B p n)

theorem inverseEulerProduct_coeff (n : ℕ) :
    coeff n (inverseEulerProduct K B p) = coeff n (inverseEulerPartial K B p n) :=
  coeff_mk _ _

theorem inverseEulerProduct_constantCoeff : constantCoeff (inverseEulerProduct K B p) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, inverseEulerProduct_coeff,
    coeff_zero_eq_constantCoeff, inverseEulerPartial_constantCoeff]

/-- The products over bounded-degree primes converge in the coefficient topology. -/
theorem tendsto_inverseEulerPartial :
    Filter.Tendsto (inverseEulerPartial K B p) Filter.atTop (𝓝 (inverseEulerProduct K B p)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop n] with N hN
  simp only [inverseEulerProduct_coeff,
    inverseEulerPartial_coeff_stable K B p (k := n) le_rfl hN]

/-- A local factor contributes its residue degree in precisely the divisible degrees. -/
theorem inverseEulerPartial_ghost_coeff (N : ℕ) {k : ℕ} (hk : 0 < k) :
    coeff k (deningerBigWittLogGhost (inverseEulerPartial K B p N)
      (inverseEulerPartial_constantCoeff K B p N)) =
      ∑ v ∈ placesDegreeLe K B p N,
        if placeDegree K B v ∣ k then (placeDegree K B v : ℂ) else 0 := by
  unfold inverseEulerPartial
  rw [deningerBigWittLogGhost_finset_prod _ _ (inverseEulerFactor_constantCoeff K B), map_sum]
  apply Finset.sum_congr rfl
  intro v _
  simpa only [inverseEulerFactor, one_pow, mul_one] using
    deningerBigWittLogGhost_factor_coeff (1 : ℂ) (placeDegree_pos K B v) hk

/-- The positive logarithmic ghost coefficients count the actual extension-valued algebra points. -/
theorem inverseEulerProduct_ghost_coeff (e : ℕ) [NeZero e] :
    coeff e (deningerBigWittLogGhost (inverseEulerProduct K B p)
      (inverseEulerProduct_constantCoeff K B p)) =
      (Nat.card (B →ₐ[K] FiniteField.Extension K p e) : ℂ) := by
  rw [deningerBigWittLogGhost_coeff_congr (inverseEulerProduct_constantCoeff K B p)
    (inverseEulerPartial_constantCoeff K B p e)
    (fun n hn => by
      rw [inverseEulerProduct_coeff]
      exact (inverseEulerPartial_coeff_stable K B p (k := n) le_rfl hn).symm)]
  rw [inverseEulerPartial_ghost_coeff K B p e (Nat.pos_of_ne_zero (NeZero.ne e)),
    card_algHom_extension_eq_closed_degree_sum K B p e]
  push_cast
  rfl

/-- The product of the reciprocal local factors over a residue-degree cutoff. -/
def eulerPartial (N : ℕ) : PowerSeries ℂ :=
  ∏ v ∈ placesDegreeLe K B p N, deningerBigWittGeom 1 (placeDegree K B v)

/-- The local geometric factors cancel the corresponding inverse factors exactly. -/
theorem eulerPartial_mul_inverse (N : ℕ) :
    eulerPartial K B p N * inverseEulerPartial K B p N = 1 := by
  classical
  unfold eulerPartial inverseEulerPartial
  rw [← Finset.prod_mul_distrib]
  simp only [inverseEulerFactor, deningerBigWittGeom_mul_factor (1 : ℂ)
    (placeDegree_pos K B _), Finset.prod_const_one]

theorem eulerPartial_eq_invOfUnit (N : ℕ) :
    eulerPartial K B p N = invOfUnit (inverseEulerPartial K B p N) 1 := by
  have hi := invOfUnit_mul (inverseEulerPartial K B p N) 1
    (inverseEulerPartial_constantCoeff K B p N)
  calc
    _ = eulerPartial K B p N *
        (invOfUnit (inverseEulerPartial K B p N) 1 * inverseEulerPartial K B p N) := by
          rw [hi, mul_one]
    _ = invOfUnit (inverseEulerPartial K B p N) 1 *
        (eulerPartial K B p N * inverseEulerPartial K B p N) := by ring
    _ = _ := by rw [eulerPartial_mul_inverse, mul_one]

/-- Each coefficient of the reciprocal-factor product stabilizes at the inverse of the full product. -/
theorem eulerPartial_coeff_stable {n N : ℕ} (hnN : n ≤ N) :
    coeff n (eulerPartial K B p N) = coeff n (invOfUnit (inverseEulerProduct K B p) 1) := by
  rw [eulerPartial_eq_invOfUnit]
  apply deningerBigWittInvOfUnit_coeff_congr
  intro k hk
  rw [inverseEulerProduct_coeff]
  exact inverseEulerPartial_coeff_stable K B p le_rfl (hk.trans hnN)

/-- The literal products of reciprocal local factors converge coefficientwise to the affine zeta series. -/
theorem tendsto_eulerPartial :
    Filter.Tendsto (eulerPartial K B p) Filter.atTop
      (𝓝 (invOfUnit (inverseEulerProduct K B p) 1)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop n] with N hN
  exact (eulerPartial_coeff_stable K B p hN).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolynomialOrderClosedPoints
