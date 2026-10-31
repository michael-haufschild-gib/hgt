import GaloisForLFunctions.BiarithmeticGeometry.Affine.NearIdentityGrids
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Rational grids near one with separated p-adic norms

The slopes `1 + p^(-(N+1)(i+1))` approach one in the real topology. Their
p-adic norms grow at separated rates. A single reciprocal prime power is a
common cyclic translation step for every finite collection of these slopes.
-/

open Filter Topology
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

def primeGridExponent (N i : ℕ) : ℕ := (N + 1) * (i + 1)

def primeGridSlope (p N i : ℕ) : ℚ := 1 + ((p : ℚ) ^ primeGridExponent N i)⁻¹

def primeGridStep (p N n : ℕ) : ℚ := ((p : ℚ) ^ primeGridExponent N n)⁻¹

theorem primeGridSlope_pos {p : ℕ} (hp : p.Prime) (N i : ℕ) :
    0 < primeGridSlope p N i := by
  have hpQ : (0 : ℚ) < p := Nat.cast_pos.mpr hp.pos
  unfold primeGridSlope
  positivity

/-- The positive rational unit determined by a prime-power grid slope. -/
def primeGridUnit {p : ℕ} (hp : p.Prime) (N i : ℕ) : ℚˣ :=
  Units.mk0 (primeGridSlope p N i) (primeGridSlope_pos hp N i).ne'

@[simp] theorem primeGridUnit_val {p : ℕ} (hp : p.Prime) (N i : ℕ) :
    (primeGridUnit hp N i : ℚ) = primeGridSlope p N i := rfl

theorem primeGridUnit_pos {p : ℕ} (hp : p.Prime) (N i : ℕ) :
    (0 : ℚ) < (primeGridUnit hp N i : ℚ) := primeGridSlope_pos hp N i

/-- Distinct positions have exponent separation at least `N+1`. -/
theorem primeGridExponent_gap (N : ℕ) {i j : ℕ} (hij : i < j) :
    (N + 1) + primeGridExponent N i ≤ primeGridExponent N j := by
  calc
    (N + 1) + primeGridExponent N i = (N + 1) * (i + 2) := by
      unfold primeGridExponent
      ring
    _ ≤ (N + 1) * (j + 1) := Nat.mul_le_mul_left _ (by omega)

private theorem padicNorm_inv_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    padicNorm p (((p : ℚ) ^ e)⁻¹) = (p : ℚ) ^ e := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpow : padicNorm p ((p : ℚ) ^ e) = ((p : ℚ) ^ e)⁻¹ := by
    induction e with
    | zero => simp only [pow_zero, padicNorm.one, inv_one]
    | succ e ih =>
      simp only [pow_succ, padicNorm.mul, ih, padicNorm.padicNorm_p hp.one_lt, mul_inv]
  rw [IsAbsoluteValue.abv_inv (padicNorm p), hpow, inv_inv]

/-- The reciprocal prime-power term strictly dominates the unit term p-adically. -/
theorem padicNorm_primeGridUnit {p : ℕ} (hp : p.Prime) (N i : ℕ) :
    padicNorm p (primeGridUnit hp N i : ℚ) = (p : ℚ) ^ primeGridExponent N i := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpQ : (1 : ℚ) < p := Nat.cast_lt.mpr hp.one_lt
  have he : 1 ≤ primeGridExponent N i := Nat.succ_le_of_lt
    (Nat.mul_pos (Nat.succ_pos N) (Nat.succ_pos i))
  have hlarge : (1 : ℚ) < (p : ℚ) ^ primeGridExponent N i :=
    hpQ.trans_le (by simpa only [pow_one] using pow_le_pow_right₀ hpQ.le he)
  have hne : padicNorm p (1 : ℚ) ≠ padicNorm p (((p : ℚ) ^ primeGridExponent N i)⁻¹) := by
    rw [padicNorm.one, padicNorm_inv_prime_pow hp]
    exact ne_of_lt hlarge
  rw [primeGridUnit_val, primeGridSlope, padicNorm.add_eq_max_of_ne hne,
    padicNorm.one, padicNorm_inv_prime_pow hp, max_eq_right hlarge.le]

theorem padicNorm_primeGridStep {p : ℕ} (hp : p.Prime) (N n : ℕ) :
    padicNorm p (primeGridStep p N n) = (p : ℚ) ^ primeGridExponent N n :=
  padicNorm_inv_prime_pow hp _

/-- Every slope in a finite grid is a natural multiple of the same translation step. -/
theorem primeGridUnit_eq_nat_mul_step {p : ℕ} (hp : p.Prime) (N n : ℕ) (i : Fin n) :
    ∃ m : ℕ, (primeGridUnit hp N i : ℚ) = (m : ℚ) * primeGridStep p N n := by
  let E := primeGridExponent N n
  let e := primeGridExponent N i
  have heE : e ≤ E := (Nat.le_add_left e (N + 1)).trans (primeGridExponent_gap N i.isLt)
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have heQ : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ hpQ
  have hEQ : (p : ℚ) ^ E ≠ 0 := pow_ne_zero _ hpQ
  have hpow : (p : ℚ) ^ (E - e) * (p : ℚ) ^ e = (p : ℚ) ^ E := by
    rw [← pow_add, Nat.sub_add_cancel heE]
  have hdiv : (p : ℚ) ^ E * ((p : ℚ) ^ e)⁻¹ = (p : ℚ) ^ (E - e) := by
    rw [← hpow, mul_assoc, mul_inv_cancel₀ heQ, mul_one]
  refine ⟨p ^ E + p ^ (E - e), ?_⟩
  change 1 + ((p : ℚ) ^ e)⁻¹ = ((p ^ E + p ^ (E - e) : ℕ) : ℚ) * ((p : ℚ) ^ E)⁻¹
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow]
  have heq : (1 + ((p : ℚ) ^ e)⁻¹) * (p : ℚ) ^ E =
      (p : ℚ) ^ E + (p : ℚ) ^ (E - e) := by
    rw [add_mul, one_mul, mul_comm (((p : ℚ) ^ e)⁻¹), hdiv]
  calc
    1 + ((p : ℚ) ^ e)⁻¹ =
        ((1 + ((p : ℚ) ^ e)⁻¹) * (p : ℚ) ^ E) * ((p : ℚ) ^ E)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hEQ, mul_one]
    _ = _ := by rw [heq]

/-- The common step divided by each slope has uniformly large p-adic norm. -/
theorem primeGridStep_div_norm_lower {p : ℕ} (hp : p.Prime) (N n : ℕ) (i : Fin n) :
    (p : ℚ) ^ (N + 1) ≤ padicNorm p (primeGridStep p N n / (primeGridUnit hp N i : ℚ)) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicNorm.div, padicNorm_primeGridStep hp, padicNorm_primeGridUnit hp]
  apply (le_div_iff₀ (pow_pos (Nat.cast_pos.mpr hp.pos) _)).mpr
  rw [← pow_add]
  exact pow_le_pow_right₀ (Nat.cast_le.mpr hp.one_le) (primeGridExponent_gap N i.isLt)

/-- In increasing index order, each slope ratio has uniformly large p-adic norm. -/
theorem primeGridRatio_norm_lower {p : ℕ} (hp : p.Prime) (N : ℕ)
    {i j : ℕ} (hij : i < j) :
    (p : ℚ) ^ (N + 1) ≤ padicNorm p ((primeGridUnit hp N j : ℚ) / (primeGridUnit hp N i : ℚ)) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicNorm.div, padicNorm_primeGridUnit hp, padicNorm_primeGridUnit hp]
  apply (le_div_iff₀ (pow_pos (Nat.cast_pos.mpr hp.pos) _)).mpr
  rw [← pow_add]
  exact pow_le_pow_right₀ (Nat.cast_le.mpr hp.one_le) (primeGridExponent_gap N hij)

/-- The common reciprocal prime-power error tends geometrically to zero. -/
theorem tendsto_primeGridReciprocal {p : ℕ} (hp : p.Prime) :
    Tendsto (fun N : ℕ => ((p : ℝ) ^ (N + 1))⁻¹) atTop (𝓝 0) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hpR).mpr hp1
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hpR.le) hi).mul_const
    ((p : ℝ)⁻¹)
  simpa only [inv_pow, pow_succ, mul_inv, zero_mul] using h

/-- Every slope tends to one in the real topology despite its growing p-adic norm. -/
theorem tendsto_primeGridUnit {p : ℕ} (hp : p.Prime) (i : ℕ) :
    Tendsto (fun N => ((primeGridUnit hp N i : ℚ) : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_primeGridReciprocal hp).pow (i + 1))
  simpa only [primeGridUnit_val, primeGridSlope, primeGridExponent, Rat.cast_add,
    Rat.cast_one, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, inv_pow, pow_mul,
    zero_pow (Nat.succ_ne_zero i), add_zero] using h

#print axioms primeGridUnit_eq_nat_mul_step
#print axioms primeGridStep_div_norm_lower
#print axioms primeGridRatio_norm_lower
#print axioms tendsto_primeGridUnit
end GaloisForLFunctions.BiarithmeticGeometry
