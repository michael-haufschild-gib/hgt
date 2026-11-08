import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hilbert coordinates for conductor-weighted arithmetic probes

Multiplication by `n^(δ/2)` identifies positive-conductor sequences of finite
weighted square mass with real `ℓ²`. The inverse coordinates preserve addition
and scalar multiplication and cover exactly those arithmetic sequences.
Finite conductor truncations converge, and conductor atoms give infinite rank.
-/

noncomputable section
open Finset Filter Topology
open scoped ENNReal
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

/-- Hilbert coordinates for positive-conductor probes of weight `n^δ`. -/
abbrev WeightedProbe (_δ : ℝ) := lp (fun _ : ℕ => ℝ) 2

/-- Arithmetic coefficients undo the square root of the conductor weight. -/
def probeCoefficients (δ : ℝ) (u : WeightedProbe δ) : ℕ → ℝ
  | 0 => 0
  | n+1 => u n*((n+1:ℕ):ℝ)^(-δ/2)

@[simp] theorem probeCoefficients_zero (δ : ℝ) (u : WeightedProbe δ) :
    probeCoefficients δ u 0=0 := rfl

@[simp] theorem probeCoefficients_succ (δ : ℝ) (u : WeightedProbe δ) (n : ℕ) :
    probeCoefficients δ u (n+1)=u n*((n+1:ℕ):ℝ)^(-δ/2) := rfl

/-- The arithmetic coefficient map respects the Hilbert addition law. -/
theorem probeCoefficients_add (δ : ℝ) (u v : WeightedProbe δ) (n : ℕ) :
    probeCoefficients δ (u+v) n=probeCoefficients δ u n+probeCoefficients δ v n := by
  cases n with
  | zero => simp only [probeCoefficients_zero, add_zero]
  | succ n => simp only [probeCoefficients_succ, lp.coeFn_add, Pi.add_apply, add_mul]

/-- Scalar multiplication acts on the original arithmetic coefficients. -/
theorem probeCoefficients_smul (δ a : ℝ) (u : WeightedProbe δ) (n : ℕ) :
    probeCoefficients δ (a • u) n=a*probeCoefficients δ u n := by
  cases n with
  | zero => simp only [probeCoefficients_zero, mul_zero]
  | succ n => simp only [probeCoefficients_succ, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, mul_assoc]

/-- The conductor weight cancels exactly against the coordinate change. -/
theorem probeCoefficients_weighted_square (δ : ℝ) (u : WeightedProbe δ) (n : ℕ) :
    ((n+1:ℕ):ℝ)^δ*(probeCoefficients δ u (n+1))^2=(u n)^2 := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  have hw : ((n+1:ℕ):ℝ)^δ*(((n+1:ℕ):ℝ)^(-δ/2)*((n+1:ℕ):ℝ)^(-δ/2))=1 := by
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    have he : δ+(-δ/2+-δ/2)=0 := by ring
    rw [he, Real.rpow_zero]
  rw [probeCoefficients_succ, mul_pow]
  calc _ = (u n)^2*(((n+1:ℕ):ℝ)^δ*
        (((n+1:ℕ):ℝ)^(-δ/2)*((n+1:ℕ):ℝ)^(-δ/2))) := by ring
       _ = _ := by rw [hw, mul_one]

/-- Weighted square mass is summable for every Hilbert probe. -/
theorem probeCoefficients_summable (δ : ℝ) (u : WeightedProbe δ) :
    Summable (fun n : ℕ => (n:ℝ)^δ*(probeCoefficients δ u n)^2) := by
  apply (summable_nat_add_iff 1).mp
  simp_rw [probeCoefficients_weighted_square]
  have hs := (lp.memℓp u).summable (show 0 < (2:ℝ≥0∞).toReal by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hs

/-- The Hilbert norm is exactly the arithmetic weighted square norm. -/
theorem probeCoefficients_mass (δ : ℝ) (u : WeightedProbe δ) :
    (∑' n : ℕ, (n:ℝ)^δ*(probeCoefficients δ u n)^2)=‖u‖^2 := by
  rw [← (probeCoefficients_summable δ u).sum_add_tsum_nat_add 1]
  simp only [sum_range_one, probeCoefficients_zero, zero_pow (by decide : 2≠0),
    mul_zero, zero_add, probeCoefficients_weighted_square]
  have hs := lp.norm_rpow_eq_tsum (show 0 < (2:ℝ≥0∞).toReal by norm_num) u
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hs.symm

/-- Arithmetic coefficients determine a Hilbert probe uniquely. -/
theorem probeCoefficients_injective (δ : ℝ) : Function.Injective (probeCoefficients δ) := by
  intro u v h
  apply lp.ext
  funext n
  have he := congrFun h (n+1)
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  exact mul_right_cancel₀ (Real.rpow_pos_of_pos hn (-δ/2)).ne'
    (show u n*((n+1:ℕ):ℝ)^(-δ/2)=v n*((n+1:ℕ):ℝ)^(-δ/2) from he)

/-- Every actual sequence of finite weighted square mass has a Hilbert representative. -/
theorem exists_probeCoefficients (δ : ℝ) (x : ℕ → ℝ) (hx0 : x 0=0)
    (hx : Summable (fun n : ℕ => (n:ℝ)^δ*(x n)^2)) :
    ∃ u : WeightedProbe δ, probeCoefficients δ u=x := by
  let f : ℕ → ℝ := fun n => x (n+1)*((n+1:ℕ):ℝ)^(δ/2)
  have hsq (n : ℕ) : ‖f n‖^((2:ℝ≥0∞).toReal)=((n+1:ℕ):ℝ)^δ*(x (n+1))^2 := by
    have hn : (0:ℝ) < (n+1:ℕ) := by positivity
    have hw : (((n+1:ℕ):ℝ)^(δ/2))^2=((n+1:ℕ):ℝ)^δ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      congr 1
      norm_num
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, f, mul_pow, hw]
    ring
  have hf : Memℓp f 2 := by
    apply (memℓp_gen_iff (show 0 < (2:ℝ≥0∞).toReal by norm_num)).mpr
    exact ((summable_nat_add_iff 1).mpr hx).congr (fun n => (hsq n).symm)
  let u : WeightedProbe δ := ⟨f, hf⟩
  refine ⟨u, ?_⟩
  funext n
  cases n with
  | zero => exact hx0.symm
  | succ n =>
    have hn : (0:ℝ) < (n+1:ℕ) := by positivity
    change (x (n+1)*((n+1:ℕ):ℝ)^(δ/2))*((n+1:ℕ):ℝ)^(-δ/2)=x (n+1)
    rw [mul_assoc, ← Real.rpow_add hn]
    have he : δ/2+-δ/2=0 := by ring
    rw [he, Real.rpow_zero, mul_one]

/-- Distinct conductor atoms form an infinite orthonormal family in weighted coordinates. -/
theorem weightedProbe_atoms_orthonormal (δ : ℝ) :
    Orthonormal ℝ (fun n : ℕ => (lp.single 2 n (1:ℝ) : WeightedProbe δ)) := by
  constructor
  · intro n
    rw [lp.norm_single (E := fun _ : ℕ => ℝ) (by norm_num)]
    norm_num
  · intro n m hnm
    rw [lp.inner_single_left (𝕜 := ℝ) (G := fun _ : ℕ => ℝ)]
    rw [lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 m (1:ℝ) hnm]
    exact inner_zero_right _

/-- The arithmetic probe carrier has infinite rank for every conductor exponent. -/
theorem weightedProbe_not_finiteDimensional (δ : ℝ) :
    ¬FiniteDimensional ℝ (WeightedProbe δ) := by
  intro h
  have h1 : Cardinal.aleph0 ≤ Module.rank ℝ (WeightedProbe δ) :=
    (weightedProbe_atoms_orthonormal δ).linearIndependent.aleph0_le_rank
  exact (not_le.mpr (Module.rank_lt_aleph0 ℝ (WeightedProbe δ))) h1

/-- Finite conductor approximations converge in the weighted Hilbert norm. -/
theorem weightedProbe_tendsto_truncate (δ : ℝ) (u : WeightedProbe δ) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (lp.single 2 n (u n) : WeightedProbe δ))
      atTop (𝓝 u) :=
  (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) u).tendsto_sum_nat

#print axioms weightedProbe_tendsto_truncate
#print axioms probeCoefficients_injective
#print axioms exists_probeCoefficients
#print axioms weightedProbe_not_finiteDimensional
#print axioms probeCoefficients_summable
#print axioms probeCoefficients_mass
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
