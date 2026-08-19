/-
# Hölder for the Schatten scale

Submultiplicativity of the approximation numbers turns the Hölder inequality for series into the
Hölder inequality for Schatten classes: a product of a Schatten-`p` and a Schatten-`q` operator lies
in Schatten `r` whenever `p⁻¹ + q⁻¹ = r⁻¹`.  In particular every power of a Schatten-`p` operator at
or above the exponent is trace class.

Main results:
* `memSchattenClass_comp` — **Hölder for the Schatten scale**.
* `memSchattenClass_one_pow` — **powers at or above the exponent are trace class**.
-/
import GaloisForLFunctions.HTGeometry.SchattenPowerIdeal
import Mathlib.Analysis.MeanInequalities

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **Hölder for the Schatten scale.** -/
theorem memSchattenClass_comp {p q r : ℝ} (hpqr : Real.HolderTriple p q r)
    {S T : H →L[ℂ] H} (hS : MemSchattenClass p S) (hT : MemSchattenClass q T) :
    MemSchattenClass r (S ∘L T) := by
  have hr0 : 0 < r := hpqr.pos'
  have hcoe : ∀ (x : ℝ) (s : ℝ), 0 ≤ x → ((Real.toNNReal x ^ s : NNReal) : ℝ) = x ^ s := by
    intro x s hx
    rw [NNReal.coe_rpow, Real.coe_toNNReal x hx]
  have hf : Summable fun n : ℕ => (Real.toNNReal (approxNumber S n)) ^ p := by
    rw [← NNReal.summable_coe]
    exact hS.congr fun n => (hcoe _ _ (approxNumber_nonneg S n)).symm
  have hg : Summable fun n : ℕ => (Real.toNNReal (approxNumber T n)) ^ q := by
    rw [← NNReal.summable_coe]
    exact hT.congr fun n => (hcoe _ _ (approxNumber_nonneg T n)).symm
  have hprodNN := NNReal.summable_mul_rpow_of_Lp_Lq hpqr hf hg
  have hprod : Summable fun n : ℕ => (approxNumber S n * approxNumber T n) ^ r := by
    have hc := NNReal.summable_coe.mpr hprodNN
    refine hc.congr fun n => ?_
    rw [NNReal.coe_rpow, NNReal.coe_mul, Real.coe_toNNReal _ (approxNumber_nonneg S n),
      Real.coe_toNNReal _ (approxNumber_nonneg T n)]
  refine Summable.of_nonneg_of_le
    (fun m => Real.rpow_nonneg (approxNumber_nonneg _ m) _) (fun m => ?_)
    (summable_comp_nat_div
      (fun n => Real.rpow_nonneg
        (mul_nonneg (approxNumber_nonneg S n) (approxNumber_nonneg T n)) r)
      hprod (by norm_num : 0 < 2))
  have hle : approxNumber (S ∘L T) m ≤ approxNumber S (m / 2) * approxNumber T (m / 2) := by
    have h1 : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
    have h2 := approxNumber_antitone (S ∘L T) h1
    have h3 : approxNumber (S ∘L T) (m / 2 + m / 2)
        ≤ approxNumber S (m / 2) * approxNumber T (m / 2) :=
      approxNumber_comp_add_le S T (m / 2) (m / 2)
    have hidx : m / 2 + m / 2 = 2 * (m / 2) := by ring
    rw [hidx] at h3
    exact le_trans h2 h3
  exact Real.rpow_le_rpow (approxNumber_nonneg _ m) hle hr0.le

omit [CompleteSpace H] in
/-- **Powers at or above the Schatten exponent are trace class.** -/
theorem memSchattenClass_one_pow {p : ℝ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemSchattenClass p T) {k : ℕ} (hk : 0 < k) (hpk : p ≤ (k : ℝ)) :
    MemSchattenClass 1 (T ^ k) := by
  have hdivpos : 0 < p / (k : ℝ) := div_pos hp (by exact_mod_cast hk)
  have hdivle : p / (k : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hk)]
    exact hpk
  exact (memSchattenClass_pow hp hT hk).mono hdivpos hdivle

end

end GaloisForLFunctions.HTGeometry
