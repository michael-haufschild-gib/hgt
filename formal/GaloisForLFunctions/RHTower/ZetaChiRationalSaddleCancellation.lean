import GaloisForLFunctions.RHTower.ZetaChiFiniteStationaryTransform
import GaloisForLFunctions.RHTower.HighBlockCutoffMonotone
import GaloisForLFunctions.RHTower.DiscreteVanDerCorput

open Complex Finset
open scoped BigOperators
noncomputable section
namespace RHTower


/-- Literal rational saddle phases are powers of one additive-character value. -/
theorem bourgainOscillation_rational_saddle_mul_eq_pow (a q n : ℕ) :
    bourgainOscillation (2 * Real.pi * (a : ℝ) * n / q) =
      bourgainOscillation (2 * Real.pi * (a : ℝ) / q) ^ n := by
  unfold bourgainOscillation
  have he : I * ((2 * Real.pi * (a : ℝ) * n / q : ℝ) : ℂ) =
      (n : ℂ) * (I * ((2 * Real.pi * (a : ℝ) / q : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [he, Complex.exp_nat_mul]

private theorem rational_saddle_phase_eq_one_iff (a q : ℕ) (hq : 0 < q) :
    bourgainOscillation (2 * Real.pi * (a : ℝ) / q) = 1 ↔ q ∣ a := by
  have he : bourgainOscillation (2 * Real.pi * (a : ℝ) / q) =
      Complex.exp (2 * (Real.pi : ℂ) * I * a / q) := by
    unfold bourgainOscillation
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq.ne'

private theorem rational_saddle_phase_pow_denominator (a q : ℕ) (hq : 0 < q) :
    bourgainOscillation (2 * Real.pi * (a : ℝ) / q) ^ q = 1 := by
  rw [← bourgainOscillation_rational_saddle_mul_eq_pow]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : 2 * Real.pi * (a : ℝ) * q / q = 2 * Real.pi * a := by field_simp
  rw [he]
  unfold bourgainOscillation
  have he' : I * ((2 * Real.pi * (a : ℝ) : ℝ) : ℂ) =
      (a : ℂ) * (2 * (Real.pi : ℂ) * I) := by push_cast; ring
  rw [he']
  exact Complex.exp_nat_mul_two_pi_mul_I a

/-- The full rational saddle residue block keeps exactly its divisibility diagonal. -/
theorem sum_bourgainOscillation_rational_saddle_period (a q : ℕ) (hq : 0 < q) :
    ∑ n ∈ Finset.range q, bourgainOscillation (2 * Real.pi * (a : ℝ) * n / q) =
      if q ∣ a then (q : ℂ) else 0 := by
  simp_rw [bourgainOscillation_rational_saddle_mul_eq_pow]
  by_cases hdiv : q ∣ a
  · rw [if_pos hdiv, (rational_saddle_phase_eq_one_iff a q hq).mpr hdiv]
    simp
  · have hne : bourgainOscillation (2 * Real.pi * (a : ℝ) / q) ≠ 1 :=
      fun h => hdiv ((rational_saddle_phase_eq_one_iff a q hq).mp h)
    rw [if_neg hdiv, geom_sum_eq hne, rational_saddle_phase_pow_denominator a q hq]
    simp

/-- Every translated incomplete rational residue sum is bounded by its denominator,
independently of the full support length. -/
theorem norm_sum_bourgainOscillation_rational_saddle_le
    (a q A K : ℕ) (hq : 0 < q) (hdiv : ¬ q ∣ a) :
    ‖∑ n ∈ Finset.range K,
      bourgainOscillation (2 * Real.pi * (a : ℝ) * (A + n : ℕ) / q)‖ ≤ q := by
  let z := bourgainOscillation (2 * Real.pi * (a : ℝ) / q)
  have hz : ‖z‖ = 1 := norm_bourgainOscillation _
  have hz1 : z ≠ 1 := fun h => hdiv ((rational_saddle_phase_eq_one_iff a q hq).mp h)
  have hzq : z ^ q = 1 := rational_saddle_phase_pow_denominator a q hq
  have hpow : z ^ K = z ^ (K % q) := by
    conv_lhs => rw [← Nat.mod_add_div K q]
    rw [pow_add, pow_mul, hzq, one_pow, mul_one]
  have heq : ∑ n ∈ Finset.range K, z ^ n = ∑ n ∈ Finset.range (K % q), z ^ n := by
    rw [geom_sum_eq hz1, geom_sum_eq hz1, hpow]
  have hnorm : ‖∑ n ∈ Finset.range K, z ^ n‖ ≤ (q : ℝ) := by
    rw [heq]
    calc
      _ ≤ ∑ n ∈ Finset.range (K % q), ‖z ^ n‖ := norm_sum_le _ _
      _ = (K % q : ℕ) := by simp [norm_pow, hz]
      _ ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt K hq).le
  have hphase (n : ℕ) : bourgainOscillation
      (2 * Real.pi * (a : ℝ) * (A + n : ℕ) / q) = z ^ A * z ^ n := by
    rw [bourgainOscillation_rational_saddle_mul_eq_pow, pow_add]
  rw [Finset.sum_congr rfl (fun n _ => hphase n), ← Finset.mul_sum,
    norm_mul, norm_pow, hz, one_pow, one_mul]
  exact hnorm

/-- The actual positive decreasing Gaussian cutoff preserves the complete
rational-saddle cancellation. No prime mask or stationary remainder is discarded. -/
theorem norm_sum_cutoff_bourgainOscillation_rational_saddle_le
    (a q A K : ℕ) (hq : 0 < q) (hdiv : ¬ q ∣ a) (hA : 0 < A)
    {N : ℝ} (hN : 0 < N) :
    ‖∑ n ∈ Finset.range K, smoothAFECutoff (((A + n : ℕ) : ℝ) / N) *
      bourgainOscillation (2 * Real.pi * (a : ℝ) * (A + n : ℕ) / q)‖ ≤
      (smoothAFECutoff ((A : ℝ) / N)).re * q := by
  let w : ℕ → ℝ := fun n => (smoothAFECutoff (((A + n : ℕ) : ℝ) / N)).re
  have hpos (n : ℕ) : 0 < ((A + n : ℕ) : ℝ) / N := by
    apply div_pos _ hN
    exact_mod_cast (by omega : 0 < A + n)
  have hw : Antitone w := by
    intro i j hij
    apply smoothAFECutoff_re_antitoneOn (hpos i) (hpos j)
    apply (div_le_div_iff_of_pos_right hN).mpr
    exact_mod_cast (show A + i ≤ A + j by omega)
  have hnn : ∀ n, 0 ≤ w n := fun n => smoothAFECutoff_re_nonneg (hpos n)
  have hbound := norm_sum_amplitude_phase_le hw hnn
    (fun L => norm_sum_bourgainOscillation_rational_saddle_le a q A L hq hdiv) K
  have heq (n : ℕ) : smoothAFECutoff (((A + n : ℕ) : ℝ) / N) = (w n : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using smoothAFECutoff_im_eq_zero (hpos n)
  simp_rw [heq]
  simpa only [w, Nat.add_zero] using hbound

end RHTower
