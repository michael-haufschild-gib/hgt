import GaloisForLFunctions.HTGeometry.GagliardoFourierConstant
import GaloisForLFunctions.HTGeometry.CosineSublevelPeriodMeasure
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The sharp chord radius for dyadic phase observations

Squaring changes a squared chord y into y(4−y). An entire orbit strictly
below three would have to remain below one, where it expands until it
leaves unless it starts at zero. A primitive cube root attains three.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks

def chordSq (z : Circle) : ℝ := (dist z 1)^2

private theorem chord_exp (a : ℝ) : chordSq (Circle.exp a) = 2-2*Real.cos a := by
  change (dist (Complex.exp ((a : ℂ)*Complex.I)) (1 : ℂ))^2 = _
  rw [dist_eq_norm]
  exact HTGeometry.normSq_exp_mul_I_sub_one a

theorem chord_square (z : Circle) : chordSq (z^2) = chordSq z * (4-chordSq z) := by
  obtain ⟨a,rfl⟩ := Circle.exp_surjective z
  have he : (Circle.exp a)^2 = Circle.exp (2*a) := by rw [two_mul,Circle.exp_add,pow_two]
  rw [he,chord_exp,chord_exp,Real.cos_two_mul]
  ring

private theorem chord_step (z : Circle) (k : ℕ) :
    chordSq (z^(2^(k+1) : ℕ)) = chordSq (z^(2^k : ℕ)) * (4-chordSq (z^(2^k : ℕ))) := by
  rw [pow_succ (2 : ℕ),pow_mul,chord_square]

/-- Every nonidentity phase is detected at some dyadic time with squared chord at least three. -/
theorem dyadic_separation (z : Circle) : (∀ k : ℕ, chordSq (z^(2^k : ℕ)) < 3) ↔ z = 1 := by
  constructor
  · intro h
    let y (k : ℕ) := chordSq (z^(2^k : ℕ))
    have hy (k : ℕ) : 0 ≤ y k := sq_nonneg _
    have next (k : ℕ) : y (k+1) = y k*(4-y k) := chord_step z k
    have small (k : ℕ) : y k < 1 := by
      by_contra! hk
      have hp := mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr (h k).le)
      have hn : y (k+1) < 3 := h (k+1)
      nlinarith only [hp,hn,next k]
    have grow (k : ℕ) : 2*y k ≤ y (k+1) := by
      have hp := mul_nonneg (hy k) (by linarith only [small k] : 0 ≤ 2-y k)
      nlinarith only [hp,next k]
    have lower (k : ℕ) : ((k : ℝ)+1)*y 0 ≤ y k := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.cast_succ]
        have hp := mul_nonneg (Nat.cast_nonneg k : 0 ≤ (k : ℝ)) (hy 0)
        linarith only [ih,grow k,hp]
    have hzero : y 0 = 0 := by
      by_contra hn
      have hp := lt_of_le_of_ne (hy 0) (Ne.symm hn)
      obtain ⟨k,hk⟩ := exists_nat_gt (1/y 0)
      have hb := (div_lt_iff₀ hp).mp hk
      linarith only [hb,lower k,small k,hp]
    have hd : (dist z 1)^2 = 0 := by simpa only [y,chordSq,pow_zero,pow_one] using hzero
    exact dist_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero : (2 : ℕ) ≠ 0)).mp hd)
  · rintro rfl k
    simp [chordSq]

/-- A cube root attains the sharp bound at every dyadic time. -/
theorem cubic_sharp : ∃ z : Circle, z ≠ 1 ∧ ∀ k : ℕ, chordSq (z^(2^k : ℕ)) = 3 := by
  let z := Circle.exp (2*Real.pi/3)
  have h : chordSq z = 3 := by rw [chord_exp,HTGeometry.cos_two_pi_div_three]; norm_num
  refine ⟨z,fun hz => ?_,?_⟩
  · rw [hz] at h
    norm_num [chordSq] at h
  · intro k
    induction k with
    | zero => simpa using h
    | succ k ih => rw [chord_step,ih]; norm_num

/-- Uniform strict radius r detects identity for all circle phases exactly when 0<r≤√3. -/
theorem dyadic_radius_iff (r : {r : ℝ // 0 < r}) :
    (∀ z : Circle, (∀ k : ℕ, dist (z^(2^k : ℕ)) 1 < r.val) ↔ z = 1) ↔ r.val ≤ Real.sqrt 3 := by
  constructor
  · intro hall
    by_contra! hr
    obtain ⟨z,hn,h⟩ := cubic_sharp
    apply hn ((hall z).mp (fun k => ?_))
    have he := h k
    change (dist (z^(2^k : ℕ)) 1)^2 = 3 at he
    have hdist : dist (z^(2^k : ℕ)) 1 = Real.sqrt 3 :=
      (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp (he.trans (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)).symm)
    exact hdist.trans_lt hr
  · intro hr z
    constructor
    · intro h
      apply (dyadic_separation z).mp
      intro k
      have ht := (h k).trans_le hr
      change (dist _ _)^2 < 3
      exact ((sq_lt_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mpr ht).trans_eq (Real.sq_sqrt (by norm_num))
    · rintro rfl k
      simpa only [one_pow,dist_self] using r.property

#print axioms chord_square
#print axioms dyadic_separation
#print axioms cubic_sharp
#print axioms dyadic_radius_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks
