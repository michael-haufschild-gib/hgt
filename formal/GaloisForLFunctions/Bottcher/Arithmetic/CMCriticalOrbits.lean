import GaloisForLFunctions.Bottcher.Arithmetic.CriticalParameterIntegrality
import GaloisForLFunctions.Bottcher.Arithmetic.SmallCMIntegers

/-!
# Cyclotomic rigidity of finite critical orbits

For degree at least three, a finite critical orbit over a CM field consists
entirely of zero and roots of unity. Integrality follows from the orbit
collision; the sharp escape bound and the CM integer gap then force rigidity.
-/

noncomputable section
namespace Bottcher.Arithmetic
open Set Bornology NumberField

private theorem bounded_highDegree_norm_le_sqrt_two (d : ℕ) (c : ℂ)
    (h : IsBounded (range (criticalOrbit (d + 1) c))) (n : ℕ) :
    ‖criticalOrbit (d + 1) c n‖ ≤ Real.sqrt 2 := by
  have hp := (bounded_criticalOrbit_iff (d + 1) c).mp h n
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  by_cases hsmall : ‖criticalOrbit (d + 1) c n‖ ≤ 1
  · nlinarith only [hsmall, hs, hs0]
  · have hone : 1 ≤ ‖criticalOrbit (d + 1) c n‖ := le_of_lt (lt_of_not_ge hsmall)
    have hpow : 1 ≤ ‖criticalOrbit (d + 1) c n‖ ^ d := one_le_pow₀ hone
    have he : d + 1 + 1 = 2 + d := by omega
    rw [he, pow_add] at hp
    have hle := mul_le_mul_of_nonneg_left hpow
      (sq_nonneg ‖criticalOrbit (d + 1) c n‖)
    nlinarith only [hp, hle, hs, hs0, norm_nonneg (criticalOrbit (d + 1) c n)]

private theorem bounded_highDegree_parameter_lt_sqrt_two (d : ℕ) (c : ℂ)
    (h : IsBounded (range (criticalOrbit (d + 1) c))) : ‖c‖ < Real.sqrt 2 := by
  cases d with
  | zero =>
    exact (cubic_criticalOrbit_unbounded_or_strict c).resolve_left (not_not.mpr h)
  | succ d =>
    have hp := (bounded_criticalOrbit_iff (d + 1 + 1) c).mp h 1
    rw [criticalOrbit_one] at hp
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    by_contra hlt
    have hn : Real.sqrt 2 ≤ ‖c‖ := le_of_not_gt hlt
    have hone : 1 ≤ ‖c‖ := by nlinarith only [hn, hs, hs0]
    have hpow := le_self_pow₀ hone (by omega : d + 1 ≠ 0)
    have he : d + 1 + 1 + 1 = 2 + (d + 1) := by omega
    rw [he, pow_add] at hp
    have hle := mul_le_mul_of_nonneg_left hpow (sq_nonneg ‖c‖)
    have hsq : 2 ≤ ‖c‖ ^ 2 := by nlinarith only [hn, hs, hs0]
    have hcube := mul_le_mul_of_nonneg_right hsq (norm_nonneg c)
    nlinarith only [hp, hle, hcube, hn, hs, hs0]

private theorem bounded_highDegree_orbit_lt_sqrt_two (d : ℕ) (c : ℂ)
    (h : IsBounded (range (criticalOrbit (d + 1) c))) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    ‖criticalOrbit (d + 1) c n‖ < Real.sqrt 2 := by
  have hnext := bounded_highDegree_norm_le_sqrt_two d c h (n + 1)
  have hreverse := norm_sub_norm_le (criticalOrbit (d + 1) c n ^ (d + 1 + 2)) (-c)
  simp only [norm_neg, sub_neg_eq_add, norm_pow, ← criticalOrbit_succ] at hreverse
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  by_contra hlt
  have hn := le_of_not_gt hlt
  have hone : 1 ≤ ‖criticalOrbit (d + 1) c n‖ := by nlinarith only [hn, hs, hs0]
  have hpow := le_self_pow₀ hone (by omega : d + 1 ≠ 0)
  have he : d + 1 + 2 = 2 + (d + 1) := by omega
  rw [he, pow_add] at hreverse
  have hle := mul_le_mul_of_nonneg_left hpow (sq_nonneg ‖criticalOrbit (d + 1) c n‖)
  have hsq : 2 ≤ ‖criticalOrbit (d + 1) c n‖ ^ 2 := by nlinarith only [hn, hs, hs0]
  have hcube := mul_le_mul_of_nonneg_right hsq (norm_nonneg (criticalOrbit (d + 1) c n))
  nlinarith only [hnext, hreverse, hc, hle, hcube, hn, hs, hs0]

private theorem finite_embedded_criticalOrbit {K : Type*} [Field K]
    (φ : K →+* ℂ) (d : ℕ) (c : K) (h : (range (criticalOrbit d c)).Finite) :
    (range (criticalOrbit d (φ c))).Finite := by
  have he : criticalOrbit d (φ c) = φ ∘ criticalOrbit d c := by
    funext n
    exact (map_criticalOrbit φ d c n).symm
  rw [he, range_comp]
  exact h.image φ

/-- A finite critical orbit in a CM field has zero or root-of-unity parameter. -/
theorem criticalOrbit_infinite_or_zero_or_finiteOrder
    {K : Type*} [Field K] [NumberField K] [IsCMField K] (d : ℕ) (c : K) :
    (range (criticalOrbit (d + 1) c)).Infinite ∨ c = 0 ∨ IsOfFinOrder c := by
  by_cases hi : (range (criticalOrbit (d + 1) c)).Infinite
  · exact Or.inl hi
  · right
    have hf := Set.not_infinite.mp hi
    have hint := (criticalOrbit_infinite_or_integral (d + 1) c).resolve_left hi
    let x : 𝓞 K := ⟨c, hint⟩
    have hx : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ < Real.sqrt 2 := by
      intro φ
      exact bounded_highDegree_parameter_lt_sqrt_two d (φ c)
        (finite_embedded_criticalOrbit φ (d + 1) c hf).isBounded
    rcases (small_cm_integer_iff x).mp hx with hz | hu
    · exact Or.inl (congrArg (fun z : 𝓞 K => (z : K)) hz)
    · exact Or.inr ((algebraMap (𝓞 K) K).toMonoidHom.isOfFinOrder hu)

/-- Every point of a finite critical orbit over a CM field is zero or a root of unity. -/
theorem criticalOrbit_infinite_or_all_cyclotomic
    {K : Type*} [Field K] [NumberField K] [IsCMField K] (d : ℕ) (c : K) :
    (range (criticalOrbit (d + 1) c)).Infinite ∨
      ∀ n, criticalOrbit (d + 1) c n = 0 ∨ IsOfFinOrder (criticalOrbit (d + 1) c n) := by
  by_cases hi : (range (criticalOrbit (d + 1) c)).Infinite
  · exact Or.inl hi
  · right
    have hf := Set.not_infinite.mp hi
    have hint := (criticalOrbit_infinite_or_integral (d + 1) c).resolve_left hi
    have hc := (criticalOrbit_infinite_or_zero_or_finiteOrder d c).resolve_left hi
    have hiiter : ∀ n, IsIntegral ℤ (criticalOrbit (d + 1) c n) := by
      intro n
      induction n with
      | zero => simpa only [criticalOrbit_zero] using isIntegral_zero (R := ℤ) (B := K)
      | succ n ih => rw [criticalOrbit_succ]; exact (ih.pow _).add hint
    intro n
    let x : 𝓞 K := ⟨criticalOrbit (d + 1) c n, hiiter n⟩
    have hx : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ < Real.sqrt 2 := by
      intro φ
      change ‖φ (criticalOrbit (d + 1) c n)‖ < Real.sqrt 2
      rw [map_criticalOrbit]
      apply bounded_highDegree_orbit_lt_sqrt_two d (φ c)
        (finite_embedded_criticalOrbit φ (d + 1) c hf).isBounded
      rcases hc with rfl | hc
      · simp only [map_zero, norm_zero, zero_le_one]
      · exact ((φ.toMonoidHom.isOfFinOrder hc).norm_eq_one).le
    rcases (small_cm_integer_iff x).mp hx with hz | hu
    · exact Or.inl (congrArg (fun z : 𝓞 K => (z : K)) hz)
    · exact Or.inr ((algebraMap (𝓞 K) K).toMonoidHom.isOfFinOrder hu)

private theorem unit_circle_sum_one {t : ℂ} (ht : ‖t‖ = 1) (hs : ‖1 + t‖ = 1) :
    t ^ 2 + t + 1 = 0 := by
  have ht2 := congrArg (fun x : ℝ => x ^ 2) ht
  rw [Complex.sq_norm, Complex.normSq_apply] at ht2
  simp only [one_pow] at ht2
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  rw [Complex.sq_norm, Complex.normSq_apply] at hs2
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    zero_add, one_pow] at hs2
  have hre : 2 * t.re + 1 = 0 := by nlinarith only [ht2, hs2]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re,
      pow_two]
    nlinarith only [ht2, hre]
  · simp only [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_im,
      pow_two]
    nlinarith only [mul_eq_zero_of_left hre t.im]

/-- Two unit sides with unit sum form exactly a cyclotomic triangle. -/
theorem complex_unit_sum_iff (t : ℂ) :
    (‖t‖ = 1 ∧ ‖1 + t‖ = 1) ↔ t ^ 2 + t + 1 = 0 := by
  constructor
  · rintro ⟨ht, hs⟩
    exact unit_circle_sum_one ht hs
  · intro ht
    have hcube : t ^ 3 = 1 := by linear_combination (t - 1) * ht
    have htor : IsOfFinOrder t :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hcube⟩
    refine ⟨htor.norm_eq_one, ?_⟩
    have he : 1 + t = -t ^ 2 := by linear_combination ht
    rw [he, norm_neg, norm_pow, htor.norm_eq_one, one_pow]

/-- The first two nonzero orbit values force the parameter ratio to have order two or three.
No cyclotomic embedding-extension argument is needed. -/
theorem criticalOrbit_infinite_or_parameter_equations
    {K : Type*} [Field K] [NumberField K] [IsCMField K] (d : ℕ) (c : K) :
    (range (criticalOrbit (d + 1) c)).Infinite ∨ c = 0 ∨
      c ^ (d + 2) = -1 ∨ (c ^ (d + 2)) ^ 2 + c ^ (d + 2) + 1 = 0 := by
  by_cases hi : (range (criticalOrbit (d + 1) c)).Infinite
  · exact Or.inl hi
  · right
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    · right
      have hc := ((criticalOrbit_infinite_or_zero_or_finiteOrder d c).resolve_left hi).resolve_left hc0
      have hiter := (criticalOrbit_infinite_or_all_cyclotomic d c).resolve_left hi
      have hsecond : criticalOrbit (d + 1) c 2 = c * (1 + c ^ (d + 2)) := by
        rw [show 2 = 1 + 1 by rfl, criticalOrbit_succ, criticalOrbit_one]
        rw [show d + 1 + 2 = d + 2 + 1 by omega, pow_succ]
        ring
      rcases hiter 2 with hz | hu
      · left
        rw [hsecond] at hz
        have hz' := (mul_eq_zero.mp hz).resolve_left hc0
        linear_combination hz'
      · right
        let φ : K →+* ℂ := Classical.choice inferInstance
        have hcnorm : ‖φ c‖ = 1 := (φ.toMonoidHom.isOfFinOrder hc).norm_eq_one
        apply φ.injective
        simp only [map_add, map_pow, map_one, map_zero]
        apply unit_circle_sum_one
        · rw [norm_pow, hcnorm, one_pow]
        · have hnorm : ‖φ (criticalOrbit (d + 1) c 2)‖ = 1 :=
            (φ.toMonoidHom.isOfFinOrder hu).norm_eq_one
          rw [hsecond, map_mul, map_add, map_one, map_pow, norm_mul,
            hcnorm, one_mul] at hnorm
          exact hnorm

end Bottcher.Arithmetic

