import GaloisForLFunctions.ArithmeticWeightTheory.ExactMonodromyPricesEveryFibreAtTheTrivialBound
import GaloisForLFunctions.ArithmeticWeightTheory.TheTrivialFibreIsTheJump
import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponentIsATailInvariant

/-!
# Amplified monodromy breaks the trivial bound only off the trivial fibre

Unamplified exact monodromy prices every fibre `x₀` at the trivial bound `(Σ a_n)^{2k}`
(`ExactMonodromyPricesEveryFibreAtTheTrivialBound`). Introducing a multiplicative amplifier `A(x)`
separates the trivial fibre `0` (`ζ`) from nontrivial fibres `x₀ ≠ 0`:

1. **Coherent amplified pricing at `0`** (`measureReal_singleton_zero_mul_amplified_pow_le`).
   At `x = 0` all phases are `1`, so for *every* measure `ν` on `GaugeTorus` (with no orthogonality
   hypothesis) and *every* continuous amplifier `A : GaugeTorus → ℂ`,
   `ν{0} · |A(0)|² · (Σ_{n ∈ s} a_n)^{2k} ≤ ∫ |A(x)|² |S_x|^{2k} dν`.
   Amplification never certifies below `(Σ a_n)^{2k}` at `ζ`.

2. **Centred-trace decoupling** (`integral_amplified_centred_sub_uncentred`,
   `integral_amplified_compl_zero_eq`). Subtracting a pole prediction `P₀` supported on the jump
   fibre `0` shifts the amplified `2k`-th moment by `ν{0} |A(0)|² (|P₀ − S₀|^{2k} − |S₀|^{2k})`.
   Orthogonality evaluates `∫ |A|² |S|^{2k} dν`, controlling only the variable fibres `x ≠ 0`, while
   the centred trace `P₀ − S₀` cancels from the orthogonality identity.

3. **Strict amplified saving off `0`** (`exists_amplified_orthonormal_strict_saving`).
   On the prime support `s = {2, 3}` with `a₂ = a₃ = 1` and `k = 1`, there exist a probability
   measure `ν` orthonormal on the amplified product support `{4, 6, 9}`, a torsion fibre `x₀ ≠ 0`,
   and a prime-supported amplifier `A` with `A(x₀) ≠ 0` such that
   `∫ |A(x)|² |S_x|² dν = 2 < 4 = ν{x₀} · |A(x₀)|² · (a₂ + a₃)²`.
   Multiplicative collision cancellation at `6 = 2·3 = 3·2` breaks the trivial bound off `0` and
   fails at `0` solely by phase coherence.
-/

open MeasureTheory Finset Complex
open scoped ComplexConjugate ENNReal Classical

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry ArithmeticGaugeTheory

/-! ### Coherent amplified pricing and centred decoupling at the trivial fibre -/

/-- At `x = 0` a nonnegative twisted sum equals the untwisted sum of its coefficients. -/
theorem norm_twistSum_zero_of_nonneg (s : Finset ℕ) {a : ℕ → ℝ} (ha : ∀ n ∈ s, 0 ≤ a n) :
    ‖twistSum s (fun n => (a n : ℂ)) 0‖ = ∑ n ∈ s, a n := by
  have h0 : twistSum s (fun n => (a n : ℂ)) 0 = ((∑ n ∈ s, a n : ℝ) : ℂ) := by
    simp only [twistSum, twist_trivial, mul_one, Complex.ofReal_sum]
  rw [h0, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg ha)]

/-- **Coherent amplified pricing at `0`.** For any finite measure `ν`, any continuous amplifier `A`,
and nonnegative weights `a`, the amplified `2k`-th moment never prices the trivial fibre below
`(Σ a_n)^{2k}`, without any orthogonality hypothesis on `ν`. -/
theorem measureReal_singleton_zero_mul_amplified_pow_le (ν : Measure GaugeTorus) [IsFiniteMeasure ν]
    (s : Finset ℕ) {a : ℕ → ℝ} (ha : ∀ n ∈ s, 0 ≤ a n) {A : GaugeTorus → ℂ} (hA : Continuous A)
    (k : ℕ) :
    ν.real {0} * ‖A 0‖ ^ 2 * (∑ n ∈ s, a n) ^ (2 * k) ≤
      ∫ x, ‖A x‖ ^ 2 * ‖twistSum s (fun n => (a n : ℂ)) x‖ ^ (2 * k) ∂ν := by
  set f : GaugeTorus → ℝ := fun x =>
    ‖A x‖ ^ 2 * ‖twistSum s (fun n => (a n : ℂ)) x‖ ^ (2 * k)
  have hf_cont : Continuous f :=
    (hA.norm.pow 2).mul ((continuous_twistSum s _).norm.pow (2 * k))
  have hf_int : Integrable f ν :=
    hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hset := setIntegral_le_integral (s := {(0 : GaugeTorus)}) hf_int
    (Filter.Eventually.of_forall fun x => by dsimp only [f]; positivity)
  rw [integral_singleton, smul_eq_mul] at hset
  simpa only [f, norm_twistSum_zero_of_nonneg s ha, mul_assoc] using hset

/-- **Centred-trace decoupling.** If the centred trace equals `c₀` at `0` (after pole subtraction)
and `-S_x` on `G \ {0}`, the centred and uncentred amplified `2k`-th moments differ solely by the
`ν{0}`-weighted jump at `0`. -/
theorem integral_amplified_centred_sub_uncentred (ν : Measure GaugeTorus) [IsFiniteMeasure ν]
    (s : Finset ℕ) (c : ℕ → ℂ) {A : GaugeTorus → ℂ} (hA : Continuous A) (c₀ : ℂ) (k : ℕ) :
    (∫ x, ‖A x‖ ^ 2 * ‖(if x = 0 then c₀ else -twistSum s c x)‖ ^ (2 * k) ∂ν) -
        (∫ x, ‖A x‖ ^ 2 * ‖twistSum s c x‖ ^ (2 * k) ∂ν) =
      ν.real {0} * ‖A 0‖ ^ 2 * (‖c₀‖ ^ (2 * k) - ‖twistSum s c 0‖ ^ (2 * k)) := by
  classical
  set g₁ : GaugeTorus → ℝ := fun x =>
    ‖A x‖ ^ 2 * ‖(if x = 0 then c₀ else -twistSum s c x)‖ ^ (2 * k)
  set g₂ : GaugeTorus → ℝ := fun x => ‖A x‖ ^ 2 * ‖twistSum s c x‖ ^ (2 * k)
  have hg₂_cont : Continuous g₂ :=
    (hA.norm.pow 2).mul ((continuous_twistSum s c).norm.pow (2 * k))
  have hg₂_int : Integrable g₂ ν :=
    hg₂_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdiff : ∀ x : GaugeTorus, g₁ x - g₂ x =
      ({(0 : GaugeTorus)} : Set GaugeTorus).indicator
        (fun _ => ‖A 0‖ ^ 2 * (‖c₀‖ ^ (2 * k) - ‖twistSum s c 0‖ ^ (2 * k))) x := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp only [g₁, g₂, ↓reduceIte, Set.mem_singleton_iff, Set.indicator_of_mem]
      ring
    · have hnot : x ∉ ({(0 : GaugeTorus)} : Set GaugeTorus) := Set.mem_singleton_iff.not.mpr hx
      rw [Set.indicator_of_notMem hnot]
      simp only [g₁, g₂, if_neg hx, norm_neg, sub_self]
  have hind_int : Integrable (({(0 : GaugeTorus)} : Set GaugeTorus).indicator
      (fun _ => ‖A 0‖ ^ 2 * (‖c₀‖ ^ (2 * k) - ‖twistSum s c 0‖ ^ (2 * k)))) ν :=
    (integrable_const _).indicator (isClosed_singleton.measurableSet)
  have hg₁_int : Integrable g₁ ν := by
    have h := hind_int.add hg₂_int
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    linarith [hdiff x]
  rw [← integral_sub hg₁_int hg₂_int]
  simp_rw [hdiff]
  rw [integral_indicator (isClosed_singleton.measurableSet), setIntegral_const, smul_eq_mul]
  ring

/-- Off `0`, the variable amplified `2k`-th moment equals the orthogonality moment minus the
uncentred `0`-fibre contribution; `c₀` does not appear. -/
theorem integral_amplified_compl_zero_eq (ν : Measure GaugeTorus) [IsFiniteMeasure ν]
    (s : Finset ℕ) (c : ℕ → ℂ) {A : GaugeTorus → ℂ} (hA : Continuous A) (k : ℕ) :
    (∫ x in ({(0 : GaugeTorus)}ᶜ : Set GaugeTorus),
        ‖A x‖ ^ 2 * ‖twistSum s c x‖ ^ (2 * k) ∂ν) =
      (∫ x, ‖A x‖ ^ 2 * ‖twistSum s c x‖ ^ (2 * k) ∂ν) -
        ν.real {0} * ‖A 0‖ ^ 2 * ‖twistSum s c 0‖ ^ (2 * k) := by
  set g : GaugeTorus → ℝ := fun x => ‖A x‖ ^ 2 * ‖twistSum s c x‖ ^ (2 * k)
  have hg_int : Integrable g ν :=
    ((hA.norm.pow 2).mul ((continuous_twistSum s c).norm.pow (2 * k))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsplit := integral_add_compl (isClosed_singleton (x := (0 : GaugeTorus))).measurableSet hg_int
  rw [integral_singleton, smul_eq_mul] at hsplit
  dsimp only [g] at hsplit ⊢
  linarith

/-! ### Strict amplified saving on a nontrivial torsion fibre -/

/-- The quarter-turn gauge point at `p = 2`: `χ(2) = i` and `χ(q) = 1` at odd primes. -/
def quarterTwoPoint : GaugeTorus :=
  fun p => if p = 2 then ((1 / 4 : ℝ) : UnitAddCircle) else 0

private theorem twist_quarterTwoPoint_two : twist quarterTwoPoint 2 = I := by
  rw [twist_prime_apply _ Nat.prime_two, quarterTwoPoint, if_pos rfl, fourier_coe_apply]
  have harg : (2 : ℂ) * ↑Real.pi * I * ↑(1 : ℤ) * ↑(1 / 4 : ℝ) / ↑(1 : ℝ) =
      ↑(Real.pi / 2) * I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

private theorem twist_quarterTwoPoint_three : twist quarterTwoPoint 3 = 1 := by
  rw [twist_prime_apply _ Nat.prime_three, quarterTwoPoint, if_neg (by decide), fourier_eval_zero]

private theorem twist_nsmul (k : ℕ) (x : GaugeTorus) (n : ℕ) :
    twist (k • x) n = twist x n ^ k := by
  induction k with
  | zero => simp [twist_trivial]
  | succ k ih => rw [succ_nsmul, twist_add, ih, pow_succ]

private theorem quarterOrbit_inj {i j : Fin 4}
    (h : (i.1 • quarterTwoPoint) = (j.1 • quarterTwoPoint)) : i = j := by
  have ht := congrArg (fun x => twist x 2) h
  rw [twist_nsmul, twist_nsmul, twist_quarterTwoPoint_two] at ht
  fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff, pow_succ] at ht ⊢ <;> norm_num at ht

/-- Uniform probability measure on the order-`4` subgroup generated by `quarterTwoPoint`. -/
def quarterTwoMeasure : Measure GaugeTorus :=
  (1 / 4 : ℝ≥0∞) • ∑ j : Fin 4, Measure.dirac (j.1 • quarterTwoPoint)

instance : IsProbabilityMeasure quarterTwoMeasure := by
  constructor
  simp only [quarterTwoMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.mem_univ, Set.indicator_of_mem, Pi.one_apply,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul, one_div]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private theorem integral_quarterTwoMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : GaugeTorus → E) (hf : Continuous f) :
    ∫ x, f x ∂quarterTwoMeasure = (1 / 4 : ℝ) • ∑ j : Fin 4, f (j.1 • quarterTwoPoint) := by
  unfold quarterTwoMeasure
  rw [integral_smul_measure, integral_finsetSum_measure fun j _ =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)]
  have h14 : ((1 / 4 : ℝ≥0∞).toReal) = (1 / 4 : ℝ) := by norm_num
  rw [h14]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact integral_dirac f (j.1 • quarterTwoPoint)

private theorem measureReal_quarterTwoMeasure_singleton (j₀ : Fin 4) :
    quarterTwoMeasure.real {j₀.1 • quarterTwoPoint} = 1 / 4 := by
  unfold Measure.real quarterTwoMeasure
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ (isClosed_singleton.measurableSet)]
  have hsum : (∑ j : Fin 4,
      ({j₀.1 • quarterTwoPoint} : Set GaugeTorus).indicator 1 (j.1 • quarterTwoPoint) : ℝ≥0∞) =
      1 := by
    rw [Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      have hne : j.1 • quarterTwoPoint ≠ j₀.1 • quarterTwoPoint :=
        fun heq => hj (quarterOrbit_inj heq)
      simp [hne]
    · simp
  rw [hsum]
  norm_num

private theorem twist_quarterOrbit_four (k : ℕ) :
    twist (k • quarterTwoPoint) 4 = (-1 : ℂ) ^ k := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, twist_mul _ (by decide) (by decide),
    twist_nsmul, twist_quarterTwoPoint_two, ← mul_pow, I_mul_I]

private theorem twist_quarterOrbit_six (j : Fin 4) :
    twist (j.1 • quarterTwoPoint) 6 = I ^ j.1 := by
  rw [show (6 : ℕ) = 2 * 3 by rfl, twist_mul _ (by decide) (by decide),
    twist_nsmul, twist_nsmul, twist_quarterTwoPoint_two, twist_quarterTwoPoint_three, one_pow,
    mul_one]

private theorem twist_quarterOrbit_nine (j : Fin 4) :
    twist (j.1 • quarterTwoPoint) 9 = 1 := by
  rw [show (9 : ℕ) = 3 * 3 by rfl, twist_mul _ (by decide) (by decide),
    twist_nsmul, twist_quarterTwoPoint_three, one_pow, mul_one]

/-- The 4-point subgroup measure is exactly orthonormal on `{4, 6, 9} = {2, 3} · {2, 3}`. -/
theorem twistOrthonormalOn_quarterTwoMeasure :
    TwistOrthonormalOn quarterTwoMeasure ({4, 6, 9} : Finset ℕ) := by
  intro m hm n hn
  have hcont : Continuous fun x : GaugeTorus => twist x m * conj (twist x n) :=
    (continuous_twist m).mul (Complex.continuous_conj.comp (continuous_twist n))
  rw [integral_quarterTwoMeasure _ hcont]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm hn
  rcases hm with rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl <;>
    simp only [Fin.sum_univ_four, twist_quarterOrbit_four, twist_quarterOrbit_six,
      twist_quarterOrbit_nine, Complex.real_smul] <;>
    norm_num [Complex.ext_iff, pow_succ]

/-- **Amplification breaks the trivial bound off `0`.** On the prime window support `{2, 3}` with
nonnegative weights `a₂ = a₃ = 1` and `k = 1`, there exist a probability measure `ν` orthonormal on
the amplified product support `{4, 6, 9}`, a nontrivial torsion fibre `x₀`, and a prime-supported
amplifier `A` such that `∫ |A|² |S|² dν = 2 < 4 = ν{x₀} |A(x₀)|² (a₂ + a₃)²`. -/
theorem exists_amplified_orthonormal_strict_saving :
    ∃ (ν : Measure GaugeTorus) (_ : IsProbabilityMeasure ν) (x₀ : GaugeTorus)
      (A : GaugeTorus → ℂ),
      x₀ ≠ 0 ∧ Continuous A ∧ A = twistSum ({2, 3} : Finset ℕ) (fun n => if n = 2 then -1 else 1) ∧
      TwistOrthonormalOn ν ({4, 6, 9} : Finset ℕ) ∧
      (∫ x, ‖A x‖ ^ 2 * ‖twistSum ({2, 3} : Finset ℕ) (fun _ => (1 : ℂ)) x‖ ^ 2 ∂ν) <
        ν.real {x₀} * ‖A x₀‖ ^ 2 * (∑ _n ∈ ({2, 3} : Finset ℕ), (1 : ℝ)) ^ 2 := by
  let x₀ : GaugeTorus := (2 : ℕ) • quarterTwoPoint
  let A : GaugeTorus → ℂ :=
    twistSum ({2, 3} : Finset ℕ) (fun n => if n = 2 then (-1 : ℂ) else 1)
  refine ⟨quarterTwoMeasure, inferInstance, x₀, A, ?_, continuous_twistSum _ _, rfl,
    twistOrthonormalOn_quarterTwoMeasure, ?_⟩
  · intro h0
    have := quarterOrbit_inj (i := ⟨2, by decide⟩) (j := ⟨0, by decide⟩) (by simpa [x₀] using h0)
    exact absurd (congrArg Fin.val this) (by decide)
  · set S : GaugeTorus → ℂ := twistSum ({2, 3} : Finset ℕ) (fun _ => (1 : ℂ))
    have hA_eq : ∀ x, A x = -twist x 2 + twist x 3 := by
      intro x
      simp only [A, twistSum, Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)]
      norm_num
    have hS_eq : ∀ x, S x = twist x 2 + twist x 3 := by
      intro x
      simp only [S, twistSum, Finset.sum_pair (by decide : (2 : ℕ) ≠ 3), one_mul]
    have hAx₀ : ‖A x₀‖ ^ 2 = 4 := by
      rw [hA_eq, show x₀ = (2 : ℕ) • quarterTwoPoint from rfl,
        twist_nsmul, twist_nsmul, twist_quarterTwoPoint_two, twist_quarterTwoPoint_three]
      have h2 : (-I ^ 2 + 1 ^ 2 : ℂ) = 2 := by norm_num
      rw [h2]
      norm_num
    have hmeas : quarterTwoMeasure.real {x₀} = 1 / 4 :=
      measureReal_quarterTwoMeasure_singleton ⟨2, by decide⟩
    have hsum : (∑ _n ∈ ({2, 3} : Finset ℕ), (1 : ℝ)) ^ 2 = 4 := by
      rw [Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)]
      norm_num
    have hint_cont : Continuous fun x : GaugeTorus => ‖A x‖ ^ 2 * ‖S x‖ ^ 2 :=
      ((continuous_twistSum _ _).norm.pow 2).mul ((continuous_twistSum _ _).norm.pow 2)
    have hint_val : ∫ x, ‖A x‖ ^ 2 * ‖S x‖ ^ 2 ∂quarterTwoMeasure = 2 := by
      rw [integral_quarterTwoMeasure _ hint_cont, smul_eq_mul, Fin.sum_univ_four]
      have hj0 : ‖A ((0 : ℕ) • quarterTwoPoint)‖ ^ 2 * ‖S ((0 : ℕ) • quarterTwoPoint)‖ ^ 2 = 0 := by
        rw [hA_eq, zero_nsmul, twist_trivial, twist_trivial]; norm_num
      have hj1 : ‖A ((1 : ℕ) • quarterTwoPoint)‖ ^ 2 * ‖S ((1 : ℕ) • quarterTwoPoint)‖ ^ 2 = 4 := by
        rw [hA_eq, hS_eq, one_nsmul, twist_quarterTwoPoint_two, twist_quarterTwoPoint_three,
          ← mul_pow, ← norm_mul]
        have hp : (-I + 1) * (I + 1) = (2 : ℂ) := by ring_nf; rw [I_sq]; ring
        rw [hp]; norm_num
      have hj2 : ‖A ((2 : ℕ) • quarterTwoPoint)‖ ^ 2 * ‖S ((2 : ℕ) • quarterTwoPoint)‖ ^ 2 = 0 := by
        rw [hS_eq, twist_nsmul, twist_nsmul, twist_quarterTwoPoint_two, twist_quarterTwoPoint_three]
        have hp : (I ^ 2 + 1 ^ 2 : ℂ) = 0 := by norm_num
        rw [hp]; norm_num
      have hj3 : ‖A ((3 : ℕ) • quarterTwoPoint)‖ ^ 2 * ‖S ((3 : ℕ) • quarterTwoPoint)‖ ^ 2 = 4 := by
        rw [hA_eq, hS_eq, twist_nsmul, twist_nsmul, twist_quarterTwoPoint_two,
          twist_quarterTwoPoint_three, ← mul_pow, ← norm_mul]
        have hp : (-I ^ 3 + 1 ^ 3) * (I ^ 3 + 1 ^ 3) = (2 : ℂ) := by
          rw [show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]
          ring_nf; rw [I_sq]; ring
        rw [hp]; norm_num
      change 1 / 4 * (‖A ((0 : ℕ) • quarterTwoPoint)‖ ^ 2 * ‖S ((0 : ℕ) • quarterTwoPoint)‖ ^ 2 +
        ‖A ((1 : ℕ) • quarterTwoPoint)‖ ^ 2 * ‖S ((1 : ℕ) • quarterTwoPoint)‖ ^ 2 +
        ‖A ((2 : ℕ) • quarterTwoPoint)‖ ^ 2 * ‖S ((2 : ℕ) • quarterTwoPoint)‖ ^ 2 +
        ‖A ((3 : ℕ) • quarterTwoPoint)‖ ^ 2 * ‖S ((3 : ℕ) • quarterTwoPoint)‖ ^ 2) = 2
      rw [hj0, hj1, hj2, hj3]
      norm_num
    rw [hint_val, hmeas, hAx₀, hsum]
    norm_num

end GaloisForLFunctions.ArithmeticWeightTheory
