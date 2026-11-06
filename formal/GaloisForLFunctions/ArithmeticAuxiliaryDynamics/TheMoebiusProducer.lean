import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMoebiusPartOfAProducer
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheUncertaintyLawOfAProducer

/-!
# The Möbius producer

The sawtooth `F_T` is negative at far `r`, and integrality forbids that. The obvious repair is one
huge letter, a multiple of `lcm(1, …, T)`, and it forces factorial alphabets. Far `r` can also be
handled by **entangled letters**: `G P` for every prime `P ≤ T`, with `G > T`, all with the same
weight `T/G`.

Let `f(r) = F_T(r) + (T/G) Σ_P (r mod G P)`.

* If `r mod G P ≥ G` for some `P`, that letter alone pays `T ≥ −F_T(r)`.
* If `r mod G P < G` for all `P`, all these residues agree: they equal `s = r mod G`, because any two
  letters share the factor `G`. So `r ≡ s` modulo every prime up to `T`, hence modulo every squarefree
  `b ≤ T`, and `F_T(r) = F_T(s)`. The problem returns to the near range, where `F_T` is known from the
  Mertens function, and the letters contribute `Z s`, with `Z = π(T) T / G`.

So `f ≥ 0` everywhere and `f ≥ 1` on `[1, G)` as soon as `Z` beats `|m(T)| + 2 η (1 + log G)`. The result
is an **explicit integer producer on a polynomial alphabet**, with a rate read from the Mertens
function. Integrality costs nothing, and the factorial alphabet of the Farkas construction is not
needed.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The primes up to `T`. -/
def primesUpTo (T : ℕ) : Finset ℕ := (Icc 1 T).filter Nat.Prime

/-- The entangled letters at `r`. -/
def entangled (T G r : ℕ) : ℝ := ∑ P ∈ primesUpTo T, ((r % (G * P) : ℕ) : ℝ)

/-- The full weight of the Möbius producer. -/
def moebiusWeight (T G r : ℕ) : ℝ := mobiusPart T r + (T : ℝ) / G * entangled T G r

/-- The near coefficient `Z = π(T) T / G`. -/
def nearCoefficient (T G : ℕ) : ℝ := (T : ℝ) / G * ((primesUpTo T).card : ℝ)

private lemma mem_primesUpTo {T P : ℕ} : P ∈ primesUpTo T ↔ P.Prime ∧ P ≤ T := by
  simp only [primesUpTo, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.pos, h2⟩, h1⟩

/-- `F_T` only sees `r` modulo the primes up to `T`. -/
theorem mobiusPart_congr {T r s : ℕ} (hsr : s ≤ r) (h : ∀ P ∈ primesUpTo T, P ∣ r - s) :
    mobiusPart T r = mobiusPart T s := by
  refine sum_congr rfl fun b hb => ?_
  obtain ⟨hb1, hbT⟩ := mem_Icc.mp hb
  by_cases hμ : ArithmeticFunction.moebius b = 0
  · simp [hμ]
  · have hsq : Squarefree b := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hμ
    have hdvd : b ∣ r - s := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq]
      refine Finset.prod_primes_dvd (r - s) (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
        fun p hp => h p ?_
      exact mem_primesUpTo.mpr ⟨Nat.prime_of_mem_primeFactors hp,
        (Nat.le_of_mem_primeFactors hp).trans hbT⟩
    have hmod : s % b = r % b := (Nat.modEq_iff_dvd' hsr).mpr hdvd
    rw [hmod]

/-- **All residues small: the near range.** If every entangled residue is below `G`, then the weight
at `r` is the weight at the near point `s = r mod G`. -/
theorem moebiusWeight_of_small {T G r : ℕ} (hG : 0 < G) (h : ∀ P ∈ primesUpTo T, r % (G * P) < G) :
    moebiusWeight T G r = mobiusPart T (r % G) + nearCoefficient T G * ((r % G : ℕ) : ℝ) := by
  have hres : ∀ P ∈ primesUpTo T, r % (G * P) = r % G := by
    intro P hP
    have h1 := Nat.mod_mul_right_mod r G P
    rw [Nat.mod_eq_of_lt (h P hP)] at h1
    exact h1
  have hcong : mobiusPart T r = mobiusPart T (r % G) := by
    refine mobiusPart_congr (Nat.mod_le r G) fun P hP => ?_
    have hd : G * P ∣ r - r % (G * P) := Nat.dvd_sub_mod r
    rw [hres P hP] at hd
    exact (dvd_mul_left P G).trans hd
  have hent : entangled T G r = ((primesUpTo T).card : ℝ) * ((r % G : ℕ) : ℝ) := by
    rw [entangled, sum_congr rfl fun P hP => by rw [hres P hP], sum_const, nsmul_eq_mul]
  rw [moebiusWeight, hcong, hent, nearCoefficient]
  ring

/-- **The positivity of the Möbius producer.** Under the near condition `Q ≤ Z`, the weight is
nonnegative everywhere and at least `1` on the near points. -/
theorem moebiusWeight_nonneg {T G : ℕ} (hG : T < G) {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hZ : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ nearCoefficient T G) (r : ℕ) :
    0 ≤ moebiusWeight T G r ∧ ((∀ P ∈ primesUpTo T, r % (G * P) < G) → 1 ≤ r % G →
      1 ≤ moebiusWeight T G r) := by
  have hG0 : 0 < G := by omega
  have hGR : (0 : ℝ) < G := by exact_mod_cast hG0
  have hnear : (∀ P ∈ primesUpTo T, r % (G * P) < G) → 1 ≤ r % G → 1 ≤ moebiusWeight T G r := by
    intro hsmall hs1
    rw [moebiusWeight_of_small hG0 hsmall]
    have hs0 : (0 : ℝ) < ((r % G : ℕ) : ℝ) := by exact_mod_cast hs1
    have hsG : ((r % G : ℕ) : ℝ) ≤ G := by exact_mod_cast (Nat.mod_lt r hG0).le
    have hlog : Real.log ((r % G : ℕ) : ℝ) ≤ Real.log G := Real.log_le_log hs0 hsG
    have hnearlaw := abs_mobiusPart_sub_one_le hs1 hη hM
    have hbound : |mobiusPart T (r % G) - 1| ≤ ((r % G : ℕ) : ℝ) * nearCoefficient T G := by
      refine hnearlaw.trans (mul_le_mul_of_nonneg_left (le_trans ?_ hZ) hs0.le)
      gcongr
    have := (abs_le.mp hbound).1
    linarith
  refine ⟨?_, hnear⟩
  by_cases hsmall : ∀ P ∈ primesUpTo T, r % (G * P) < G
  · by_cases hs : 1 ≤ r % G
    · have := hnear hsmall hs
      linarith
    · have hs0 : r % G = 0 := by omega
      rw [moebiusWeight_of_small hG0 hsmall, hs0]
      have hF : mobiusPart T 0 = 0 := by
        simp [mobiusPart]
      rw [hF]
      simp
  · push Not at hsmall
    obtain ⟨P, hP, hlarge⟩ := hsmall
    have hent : (G : ℝ) ≤ entangled T G r := by
      have h1 : ((r % (G * P) : ℕ) : ℝ) ≤ entangled T G r :=
        Finset.single_le_sum (f := fun Q => ((r % (G * Q) : ℕ) : ℝ))
          (fun _ _ => Nat.cast_nonneg _) hP
      have h2 : (G : ℝ) ≤ ((r % (G * P) : ℕ) : ℝ) := by exact_mod_cast hlarge
      linarith
    have hpay : (T : ℝ) ≤ (T : ℝ) / G * entangled T G r := by
      calc (T : ℝ) = (T : ℝ) / G * G := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hent (by positivity)
    have hF := (abs_le.mp (abs_mobiusPart_le T r)).1
    rw [moebiusWeight]
    linarith

/-- The window of the Möbius producer is `[1, G)`. -/
theorem one_le_moebiusWeight {T G : ℕ} (hG : T < G) {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y)
    (hZ : |mobiusHarmonic T| + 2 * η * (1 + Real.log G) ≤ nearCoefficient T G)
    {r : ℕ} (hr : r ∈ Ico 1 G) : 1 ≤ moebiusWeight T G r := by
  obtain ⟨hr1, hrG⟩ := mem_Ico.mp hr
  refine (moebiusWeight_nonneg hG hη hM hZ r).2 (fun P hP => ?_) ?_
  · have hPpos : 0 < P := (mem_primesUpTo.mp hP).1.pos
    have hle : G ≤ G * P := Nat.le_mul_of_pos_right G hPpos
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hrG
  · rw [Nat.mod_eq_of_lt hrG]
    exact hr1

/-- The harmonic slope of the Möbius part. -/
def mobiusSlope (T : ℕ) : ℝ :=
  ∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) * Real.log b

/-- The pronic series of the Möbius part: its slope is `Σ F_T(r) / (r (r + 1))`. -/
theorem hasSum_mobiusPart (T : ℕ) :
    HasSum (fun j : ℕ => mobiusPart T (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) (mobiusSlope T) := by
  have hfun : (fun j : ℕ => mobiusPart T (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) = fun j : ℕ =>
      ∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ)) *
        (((j + 1) % b : ℕ) / (b : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    funext j
    rw [mobiusPart, sum_div]
    refine sum_congr rfl fun b _ => ?_
    ring
  rw [hfun, mobiusSlope]
  refine hasSum_sum fun b hb => ?_
  have hb1 := (mem_Icc.mp hb).1
  have h := (hasSum_mod_div_pronic hb1).mul_left (-(ArithmeticFunction.moebius b : ℝ))
  have hval : -(ArithmeticFunction.moebius b : ℝ) * (Real.log b / b) =
      (-(ArithmeticFunction.moebius b : ℝ) / b) * Real.log b := by ring
  rwa [hval] at h

private lemma sum_ite_lt_le {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (n G : ℕ) :
    ∑ j ∈ range n, (if j + 1 < G then f j else 0) ≤ ∑ j ∈ range (G - 1), f j := by
  classical
  rw [← sum_filter]
  refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hf j
  have := (mem_filter.mp hj).2
  exact mem_range.mpr (by omega)

/-- **The slope of the Möbius part is at most the main term.** Using only the near law,
`λ(T) ≤ 1 − 1/G + Q (1 + log G) + T/G`, with `Q = |m(T)| + 2 η (1 + log G)`. No prime number theorem
enters. -/
theorem mobiusSlope_le {T G : ℕ} (hG : 2 ≤ G) {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y) :
    mobiusSlope T ≤ 1 - 1 / (G : ℝ) +
      (|mobiusHarmonic T| + 2 * η * (1 + Real.log G)) * (1 + Real.log G) + (T : ℝ) / G := by
  have hGR : (0 : ℝ) < G := by exact_mod_cast (by omega : 0 < G)
  have hlogG : 0 ≤ Real.log (G : ℝ) := Real.log_natCast_nonneg G
  set Q : ℝ := |mobiusHarmonic T| + 2 * η * (1 + Real.log G) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine le_of_tendsto' (hasSum_mobiusPart T).tendsto_sum_nat fun n => ?_
  -- Pointwise bound on the terms.
  have hterm : ∀ j : ℕ, mobiusPart T (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) ≤
      (if j + 1 < G then realStep 1 j else 0) + (if j + 1 < G then Q * (1 / ((j : ℝ) + 2)) else 0) +
        (T : ℝ) * tailStep (G - 1) 1 j := by
    intro j
    have hpron : 0 < ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
    have hR := IsProducer.realStep_one j
    by_cases hj : j + 1 < G
    · rw [if_pos hj, if_pos hj, tailStep, if_neg (by omega), mul_zero, add_zero, hR,
        div_le_iff₀ hpron]
      have hnear := (abs_le.mp (abs_mobiusPart_sub_one_le (T := T) (s := j + 1) (by omega) hη hM)).2
      have hlog : Real.log ((j + 1 : ℕ) : ℝ) ≤ Real.log G :=
        Real.log_le_log (by positivity) (by exact_mod_cast hj.le)
      have hQbound : |mobiusHarmonic T| + 2 * η * (1 + Real.log ((j + 1 : ℕ) : ℝ)) ≤ Q := by
        rw [hQ]
        gcongr
      have hle : mobiusPart T (j + 1) ≤ 1 + ((j : ℝ) + 1) * Q := by
        have h1 := mul_le_mul_of_nonneg_left hQbound (by positivity : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))
        push_cast at h1 hnear
        linarith
      have hval : (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) + Q * (1 / ((j : ℝ) + 2))) *
          (((j : ℝ) + 1) * ((j : ℝ) + 2)) = 1 + ((j : ℝ) + 1) * Q := by
        field_simp
      rw [hval]
      exact hle
    · rw [if_neg hj, if_neg hj, tailStep, if_pos (by omega), zero_add, zero_add, hR,
        div_le_iff₀ hpron]
      have hF := (abs_le.mp (abs_mobiusPart_le T (j + 1))).2
      have hval : (T : ℝ) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) *
          (((j : ℝ) + 1) * ((j : ℝ) + 2)) = T := by
        field_simp
      rw [hval]
      exact hF
  refine (sum_le_sum fun j _ => hterm j).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
  -- The window mass.
  have hA : ∑ j ∈ range n, (if j + 1 < G then realStep 1 j else 0) ≤ 1 - 1 / (G : ℝ) := by
    refine (sum_ite_lt_le (fun j => realStep_nonneg zero_le_one j) n G).trans (le_of_eq ?_)
    rw [sum_range_realStep, Real.rpow_neg_one, ← one_div]
    congr 2
    have : ((G - 1 : ℕ) : ℝ) = (G : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]; ring
  -- The harmonic mass.
  have hB : ∑ j ∈ range n, (if j + 1 < G then Q * (1 / ((j : ℝ) + 2)) else 0) ≤
      Q * (1 + Real.log G) := by
    refine (sum_ite_lt_le (fun j => by positivity) n G).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hQ0
    have hH := harmonic_le_one_add_log G
    rw [harmonic_eq_sum_Icc] at hH
    push_cast at hH
    obtain ⟨g, rfl⟩ : ∃ g, G = g + 2 := ⟨G - 2, by omega⟩
    have hrew : g + 2 - 1 = g + 1 := by omega
    rw [hrew]
    have hIcc : ∑ j ∈ range (g + 1), (1 : ℝ) / ((j : ℝ) + 2) ≤
        ∑ i ∈ Icc 1 (g + 2), ((i : ℝ))⁻¹ := by
      have hind : ∀ m : ℕ, ∑ j ∈ range m, (1 : ℝ) / ((j : ℝ) + 2) ≤
          ∑ i ∈ Icc 1 (m + 1), ((i : ℝ))⁻¹ := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega)]
          have hc : (((m + 1 + 1 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / ((m : ℝ) + 2) := by
            push_cast
            rw [one_div]
            congr 1
            ring
          rw [hc]
          linarith
      exact hind (g + 1)
    exact hIcc.trans hH
  -- The tail mass.
  have hC : ∑ j ∈ range n, tailStep (G - 1) 1 j ≤ 1 / (G : ℝ) := by
    refine (sum_range_tailStep_le zero_le_one (G - 1) n).trans (le_of_eq ?_)
    have : ((G - 1 : ℕ) : ℝ) + 1 = (G : ℝ) := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this, Real.rpow_neg_one, one_div]
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hCmul : (T : ℝ) * ∑ j ∈ range n, tailStep (G - 1) 1 j ≤ (T : ℝ) / G := by
    calc _ ≤ (T : ℝ) * (1 / (G : ℝ)) := mul_le_mul_of_nonneg_left hC hT0
      _ = _ := by ring
  linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
