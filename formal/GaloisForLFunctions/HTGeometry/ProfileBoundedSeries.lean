import GaloisForLFunctions.HTGeometry.GammaProfileProduct
import GaloisForLFunctions.HTGeometry.GevreyJetMonomial
import GaloisForLFunctions.HTGeometry.RegularFactorialProfile
import GaloisForLFunctions.HTGeometry.GevreyFormalSeries

/-!
# Series dominated by a gamma profile

A formal series is *profile bounded* when its coefficients satisfy `‖a_k‖ ≤ c (k+1)^a Θ(k)` for some
constants.  The polynomial correction is what makes the class closed under Cauchy products:
submultiplicativity of the profile handles the two profile factors, the polynomial factors are
absorbed into `(n+1)^{a+b}`, and the number of terms contributes one more power.

The class contains every convergent series, is closed under sums, products and the Euler operator,
and therefore contains every polynomial expression in the jets of a profile-bounded series — which
is exactly what a Taylor defect is built from.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-- A formal series whose coefficients are dominated by the gamma profile up to a fixed polynomial
factor. -/
def HasProfileBound (s β : ℝ) (A : PowerSeries ℂ) : Prop :=
  ∃ (c : ℝ) (a : ℕ), 0 ≤ c ∧
    ∀ k : ℕ, ‖PowerSeries.coeff k A‖ ≤ c * ((k : ℝ) + 1) ^ a * gammaProfile s β k

theorem hasProfileBound_zero {s β : ℝ} : HasProfileBound s β 0 := by
  refine ⟨0, 0, le_rfl, fun k => ?_⟩
  simp

theorem hasProfileBound_of_norm_le {s β : ℝ} {A : PowerSeries ℂ} {c : ℝ} {a : ℕ} (hc : 0 ≤ c)
    (h : ∀ k : ℕ, ‖PowerSeries.coeff k A‖ ≤ c * ((k : ℝ) + 1) ^ a * gammaProfile s β k) :
    HasProfileBound s β A := ⟨c, a, hc, h⟩

/-- **The class is closed under sums.** -/
theorem HasProfileBound.add {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {A B : PowerSeries ℂ}
    (hA : HasProfileBound s β A) (hB : HasProfileBound s β B) : HasProfileBound s β (A + B) := by
  obtain ⟨cA, a, hcA, hA'⟩ := hA
  obtain ⟨cB, b, hcB, hB'⟩ := hB
  refine ⟨cA + cB, max a b, by linarith, fun k => ?_⟩
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpa : ((k : ℝ) + 1) ^ a ≤ ((k : ℝ) + 1) ^ (max a b) :=
    pow_le_pow_right₀ hk (le_max_left _ _)
  have hpb : ((k : ℝ) + 1) ^ b ≤ ((k : ℝ) + 1) ^ (max a b) :=
    pow_le_pow_right₀ hk (le_max_right _ _)
  have hΘ : (0 : ℝ) ≤ gammaProfile s β k := (gammaProfile_pos hs.le hβ k).le
  have h1 : ‖PowerSeries.coeff k A‖ ≤ cA * ((k : ℝ) + 1) ^ (max a b) * gammaProfile s β k := by
    refine le_trans (hA' k) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpa hcA) hΘ
  have h2 : ‖PowerSeries.coeff k B‖ ≤ cB * ((k : ℝ) + 1) ^ (max a b) * gammaProfile s β k := by
    refine le_trans (hB' k) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpb hcB) hΘ
  rw [map_add]
  refine le_trans (norm_add_le _ _) ?_
  nlinarith [h1, h2]

/-- **The class is closed under Cauchy products.** -/
theorem HasProfileBound.mul {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {A B : PowerSeries ℂ}
    (hA : HasProfileBound s β A) (hB : HasProfileBound s β B) : HasProfileBound s β (A * B) := by
  classical
  obtain ⟨cA, a, hcA, hA'⟩ := hA
  obtain ⟨cB, b, hcB, hB'⟩ := hB
  refine ⟨cA * cB, a + b + 1, mul_nonneg hcA hcB, fun n => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hterm : ∀ p : ℕ × ℕ, p.1 + p.2 = n →
      ‖PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 B‖
        ≤ cA * cB * ((n : ℝ) + 1) ^ (a + b) * gammaProfile s β n := by
    intro p hp
    have hp1 : (p.1 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (p.1 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (by omega)
      linarith
    have hp2 : (p.2 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (p.2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (by omega)
      linarith
    have hΘ1 : (0 : ℝ) < gammaProfile s β p.1 := gammaProfile_pos hs.le hβ _
    have hΘ2 : (0 : ℝ) < gammaProfile s β p.2 := gammaProfile_pos hs.le hβ _
    have hsubmul : gammaProfile s β p.1 * gammaProfile s β p.2 ≤ gammaProfile s β n := by
      have h := gammaProfile_mul_le hs hβ p.1 p.2
      rwa [hp] at h
    have hbound1 : ‖PowerSeries.coeff p.1 A‖ ≤ cA * ((n : ℝ) + 1) ^ a * gammaProfile s β p.1 := by
      refine le_trans (hA' p.1) ?_
      refine mul_le_mul_of_nonneg_right ?_ hΘ1.le
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hp1 a) hcA
    have hbound2 : ‖PowerSeries.coeff p.2 B‖ ≤ cB * ((n : ℝ) + 1) ^ b * gammaProfile s β p.2 := by
      refine le_trans (hB' p.2) ?_
      refine mul_le_mul_of_nonneg_right ?_ hΘ2.le
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hp2 b) hcB
    rw [norm_mul]
    calc ‖PowerSeries.coeff p.1 A‖ * ‖PowerSeries.coeff p.2 B‖
        ≤ (cA * ((n : ℝ) + 1) ^ a * gammaProfile s β p.1) *
            (cB * ((n : ℝ) + 1) ^ b * gammaProfile s β p.2) :=
          mul_le_mul hbound1 hbound2 (norm_nonneg _) (by positivity)
      _ = (cA * cB * ((n : ℝ) + 1) ^ (a + b)) *
            (gammaProfile s β p.1 * gammaProfile s β p.2) := by
          rw [pow_add]; ring
      _ ≤ (cA * cB * ((n : ℝ) + 1) ^ (a + b)) * gammaProfile s β n :=
          mul_le_mul_of_nonneg_left hsubmul (by positivity)
      _ = cA * cB * ((n : ℝ) + 1) ^ (a + b) * gammaProfile s β n := by ring
  rw [PowerSeries.coeff_mul]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun p hp => hterm p (by simpa using hp))) ?_
  simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  have hexp : cA * cB * ((n : ℝ) + 1) ^ (a + b + 1) * gammaProfile s β n
      = ((n : ℝ) + 1) * (cA * cB * ((n : ℝ) + 1) ^ (a + b) * gammaProfile s β n) := by
    rw [pow_succ]
    ring
  rw [hexp]
  push_cast
  exact le_rfl

/-- **The class is closed under powers.** -/
theorem HasProfileBound.pow {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {A : PowerSeries ℂ}
    (hA : HasProfileBound s β A) : ∀ e : ℕ, HasProfileBound s β (A ^ e)
  | 0 => by
      rw [pow_zero]
      refine ⟨1, 0, zero_le_one, fun k => ?_⟩
      have hΘ : (0 : ℝ) < gammaProfile s β k := gammaProfile_pos hs.le hβ _
      by_cases hk : k = 0
      · subst hk
        rw [PowerSeries.coeff_zero_one]
        simp only [pow_zero, one_mul, mul_one, norm_one]
        rw [gammaProfile]
        norm_num
      · rw [PowerSeries.coeff_one, if_neg hk, norm_zero]
        positivity
  | (e + 1) => by
      rw [pow_succ]
      exact (HasProfileBound.pow hs hβ hA e).mul hs hβ hA

theorem hasProfileBound_one {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    HasProfileBound s β 1 := by
  refine ⟨1, 0, zero_le_one, fun k => ?_⟩
  have hΘ : (0 : ℝ) < gammaProfile s β k := gammaProfile_pos hs.le hβ _
  by_cases hk : k = 0
  · subst hk
    rw [PowerSeries.coeff_zero_one]
    simp only [pow_zero, one_mul, mul_one, norm_one]
    rw [gammaProfile]
    norm_num
  · rw [PowerSeries.coeff_one, if_neg hk, norm_zero]
    positivity

/-! ### Products of tails, with the polynomial correction -/

/-- **Two profile-bounded factors vanishing below order `N+1` gain a shifted profile value.** -/
theorem norm_coeff_mul_le_of_vanishing_poly {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {N : ℕ}
    {A B : PowerSeries ℂ} {cA cB : ℝ} {a b : ℕ} (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hA : ∀ k : ℕ, ‖PowerSeries.coeff k A‖ ≤ cA * ((k : ℝ) + 1) ^ a * gammaProfile s β k)
    (hB : ∀ k : ℕ, ‖PowerSeries.coeff k B‖ ≤ cB * ((k : ℝ) + 1) ^ b * gammaProfile s β k)
    (hA0 : ∀ k, k ≤ N → PowerSeries.coeff k A = 0)
    (hB0 : ∀ k, k ≤ N → PowerSeries.coeff k B = 0)
    (n : ℕ) :
    ‖PowerSeries.coeff n (A * B)‖
      ≤ cA * cB * ((n : ℝ) + 1) ^ (a + b + 1) *
        (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
  classical
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hEnd : (0 : ℝ) < gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1)) :=
    mul_pos (gammaProfile_pos hs.le hβ _) (gammaProfile_pos hs.le hβ _)
  have hterm : ∀ p : ℕ × ℕ, p.1 + p.2 = n →
      ‖PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 B‖
        ≤ cA * cB * ((n : ℝ) + 1) ^ (a + b) *
          (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
    intro p hp
    have hnn : (0 : ℝ) ≤ cA * cB * ((n : ℝ) + 1) ^ (a + b) *
        (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
      have h0 : (0 : ℝ) ≤ cA * cB := mul_nonneg hcA hcB
      have h1 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (a + b) := by positivity
      exact mul_nonneg (mul_nonneg h0 h1) hEnd.le
    by_cases h1 : p.1 ≤ N
    · rw [hA0 p.1 h1, zero_mul, norm_zero]
      exact hnn
    by_cases h2 : p.2 ≤ N
    · rw [hB0 p.2 h2, mul_zero, norm_zero]
      exact hnn
    push Not at h1 h2
    have hp1 : N + 1 ≤ p.1 := h1
    have hple : p.1 + (N + 1) ≤ n := by omega
    have hp2 : p.2 = n - p.1 := by omega
    have hend := gammaProfilePair_le_endpoint hs hβ (p := N + 1) (i := p.1) (n := n) hp1 hple
    have hc1 : (p.1 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (p.1 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (by omega)
      linarith
    have hc2 : (p.2 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (p.2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (by omega)
      linarith
    have hb1 : ‖PowerSeries.coeff p.1 A‖ ≤ cA * ((n : ℝ) + 1) ^ a * gammaProfile s β p.1 := by
      refine le_trans (hA p.1) ?_
      refine mul_le_mul_of_nonneg_right ?_ (gammaProfile_pos hs.le hβ _).le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc1 a) hcA
    have hb2 : ‖PowerSeries.coeff p.2 B‖ ≤ cB * ((n : ℝ) + 1) ^ b * gammaProfile s β p.2 := by
      refine le_trans (hB p.2) ?_
      refine mul_le_mul_of_nonneg_right ?_ (gammaProfile_pos hs.le hβ _).le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc2 b) hcB
    rw [norm_mul]
    calc ‖PowerSeries.coeff p.1 A‖ * ‖PowerSeries.coeff p.2 B‖
        ≤ (cA * ((n : ℝ) + 1) ^ a * gammaProfile s β p.1) *
            (cB * ((n : ℝ) + 1) ^ b * gammaProfile s β p.2) :=
          mul_le_mul hb1 hb2 (norm_nonneg _)
            (mul_nonneg (mul_nonneg hcA (by positivity)) (gammaProfile_pos hs.le hβ _).le)
      _ = (cA * cB * ((n : ℝ) + 1) ^ (a + b)) *
            (gammaProfile s β p.1 * gammaProfile s β (n - p.1)) := by
          rw [hp2, pow_add]; ring
      _ ≤ (cA * cB * ((n : ℝ) + 1) ^ (a + b)) *
            (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) :=
          mul_le_mul_of_nonneg_left hend (by positivity)
      _ = cA * cB * ((n : ℝ) + 1) ^ (a + b) *
            (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by ring
  rw [PowerSeries.coeff_mul]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun p hp => hterm p (by simpa using hp))) ?_
  simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  have hexp : cA * cB * ((n : ℝ) + 1) ^ (a + b + 1) *
      (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1)))
      = ((n : ℝ) + 1) * (cA * cB * ((n : ℝ) + 1) ^ (a + b) *
        (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1)))) := by
    rw [pow_succ]
    ring
  rw [hexp]
  push_cast
  exact le_rfl

/-! ### Jet monomials -/

theorem jetMonomialValue_single_pow {ι A : Type*} [CommRing A] (L : ι → A) (i : ι) (e : ℕ) :
    jetMonomialValue L (Finsupp.single i e) = L i ^ e := by
  have h : (Finsupp.single i e).prod (fun (i : ι) (k : ℕ) => L i ^ k) = L i ^ e :=
    Finsupp.prod_single_index (pow_zero (L i))
  rw [jetMonomialValue, h]

/-- **The class is closed under jet monomials.** -/
theorem HasProfileBound.jetMonomialValue {ι : Type*} {s β : ℝ} (hs : 0 < s) (hβ : 0 < β)
    {L : ι → PowerSeries ℂ} (hL : ∀ i, HasProfileBound s β (L i)) (α : ι →₀ ℕ) :
    HasProfileBound s β (jetMonomialValue L α) := by
  classical
  refine Finsupp.induction α ?_ ?_
  · rw [jetMonomialValue_zero]
    exact hasProfileBound_one hs hβ
  · intro i e f _ _ ih
    rw [jetMonomialValue_add, jetMonomialValue_single_pow]
    exact ((hL i).pow hs hβ e).mul hs hβ ih

/-- **A jet monomial of degree at least two in a tail gains a shifted profile value.**  Splitting off
one factor leaves a monomial of degree at least one, which vanishes below the same order, and the
two-tail convolution bound applies. -/
theorem norm_coeff_jetMonomialValue_le_of_two_le {ι : Type*} [DecidableEq ι] {s β : ℝ}
    (hs : 0 < s) (hβ : 0 < β) {N : ℕ} {L : ι → PowerSeries ℂ}
    (hL : ∀ i, HasProfileBound s β (L i))
    (hL0 : ∀ i, (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ L i)
    {α : ι →₀ ℕ} (hα : 2 ≤ jetDegree α) :
    ∃ (c : ℝ) (a : ℕ), 0 ≤ c ∧ ∀ n : ℕ,
      ‖PowerSeries.coeff n (jetMonomialValue L α)‖
        ≤ c * ((n : ℝ) + 1) ^ a *
          (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
  classical
  have hαne : α ≠ 0 := by
    intro h
    rw [h] at hα
    rw [jetDegree] at hα
    simp at hα
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hαne
  have hαi : 1 ≤ α i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  set γ : ι →₀ ℕ := Finsupp.single i (α i - 1) + Finsupp.erase i α with hγ
  have hdecomp : α = Finsupp.single i 1 + γ := by
    rw [hγ, ← add_assoc, ← Finsupp.single_add, show 1 + (α i - 1) = α i from by omega,
      Finsupp.single_add_erase]
  have hdeg : jetDegree α = 1 + jetDegree γ := by
    conv_lhs => rw [hdecomp]
    rw [jetDegree_add, jetDegree_single]
  have hdegγ : 1 ≤ jetDegree γ := by omega
  have hprod : jetMonomialValue L α = L i * jetMonomialValue L γ := by
    conv_lhs => rw [hdecomp]
    rw [jetMonomialValue_add, jetMonomialValue_single]
  have hdvdγ : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ jetMonomialValue L γ :=
    X_pow_dvd_jetMonomialValue hL0 (jetDegree γ) γ rfl hdegγ
  have hvanγ : ∀ k, k ≤ N → PowerSeries.coeff k (jetMonomialValue L γ) = 0 := by
    intro k hk
    exact (PowerSeries.X_pow_dvd_iff.mp hdvdγ) k (by omega)
  have hvani : ∀ k, k ≤ N → PowerSeries.coeff k (L i) = 0 := by
    intro k hk
    exact (PowerSeries.X_pow_dvd_iff.mp (hL0 i)) k (by omega)
  obtain ⟨cA, a, hcA, hA⟩ := hL i
  obtain ⟨cB, b, hcB, hB⟩ := HasProfileBound.jetMonomialValue hs hβ hL γ
  refine ⟨cA * cB, a + b + 1, mul_nonneg hcA hcB, fun n => ?_⟩
  rw [hprod]
  exact norm_coeff_mul_le_of_vanishing_poly hs hβ hcA hcB hA hB hvani hvanγ n

/-! ### Convergent series are profile bounded -/

open Filter Topology

theorem exists_pow_le_const_mul_factorial (x : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, x ^ k ≤ c * ((k ! : ℕ) : ℝ) := by
  classical
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop x
  have hev : ∀ᶠ k : ℕ in atTop, x ^ k / ((k ! : ℕ) : ℝ) ≤ 1 := by
    have hmem : {y : ℝ | y < 1} ∈ 𝓝 (0 : ℝ) := gt_mem_nhds (by norm_num)
    filter_upwards [h hmem] with k hk
    exact le_of_lt hk
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  refine ⟨1 + ∑ j ∈ Finset.range K, |x| ^ j, by positivity, fun k => ?_⟩
  have hfac1 : (1 : ℝ) ≤ ((k ! : ℕ) : ℝ) := by
    have : 1 ≤ k ! := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
    exact_mod_cast this
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range K, |x| ^ j :=
    Finset.sum_nonneg fun j _ => by positivity
  by_cases hk : K ≤ k
  · have h1 := hK k hk
    rw [div_le_one (by linarith)] at h1
    nlinarith [h1, hfac1, hsum0]
  · push Not at hk
    have hmem : k ∈ Finset.range K := Finset.mem_range.mpr hk
    have h1 : x ^ k ≤ |x| ^ k := le_trans (le_abs_self _) (le_of_eq (abs_pow x k))
    have h2 : |x| ^ k ≤ ∑ j ∈ Finset.range K, |x| ^ j :=
      Finset.single_le_sum (f := fun j : ℕ => |x| ^ j) (fun j _ => by positivity) hmem
    nlinarith [h1, h2, hfac1, hsum0]

theorem exists_pow_le_const_mul_factorial_rpow {s : ℝ} (hs : 0 < s) {M : ℝ} (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, M ^ k ≤ c * (((k ! : ℕ) : ℝ)) ^ s := by
  obtain ⟨c₀, hc₀, h⟩ := exists_pow_le_const_mul_factorial (M ^ (1 / s))
  refine ⟨c₀ ^ s, Real.rpow_pos_of_pos hc₀ s, fun k => ?_⟩
  have hroot : (0 : ℝ) < M ^ (1 / s) := Real.rpow_pos_of_pos hM _
  have hid : ((M ^ (1 / s)) ^ k) ^ s = M ^ k := by
    rw [← Real.rpow_natCast (M ^ (1 / s)) k, ← Real.rpow_mul hM.le,
      show 1 / s * (k : ℝ) = (k : ℝ) * (1 / s) by ring, Real.rpow_mul hM.le,
      ← Real.rpow_mul (Real.rpow_nonneg hM.le _),
      show 1 / s * s = 1 by field_simp, Real.rpow_one, Real.rpow_natCast]
  have hstep : ((M ^ (1 / s)) ^ k) ^ s ≤ (c₀ * ((k ! : ℕ) : ℝ)) ^ s :=
    Real.rpow_le_rpow (by positivity) (h k) hs.le
  rw [hid] at hstep
  refine le_trans hstep (le_of_eq ?_)
  rw [Real.mul_rpow hc₀.le (Nat.cast_nonneg _)]

/-- **A convergent series is profile bounded.**  The gamma profile beats every geometric growth. -/
theorem hasProfileBound_of_isGevreySeries_zero {s β : ℝ} (hs : 0 < s) (hirr : Irrational s)
    (hβ : 0 < β) {A : PowerSeries ℂ} (hA : IsGevreySeries 0 A) :
    HasProfileBound s β A := by
  obtain ⟨C, L, hC, hL, hbd⟩ := hA
  have hprof := isRegularFactorialProfile_gammaProfile_of_irrational hs hirr hβ
  have hc₁ : 0 < β * (s + 1 - ((⌈s⌉₊ : ℕ) : ℝ)) ^ s := hprof.c₁_pos
  set c₁ : ℝ := β * (s + 1 - ((⌈s⌉₊ : ℕ) : ℝ)) ^ s with hc₁def
  have hlow : ∀ k : ℕ, c₁ ^ k * (((k ! : ℕ) : ℝ)) ^ s ≤ gammaProfile s β k := by
    intro k
    have h := hprof.block_lower (a := 0) (b := k) (Nat.zero_le k)
    rw [gammaProfile_zero, Nat.factorial_zero, Nat.sub_zero] at h
    simpa using h
  obtain ⟨c, hc, hpow⟩ := exists_pow_le_const_mul_factorial_rpow hs
    (M := L / c₁) (by positivity)
  refine ⟨C * c, 0, by positivity, fun k => ?_⟩
  have hgeo : L ^ k = c₁ ^ k * (L / c₁) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hAk : ‖PowerSeries.coeff k A‖ ≤ C * L ^ k := by
    have h := hbd k
    simpa using h
  have hstep : C * L ^ k ≤ C * c * gammaProfile s β k := by
    rw [hgeo]
    have h1 : (L / c₁) ^ k ≤ c * (((k ! : ℕ) : ℝ)) ^ s := hpow k
    have h2 : c₁ ^ k * ((L / c₁) ^ k) ≤ c₁ ^ k * (c * (((k ! : ℕ) : ℝ)) ^ s) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : c₁ ^ k * (c * (((k ! : ℕ) : ℝ)) ^ s) = c * (c₁ ^ k * (((k ! : ℕ) : ℝ)) ^ s) := by
      ring
    have h4 : c * (c₁ ^ k * (((k ! : ℕ) : ℝ)) ^ s) ≤ c * gammaProfile s β k :=
      mul_le_mul_of_nonneg_left (hlow k) hc.le
    nlinarith [h2, h3, h4, hC.le]
  calc ‖PowerSeries.coeff k A‖ ≤ C * L ^ k := hAk
    _ ≤ C * c * gammaProfile s β k := hstep
    _ = C * c * ((k : ℝ) + 1) ^ (0 : ℕ) * gammaProfile s β k := by rw [pow_zero]; ring

/-! ### The defect term -/

/-- **A profile-bounded multiple of a jet monomial of degree at least two in a tail.** -/
theorem norm_coeff_mul_jetMonomialValue_le_of_two_le {ι : Type*} [DecidableEq ι] {s β : ℝ}
    (hs : 0 < s) (hβ : 0 < β) {N : ℕ} {L : ι → PowerSeries ℂ} {D : PowerSeries ℂ}
    (hD : HasProfileBound s β D)
    (hL : ∀ i, HasProfileBound s β (L i))
    (hL0 : ∀ i, (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ L i)
    {α : ι →₀ ℕ} (hα : 2 ≤ jetDegree α) :
    ∃ (c : ℝ) (a : ℕ), 0 ≤ c ∧ ∀ n : ℕ,
      ‖PowerSeries.coeff n (D * jetMonomialValue L α)‖
        ≤ c * ((n : ℝ) + 1) ^ a *
          (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
  classical
  have hαne : α ≠ 0 := by
    intro h
    rw [h] at hα
    rw [jetDegree] at hα
    simp at hα
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hαne
  have hαi : 1 ≤ α i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  set γ : ι →₀ ℕ := Finsupp.single i (α i - 1) + Finsupp.erase i α with hγ
  have hdecomp : α = Finsupp.single i 1 + γ := by
    rw [hγ, ← add_assoc, ← Finsupp.single_add, show 1 + (α i - 1) = α i from by omega,
      Finsupp.single_add_erase]
  have hdeg : jetDegree α = 1 + jetDegree γ := by
    conv_lhs => rw [hdecomp]
    rw [jetDegree_add, jetDegree_single]
  have hdegγ : 1 ≤ jetDegree γ := by omega
  have hprod : D * jetMonomialValue L α = L i * (D * jetMonomialValue L γ) := by
    conv_lhs => rw [hdecomp]
    rw [jetMonomialValue_add, jetMonomialValue_single]
    ring
  have hdvdγ : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ D * jetMonomialValue L γ :=
    Dvd.dvd.mul_left (X_pow_dvd_jetMonomialValue hL0 (jetDegree γ) γ rfl hdegγ) _
  have hvanγ : ∀ k, k ≤ N → PowerSeries.coeff k (D * jetMonomialValue L γ) = 0 := by
    intro k hk
    exact (PowerSeries.X_pow_dvd_iff.mp hdvdγ) k (by omega)
  have hvani : ∀ k, k ≤ N → PowerSeries.coeff k (L i) = 0 := by
    intro k hk
    exact (PowerSeries.X_pow_dvd_iff.mp (hL0 i)) k (by omega)
  obtain ⟨cA, a, hcA, hA⟩ := hL i
  obtain ⟨cB, b, hcB, hB⟩ := hD.mul hs hβ (HasProfileBound.jetMonomialValue hs hβ hL γ)
  refine ⟨cA * cB, a + b + 1, mul_nonneg hcA hcB, fun n => ?_⟩
  rw [hprod]
  exact norm_coeff_mul_le_of_vanishing_poly hs hβ hcA hcB hA hB hvani hvanγ n

end GaloisForLFunctions.HTGeometry
