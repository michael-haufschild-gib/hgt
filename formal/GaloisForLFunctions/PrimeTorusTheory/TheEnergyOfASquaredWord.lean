import GaloisForLFunctions.PrimeTorusTheory.SquaredWordsForbidAlignment

/-!
# The energy of a squared word

The phase of a squared word `c` at the letters `x + a + b` has integer coefficients
`r(n) = Σ_{a+b=n} c_a c_b`. Its precision is governed by the additive energy `Σ_n r(n)²`, not by the
mass `(Σ|c_a|)²`.

Most sign patterns on `[0, M]` have energy `≲ M²`: the fourth moment of a Rademacher sum at each
frequency is at most three times the squared variance. The moment map cannot separate them once
`Π_{j≤k}(C(M+1,j+1)+1) < 2^M`, and the difference of two low energy patterns has low energy, since
the energy is a fourth power mean on the Fourier side.

* `energy_eq`: `Q Σ_n r(n)² = Σ_{j<Q} |Σ_a c_a e(ja/Q)|⁴`.
* `sum_powerset_four`: the fourth moment of a Rademacher sum.
* `exists_lowEnergy_word`: a word of order `k`, with `c_0 ≠ 0`, of energy at most `12 (M+1)²`.
-/

open Finset

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-! ### Additive characters -/

/-- The root of unity `e(1/Q)`. -/
def omega (Q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / Q)

/-- The additive character `n ↦ e(jn/Q)`. -/
def chi (Q j n : ℕ) : ℂ := omega Q ^ (j * n)

theorem omega_primitive {Q : ℕ} (hQ : 0 < Q) : IsPrimitiveRoot (omega Q) Q :=
  Complex.isPrimitiveRoot_exp Q hQ.ne'

theorem norm_omega {Q : ℕ} (hQ : 0 < Q) : ‖omega Q‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (omega_primitive hQ).pow_eq_one hQ.ne'

theorem norm_chi {Q : ℕ} (hQ : 0 < Q) (j n : ℕ) : ‖chi Q j n‖ = 1 := by
  rw [chi, norm_pow, norm_omega hQ, one_pow]

theorem chi_add (Q j a b : ℕ) : chi Q j (a + b) = chi Q j a * chi Q j b := by
  rw [chi, chi, chi, mul_add, pow_add]

theorem conj_mul_self_of_norm {z : ℂ} (hz : ‖z‖ = 1) : (starRingEnd ℂ) z * z = 1 := by
  rw [Complex.conj_mul', hz]
  simp

/-- Orthogonality of the additive characters on `[0, Q)`. -/
theorem sum_chi_mul_conj {Q n m : ℕ} (hQ : 0 < Q) (hn : n < Q) (hm : m < Q) :
    ∑ j ∈ range Q, chi Q j n * (starRingEnd ℂ) (chi Q j m) = if n = m then (Q : ℂ) else 0 := by
  have hprim := omega_primitive hQ
  set ζ : ℂ := omega Q ^ n * (starRingEnd ℂ) (omega Q ^ m) with hζ
  have hterm : ∀ j, chi Q j n * (starRingEnd ℂ) (chi Q j m) = ζ ^ j := by
    intro j
    rw [hζ, mul_pow, ← map_pow, chi, chi, ← pow_mul, ← pow_mul, mul_comm n j, mul_comm m j]
  simp only [hterm]
  have hnm : ‖omega Q ^ m‖ = 1 := by rw [norm_pow, norm_omega hQ, one_pow]
  have hconj := conj_mul_self_of_norm hnm
  split_ifs with h
  · subst h
    have : ζ = 1 := by
      rw [hζ, mul_comm]
      exact hconj
    simp [this]
  · have hne : ζ ≠ 1 := by
      intro h1
      apply h
      apply hprim.pow_inj hn hm
      calc omega Q ^ n = omega Q ^ n * ((starRingEnd ℂ) (omega Q ^ m) * omega Q ^ m) := by
            rw [hconj, mul_one]
        _ = ζ * omega Q ^ m := by rw [hζ, mul_assoc]
        _ = omega Q ^ m := by rw [h1, one_mul]
    have hpow : ζ ^ Q = 1 := by
      rw [hζ, mul_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm n Q, mul_comm m Q, pow_mul, pow_mul,
        hprim.pow_eq_one, one_pow, one_pow, map_one, one_mul]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- **Parseval on `[0, Q)`.** -/
theorem sum_normSq_transform {Q N : ℕ} (hQ : 0 < Q) (hN : N ≤ Q) (f : ℕ → ℝ) :
    ∑ j ∈ range Q, ‖∑ n ∈ range N, (f n : ℂ) * chi Q j n‖ ^ 2 = (Q : ℝ) * ∑ n ∈ range N, f n ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  have key : ∀ j, ((‖∑ n ∈ range N, (f n : ℂ) * chi Q j n‖ : ℂ)) ^ 2 =
      ∑ n ∈ range N, ∑ m ∈ range N,
        (f n : ℂ) * (f m : ℂ) * (chi Q j n * (starRingEnd ℂ) (chi Q j m)) := by
    intro j
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  simp only [key]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hnQ : n < Q := lt_of_lt_of_le (mem_range.mp hn) hN
  have horth : ∀ m ∈ range N, (f n : ℂ) * (f m : ℂ) *
      ∑ j ∈ range Q, chi Q j n * (starRingEnd ℂ) (chi Q j m) =
      if n = m then (Q : ℂ) * (f n : ℂ) ^ 2 else 0 := by
    intro m hm
    rw [sum_chi_mul_conj hQ hnQ (lt_of_lt_of_le (mem_range.mp hm) hN)]
    split_ifs with h
    · subst h
      ring
    · simp
  rw [sum_congr rfl horth, sum_ite_eq, if_pos hn]

/-! ### Convolution and energy -/

/-- The coefficient of `x + n` in the square of the word `c`. -/
def conv (M : ℕ) (c : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), if a + b = n then (c a : ℝ) * (c b : ℝ) else 0

/-- The additive energy of the word `c`. -/
def wordEnergy (M : ℕ) (c : ℕ → ℤ) : ℝ := ∑ n ∈ range (2 * M + 1), conv M c n ^ 2

theorem wordEnergy_nonneg (M : ℕ) (c : ℕ → ℤ) : 0 ≤ wordEnergy M c :=
  sum_nonneg fun _ _ => sq_nonneg _

/-- Grouping the double sum of a squared word by `a + b`. -/
theorem sum_sum_eq_sum_conv {A : Type*} [AddCommGroup A] [Module ℝ A] (M : ℕ) (c : ℕ → ℤ)
    (g : ℕ → A) :
    ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), ((c a : ℝ) * (c b : ℝ)) • g (a + b) =
      ∑ n ∈ range (2 * M + 1), conv M c n • g n := by
  symm
  unfold conv
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a ha => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun b hb => ?_
  simp only [ite_smul, zero_smul]
  rw [sum_ite_eq, if_pos]
  have h1 := Nat.lt_succ_iff.mp (mem_range.mp ha)
  have h2 := Nat.lt_succ_iff.mp (mem_range.mp hb)
  exact mem_range.mpr (by omega)

/-- The transform of a word at the frequency `j`. -/
def wordT (Q M : ℕ) (c : ℕ → ℤ) (j : ℕ) : ℂ :=
  ∑ a ∈ range (M + 1), (c a : ℂ) * chi Q j a

theorem wordT_sq (Q M : ℕ) (c : ℕ → ℤ) (j : ℕ) :
    wordT Q M c j ^ 2 = ∑ n ∈ range (2 * M + 1), (conv M c n : ℂ) * chi Q j n := by
  have h := sum_sum_eq_sum_conv (A := ℂ) M c (chi Q j)
  simp only [Complex.real_smul] at h
  rw [← h, wordT, sq, Finset.sum_mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [chi_add]
  push_cast
  ring

/-- **The energy is a fourth power mean.** -/
theorem energy_eq {Q M : ℕ} (hQ : 2 * M + 1 ≤ Q) (c : ℕ → ℤ) :
    (Q : ℝ) * wordEnergy M c = ∑ j ∈ range Q, ‖wordT Q M c j‖ ^ 4 := by
  have hQ0 : 0 < Q := by omega
  rw [wordEnergy, ← sum_normSq_transform hQ0 hQ (conv M c)]
  refine sum_congr rfl fun j _ => ?_
  rw [← wordT_sq, norm_pow]
  ring

/-! ### The fourth moment of a Rademacher sum -/

/-- The sign pattern of a set. -/
def sgn (S : Finset ℕ) (a : ℕ) : ℝ := if a ∈ S then 1 else -1

theorem sgn_insert_of_ne {S : Finset ℕ} {a b : ℕ} (h : a ≠ b) : sgn (insert b S) a = sgn S a := by
  simp [sgn, h]

theorem sgn_insert_self (S : Finset ℕ) (b : ℕ) : sgn (insert b S) b = 1 := by
  simp [sgn]

theorem sgn_of_not_mem {S : Finset ℕ} {b : ℕ} (h : b ∉ S) : sgn S b = -1 := by
  simp [sgn, h]

/-- The two values of the sum over `insert b s`, in terms of the sum over `s`. -/
theorem sum_insert_sgn {s S : Finset ℕ} {b : ℕ} (hb : b ∉ s) (hS : S ⊆ s) (u : ℕ → ℝ) :
    (∑ a ∈ insert b s, sgn S a * u a = ∑ a ∈ s, sgn S a * u a - u b) ∧
      (∑ a ∈ insert b s, sgn (insert b S) a * u a = ∑ a ∈ s, sgn S a * u a + u b) := by
  constructor
  · rw [sum_insert hb, sgn_of_not_mem (fun h => hb (hS h))]
    ring
  · rw [sum_insert hb, sgn_insert_self, add_comm]
    congr 1
    · refine sum_congr rfl fun a ha => ?_
      rw [sgn_insert_of_ne (fun h : a = b => hb (h ▸ ha))]
    · ring

/-- The second moment of a Rademacher sum. -/
theorem sum_powerset_sq (s : Finset ℕ) (u : ℕ → ℝ) :
    ∑ S ∈ s.powerset, (∑ a ∈ s, sgn S a * u a) ^ 2 = 2 ^ s.card * ∑ a ∈ s, u a ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [sum_powerset_insert hb, card_insert_of_notMem hb, sum_insert hb, ← sum_add_distrib]
    have hterm : ∀ S ∈ s.powerset,
        (∑ a ∈ insert b s, sgn S a * u a) ^ 2 + (∑ a ∈ insert b s, sgn (insert b S) a * u a) ^ 2 =
          2 * (∑ a ∈ s, sgn S a * u a) ^ 2 + 2 * u b ^ 2 := by
      intro S hS
      obtain ⟨h1, h2⟩ := sum_insert_sgn hb (mem_powerset.mp hS) u
      rw [h1, h2]
      ring
    rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ih, sum_const, card_powerset, nsmul_eq_mul]
    push_cast
    ring

/-- **Khintchine in degree four.** -/
theorem sum_powerset_four (s : Finset ℕ) (u : ℕ → ℝ) :
    ∑ S ∈ s.powerset, (∑ a ∈ s, sgn S a * u a) ^ 4 ≤ 2 ^ s.card * (3 * (∑ a ∈ s, u a ^ 2) ^ 2) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [sum_powerset_insert hb, card_insert_of_notMem hb, sum_insert hb, ← sum_add_distrib]
    have hterm : ∀ S ∈ s.powerset,
        (∑ a ∈ insert b s, sgn S a * u a) ^ 4 + (∑ a ∈ insert b s, sgn (insert b S) a * u a) ^ 4 =
          2 * (∑ a ∈ s, sgn S a * u a) ^ 4 + 12 * u b ^ 2 * (∑ a ∈ s, sgn S a * u a) ^ 2 +
            2 * u b ^ 4 := by
      intro S hS
      obtain ⟨h1, h2⟩ := sum_insert_sgn hb (mem_powerset.mp hS) u
      rw [h1, h2]
      ring
    rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
      sum_powerset_sq, sum_const, card_powerset, nsmul_eq_mul]
    set A := ∑ a ∈ s, u a ^ 2 with hA
    have hA0 : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
    have hp : (0 : ℝ) < 2 ^ s.card := by positivity
    have hu4 : 0 ≤ u b ^ 4 := by positivity
    have hexp : ((2 : ℝ) ^ (s.card + 1)) * (3 * (u b ^ 2 + A) ^ 2) =
        2 ^ s.card * (6 * A ^ 2 + 12 * u b ^ 2 * A + 6 * u b ^ 4) := by
      rw [pow_succ]
      ring
    rw [hexp]
    push_cast
    have h4 : 2 * ∑ S ∈ s.powerset, (∑ a ∈ s, sgn S a * u a) ^ 4 ≤
        2 * ((2 : ℝ) ^ s.card * (3 * A ^ 2)) := by linarith
    nlinarith [mul_nonneg hp.le hu4]

/-- The transform of a sign pattern at the frequency `j`. -/
def signT (Q M j : ℕ) (S : Finset ℕ) : ℂ :=
  ∑ a ∈ range (M + 1), (sgn S a : ℂ) * chi Q j a

/-- The fourth moment of the transform of a sign pattern. -/
theorem sum_powerset_norm_four {Q : ℕ} (hQ : 0 < Q) (M j : ℕ) :
    ∑ S ∈ (range (M + 1)).powerset, ‖signT Q M j S‖ ^ 4 ≤
      2 ^ (M + 1) * (6 * ((M : ℝ) + 1) ^ 2) := by
  set s := range (M + 1) with hs
  have hcard : s.card = M + 1 := card_range _
  set u : ℕ → ℝ := fun a => (chi Q j a).re with hu
  set v : ℕ → ℝ := fun a => (chi Q j a).im with hv
  have hre : ∀ S, (signT Q M j S).re = ∑ a ∈ s, sgn S a * u a := by
    intro S
    rw [signT, Complex.re_sum]
    exact sum_congr rfl fun a _ => Complex.re_ofReal_mul _ _
  have him : ∀ S, (signT Q M j S).im = ∑ a ∈ s, sgn S a * v a := by
    intro S
    rw [signT, Complex.im_sum]
    exact sum_congr rfl fun a _ => Complex.im_ofReal_mul _ _
  have hpt : ∀ S, ‖signT Q M j S‖ ^ 4 ≤
      2 * (∑ a ∈ s, sgn S a * u a) ^ 4 + 2 * (∑ a ∈ s, sgn S a * v a) ^ 4 := by
    intro S
    have h1 : ‖signT Q M j S‖ ^ 2 = (signT Q M j S).re ^ 2 + (signT Q M j S).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have e : ‖signT Q M j S‖ ^ 4 = (‖signT Q M j S‖ ^ 2) ^ 2 := by ring
    rw [e, h1, hre, him]
    nlinarith [sq_nonneg ((∑ a ∈ s, sgn S a * u a) ^ 2 - (∑ a ∈ s, sgn S a * v a) ^ 2)]
  have hunit : ∑ a ∈ s, u a ^ 2 + ∑ a ∈ s, v a ^ 2 = (M : ℝ) + 1 := by
    rw [← sum_add_distrib]
    have : ∀ a ∈ s, u a ^ 2 + v a ^ 2 = 1 := by
      intro a _
      have h1 := norm_chi hQ j a
      have h2 : ‖chi Q j a‖ ^ 2 = (chi Q j a).re ^ 2 + (chi Q j a).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      rw [h1] at h2
      simp only [hu, hv]
      linarith
    rw [sum_congr rfl this, sum_const, hcard]
    simp
  have hU0 : 0 ≤ ∑ a ∈ s, u a ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hV0 : 0 ≤ ∑ a ∈ s, v a ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hu4 := sum_powerset_four s u
  have hv4 := sum_powerset_four s v
  rw [hcard] at hu4 hv4
  have hp : (0 : ℝ) < 2 ^ (M + 1) := by positivity
  calc ∑ S ∈ s.powerset, ‖signT Q M j S‖ ^ 4
      ≤ ∑ S ∈ s.powerset, (2 * (∑ a ∈ s, sgn S a * u a) ^ 4 + 2 * (∑ a ∈ s, sgn S a * v a) ^ 4) :=
        sum_le_sum fun S _ => hpt S
    _ = 2 * ∑ S ∈ s.powerset, (∑ a ∈ s, sgn S a * u a) ^ 4 +
          2 * ∑ S ∈ s.powerset, (∑ a ∈ s, sgn S a * v a) ^ 4 := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ 2 * (2 ^ (M + 1) * (3 * (∑ a ∈ s, u a ^ 2) ^ 2)) +
          2 * (2 ^ (M + 1) * (3 * (∑ a ∈ s, v a ^ 2) ^ 2)) := by linarith
    _ ≤ 2 ^ (M + 1) * (6 * ((M : ℝ) + 1) ^ 2) := by
        rw [← hunit]
        nlinarith [mul_nonneg hU0 hV0, mul_nonneg hp.le (mul_nonneg hU0 hV0)]

/-! ### The word -/

/-- The fourth power mean of a sign pattern, without normalization. -/
def signEnergy (Q M : ℕ) (S : Finset ℕ) : ℝ := ∑ j ∈ range Q, ‖signT Q M j S‖ ^ 4

theorem signEnergy_nonneg (Q M : ℕ) (S : Finset ℕ) : 0 ≤ signEnergy Q M S :=
  sum_nonneg fun _ _ => by positivity

/-- The total fourth power mean of all sign patterns. -/
theorem sum_signEnergy_le {Q : ℕ} (hQ : 0 < Q) (M : ℕ) :
    ∑ S ∈ (range (M + 1)).powerset, signEnergy Q M S ≤
      2 ^ (M + 1) * ((Q : ℝ) * (6 * ((M : ℝ) + 1) ^ 2)) := by
  unfold signEnergy
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _j ∈ range Q, (2 : ℝ) ^ (M + 1) * (6 * ((M : ℝ) + 1) ^ 2) :=
        sum_le_sum fun j _ => sum_powerset_norm_four hQ M j
    _ = _ := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring

/-- **At least half of all sign patterns have low energy.** -/
theorem card_lowEnergy_ge {Q : ℕ} (hQ : 0 < Q) (M : ℕ) :
    2 ^ M ≤ ((range (M + 1)).powerset.filter fun S =>
      signEnergy Q M S ≤ 12 * (Q : ℝ) * ((M : ℝ) + 1) ^ 2).card := by
  classical
  set U := (range (M + 1)).powerset with hU
  set B : ℝ := 12 * (Q : ℝ) * ((M : ℝ) + 1) ^ 2 with hB
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hBpos : 0 < B := by positivity
  have hcardU : U.card = 2 ^ (M + 1) := by simp [hU]
  have hsplit := card_filter_add_card_filter_not (s := U) (fun S => signEnergy Q M S ≤ B)
  have hbad : ((U.filter fun S => ¬ signEnergy Q M S ≤ B).card : ℝ) * B ≤ 2 ^ M * B := by
    have h1 : ((U.filter fun S => ¬ signEnergy Q M S ≤ B).card : ℝ) * B ≤
        ∑ S ∈ U.filter (fun S => ¬ signEnergy Q M S ≤ B), signEnergy Q M S := by
      rw [← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum fun S hS => ?_
      exact (not_le.mp (mem_filter.mp hS).2).le
    have h2 : ∑ S ∈ U.filter (fun S => ¬ signEnergy Q M S ≤ B), signEnergy Q M S ≤
        ∑ S ∈ U, signEnergy Q M S :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ => signEnergy_nonneg Q M S
    have h3 := sum_signEnergy_le hQ M
    have e : (2 : ℝ) ^ (M + 1) * ((Q : ℝ) * (6 * ((M : ℝ) + 1) ^ 2)) = 2 ^ M * B := by
      rw [hB, pow_succ]
      ring
    rw [e] at h3
    linarith
  have hbad' : (U.filter fun S => ¬ signEnergy Q M S ≤ B).card ≤ 2 ^ M := by
    have := le_of_mul_le_mul_right hbad hBpos
    exact_mod_cast this
  rw [hcardU, pow_succ] at hsplit
  omega

/-- The energy of a difference of two sign patterns is at most the larger of the two, on average. -/
theorem wordEnergy_sub_le {M : ℕ} {S T : Finset ℕ} {B : ℝ} (hS : signEnergy (2 * M + 1) M S ≤ B)
    (hT : signEnergy (2 * M + 1) M T ≤ B) :
    (((2 * M + 1 : ℕ) : ℝ)) *
      wordEnergy M (fun a => (if a ∈ S then 1 else 0) - (if a ∈ T then 1 else 0)) ≤ B := by
  rw [energy_eq le_rfl]
  set Q := 2 * M + 1 with hQ
  set c : ℕ → ℤ := fun a => (if a ∈ S then 1 else 0) - (if a ∈ T then 1 else 0) with hc
  have htrans : ∀ j, wordT Q M c j = (signT Q M j S - signT Q M j T) / 2 := by
    intro j
    rw [wordT, signT, signT, ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun a _ => ?_
    simp only [hc, sgn]
    by_cases h1 : a ∈ S <;> by_cases h2 : a ∈ T <;> (simp [h1, h2]; try ring)
  have hpt : ∀ j, ‖wordT Q M c j‖ ^ 4 ≤ (‖signT Q M j S‖ ^ 4 + ‖signT Q M j T‖ ^ 4) / 2 := by
    intro j
    set p := ‖signT Q M j S‖ with hp
    set q := ‖signT Q M j T‖ with hq
    have hp0 : 0 ≤ p := norm_nonneg _
    have hq0 : 0 ≤ q := norm_nonneg _
    have h1 : ‖wordT Q M c j‖ ≤ (p + q) / 2 := by
      rw [htrans, norm_div]
      simp only [Complex.norm_ofNat]
      exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    have h2 : ‖wordT Q M c j‖ ^ 4 ≤ ((p + q) / 2) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 4
    refine h2.trans ?_
    have h3 : ((p + q) / 2) ^ 2 ≤ (p ^ 2 + q ^ 2) / 2 := by nlinarith [sq_nonneg (p - q)]
    have h4 : ((p + q) / 2) ^ 4 ≤ ((p ^ 2 + q ^ 2) / 2) ^ 2 := by
      have e : ((p + q) / 2) ^ 4 = (((p + q) / 2) ^ 2) ^ 2 := by ring
      rw [e]
      exact pow_le_pow_left₀ (by positivity) h3 2
    refine h4.trans ?_
    nlinarith [sq_nonneg (p ^ 2 - q ^ 2)]
  calc ∑ j ∈ range Q, ‖wordT Q M c j‖ ^ 4
      ≤ ∑ j ∈ range Q, (‖signT Q M j S‖ ^ 4 + ‖signT Q M j T‖ ^ 4) / 2 :=
        sum_le_sum fun j _ => hpt j
    _ = (signEnergy Q M S + signEnergy Q M T) / 2 := by
        rw [← sum_div, sum_add_distrib]
        rfl
    _ ≤ B := by linarith

/-- **A word of low energy.** Two sign patterns of low energy have the same moments once
`Π_{j≤k}(C(M+1,j+1)+1) < 2^M`. -/
theorem exists_lowEnergy_word_aux {M k : ℕ}
    (h : ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ M) :
    ∃ c, IsWord M c ∧ (∀ j ≤ k, binomMoment M c j = 0) ∧ wordEnergy M c ≤ 12 * ((M : ℝ) + 1) ^ 2 := by
  classical
  set Q := 2 * M + 1 with hQ
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  set B : ℝ := 12 * (Q : ℝ) * ((M : ℝ) + 1) ^ 2 with hB
  set U := (range (M + 1)).powerset.filter fun S => signEnergy Q M S ≤ B with hU
  set V := Finset.pi (range (k + 1)) (fun j => range ((M + 1).choose (j + 1) + 1)) with hV
  have hcardU : 2 ^ M ≤ U.card := card_lowEnergy_ge hQ0 M
  have hcardV : V.card = ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) := by
    simp [hV, Finset.card_pi]
  let F : Finset ℕ → (∀ j ∈ range (k + 1), ℕ) := fun S j _ => ∑ a ∈ S, a.choose j
  have hF : ∀ S ∈ U, F S ∈ V := by
    intro S hS
    refine Finset.mem_pi.mpr fun j _ => Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
    rw [← sum_range_choose_eq]
    exact Finset.sum_le_sum_of_subset (Finset.mem_powerset.mp (mem_filter.mp hS).1)
  obtain ⟨S, hS, T, hT, hne, hST⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := U) (t := V) (f := F)
      (by rw [hcardV]; exact lt_of_lt_of_le h hcardU) hF
  have hSM := Finset.mem_powerset.mp (mem_filter.mp hS).1
  have hTM := Finset.mem_powerset.mp (mem_filter.mp hT).1
  refine ⟨fun a => (if a ∈ S then 1 else 0) - (if a ∈ T then 1 else 0), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a
    by_cases h1 : a ∈ S <;> by_cases h2 : a ∈ T <;> simp [h1, h2]
  · intro a ha
    have h1 : a ∉ S := fun h => by
      have := Finset.mem_range.mp (hSM h); omega
    have h2 : a ∉ T := fun h => by
      have := Finset.mem_range.mp (hTM h); omega
    simp [h1, h2]
  · by_contra hall
    push Not at hall
    apply hne
    ext a
    have := hall a
    by_cases h1 : a ∈ S <;> by_cases h2 : a ∈ T <;> simp_all
  · intro j hj
    have hj' : j ∈ range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have e := congrFun (congrFun hST j) hj'
    simp only [F] at e
    unfold binomMoment
    have hS' : ∑ a ∈ range (M + 1), (if a ∈ S then 1 else 0 : ℤ) * (a.choose j : ℤ) =
        ∑ a ∈ S, (a.choose j : ℤ) := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hSM]
    have hT' : ∑ a ∈ range (M + 1), (if a ∈ T then 1 else 0 : ℤ) * (a.choose j : ℤ) =
        ∑ a ∈ T, (a.choose j : ℤ) := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTM]
    simp only [sub_mul, Finset.sum_sub_distrib, hS', hT']
    have e' : (∑ a ∈ S, (a.choose j : ℤ)) = ∑ a ∈ T, (a.choose j : ℤ) := by exact_mod_cast e
    rw [e', sub_self]
  · have h1 := wordEnergy_sub_le (mem_filter.mp hS).2 (mem_filter.mp hT).2
    rw [hB] at h1
    have e : 12 * (Q : ℝ) * ((M : ℝ) + 1) ^ 2 = (Q : ℝ) * (12 * ((M : ℝ) + 1) ^ 2) := by ring
    rw [e] at h1
    exact le_of_mul_le_mul_left h1 hQr

/-- Shifting a word past its leading zeros does not change the absolute values of its transform. -/
theorem norm_wordT_shift {Q M ν : ℕ} (hQ : 0 < Q) {c : ℕ → ℤ} (hsup : ∀ a, M < a → c a = 0)
    (hmin : ∀ a < ν, c a = 0) (j : ℕ) :
    ‖wordT Q M (fun a => c (a + ν)) j‖ = ‖wordT Q M c j‖ := by
  have hshift : wordT Q M c j = wordT Q M (fun a => c (a + ν)) j * chi Q j ν := by
    unfold wordT
    have hsub : ∑ a ∈ range (M + 1), (c a : ℂ) * chi Q j a =
        ∑ a ∈ range (ν + (M + 1)), (c a : ℂ) * chi Q j a := by
      refine Finset.sum_subset (fun a ha => ?_) fun a _ ha => ?_
      · simp only [Finset.mem_range] at ha ⊢
        omega
      · have : M < a := by
          simp only [Finset.mem_range] at ha
          omega
        simp [hsup a this]
    rw [hsub, Finset.sum_range_add, Finset.sum_eq_zero fun a ha => by
      simp [hmin a (Finset.mem_range.mp ha)], zero_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [add_comm ν a, chi_add]
    ring
  rw [hshift, norm_mul, norm_chi hQ, mul_one]

/-- **A word of order `k`, with `c_0 ≠ 0`, of energy at most `12 (M+1)²`.** -/
theorem exists_lowEnergy_word {M k : ℕ}
    (h : ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ M) :
    ∃ c, IsWord M c ∧ (∀ j ≤ k, binomMoment M c j = 0) ∧ c 0 ≠ 0 ∧
      wordEnergy M c ≤ 12 * ((M : ℝ) + 1) ^ 2 := by
  obtain ⟨c, hc, hm, hE⟩ := exists_lowEnergy_word_aux h
  obtain ⟨ν, hmin, hν, hm'⟩ := exists_shift_zero_ne_min hc.support hc.ne_zero hm
  refine ⟨fun a => c (a + ν), ⟨fun a => hc.bound _, fun a ha => hc.support _ (by omega), ⟨0, hν⟩⟩,
    hm', hν, ?_⟩
  have hQ : 0 < 2 * M + 1 := by omega
  have hQr : (0 : ℝ) < ((2 * M + 1 : ℕ) : ℝ) := by exact_mod_cast hQ
  have e : wordEnergy M (fun a => c (a + ν)) = wordEnergy M c := by
    have h1 := energy_eq (le_refl (2 * M + 1)) (fun a => c (a + ν))
    have h2 := energy_eq (le_refl (2 * M + 1)) c
    have h3 : ∑ j ∈ range (2 * M + 1), ‖wordT (2 * M + 1) M (fun a => c (a + ν)) j‖ ^ 4 =
        ∑ j ∈ range (2 * M + 1), ‖wordT (2 * M + 1) M c j‖ ^ 4 :=
      sum_congr rfl fun j _ => by rw [norm_wordT_shift hQ hc.support hmin]
    rw [h3, ← h2] at h1
    exact mul_left_cancel₀ hQr.ne' h1
  rw [e]
  exact hE

end

end GaloisForLFunctions.PrimeTorusTheory
