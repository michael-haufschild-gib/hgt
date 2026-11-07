import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMeanValueOfTheMultiplicity

/-!
# The smooth mean value of the multiplicity

The sharp mean value `|Σ_{r<n} g(r) − n w/2| ≤ E/8` loses the first moment `E` of the coefficients, because a
sharp cut sees a sawtooth at its largest. Window sums lose nothing of the kind. A `k`-periodic sequence of mean
zero has window sums bounded by `k` times its size, for every window length, and the window sum is again
periodic of mean zero. So after `A` windows of length `L`,

`|I_L^A g(n) − L^A w/2| ≤ K^A Σ |c(k)|`.

A nonnegative `g` satisfies `I_L^{A+1} g(n) ≤ L^A Σ_{r ∈ [n, n + (A+1) L)} g(r)`, and a block at scale `L` costs slope
`≍ (block)/L²`. Taking `L = 3K` and `A ≍ log K` absorbs the coefficient mass, which gives the **peak law**

`w ≤ 100 (1 + log K)² (K T + m)`.

The peak is bounded by the excess at scale `K`, with no first moment. This is sharp on the Möbius producers, whose
peak is about `K ε`.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The window sum `Σ_{j<L} f(n + j)`. -/
def windowSum (L : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range L, f (n + j)

/-- The iterated window sum `I_L^A f`. -/
def smoothSum (L : ℕ) : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, f => f
  | A + 1, f => windowSum L (smoothSum L A f)

/-- A `k`-periodic sequence of mean zero. -/
structure IsMeanZero (k : ℕ) (f : ℕ → ℝ) : Prop where
  periodic : ∀ n, f (n + k) = f n
  mean : ∑ n ∈ range k, f n = 0

namespace IsMeanZero

variable {k : ℕ} {f : ℕ → ℝ}

/-- A full period sums to zero from any starting point. -/
theorem sum_shift (h : IsMeanZero k f) (n : ℕ) : ∑ j ∈ range k, f (n + j) = 0 := by
  induction n with
  | zero => simpa using h.mean
  | succ n ih =>
    have h1 := Finset.sum_range_succ (fun j => f (n + j)) k
    have h2 := Finset.sum_range_succ' (fun j => f (n + j)) k
    have h3 : ∑ j ∈ range k, f (n + 1 + j) = ∑ j ∈ range k, f (n + (j + 1)) :=
      sum_congr rfl fun j _ => by rw [show n + 1 + j = n + (j + 1) by ring]
    have hp := h.periodic n
    simp only [add_zero] at h2
    rw [h3]
    linarith

/-- Any whole number of periods sums to zero. -/
theorem sum_mul (h : IsMeanZero k f) (n q : ℕ) : ∑ j ∈ range (k * q), f (n + j) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add]
    have := h.sum_shift (n + k * q)
    simpa only [add_assoc] using this

/-- **A window of any length costs at most one period.** -/
theorem abs_windowSum_le (h : IsMeanZero k f) {S : ℝ} (hS : ∀ n, |f n| ≤ S) (L n : ℕ)
    (hk : 0 < k) : |windowSum L f n| ≤ (k : ℝ) * S := by
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS 0)
  have hsplit : L = k * (L / k) + L % k := (Nat.div_add_mod L k).symm
  rw [windowSum, hsplit, Finset.sum_range_add, h.sum_mul, zero_add]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun j _ => hS _).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  have hmod : ((L % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt L hk).le
  exact mul_le_mul_of_nonneg_right hmod hS0

/-- A window sum is again periodic of mean zero. -/
theorem windowSum (h : IsMeanZero k f) (L : ℕ) : IsMeanZero k (windowSum L f) := by
  refine ⟨fun n => ?_, ?_⟩
  · refine sum_congr rfl fun j _ => ?_
    rw [show n + k + j = n + j + k by ring, h.periodic]
  · simp only [ArithmeticAuxiliaryDynamics.windowSum]
    rw [sum_comm]
    refine sum_eq_zero fun j _ => ?_
    have := h.sum_shift j
    rw [← this]
    exact sum_congr rfl fun n _ => by rw [add_comm]

/-- **Iterated windows.** `|I_L^A f| ≤ k^A S`, for every window length. -/
theorem smoothSum (h : IsMeanZero k f) {S : ℝ} (hS : ∀ n, |f n| ≤ S) (hk : 0 < k) (L A : ℕ) :
    IsMeanZero k (smoothSum L A f) ∧ ∀ n, |smoothSum L A f n| ≤ (k : ℝ) ^ A * S := by
  induction A with
  | zero =>
    refine ⟨h, fun n => ?_⟩
    simpa [ArithmeticAuxiliaryDynamics.smoothSum] using hS n
  | succ A ih =>
    refine ⟨ih.1.windowSum L, fun n => ?_⟩
    have h1 := ih.1.abs_windowSum_le ih.2 L n hk
    rw [pow_succ]
    calc _ ≤ (k : ℝ) * ((k : ℝ) ^ A * S) := h1
      _ = _ := by ring

end IsMeanZero

/-- Iterated windows are linear, and a constant is multiplied by `L^A`. -/
theorem smoothSum_const_add_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (φ : ι → ℕ → ℝ) (C : ℝ) (L A n : ℕ) :
    smoothSum L A (fun r => C + ∑ i ∈ s, a i * φ i r) n =
      (L : ℝ) ^ A * C + ∑ i ∈ s, a i * smoothSum L A (φ i) n := by
  induction A generalizing n with
  | zero => simp [smoothSum]
  | succ A ih =>
    simp only [smoothSum, windowSum]
    simp_rw [ih]
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, pow_succ]
    congr 1
    · ring
    · rw [sum_comm]
      exact sum_congr rfl fun i _ => by rw [mul_sum]

/-- The centred residue `(r mod k) − (k − 1)/2`. -/
def residue (k r : ℕ) : ℝ := ((r % k : ℕ) : ℝ) - ((k : ℝ) - 1) / 2

theorem isMeanZero_residue {k : ℕ} (hk : 0 < k) : IsMeanZero k (residue k) := by
  refine ⟨fun n => ?_, ?_⟩
  · simp only [residue, Nat.add_mod_right]
  · simp only [residue]
    rw [sum_sub_distrib, sum_range_mod hk k, Nat.mod_self, sum_const, card_range, nsmul_eq_mul]
    push_cast
    ring

theorem abs_residue_le {k : ℕ} (hk : 0 < k) (r : ℕ) : |residue k r| ≤ k := by
  have h0 : (0 : ℝ) ≤ ((r % k : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((r % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt r hk).le
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [residue, abs_le]
  constructor <;> linarith

/-- The multiplicity is its mean plus centred sawteeth. -/
theorem stepWeight_eq_mean_add {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) (r : ℕ) :
    (stepWeight c r : ℝ) = (peak c : ℝ) / 2 + ∑ k ∈ c.support, (-(c k : ℝ) / k) * residue k r := by
  have hb : ∑ k ∈ c.support, (c k : ℝ) / k = 0 := hbal
  have hmean : (peak c : ℝ) / 2 = ∑ k ∈ c.support, (-(c k : ℝ) / k) * (((k : ℝ) - 1) / 2) := by
    have hterm : ∀ k ∈ c.support, (-(c k : ℝ) / k) * (((k : ℝ) - 1) / 2) =
        -(c k : ℝ) / 2 + ((c k : ℝ) / k) / 2 := by
      intro k hk
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr fun h => by
        subst h
        exact Finsupp.mem_support_iff.mp hk hc0
      field_simp
      ring
    rw [sum_congr rfl hterm, sum_add_distrib, ← sum_div, ← sum_div, hb, zero_div, add_zero, peak]
    push_cast
    rw [sum_neg_distrib]
  rw [stepWeight_eq_sum_mod hc0 hbal r, hmean, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [residue]
  ring

/-- **The smooth mean value.** `|I_L^A g(n) − L^A w/2| ≤ K^A Σ |c(k)|`, for every window length. -/
theorem abs_smoothSum_stepWeight_sub_le {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) {K : ℕ}
    (hK : AlphabetLE c K) (L A n : ℕ) :
    |smoothSum L A (fun r => (stepWeight c r : ℝ)) n - (L : ℝ) ^ A * ((peak c : ℝ) / 2)| ≤
      (K : ℝ) ^ A * coeffMass c := by
  have hfun : (fun r => (stepWeight c r : ℝ)) = fun r => (peak c : ℝ) / 2 +
      ∑ k ∈ c.support, (-(c k : ℝ) / k) * residue k r := by
    funext r
    exact stepWeight_eq_mean_add hc0 hbal r
  rw [hfun, smoothSum_const_add_sum, add_sub_cancel_left, coeffMass, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h
    exact Finsupp.mem_support_iff.mp hk hc0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hK k hk
  have hsm := ((isMeanZero_residue hk0).smoothSum (abs_residue_le hk0) hk0 L A).2 n
  rw [abs_mul, abs_div, abs_neg, abs_of_pos hkR]
  have habs := abs_nonneg (c k : ℝ)
  calc |(c k : ℝ)| / k * |smoothSum L A (residue k) n|
      ≤ |(c k : ℝ)| / k * ((k : ℝ) ^ A * k) := by gcongr
    _ = (k : ℝ) ^ A * |(c k : ℝ)| := by field_simp
    _ ≤ (K : ℝ) ^ A * |(c k : ℝ)| := by gcongr

/-- A nonnegative sequence: `I_L^{A+1} g(n) ≤ L^A Σ_{x < (A+1) L} g(n + x)`. -/
theorem smoothSum_succ_le {g : ℕ → ℝ} (hg : ∀ r, 0 ≤ g r) (L A n : ℕ) :
    smoothSum L (A + 1) g n ≤ (L : ℝ) ^ A * ∑ x ∈ range ((A + 1) * L), g (n + x) := by
  induction A generalizing n with
  | zero => simp [smoothSum, windowSum]
  | succ A ih =>
    have hstep : ∀ j ∈ range L, smoothSum L (A + 1) g (n + j) ≤
        (L : ℝ) ^ A * ∑ x ∈ range ((A + 1 + 1) * L), g (n + x) := by
      intro j hj
      refine (ih (n + j)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have hjL := mem_range.mp hj
      have h1 := Finset.sum_range_add (fun x => g (n + x)) j ((A + 1) * L)
      have h2 : ∑ x ∈ range j, g (n + x) ≥ 0 := sum_nonneg fun _ _ => hg _
      have h3 : ∑ x ∈ range (j + (A + 1) * L), g (n + x) ≤ ∑ x ∈ range ((A + 1 + 1) * L), g (n + x) := by
        refine sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr ?_) fun _ _ _ => hg _
        have : (A + 1 + 1) * L = (A + 1) * L + L := by ring
        omega
      have h4 : ∑ x ∈ range ((A + 1) * L), g (n + j + x) =
          ∑ x ∈ range ((A + 1) * L), g (n + (j + x)) :=
        sum_congr rfl fun x _ => by rw [add_assoc]
      rw [h4]
      linarith
    change windowSum L (smoothSum L (A + 1) g) n ≤ _
    rw [windowSum]
    refine (sum_le_sum hstep).trans (le_of_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul, pow_succ]
    ring

/-- `3^{A+1} ≥ 4 K²` once `A ≥ 1 + 2 log K`. -/
private lemma three_pow_ge {K : ℝ} (hK0 : 0 < K) {A : ℕ} (hA1 : 1 + 2 * Real.log K ≤ (A : ℝ)) :
    4 * K ^ 2 ≤ (3 : ℝ) ^ (A + 1) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have he3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h1 : Real.exp ((A : ℝ) + 1) ≤ (3 : ℝ) ^ (A + 1) := by
    have heq : Real.exp ((A : ℝ) + 1) = Real.exp 1 ^ (A + 1) := by
      rw [Real.exp_one_pow]
      push_cast
      rfl
    rw [heq]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le he3 _
  have h2 : Real.exp (2 + 2 * Real.log K) ≤ Real.exp ((A : ℝ) + 1) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (2 + 2 * Real.log K) = Real.exp 1 ^ 2 * K ^ 2 := by
    have h4 : Real.exp (2 * Real.log K) = K ^ 2 := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hK0]
      norm_num
    rw [Real.exp_add, h4, Real.exp_one_pow]
    norm_num
  have h4 : (4 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith
  have h5 : 4 * K ^ 2 ≤ Real.exp 1 ^ 2 * K ^ 2 := mul_le_mul_of_nonneg_right h4 (by positivity)
  linarith

/-- The power of `1/3` absorbs the coefficient mass. -/
private lemma coeff_term_le {K l m T M P : ℝ} (hK0 : 0 < K) (hl0 : 0 ≤ l) (hlK : l ≤ K - 1) (hm : 0 < m)
    (hT : 0 < T) (hmass : M ≤ 2 * K * (m * (1 + l) + (K + 1) * T)) (hP : 4 * K ^ 2 ≤ P) :
    1 / P * M ≤ m + T := by
  have hPpos : 0 < P := lt_of_lt_of_le (by positivity) hP
  rw [one_div, inv_mul_le_iff₀ hPpos]
  have hK1 : 1 ≤ K := by linarith
  have h1 : m * (1 + l) ≤ m * K := mul_le_mul_of_nonneg_left (by linarith) hm.le
  have h2 : (K + 1) * T ≤ 2 * K * T := mul_le_mul_of_nonneg_right (by linarith) hT.le
  have h3 : m * (1 + l) + (K + 1) * T ≤ 2 * K * (m + T) := by nlinarith
  have h4 : 2 * K * (m * (1 + l) + (K + 1) * T) ≤ 2 * K * (2 * K * (m + T)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : 4 * K ^ 2 * (m + T) ≤ P * (m + T) := mul_le_mul_of_nonneg_right hP (by positivity)
  calc M ≤ 2 * K * (m * (1 + l) + (K + 1) * T) := hmass
    _ ≤ 2 * K * (2 * K * (m + T)) := h4
    _ = 4 * K ^ 2 * (m + T) := by ring
    _ ≤ _ := h5

/-- The real arithmetic of the peak law. -/
private lemma peak_core {K l A T m w : ℝ} (hK : 1 ≤ K) (hl0 : 0 ≤ l) (hA1 : 1 + 2 * l ≤ A)
    (hA2 : A < 1 + 2 * l + 1) (hT : 0 < T) (hm : 0 < m)
    (hw : w ≤ 2 * ((A + 2) ^ 2 * (3 * K) * T + (A + 1) * m + (m + T))) :
    w ≤ 100 * (1 + l) ^ 2 * (K * T + m) := by
  have hA3 : A + 2 ≤ 4 * (1 + l) := by linarith
  have hA0 : 0 ≤ A + 2 := by linarith
  have hsq : (A + 2) ^ 2 ≤ 16 * (1 + l) ^ 2 := by
    calc (A + 2) ^ 2 ≤ (4 * (1 + l)) ^ 2 := pow_le_pow_left₀ hA0 hA3 2
      _ = _ := by ring
  have hKT : 0 < K * T := by positivity
  have h1l : 1 ≤ (1 + l) ^ 2 := by nlinarith
  have hfirst : (A + 2) ^ 2 * (3 * K) * T ≤ 48 * (1 + l) ^ 2 * (K * T) := by
    calc (A + 2) ^ 2 * (3 * K) * T = (A + 2) ^ 2 * (3 * (K * T)) := by ring
      _ ≤ 16 * (1 + l) ^ 2 * (3 * (K * T)) := mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = _ := by ring
  have hA5 : A + 1 ≤ 3 * (1 + l) ^ 2 := by nlinarith
  have hsecond : (A + 1) * m ≤ 3 * (1 + l) ^ 2 * m := mul_le_mul_of_nonneg_right hA5 hm.le
  have hT1 : T ≤ K * T := by nlinarith
  have hT2 : K * T ≤ (1 + l) ^ 2 * (K * T) := by nlinarith
  have hm1 : m ≤ (1 + l) ^ 2 * m := by nlinarith
  have hexp : 100 * (1 + l) ^ 2 * (K * T + m) = 100 * ((1 + l) ^ 2 * (K * T)) + 100 * ((1 + l) ^ 2 * m) := by
    ring
  rw [hexp]
  have hX : 0 ≤ (1 + l) ^ 2 * (K * T) := by positivity
  have hY : 0 ≤ (1 + l) ^ 2 * m := by positivity
  linarith

namespace IsProducer

variable {c : ℕ →₀ ℤ} {m B : ℕ}

/-- **A block at scale `n + N` costs excess.** -/
theorem sum_sub_le_excess (hP : IsProducer c m B) {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    ∑ x ∈ range N, ((stepWeight c (n + x) : ℝ) - m) ≤ ((n : ℝ) + N) ^ 2 * excess c m B := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  have hsum : ∑ j ∈ range (d + N), excessTerm m B c j ≤ excess c m B :=
    sum_le_hasSum _ (fun j _ => hP.excessTerm_nonneg j) hP.hasSum_excess
  rw [Finset.sum_range_add] at hsum
  have hfirst : 0 ≤ ∑ j ∈ range d, excessTerm m B c j :=
    sum_nonneg fun j _ => hP.excessTerm_nonneg j
  have hsub : ∑ x ∈ range N, excessTerm m B c (d + x) ≤ excess c m B := by linarith
  have hD : (0 : ℝ) ≤ (((d + 1 : ℕ) : ℝ) + N) ^ 2 := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hsub hD)
  rw [mul_sum]
  refine sum_le_sum fun x hx => ?_
  have hxN : (x : ℝ) + 1 ≤ N := by exact_mod_cast mem_range.mp hx
  have hE := hP.excessTerm_nonneg (d + x)
  have hid := tailWeight_eq c m B (d + x)
  have hlow : (stepWeight c (d + 1 + x) : ℝ) - m ≤ tailWeight c m B (d + x) := by
    rw [tailWeight, show d + x + 1 = d + 1 + x by ring]
    split_ifs
    · exact le_rfl
    · have := hP.m_pos
      linarith
  have hprod : (((d + x : ℕ) : ℝ) + 1) * (((d + x : ℕ) : ℝ) + 2) ≤ (((d + 1 : ℕ) : ℝ) + N) ^ 2 := by
    push_cast
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  rw [hid] at hlow
  calc _ ≤ excessTerm m B c (d + x) * (((d + x : ℕ) : ℝ) + 1) * (((d + x : ℕ) : ℝ) + 2) := by
        linarith
    _ = excessTerm m B c (d + x) * ((((d + x : ℕ) : ℝ) + 1) * (((d + x : ℕ) : ℝ) + 2)) := by ring
    _ ≤ excessTerm m B c (d + x) * (((d + 1 : ℕ) : ℝ) + N) ^ 2 :=
        mul_le_mul_of_nonneg_left hprod hE
    _ = _ := by ring

/-- **The peak at scale `L`.** For every window length `L ≥ 1` and `A`,
`w ≤ 2 ((A + 2)² L T + (A + 1) m + (K/L)^{A+1} Σ |c(k)|)`. -/
theorem peak_le_window (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) {L : ℕ} (hL : 1 ≤ L)
    (A : ℕ) :
    (peak c : ℝ) ≤ 2 * (((A : ℝ) + 2) ^ 2 * L * excess c m B + ((A : ℝ) + 1) * m +
      ((K : ℝ) / L) ^ (A + 1) * coeffMass c) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hg : ∀ r, 0 ≤ (stepWeight c r : ℝ) := fun r => by exact_mod_cast hP.nonneg r
  have h1 := (abs_le.mp (abs_smoothSum_stepWeight_sub_le hP.zero hP.balanced hK L (A + 1) L)).1
  have h2 := smoothSum_succ_le hg L A L
  have h3 := hP.sum_sub_le_excess hL ((A + 1) * L)
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at h3
  have hN : ((L : ℝ) + (((A + 1) * L : ℕ) : ℝ)) ^ 2 = ((A : ℝ) + 2) ^ 2 * ((L : ℝ) * L) := by
    push_cast
    ring
  rw [hN] at h3
  have hNm : ((((A + 1) * L : ℕ) : ℝ)) * (m : ℝ) = ((A : ℝ) + 1) * (L : ℝ) * m := by
    push_cast
    ring
  rw [hNm] at h3
  set T := excess c m B with hT
  set S := ∑ x ∈ range ((A + 1) * L), (stepWeight c (L + x) : ℝ) with hS
  have hS' : S ≤ ((A : ℝ) + 2) ^ 2 * ((L : ℝ) * L) * T + ((A : ℝ) + 1) * L * m := by linarith
  have hLA : (0 : ℝ) < (L : ℝ) ^ A := by positivity
  have hmain : (L : ℝ) ^ (A + 1) * ((peak c : ℝ) / 2) ≤
      (L : ℝ) ^ A * (((A : ℝ) + 2) ^ 2 * ((L : ℝ) * L) * T + ((A : ℝ) + 1) * L * m) +
        (K : ℝ) ^ (A + 1) * coeffMass c := by
    have h4 := mul_le_mul_of_nonneg_left hS' hLA.le
    linarith
  have hpow : ((K : ℝ) / L) ^ (A + 1) * coeffMass c * (L : ℝ) ^ (A + 1) =
      (K : ℝ) ^ (A + 1) * coeffMass c := by
    rw [div_pow]
    field_simp
  have hLA1 : (0 : ℝ) < (L : ℝ) ^ (A + 1) := by positivity
  have hdiv : (L : ℝ) ^ (A + 1) * ((peak c : ℝ) / 2) ≤
      (L : ℝ) ^ (A + 1) * (((A : ℝ) + 2) ^ 2 * L * T + ((A : ℝ) + 1) * m +
        ((K : ℝ) / L) ^ (A + 1) * coeffMass c) := by
    refine hmain.trans (le_of_eq ?_)
    rw [← hpow, pow_succ]
    ring
  have := le_of_mul_le_mul_left hdiv hLA1
  linarith

/-- **The peak law.** `w ≤ 100 (1 + log K)² (K T + m)`. -/
theorem peak_le (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) (hK1 : 1 ≤ K) :
    (peak c : ℝ) ≤ 100 * (1 + Real.log K) ^ 2 * ((K : ℝ) * excess c m B + m) := by
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hl0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
  have hlK : Real.log (K : ℝ) ≤ (K : ℝ) - 1 := Real.log_le_sub_one_of_pos hK0
  have hT0 := hP.excess_pos
  have hm := hP.m_pos
  obtain ⟨A, hAdef⟩ : ∃ A, A = ⌈1 + 2 * Real.log (K : ℝ)⌉₊ := ⟨_, rfl⟩
  have hA1 : 1 + 2 * Real.log (K : ℝ) ≤ (A : ℝ) := hAdef ▸ Nat.le_ceil _
  have hA2 : (A : ℝ) < 1 + 2 * Real.log (K : ℝ) + 1 :=
    hAdef ▸ Nat.ceil_lt_add_one (by linarith)
  have hmain := hP.peak_le_window hK (L := 3 * K) (by omega) A
  have hLcast : ((3 * K : ℕ) : ℝ) = 3 * (K : ℝ) := by push_cast; ring
  rw [hLcast] at hmain
  have hratio : ((K : ℝ) / (3 * (K : ℝ))) ^ (A + 1) = 1 / (3 : ℝ) ^ (A + 1) := by
    have h3 : (K : ℝ) / (3 * (K : ℝ)) = 1 / 3 := by field_simp
    rw [h3, div_pow, one_pow]
  have hterm : ((K : ℝ) / (3 * (K : ℝ))) ^ (A + 1) * coeffMass c ≤ (m : ℝ) + excess c m B := by
    rw [hratio]
    exact coeff_term_le hK0 hl0 hlK hm hT0 (hP.coeffMass_le hK) (three_pow_ge hK0 hA1)
  exact peak_core hKR hl0 hA1 hA2 hT0 hm (hmain.trans (by
    have := hterm
    linarith))

end IsProducer

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
