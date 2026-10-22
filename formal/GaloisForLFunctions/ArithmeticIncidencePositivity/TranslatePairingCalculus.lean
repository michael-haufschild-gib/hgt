import GaloisForLFunctions.ArithmeticCriticalityTheory.PoleConductanceWindowWeilPositivity

/-!
# The pairing calculus of finite translate combinations

Every estimate of the prime side of the critical form in this programme is an estimate of
`∫ A B` for functions `A`, `B` built from one test by finite combinations of translates. This file
is that calculus: the pairing `⟪A, B⟫ = ∫ A B` on continuous compactly supported functions, its
bilinearity, translation invariance and Cauchy–Schwarz inequality; the autocorrelation
`A(t) = ⟪F, F(· + t)⟫` with its bound `|A(t)| ≤ A(0)` and its vanishing beyond the support
diameter; finite translate combinations with the Gram expansion
`⟪Σ α_k F(· + c_k), Σ β_j F(· + d_j)⟫ = Σ α_k β_j A(d_j − c_k)` and the Gram bound by the product
of the coefficient masses; and the geometric train `S_N = Σ_{k ≤ N} z^k F(· + kL)` with its
resolvent identity `S_N − z S_N(· + L) = F − z^{N+1} F(· + (N+1)L)`.
-/

open MeasureTheory Set
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {F A B₁ B₂ : ℝ → ℝ}

/-! ### The pairing of continuous compactly supported functions

All objects of this file are finite combinations of translates of one test, so the only analysis
needed is the bilinearity and translation invariance of `∫ A B`. -/

/-- Continuous with compact support: the class on which the pairing is bilinear. -/
def ContCompact (A : ℝ → ℝ) : Prop := Continuous A ∧ HasCompactSupport A

theorem ContCompact.integrable_mul (hA : ContCompact A) (hB : ContCompact B₁) :
    Integrable (fun u => A u * B₁ u) :=
  Continuous.integrable_of_hasCompactSupport (hA.1.mul hB.1) hA.2.mul_right

theorem ContCompact.translate (hA : ContCompact A) (t : ℝ) : ContCompact (fun u => A (u + t)) :=
  ⟨hA.1.comp (continuous_id.add continuous_const),
    hA.2.comp_homeomorph (Homeomorph.addRight t)⟩

theorem ContCompact.add_nice (hA : ContCompact A) (hB : ContCompact B₁) : ContCompact (fun u => A u + B₁ u) :=
  ⟨hA.1.add hB.1, hA.2.add hB.2⟩

theorem ContCompact.sub_nice (hA : ContCompact A) (hB : ContCompact B₁) : ContCompact (fun u => A u - B₁ u) :=
  ⟨hA.1.sub hB.1, hA.2.sub hB.2⟩

theorem ContCompact.const_mul_nice (c : ℝ) (hA : ContCompact A) : ContCompact (fun u => c * A u) :=
  ⟨continuous_const.mul hA.1, hA.2.mul_left⟩

/-- The pairing `⟪A, B⟫ = ∫ A B`. -/
def testPairing (A B : ℝ → ℝ) : ℝ := ∫ u, A u * B u

theorem testPairing_comm (A B : ℝ → ℝ) : testPairing A B = testPairing B A :=
  integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)

theorem testPairing_self_nonneg (A : ℝ → ℝ) : 0 ≤ testPairing A A :=
  integral_nonneg fun u => mul_self_nonneg _

/-- Translation invariance of the pairing. -/
theorem testPairing_translate (A B : ℝ → ℝ) (c : ℝ) :
    testPairing (fun u => A (u + c)) (fun u => B (u + c)) = testPairing A B :=
  integral_add_right_eq_self (fun x => A x * B x) c

theorem testPairing_add_left (h₁ : ContCompact A) (h₂ : ContCompact B₁) (hB : ContCompact B₂) :
    testPairing (fun u => A u + B₁ u) B₂ = testPairing A B₂ + testPairing B₁ B₂ := by
  have hi₁ : Integrable (fun u => A u * B₂ u) := h₁.integrable_mul hB
  have hi₂ : Integrable (fun u => B₁ u * B₂ u) := h₂.integrable_mul hB
  have hpt : ∀ u, (A u + B₁ u) * B₂ u = A u * B₂ u + B₁ u * B₂ u := fun u => by ring
  show (∫ u, (A u + B₁ u) * B₂ u) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hi₁ hi₂]
  rfl

theorem testPairing_sub_left (h₁ : ContCompact A) (h₂ : ContCompact B₁) (hB : ContCompact B₂) :
    testPairing (fun u => A u - B₁ u) B₂ = testPairing A B₂ - testPairing B₁ B₂ := by
  have hi₁ : Integrable (fun u => A u * B₂ u) := h₁.integrable_mul hB
  have hi₂ : Integrable (fun u => B₁ u * B₂ u) := h₂.integrable_mul hB
  have hpt : ∀ u, (A u - B₁ u) * B₂ u = A u * B₂ u - B₁ u * B₂ u := fun u => by ring
  show (∫ u, (A u - B₁ u) * B₂ u) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hi₁ hi₂]
  rfl

theorem testPairing_const_mul_left (c : ℝ) (A B : ℝ → ℝ) :
    testPairing (fun u => c * A u) B = c * testPairing A B := by
  have hpt : ∀ u, c * A u * B u = c * (A u * B u) := fun u => by ring
  show (∫ u, c * A u * B u) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  rfl

theorem testPairing_add_right (hA : ContCompact A) (h₁ : ContCompact B₁) (h₂ : ContCompact B₂) :
    testPairing A (fun u => B₁ u + B₂ u) = testPairing A B₁ + testPairing A B₂ := by
  rw [testPairing_comm, testPairing_add_left h₁ h₂ hA, testPairing_comm B₁ A, testPairing_comm B₂ A]

theorem testPairing_sub_right (hA : ContCompact A) (h₁ : ContCompact B₁) (h₂ : ContCompact B₂) :
    testPairing A (fun u => B₁ u - B₂ u) = testPairing A B₁ - testPairing A B₂ := by
  rw [testPairing_comm, testPairing_sub_left h₁ h₂ hA, testPairing_comm B₁ A, testPairing_comm B₂ A]

theorem testPairing_const_mul_right (c : ℝ) (A B : ℝ → ℝ) :
    testPairing A (fun u => c * B u) = c * testPairing A B := by
  rw [testPairing_comm, testPairing_const_mul_left, testPairing_comm B A]

/-! ### Autocorrelation as a pairing -/

theorem autoCorr_eq_testPairing (F : ℝ → ℝ) (t : ℝ) :
    autoCorr F t = testPairing F (fun u => F (u + t)) := rfl

/-- The pairing of two translates of a test is an autocorrelation value. -/
theorem testPairing_translate_pair (F : ℝ → ℝ) (a b : ℝ) :
    testPairing (fun u => F (u + a)) (fun u => F (u + b)) = autoCorr F (b - a) := by
  have h : (fun u : ℝ => F (u + b)) = fun u => (fun x => F (x + (b - a))) (u + a) := by
    funext u
    show F (u + b) = F (u + a + (b - a))
    rw [show u + a + (b - a) = u + b by ring]
  rw [h, testPairing_translate F (fun x => F (x + (b - a))) a, autoCorr_eq_testPairing]

/-- `|A(t)| ≤ A(0)`: the autocorrelation of a test is largest at the origin. -/
theorem abs_autoCorr_le_autoCorr_zero (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    |autoCorr F t| ≤ autoCorr F 0 := by
  have hN : ContCompact F := ⟨hF, hFc⟩
  have hNt : ContCompact (fun u => F (u + t)) := hN.translate t
  have h0 : autoCorr F 0 = testPairing F F := by
    rw [autoCorr_eq_testPairing]
    exact congrArg (testPairing F) (by funext u; rw [add_zero])
  have ht0 : testPairing (fun u => F (u + t)) (fun u => F (u + t)) = autoCorr F 0 := by
    rw [testPairing_translate F F t, h0]
  have hsum : 0 ≤ testPairing F F - 2 * autoCorr F t + autoCorr F 0 := by
    have hexp : testPairing (fun u => F u - F (u + t)) (fun u => F u - F (u + t))
        = testPairing F F - 2 * autoCorr F t + autoCorr F 0 := by
      rw [testPairing_sub_left hN hNt (hN.sub_nice hNt), testPairing_sub_right hN hN hNt,
        testPairing_sub_right hNt hN hNt, ht0, testPairing_comm (fun u => F (u + t)) F,
        ← autoCorr_eq_testPairing]
      ring
    exact hexp ▸ testPairing_self_nonneg _
  have hdiff : 0 ≤ testPairing F F + 2 * autoCorr F t + autoCorr F 0 := by
    have hexp : testPairing (fun u => F u + F (u + t)) (fun u => F u + F (u + t))
        = testPairing F F + 2 * autoCorr F t + autoCorr F 0 := by
      rw [testPairing_add_left hN hNt (hN.add_nice hNt), testPairing_add_right hN hN hNt,
        testPairing_add_right hNt hN hNt, ht0, testPairing_comm (fun u => F (u + t)) F,
        ← autoCorr_eq_testPairing]
      ring
    exact hexp ▸ testPairing_self_nonneg _
  rw [abs_le]
  rw [← h0] at hsum hdiff
  constructor <;> linarith

/-- `A(0) ≥ 0`. -/
theorem autoCorr_zero_nonneg (hF : Continuous F) (hFc : HasCompactSupport F) :
    0 ≤ autoCorr F 0 :=
  le_trans (abs_nonneg _) (abs_autoCorr_le_autoCorr_zero hF hFc 0)

/-- Beyond twice the support radius the autocorrelation vanishes. -/
theorem autoCorr_eq_zero_of_support {B : ℝ} (hsupp : ∀ x, B < |x| → F x = 0) {t : ℝ}
    (ht : 2 * B < |t|) : autoCorr F t = 0 := by
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases h1 : F x = 0
  · simp [h1]
  by_cases h2 : F (x + t) = 0
  · simp [h2]
  have b1 : |x| ≤ B := not_lt.mp fun h => h1 (hsupp x h)
  have b2 : |x + t| ≤ B := not_lt.mp fun h => h2 (hsupp _ h)
  have h3 : |t| ≤ |x + t| + |x| := by
    have := abs_sub (x + t) x
    rwa [add_sub_cancel_left] at this
  exact absurd ht (not_lt.mpr (by linarith))

/-! ### Finite combinations of translates and the Gram bound -/

/-- `translateComb F n α c = Σ_{k < n} α k · F(· + c k)`: a finite real combination of right
translates of one test. Every train of this file is of this shape. -/
def translateComb (F : ℝ → ℝ) (n : ℕ) (α c : ℕ → ℝ) : ℝ → ℝ :=
  fun u => ∑ k ∈ Finset.range n, α k * F (u + c k)

theorem translateComb_succ (F : ℝ → ℝ) (n : ℕ) (α c : ℕ → ℝ) :
    translateComb F (n + 1) α c = fun u => translateComb F n α c u + α n * F (u + c n) := by
  funext u; simp [translateComb, Finset.sum_range_succ]

theorem ContCompact.comb (hF : ContCompact F) (n : ℕ) (α c : ℕ → ℝ) :
    ContCompact (translateComb F n α c) := by
  induction n with
  | zero =>
      have h : translateComb F 0 α c = fun _ => (0 : ℝ) := by funext u; simp [translateComb]
      rw [h]
      exact ⟨continuous_const, HasCompactSupport.intro isCompact_empty fun x _ => rfl⟩
  | succ n ih =>
      rw [translateComb_succ]
      exact ih.add_nice (ContCompact.const_mul_nice (α n) (hF.translate (c n)))

/-- Pairing a single translate against a combination. -/
theorem testPairing_single_comb (hF : ContCompact F) (a : ℝ) (m : ℕ) (β d : ℕ → ℝ) :
    testPairing (fun u => F (u + a)) (translateComb F m β d)
      = ∑ j ∈ Finset.range m, β j * autoCorr F (d j - a) := by
  induction m with
  | zero => simp [translateComb, testPairing]
  | succ m ih =>
      rw [translateComb_succ, testPairing_add_right (hF.translate a) (hF.comb m β d)
        (ContCompact.const_mul_nice (β m) (hF.translate (d m))), ih, testPairing_const_mul_right,
        testPairing_translate_pair, Finset.sum_range_succ]

/-- Pairing the test itself against a combination. -/
theorem testPairing_test_comb (hF : ContCompact F) (m : ℕ) (β d : ℕ → ℝ) :
    testPairing F (translateComb F m β d) = ∑ j ∈ Finset.range m, β j * autoCorr F (d j) := by
  have h := testPairing_single_comb hF 0 m β d
  simpa using h

/-- The Gram expansion: the pairing of two combinations is the double sum of autocorrelations. -/
theorem testPairing_comb (hF : ContCompact F) (n m : ℕ) (α c β d : ℕ → ℝ) :
    testPairing (translateComb F n α c) (translateComb F m β d)
      = ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m, α k * β j * autoCorr F (d j - c k) := by
  induction n with
  | zero => simp [translateComb, testPairing]
  | succ n ih =>
      rw [translateComb_succ, testPairing_add_left (hF.comb n α c)
        (ContCompact.const_mul_nice (α n) (hF.translate (c n))) (hF.comb m β d), ih,
        testPairing_const_mul_left, testPairing_single_comb hF, Finset.sum_range_succ, Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

/-- The Gram bound: a pairing of combinations is at most the product of the coefficient masses
times `A(0)`. -/
theorem abs_testPairing_comb_le (hF : ContCompact F) {n m : ℕ} {α c β d : ℕ → ℝ} {Ma Mb : ℝ}
    (hα : ∑ k ∈ Finset.range n, |α k| ≤ Ma) (hβ : ∑ j ∈ Finset.range m, |β j| ≤ Mb)
    (hMb : 0 ≤ Mb) :
    |testPairing (translateComb F n α c) (translateComb F m β d)| ≤ Ma * (Mb * autoCorr F 0) := by
  have h0 : 0 ≤ autoCorr F 0 := autoCorr_zero_nonneg hF.1 hF.2
  have inner : ∀ k, |∑ j ∈ Finset.range m, α k * β j * autoCorr F (d j - c k)|
      ≤ |α k| * (Mb * autoCorr F 0) := by
    intro k
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hb : ∀ j ∈ Finset.range m, |α k * β j * autoCorr F (d j - c k)|
        ≤ |α k| * (|β j| * autoCorr F 0) := by
      intro j _
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (abs_autoCorr_le_autoCorr_zero hF.1 hF.2 _) (abs_nonneg _))
        (abs_nonneg _)
    refine le_trans (Finset.sum_le_sum hb) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hβ h0
  rw [testPairing_comb hF]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun k _ => inner k) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hα (mul_nonneg hMb h0)

/-! ### The geometric train at one spacing -/

/-- Partial geometric sums are bounded by `1/(1−z)`. -/
theorem sum_pow_le_inv_one_sub {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, z ^ k ≤ 1 / (1 - z) := by
  have h1 : (0 : ℝ) < 1 - z := by linarith
  rw [le_div_iff₀ h1]
  have h3 : (∑ k ∈ Finset.range n, z ^ k) * (1 - z) = 1 - z ^ n := by
    have h := geom_sum_mul z n
    linear_combination -h
  rw [h3]
  have : 0 ≤ z ^ n := pow_nonneg hz0 n
  linarith

theorem sum_abs_pow_le_inv_one_sub {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, |z ^ k| ≤ 1 / (1 - z) := by
  have h : ∑ k ∈ Finset.range n, |z ^ k| = ∑ k ∈ Finset.range n, z ^ k :=
    Finset.sum_congr rfl fun k _ => abs_of_pos (pow_pos hz0 k)
  rw [h]
  exact sum_pow_le_inv_one_sub hz0.le hz1 n

/-- Partial sums of `|z^k|` are bounded by `1/(1 − |z|)`, for signed ratios too. -/
theorem sum_abs_pow_le_inv_one_sub_abs {z : ℝ} (hz : |z| < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, |z ^ k| ≤ 1 / (1 - |z|) := by
  have h : ∑ k ∈ Finset.range n, |z ^ k| = ∑ k ∈ Finset.range n, |z| ^ k :=
    Finset.sum_congr rfl fun k _ => abs_pow z k
  rw [h]
  exact sum_pow_le_inv_one_sub (abs_nonneg z) hz n

/-- The geometric train `S_N(u) = Σ_{k ≤ N} z^k F(u + kL)`: the truncated resolvent of the test
for the translation by `L`. -/
def geoTrain (z L : ℝ) (F : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
  translateComb F (N + 1) (fun k => z ^ k) (fun k => (k : ℝ) * L)

/-- The tail translate dropped by the truncation. -/
def geoTail (z L : ℝ) (F : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
  translateComb F 1 (fun _ => z ^ (N + 1)) (fun _ => ((N : ℝ) + 1) * L)

theorem geoTrain_shift (z L : ℝ) (F : ℝ → ℝ) (N : ℕ) (t : ℝ) :
    (fun u => geoTrain z L F N (u + t))
      = translateComb F (N + 1) (fun k => z ^ k) (fun k => (k : ℝ) * L + t) := by
  funext u
  simp only [geoTrain, translateComb]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show u + t + (k : ℝ) * L = u + ((k : ℝ) * L + t) by ring]

theorem geoTail_shift (z L : ℝ) (F : ℝ → ℝ) (N : ℕ) (t : ℝ) :
    (fun u => geoTail z L F N (u + t))
      = translateComb F 1 (fun _ => z ^ (N + 1)) (fun _ => ((N : ℝ) + 1) * L + t) := by
  funext u
  simp only [geoTail, translateComb]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show u + t + ((N : ℝ) + 1) * L = u + (((N : ℝ) + 1) * L + t) by ring]

theorem geoTail_apply (z L : ℝ) (F : ℝ → ℝ) (N : ℕ) (u : ℝ) :
    geoTail z L F N u = z ^ (N + 1) * F (u + ((N : ℝ) + 1) * L) := by
  simp [geoTail, translateComb]

/-- The resolvent identity of the train: `S_N − z S_N(· + L) = F − tail`. -/
theorem geoTrain_resolvent (z L : ℝ) (F : ℝ → ℝ) (N : ℕ) (u : ℝ) :
    geoTrain z L F N u - z * geoTrain z L F N (u + L) = F u - geoTail z L F N u := by
  set g : ℕ → ℝ := fun j => z ^ j * F (u + (j : ℝ) * L) with hg
  have h1 : geoTrain z L F N u = ∑ k ∈ Finset.range (N + 1), g k := rfl
  have h2 : z * geoTrain z L F N (u + L) = ∑ k ∈ Finset.range (N + 1), g (k + 1) := by
    simp only [geoTrain, translateComb, Finset.mul_sum, hg]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [show u + L + (k : ℝ) * L = u + ((k : ℝ) + 1) * L by ring]
    ring
  rw [h1, h2, ← Finset.sum_sub_distrib, Finset.sum_range_sub' g (N + 1), geoTail_apply, hg]
  push_cast
  simp

/-! ### Two-term expansions of the pairing -/

theorem testPairing_add_add {A₁ A₂ B₁' B₂' : ℝ → ℝ} (hA₁ : ContCompact A₁) (hA₂ : ContCompact A₂)
    (hB₁ : ContCompact B₁') (hB₂ : ContCompact B₂') :
    testPairing (fun u => A₁ u + A₂ u) (fun u => B₁' u + B₂' u)
      = testPairing A₁ B₁' + testPairing A₁ B₂' + testPairing A₂ B₁' + testPairing A₂ B₂' := by
  rw [testPairing_add_left hA₁ hA₂ (hB₁.add_nice hB₂), testPairing_add_right hA₁ hB₁ hB₂,
    testPairing_add_right hA₂ hB₁ hB₂]
  ring

theorem testPairing_sub_smul_left {A₁ A₂ B' : ℝ → ℝ} (hA₁ : ContCompact A₁) (hA₂ : ContCompact A₂)
    (hB : ContCompact B') (z : ℝ) :
    testPairing (fun u => A₁ u - z * A₂ u) B' = testPairing A₁ B' - z * testPairing A₂ B' := by
  rw [testPairing_sub_left hA₁ (ContCompact.const_mul_nice z hA₂) hB, testPairing_const_mul_left]

theorem testPairing_sub_smul_sub_smul {A₁ A₂ B₁' B₂' : ℝ → ℝ} (hA₁ : ContCompact A₁) (hA₂ : ContCompact A₂)
    (hB₁ : ContCompact B₁') (hB₂ : ContCompact B₂') (z : ℝ) :
    testPairing (fun u => A₁ u - z * A₂ u) (fun u => B₁' u - z * B₂' u)
      = testPairing A₁ B₁' - z * testPairing A₁ B₂' - z * testPairing A₂ B₁' + z ^ 2 * testPairing A₂ B₂' := by
  rw [testPairing_sub_smul_left hA₁ hA₂ (hB₁.sub_nice (ContCompact.const_mul_nice z hB₂)) z,
    testPairing_sub_right hA₁ hB₁ (ContCompact.const_mul_nice z hB₂),
    testPairing_sub_right hA₂ hB₁ (ContCompact.const_mul_nice z hB₂), testPairing_const_mul_right,
    testPairing_const_mul_right]
  ring


theorem testPairing_cauchy_schwarz (hA : ContCompact A) (hB : ContCompact B₁) :
    testPairing A B₁ ^ 2 ≤ testPairing A A * testPairing B₁ B₁ := by
  have hq : ∀ t : ℝ, 0 ≤ testPairing B₁ B₁ * (t * t) + -2 * testPairing A B₁ * t + testPairing A A := by
    intro t
    have hexp : testPairing (fun u => A u - t * B₁ u) (fun u => A u - t * B₁ u)
        = testPairing B₁ B₁ * (t * t) + -2 * testPairing A B₁ * t + testPairing A A := by
      rw [testPairing_sub_smul_sub_smul hA hB hA hB t, testPairing_comm B₁ A]
      ring
    exact hexp ▸ testPairing_self_nonneg _
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]


theorem testPairing_self_eq_autoCorr_zero (F : ℝ → ℝ) : testPairing F F = autoCorr F 0 := by
  rw [autoCorr_eq_testPairing]
  exact congrArg (testPairing F) (by funext u; rw [add_zero])

theorem testPairing_sub_sub {A₁ A₂ B₁' B₂' : ℝ → ℝ} (h₁ : ContCompact A₁) (h₂ : ContCompact A₂)
    (k₁ : ContCompact B₁') (k₂ : ContCompact B₂') :
    testPairing (fun u => A₁ u - A₂ u) (fun u => B₁' u - B₂' u)
      = testPairing A₁ B₁' - testPairing A₁ B₂' - testPairing A₂ B₁' + testPairing A₂ B₂' := by
  rw [testPairing_sub_left h₁ h₂ (k₁.sub_nice k₂), testPairing_sub_right h₁ k₁ k₂, testPairing_sub_right h₂ k₁ k₂]
  ring

/-! ### Combinations indexed by an arbitrary finite set -/

/-- `finsetComb F s α c = Σ_{i ∈ s} α i · F(· + c i)`: a finite combination of translates indexed
by an arbitrary finite set. -/
def finsetComb {ι : Type*} (F : ℝ → ℝ) (s : Finset ι) (α c : ι → ℝ) : ℝ → ℝ :=
  fun u => ∑ i ∈ s, α i * F (u + c i)

theorem contCompact_finsetComb {ι : Type*} [DecidableEq ι] (hF : ContCompact F) (s : Finset ι)
    (α c : ι → ℝ) : ContCompact (finsetComb F s α c) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h : finsetComb F ∅ α c = fun _ => (0 : ℝ) := by funext u; simp [finsetComb]
      rw [h]
      exact ⟨continuous_const, HasCompactSupport.intro isCompact_empty fun x _ => rfl⟩
  | insert i s hi ih =>
      have h : finsetComb F (insert i s) α c
          = fun u => α i * F (u + c i) + finsetComb F s α c u := by
        funext u
        simp [finsetComb, Finset.sum_insert hi]
      rw [h]
      exact (ContCompact.const_mul_nice (α i) (hF.translate (c i))).add_nice ih

/-- Pairing a single translate against a finite-set-indexed combination. -/
theorem testPairing_single_finsetComb {κ : Type*} (hF : ContCompact F) (a : ℝ) (t : Finset κ)
    (β d : κ → ℝ) :
    testPairing (fun u => F (u + a)) (finsetComb F t β d)
      = ∑ j ∈ t, β j * autoCorr F (d j - a) := by
  classical
  induction t using Finset.induction with
  | empty => simp [finsetComb, testPairing]
  | insert j t hj iht =>
      have hs2 : finsetComb F (insert j t) β d
          = fun u => β j * F (u + d j) + finsetComb F t β d u := by
        funext u
        simp [finsetComb, Finset.sum_insert hj]
      rw [hs2, testPairing_add_right (hF.translate a)
        (ContCompact.const_mul_nice (β j) (hF.translate (d j)))
        (contCompact_finsetComb hF t β d), iht, testPairing_const_mul_right,
        testPairing_translate_pair, Finset.sum_insert hj]

/-- The Gram expansion for combinations indexed by arbitrary finite sets. -/
theorem testPairing_finsetComb {ι κ : Type*} (hF : ContCompact F) (s : Finset ι) (t : Finset κ)
    (α c : ι → ℝ) (β d : κ → ℝ) :
    testPairing (finsetComb F s α c) (finsetComb F t β d)
      = ∑ i ∈ s, ∑ j ∈ t, α i * β j * autoCorr F (d j - c i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [finsetComb, testPairing]
  | insert i s hi ih =>
      have hsplit : finsetComb F (insert i s) α c
          = fun u => α i * F (u + c i) + finsetComb F s α c u := by
        funext u
        simp [finsetComb, Finset.sum_insert hi]
      rw [hsplit, testPairing_add_left
        (ContCompact.const_mul_nice (α i) (hF.translate (c i)))
        (contCompact_finsetComb hF s α c) (contCompact_finsetComb hF t β d), ih,
        testPairing_const_mul_left, testPairing_single_finsetComb hF (c i) t β d,
        Finset.sum_insert hi, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring

end GaloisForLFunctions.ArithmeticIncidencePositivity
