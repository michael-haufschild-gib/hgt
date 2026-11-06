import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeCanonicalSystem
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# The anchor flow of a lattice window

Evaluation of a lattice window at a real anchor `s` is the discrete form of the canonical flow of
the window tower. Let `a^{(n)}` be the Levinson predictors, and put

* `L_n(s) = 1 + Σ_k a_k s^{k+1}`, the left trace (the reversed orthogonal polynomial);
* `R_n(s) = s^n + Σ_k a_{n−1−k} s^k`, the right trace (the monic orthogonal polynomial);
* `K_n(s,t) = Σ_{k<n} R_k(s)R_k(t)/E_k`, the reproducing kernel of the window of size `n`.

With `γ_n` the reflection coefficients:

* **Szegő step** (`latticeLeftTrace_succ`, `latticeRightTrace_succ`):
  `L_{n+1} = L_n − γ_n s R_n`, `R_{n+1} = s R_n − γ_n L_n`;
* **Flux** (`latticeFlux`): `L_n(s)L_n(t) − R_n(s)R_n(t) = (1−st) E_n K_n(s,t)`;
* **The kernel is literal** (`windowEval_sq_le_latticeKernel`, `exists_windowEval_eq_latticeKernel`):
  `K_n(s,s)` is the sharp constant of `(Σ_k x_k s^k)² ≤ K_n(s,s) T_n(x)`;
* **Riccati** (`latticeRiccati`): the reflection `r_n = R_n/L_n` obeys
  `r_{n+1} = (s r_n − γ_n)/(1 − γ_n s r_n)`. In `L = artanh r` this is
  `artanh r_{n+1} = artanh(s r_n) − artanh γ_n` (`artanh_latticeReflection_succ`): a contraction
  followed by an additive kick, the discrete form of `L′ = q − sinh 2L`;
* **Contact** (`latticeReflection_contact`): at a first vanishing margin `r` hits exactly `−γ_n = ±1`.
-/

noncomputable section

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open Finset Set

variable (κ : ℤ → ℝ)

/-- The left trace `L_n(s) = 1 + Σ_k a_k s^{k+1}`. -/
def latticeLeftTrace (s : ℝ) (n : ℕ) : ℝ :=
  1 + ∑ k : Fin n, levinsonPred κ n k * s ^ ((k : ℕ) + 1)

/-- The right trace `R_n(s) = s^n + Σ_k a_{n−1−k} s^k`. -/
def latticeRightTrace (s : ℝ) (n : ℕ) : ℝ :=
  s ^ n + ∑ k : Fin n, levinsonPred κ n (Fin.rev k) * s ^ (k : ℕ)

/-- The reproducing kernel `K_n(s,t) = Σ_{k<n} R_k(s)R_k(t)/E_k` of the window of size `n`. -/
def latticeKernel (s t : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, latticeRightTrace κ s k * latticeRightTrace κ t k / levinsonErr κ k

/-- The anchor reflection `r_n = R_n/L_n`. -/
def latticeReflection (s : ℝ) (n : ℕ) : ℝ := latticeRightTrace κ s n / latticeLeftTrace κ s n

/-- Evaluation of the window polynomial at a real point. -/
def windowEval (s : ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ := ∑ k : Fin n, x k * s ^ (k : ℕ)

@[simp] theorem latticeLeftTrace_zero (s : ℝ) : latticeLeftTrace κ s 0 = 1 := by
  simp [latticeLeftTrace]

@[simp] theorem latticeRightTrace_zero (s : ℝ) : latticeRightTrace κ s 0 = 1 := by
  simp [latticeRightTrace]

variable {κ}

/-- The left half of the Szegő step. -/
theorem latticeLeftTrace_succ (s : ℝ) (n : ℕ) :
    latticeLeftTrace κ s (n + 1) =
      latticeLeftTrace κ s n - reflCoeff κ n * s * latticeRightTrace κ s n := by
  simp only [latticeLeftTrace, latticeRightTrace, levinsonPred_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have h : ∑ k : Fin n, (levinsonPred κ n k - reflCoeff κ n * levinsonPred κ n (Fin.rev k)) *
      s ^ ((k : ℕ) + 1) = ∑ k : Fin n, levinsonPred κ n k * s ^ ((k : ℕ) + 1) -
        reflCoeff κ n * s * ∑ k : Fin n, levinsonPred κ n (Fin.rev k) * s ^ (k : ℕ) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [h]
  ring

/-- The right half of the Szegő step. -/
theorem latticeRightTrace_succ (s : ℝ) (n : ℕ) :
    latticeRightTrace κ s (n + 1) =
      s * latticeRightTrace κ s n - reflCoeff κ n * latticeLeftTrace κ s n := by
  have hrs (j : Fin n) : Fin.rev j.succ = (Fin.rev j).castSucc := by
    ext
    simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
    omega
  simp only [latticeLeftTrace, latticeRightTrace, levinsonPred_succ]
  rw [Fin.sum_univ_succ]
  simp only [hrs, Fin.rev_zero, Fin.snoc_last, Fin.snoc_castSucc, Fin.rev_rev, Fin.val_zero,
    Fin.val_succ, pow_zero, mul_one]
  have h : ∑ k : Fin n, (levinsonPred κ n (Fin.rev k) - reflCoeff κ n * levinsonPred κ n k) *
      s ^ ((k : ℕ) + 1) = s * ∑ k : Fin n, levinsonPred κ n (Fin.rev k) * s ^ (k : ℕ) -
        reflCoeff κ n * ∑ k : Fin n, levinsonPred κ n k * s ^ ((k : ℕ) + 1) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [h]
  ring

theorem latticeKernel_succ (s t : ℝ) (n : ℕ) :
    latticeKernel κ s t (n + 1) = latticeKernel κ s t n +
      latticeRightTrace κ s n * latticeRightTrace κ t n / levinsonErr κ n :=
  sum_range_succ _ _

/-- **The flux identity** (Christoffel–Darboux):
`L_n(s)L_n(t) − R_n(s)R_n(t) = (1−st) E_n K_n(s,t)`. -/
theorem latticeFlux (s t : ℝ) :
    ∀ n : ℕ, (∀ k < n, levinsonErr κ k ≠ 0) →
      latticeLeftTrace κ s n * latticeLeftTrace κ t n -
        latticeRightTrace κ s n * latticeRightTrace κ t n =
        (1 - s * t) * levinsonErr κ n * latticeKernel κ s t n
  | 0, _ => by simp [latticeKernel]
  | n + 1, h => by
    have ih := latticeFlux s t n fun k hk => h k (by omega)
    have hE := h n (by omega)
    rw [latticeLeftTrace_succ, latticeLeftTrace_succ, latticeRightTrace_succ,
      latticeRightTrace_succ, levinsonErr_succ_eq_mul hE, latticeKernel_succ]
    have he : levinsonErr κ n * (latticeKernel κ s t n +
        latticeRightTrace κ s n * latticeRightTrace κ t n / levinsonErr κ n) =
        levinsonErr κ n * latticeKernel κ s t n +
          latticeRightTrace κ s n * latticeRightTrace κ t n := by
      field_simp
    linear_combination (1 - reflCoeff κ n ^ 2) * ih - (1 - s * t) * (1 - reflCoeff κ n ^ 2) * he

/-- Evaluation splits along the mirror one-collar decomposition. -/
theorem windowEval_snoc (s : ℝ) (n : ℕ) (x : Fin n → ℝ) (x₁ : ℝ) :
    windowEval s (n + 1) (Fin.snoc x x₁) =
      windowEval s n (fun k => x k - x₁ * levinsonPred κ n (Fin.rev k)) +
        x₁ * latticeRightTrace κ s n := by
  simp only [windowEval, latticeRightTrace]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have h : ∑ k : Fin n, (x k - x₁ * levinsonPred κ n (Fin.rev k)) * s ^ (k : ℕ) =
      ∑ k : Fin n, x k * s ^ (k : ℕ) -
        x₁ * ∑ k : Fin n, levinsonPred κ n (Fin.rev k) * s ^ (k : ℕ) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [h]
  ring

/-- The Cauchy step of the orthogonal decomposition. -/
private theorem cauchy_step {A K T E R x₁ : ℝ} (hA : A ^ 2 ≤ K * T) (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hE : 0 < E) : (A + x₁ * R) ^ 2 ≤ (K + R ^ 2 / E) * (E * x₁ ^ 2 + T) := by
  have hab : (A * x₁ * R) ^ 2 ≤ (K * E * x₁ ^ 2) * (R ^ 2 * T / E) := by
    have h : (K * E * x₁ ^ 2) * (R ^ 2 * T / E) = K * T * (x₁ ^ 2 * R ^ 2) := by
      field_simp
    rw [h]
    nlinarith only [mul_le_mul_of_nonneg_right hA (mul_nonneg (sq_nonneg x₁) (sq_nonneg R))]
  have ha : 0 ≤ K * E * x₁ ^ 2 := by positivity
  have hb : 0 ≤ R ^ 2 * T / E := by positivity
  have hsq : (2 * (A * x₁ * R)) ^ 2 ≤ (K * E * x₁ ^ 2 + R ^ 2 * T / E) ^ 2 := by
    nlinarith only [hab, sq_nonneg (K * E * x₁ ^ 2 - R ^ 2 * T / E)]
  have hc := (abs_le_of_sq_le_sq' hsq (add_nonneg ha hb)).2
  have he : (K + R ^ 2 / E) * (E * x₁ ^ 2 + T) =
      K * E * x₁ ^ 2 + K * T + R ^ 2 * x₁ ^ 2 + R ^ 2 * T / E := by
    field_simp
    ring
  rw [he]
  nlinarith only [hA, hc]

theorem latticeKernel_nonneg (s : ℝ) {n : ℕ} (h : ∀ k < n, 0 < levinsonErr κ k) :
    0 ≤ latticeKernel κ s s n :=
  sum_nonneg fun k hk => div_nonneg (mul_self_nonneg _) (h k (Finset.mem_range.mp hk)).le

/-- **The kernel bound**: on a positive window, `(Σ_k x_k s^k)² ≤ K_n(s,s) T_n(x)`. -/
theorem windowEval_sq_le_latticeKernel (hκ : IsEvenSeq κ) (s : ℝ) :
    ∀ n : ℕ, (∀ k < n, 0 < levinsonErr κ k) → ∀ x : Fin n → ℝ,
      windowEval s n x ^ 2 ≤ latticeKernel κ s s n * toeplitzForm κ n x ∧
        0 ≤ toeplitzForm κ n x
  | 0, _ => fun x => by simp [windowEval, latticeKernel, toeplitzForm]
  | n + 1, h => fun x => by
    have hlow : ∀ k < n, 0 < levinsonErr κ k := fun k hk => h k (by omega)
    have hE := h n (by omega)
    have hne : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => (hlow k hk).ne'
    have hp := levinson_isPredictor hκ hne
    have herr := predErr_levinson hκ hne
    rw [← Fin.snoc_init_self x]
    set x₁ := x (Fin.last n)
    set y := Fin.init x
    have hdecomp := toeplitzForm_snoc hκ hp y x₁
    rw [herr] at hdecomp
    obtain ⟨hA, hT⟩ := windowEval_sq_le_latticeKernel hκ s n hlow
      (fun k => y k - x₁ * levinsonPred κ n (Fin.rev k))
    rw [hdecomp, windowEval_snoc, latticeKernel_succ]
    refine ⟨?_, add_nonneg (mul_nonneg hE.le (sq_nonneg _)) hT⟩
    have hc := cauchy_step (R := latticeRightTrace κ s n) (x₁ := x₁) hA
      (latticeKernel_nonneg s hlow) hT hE
    rw [show latticeRightTrace κ s n * latticeRightTrace κ s n / levinsonErr κ n =
      latticeRightTrace κ s n ^ 2 / levinsonErr κ n by rw [sq]]
    exact hc

/-- **The kernel is attained**: there is a window vector with `F_x(s) = T_n(x) = K_n(s,s)`. -/
theorem exists_windowEval_eq_latticeKernel (hκ : IsEvenSeq κ) (s : ℝ) :
    ∀ n : ℕ, (∀ k < n, 0 < levinsonErr κ k) → ∃ x : Fin n → ℝ,
      windowEval s n x = latticeKernel κ s s n ∧ toeplitzForm κ n x = latticeKernel κ s s n
  | 0, _ => ⟨Fin.elim0, by simp [windowEval, latticeKernel], by simp [toeplitzForm, latticeKernel]⟩
  | n + 1, h => by
    have hlow : ∀ k < n, 0 < levinsonErr κ k := fun k hk => h k (by omega)
    have hE := h n (by omega)
    have hne : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => (hlow k hk).ne'
    have hp := levinson_isPredictor hκ hne
    have herr := predErr_levinson hκ hne
    obtain ⟨x, hx, hT⟩ := exists_windowEval_eq_latticeKernel hκ s n hlow
    set c := latticeRightTrace κ s n / levinsonErr κ n with hc
    have hres : (fun k => (x k + c * levinsonPred κ n (Fin.rev k)) -
        c * levinsonPred κ n (Fin.rev k)) = x := by
      funext k
      ring
    refine ⟨Fin.snoc (fun k => x k + c * levinsonPred κ n (Fin.rev k)) c, ?_, ?_⟩
    · rw [windowEval_snoc, hres, hx, latticeKernel_succ, hc]
      field_simp
    · rw [toeplitzForm_snoc hκ hp, herr, hres, hT, latticeKernel_succ, hc]
      field_simp
      ring

/-- The kernel of a nonempty positive window is positive. -/
theorem latticeKernel_pos (s : ℝ) {n : ℕ} (hn : 0 < n) (h : ∀ k < n, 0 < levinsonErr κ k) :
    0 < latticeKernel κ s s n := by
  refine sum_pos' (fun k hk => div_nonneg (mul_self_nonneg _)
    (h k (Finset.mem_range.mp hk)).le) ⟨0, Finset.mem_range.mpr hn, ?_⟩
  simpa using h 0 hn

/-- The anchor identity `L² − R² = (1−s²) E_n K_n`. -/
theorem latticeAnchorIdentity (s : ℝ) {n : ℕ} (h : ∀ k < n, levinsonErr κ k ≠ 0) :
    latticeLeftTrace κ s n ^ 2 - latticeRightTrace κ s n ^ 2 =
      (1 - s ^ 2) * levinsonErr κ n * latticeKernel κ s s n := by
  have hf := latticeFlux s s n h
  rw [sq, sq, sq]
  exact hf

/-- Below contact the reflection lies strictly inside `(−1,1)`. -/
theorem latticeReflection_sq_lt {s : ℝ} (hs : s ^ 2 < 1) {n : ℕ} (hn : 0 < n)
    (h : ∀ k ≤ n, 0 < levinsonErr κ k) :
    latticeLeftTrace κ s n ≠ 0 ∧ latticeReflection κ s n ^ 2 < 1 := by
  have hlt : ∀ k < n, 0 < levinsonErr κ k := fun k hk => h k hk.le
  have hid := latticeAnchorIdentity s (fun k hk => (hlt k hk).ne') (κ := κ) (n := n)
  have hpos : 0 < (1 - s ^ 2) * levinsonErr κ n * latticeKernel κ s s n :=
    mul_pos (mul_pos (by linarith only [hs]) (h n le_rfl)) (latticeKernel_pos s hn hlt)
  have hL : latticeLeftTrace κ s n ≠ 0 := by
    intro h0
    rw [h0] at hid
    nlinarith only [hid, hpos, sq_nonneg (latticeRightTrace κ s n)]
  refine ⟨hL, ?_⟩
  have hLp : 0 < latticeLeftTrace κ s n ^ 2 := by positivity
  rw [latticeReflection, div_pow, div_lt_one hLp]
  linarith only [hid, hpos]

theorem latticeReflection_zero (s : ℝ) : latticeReflection κ s 0 = 1 := by
  simp [latticeReflection]

/-- **The lattice Riccati equation**: `r_{n+1} = (s r_n − γ_n)/(1 − γ_n s r_n)`. -/
theorem latticeRiccati {s : ℝ} {n : ℕ} (hL : latticeLeftTrace κ s n ≠ 0)
    (hL' : latticeLeftTrace κ s (n + 1) ≠ 0) :
    latticeReflection κ s (n + 1) =
      (s * latticeReflection κ s n - reflCoeff κ n) /
        (1 - reflCoeff κ n * (s * latticeReflection κ s n)) := by
  have hf : latticeLeftTrace κ s (n + 1) = latticeLeftTrace κ s n *
      (1 - reflCoeff κ n * (s * latticeReflection κ s n)) := by
    rw [latticeLeftTrace_succ, latticeReflection]
    field_simp
  have hne : 1 - reflCoeff κ n * (s * latticeReflection κ s n) ≠ 0 := fun h0 =>
    hL' (by rw [hf, h0, mul_zero])
  rw [latticeReflection, latticeRightTrace_succ, hf]
  rw [div_eq_div_iff (mul_ne_zero hL hne) hne, latticeReflection]
  field_simp

/-- **The discrete form of `(log K)′ = 2m`**: one step multiplies the kernel by
`1 + (1−s²) r²/(1−r²)`. -/
theorem latticeKernel_succ_eq_mul {s : ℝ} (hs : s ^ 2 < 1) {n : ℕ} (hn : 0 < n)
    (h : ∀ k ≤ n, 0 < levinsonErr κ k) :
    latticeKernel κ s s (n + 1) = latticeKernel κ s s n *
      (1 + (1 - s ^ 2) * latticeReflection κ s n ^ 2 / (1 - latticeReflection κ s n ^ 2)) := by
  obtain ⟨hL, hr⟩ := latticeReflection_sq_lt hs hn h
  have hlt : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => (h k hk.le).ne'
  have hid := latticeAnchorIdentity s hlt (κ := κ)
  have hE := (h n le_rfl).ne'
  have hne : 1 - latticeReflection κ s n ^ 2 ≠ 0 := by linarith only [hr]
  have hD : latticeLeftTrace κ s n ^ 2 - latticeRightTrace κ s n ^ 2 ≠ 0 := by
    intro h0
    apply hne
    rw [latticeReflection, div_pow]
    field_simp
    linarith only [h0]
  have hr' : (1 - latticeReflection κ s n ^ 2) * latticeLeftTrace κ s n ^ 2 =
      latticeLeftTrace κ s n ^ 2 - latticeRightTrace κ s n ^ 2 := by
    rw [latticeReflection, div_pow]
    field_simp
  have hrr : latticeReflection κ s n ^ 2 * latticeLeftTrace κ s n ^ 2 =
      latticeRightTrace κ s n ^ 2 := by
    rw [latticeReflection, div_pow]
    field_simp
  rw [latticeKernel_succ]
  field_simp
  have hmain : latticeRightTrace κ s n * latticeRightTrace κ s n *
      (1 - latticeReflection κ s n ^ 2) = latticeReflection κ s n ^ 2 *
        ((1 - latticeReflection κ s n ^ 2) * latticeLeftTrace κ s n ^ 2) := by
    rw [← sq, ← hrr]
    ring
  rw [hr', hid] at hmain
  linear_combination hmain

/-! ### Admission and the additive kick -/

/-- The kick is a disc automorphism: for `w² < 1`, the identity
`(1−γw)² − (w−γ)² = (1−γ²)(1−w²)` makes admission of `γ` the same as admission of the image. -/
theorem sq_sub_lt_sq_iff {w γ : ℝ} (hw : w ^ 2 < 1) :
    (w - γ) ^ 2 < (1 - γ * w) ^ 2 ↔ γ ^ 2 < 1 := by
  have hid : (1 - γ * w) ^ 2 - (w - γ) ^ 2 = (1 - γ ^ 2) * (1 - w ^ 2) := by ring
  have hw' : 0 < 1 - w ^ 2 := by linarith only [hw]
  constructor
  · intro h
    have hpos : 0 < (1 - γ ^ 2) * (1 - w ^ 2) := by linarith only [hid, h]
    have := (pos_iff_pos_of_mul_pos hpos).mpr hw'
    linarith only [this]
  · intro h
    have hpos : 0 < (1 - γ ^ 2) * (1 - w ^ 2) := mul_pos (by linarith only [h]) hw'
    linarith only [hid, hpos]

/-- The next margin is positive iff the next step of the flow is admitted. -/
theorem levinsonErr_succ_pos_iff {n : ℕ} {w : ℝ} (hw : w ^ 2 < 1) (hE : 0 < levinsonErr κ n) :
    0 < levinsonErr κ (n + 1) ↔ (w - reflCoeff κ n) ^ 2 < (1 - reflCoeff κ n * w) ^ 2 := by
  rw [sq_sub_lt_sq_iff hw, levinsonErr_succ_eq_mul hE.ne']
  constructor
  · intro h
    have := (pos_iff_pos_of_mul_pos h).mp hE
    linarith only [this]
  · intro h
    exact mul_pos hE (by linarith only [h])

private theorem artanh_mobius {w γ : ℝ} (hw : w ∈ Ioo (-1 : ℝ) 1) (hγ : γ ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh ((w - γ) / (1 - γ * w)) = Real.artanh w - Real.artanh γ := by
  have hden : 0 < 1 - γ * w := by nlinarith only [hw.1, hw.2, hγ.1, hγ.2]
  have hw1 : 0 < 1 + w := by linarith only [hw.1]
  have hw2 : 0 < 1 - w := by linarith only [hw.2]
  have hg1 : 0 < 1 + γ := by linarith only [hγ.1]
  have hg2 : 0 < 1 - γ := by linarith only [hγ.2]
  have hne := hden.ne'
  have hplus : 1 + (w - γ) / (1 - γ * w) = (1 + w) * (1 - γ) / (1 - γ * w) := by
    rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
    ring
  have hminus : 1 - (w - γ) / (1 - γ * w) = (1 - w) * (1 + γ) / (1 - γ * w) := by
    rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
    ring
  have hRp : 0 < (1 + w) * (1 - γ) / (1 - γ * w) := by positivity
  have hRm : 0 < (1 - w) * (1 + γ) / (1 - γ * w) := by positivity
  have hR : (w - γ) / (1 - γ * w) ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith only [hplus, hminus, hRp, hRm]
  rw [Real.artanh_eq_half_log hR, Real.artanh_eq_half_log (Ioo_subset_Icc_self hw),
    Real.artanh_eq_half_log (Ioo_subset_Icc_self hγ), hplus, hminus,
    Real.log_div hRp.ne' hRm.ne', Real.log_div hw1.ne' hw2.ne', Real.log_div hg1.ne' hg2.ne',
    Real.log_div (mul_pos hw1 hg2).ne' hden.ne', Real.log_div (mul_pos hw2 hg1).ne' hden.ne',
    Real.log_mul hw1.ne' hg2.ne', Real.log_mul hw2.ne' hg1.ne']
  ring

/-- `|artanh(s r)| ≤ |artanh r|` for `0 ≤ s ≤ 1`: the free step contracts towards zero. -/
theorem abs_artanh_mul_le {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hr : r ∈ Ioo (-1 : ℝ) 1) :
    |Real.artanh (s * r)| ≤ |Real.artanh r| := by
  have hsr : s * r ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith only [hs0, hs1, hr.1, hr.2]
  rcases le_total 0 r with h | h
  · have h1 : 0 ≤ Real.artanh (s * r) := Real.artanh_nonneg (mul_nonneg hs0 h)
    have h2 : 0 ≤ Real.artanh r := Real.artanh_nonneg h
    rw [abs_of_nonneg h1, abs_of_nonneg h2]
    exact (Real.artanh_le_artanh_iff hsr hr).mpr (by nlinarith only [hs1, h])
  · have h1 : Real.artanh (s * r) ≤ 0 :=
      Real.artanh_nonpos (mul_nonpos_of_nonneg_of_nonpos hs0 h)
    have h2 : Real.artanh r ≤ 0 := Real.artanh_nonpos h
    rw [abs_of_nonpos h1, abs_of_nonpos h2]
    exact neg_le_neg ((Real.artanh_le_artanh_iff hr hsr).mpr (by nlinarith only [hs1, h]))

/-- **The hyperbolic form of the lattice flow**: a free step `L ↦ artanh(s tanh L)` followed by the
additive kick `−artanh γ_n`. -/
theorem artanh_latticeReflection_succ {s : ℝ} (hs : s ^ 2 < 1) {n : ℕ}
    (hw : (s * latticeReflection κ s n) ^ 2 < 1) (hL : latticeLeftTrace κ s n ≠ 0)
    (hE : 0 < levinsonErr κ n) (hE' : 0 < levinsonErr κ (n + 1)) :
    Real.artanh (latticeReflection κ s (n + 1)) =
      Real.artanh (s * latticeReflection κ s n) - Real.artanh (reflCoeff κ n) := by
  have _ := hs
  have hγ : reflCoeff κ n ^ 2 < 1 := by
    rw [levinsonErr_succ_eq_mul hE.ne'] at hE'
    have := (pos_iff_pos_of_mul_pos hE').mp hE
    linarith only [this]
  have hwI : s * latticeReflection κ s n ∈ Ioo (-1 : ℝ) 1 :=
    abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hw)
  have hγI : reflCoeff κ n ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hγ)
  have hden : 0 < 1 - reflCoeff κ n * (s * latticeReflection κ s n) := by
    nlinarith only [hwI.1, hwI.2, hγI.1, hγI.2]
  have hL' : latticeLeftTrace κ s (n + 1) ≠ 0 := by
    rw [latticeLeftTrace_succ]
    have hf : latticeLeftTrace κ s n - reflCoeff κ n * s * latticeRightTrace κ s n =
        latticeLeftTrace κ s n * (1 - reflCoeff κ n * (s * latticeReflection κ s n)) := by
      rw [latticeReflection]
      field_simp
    rw [hf]
    exact mul_ne_zero hL hden.ne'
  rw [latticeRiccati hL hL', artanh_mobius hwI hγI]

/-- **The restoring bound of the lattice**: `|L_{n+1}| ≤ |L_n| + |artanh γ_n|`, for `0 ≤ s < 1`, past
the first step. -/
theorem abs_artanh_latticeReflection_succ_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {n : ℕ}
    (hn : 0 < n) (h : ∀ k ≤ n + 1, 0 < levinsonErr κ k) :
    |Real.artanh (latticeReflection κ s (n + 1))| ≤
      |Real.artanh (latticeReflection κ s n)| + |Real.artanh (reflCoeff κ n)| := by
  have hs : s ^ 2 < 1 := by nlinarith only [hs0, hs1]
  obtain ⟨hL, hr⟩ := latticeReflection_sq_lt hs hn fun k hk => h k (by omega)
  have hrI := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hr)
  have hw : (s * latticeReflection κ s n) ^ 2 < 1 := by
    rw [mul_pow]
    nlinarith only [hr, hs, sq_nonneg s, sq_nonneg (latticeReflection κ s n)]
  rw [artanh_latticeReflection_succ hs hw hL (h n (by omega)) (h (n + 1) le_rfl)]
  refine (abs_sub _ _).trans (add_le_add_left ?_ _)
  exact abs_artanh_mul_le hs0 hs1.le hrI

/-! ### Contact -/

/-- At every positive stage the left trace is nonzero and `s r_n` lies inside the disc. -/
theorem latticeAnchor_sq_lt {s : ℝ} (hs : s ^ 2 < 1) {n : ℕ} (h : ∀ k ≤ n, 0 < levinsonErr κ k) :
    latticeLeftTrace κ s n ≠ 0 ∧ (s * latticeReflection κ s n) ^ 2 < 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [latticeReflection_zero] using hs
  · obtain ⟨hL, hr⟩ := latticeReflection_sq_lt hs hn h
    refine ⟨hL, ?_⟩
    rw [mul_pow]
    nlinarith only [hr, hs, sq_nonneg s, sq_nonneg (latticeReflection κ s n)]

/-- **Contact of the lattice flow.** At a first vanishing margin the reflection coefficient has
square one and the anchor reflection equals `−γ_n = ±1`, whatever the anchor. -/
theorem latticeReflection_contact {s : ℝ} (hs : s ^ 2 < 1) {n : ℕ}
    (h : ∀ k ≤ n, 0 < levinsonErr κ k) (h0 : levinsonErr κ (n + 1) = 0) :
    reflCoeff κ n ^ 2 = 1 ∧ latticeReflection κ s (n + 1) = -reflCoeff κ n := by
  have hγ := reflCoeff_sq_of_critical (h n le_rfl).ne' h0
  refine ⟨hγ, ?_⟩
  obtain ⟨hL, hr⟩ := latticeAnchor_sq_lt hs h
  have hden : 1 - reflCoeff κ n * (s * latticeReflection κ s n) ≠ 0 := by
    intro h1
    have hγw : reflCoeff κ n * (s * latticeReflection κ s n) = 1 := by linarith only [h1]
    have hsq : (reflCoeff κ n * (s * latticeReflection κ s n)) ^ 2 = 1 := by rw [hγw, one_pow]
    rw [mul_pow, hγ, one_mul] at hsq
    linarith only [hsq, hr]
  have hL' : latticeLeftTrace κ s (n + 1) ≠ 0 := by
    have hf : latticeLeftTrace κ s (n + 1) = latticeLeftTrace κ s n *
        (1 - reflCoeff κ n * (s * latticeReflection κ s n)) := by
      rw [latticeLeftTrace_succ, latticeReflection]
      field_simp
    rw [hf]
    exact mul_ne_zero hL hden
  rw [latticeRiccati hL hL', div_eq_iff hden]
  linear_combination (-(s * latticeReflection κ s n)) * hγ

end GaloisForLFunctions.GrowingWindowsOfSpecZ
