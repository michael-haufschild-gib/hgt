import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheSzegoVerblunskyLaw

/-!
# Why the datum `(β, s) = (1, 0)` is critical

Adding a log-conductor `s` to a window form adds `s ‖f‖²`: an absolutely continuous spectral density `s` to
the spectral measure of the form. On a lattice this is the Toeplitz form of `κ_s(d) = κ(d) + s δ_{d,0}`
(`withSlack`, `toeplitzForm_withSlack`). Then:

* **`s > 0` is the Szegő side** (`le_levinsonErr_withSlack`, `summable_reflCoeff_sq_withSlack`). Over a nonnegative form the margins
  stay above `s`, and the reflection coefficients are square-summable.
* **`s < 0` is empty** (`exists_toeplitzForm_withSlack_neg`). If the margins of `κ` tend to `0`, then the form of `κ_s` is negative at
  a finite size.
* **`s = 0` is the threshold.** So a positive form with margins tending to zero is exactly the boundary between Szegő and failure
  (`lattice_trichotomy`), and for `Spec ℤ` this boundary position of every lattice is RH
  (`riemannHypothesis_iff_every_lattice_is_at_threshold`).

The answer to *why `(1, 0)`*: the spectral measure of the Weil form is a sum of atoms at the zeros, with zero absolutely continuous
density. A positive `s` gives Szegő's regime, with slack; a negative `s` cannot be paid by atoms, since test functions can
concentrate between them. Zero slack is singularity of the spectral measure. The pole weight enters through the residue
(`datum_classification`).

**The first reflectors** (`reflCoeff_zero_eq`, `reflCoeff_one_eq`). `γ₀ = κ₁/κ₀` is the Born term and
`γ₁ = (κ₀κ₂ − κ₁²)/(κ₀² − κ₁²)`. So the first reflector beyond Born is the Turán–Laguerre form of the
echo: it is present even at an echo-free site `κ₂ = 0`, so reflectors do not stay on the support of the echo train.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GrowingWindowsOfSpecZ ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis

noncomputable section

/-- The lattice data with slack `s`: `κ_s(d) = κ(d) + s δ_{d,0}`. -/
def withSlack (κ : ℤ → ℝ) (s : ℝ) (d : ℤ) : ℝ := κ d + if d = 0 then s else 0

variable {κ : ℤ → ℝ}

theorem withSlack_isEven (hκ : IsEvenSeq κ) (s : ℝ) : IsEvenSeq (withSlack κ s) := fun d => by
  simp only [withSlack, hκ d, neg_eq_zero]

/-- Slack adds a multiple of the identity. -/
theorem toeplitzForm_withSlack (κ : ℤ → ℝ) (s : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    toeplitzForm (withSlack κ s) n x = toeplitzForm κ n x + s * ∑ i, x i ^ 2 := by
  simp only [toeplitzForm, withSlack, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [sq]
    ring
  · intro j _ hj
    have : ((i : ℤ) - j) ≠ 0 := by
      intro h
      apply hj
      apply Fin.ext
      omega
    simp [this]
  · simp

theorem toeplitzForm_zero_vector (κ : ℤ → ℝ) (n : ℕ) : toeplitzForm κ n (fun _ => 0) = 0 := by
  simp [toeplitzForm]

/-- `T_{n+1}(1, a) = E_n` at the Levinson predictor. -/
theorem toeplitzForm_levinsonVec (hκ : IsEvenSeq κ) {n : ℕ} (h : ∀ k < n, levinsonErr κ k ≠ 0) :
    toeplitzForm κ (n + 1) (Fin.cons 1 (levinsonPred κ n)) = levinsonErr κ n := by
  have ha := levinson_isPredictor hκ h
  rw [toeplitzForm_cons hκ ha, predErr_levinson hκ h]
  have e : (fun k => levinsonPred κ n k - 1 * levinsonPred κ n k) = fun _ => 0 := by
    funext k
    ring
  rw [e, toeplitzForm_zero_vector]
  ring

theorem one_le_sum_sq_cons {n : ℕ} (a : Fin n → ℝ) :
    1 ≤ ∑ i, (Fin.cons (1 : ℝ) a : Fin (n + 1) → ℝ) i ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, one_pow]
  have : 0 ≤ ∑ i : Fin n, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- **The Szegő side.** With slack `s > 0` over a nonnegative form the margins stay above `s`. -/
theorem le_levinsonErr_withSlack (hκ : IsEvenSeq κ) (hT : ∀ n x, 0 ≤ toeplitzForm κ n x) {s : ℝ}
    (hs : 0 < s) (n : ℕ) : s ≤ levinsonErr (withSlack κ s) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hne : ∀ k < n, levinsonErr (withSlack κ s) k ≠ 0 := fun k hk =>
      (lt_of_lt_of_le hs (ih k hk)).ne'
    have hv := toeplitzForm_levinsonVec (withSlack_isEven hκ s) hne
    rw [← hv, toeplitzForm_withSlack]
    have h1 := hT (n + 1) (Fin.cons 1 (levinsonPred (withSlack κ s) n))
    have h2 := one_le_sum_sq_cons (levinsonPred (withSlack κ s) n)
    nlinarith

/-- **Slack makes the reflection coefficients square-summable.** -/
theorem summable_reflCoeff_sq_withSlack (hκ : IsEvenSeq κ) (hT : ∀ n x, 0 ≤ toeplitzForm κ n x)
    {s : ℝ} (hs : 0 < s) : Summable fun k => reflCoeff (withSlack κ s) k ^ 2 :=
  (levinsonErr_bounded_below_iff fun n =>
    lt_of_lt_of_le hs (le_levinsonErr_withSlack hκ hT hs n)).mp
      ⟨s, hs, le_levinsonErr_withSlack hκ hT hs⟩

/-- **Negative slack fails at a finite size.** -/
theorem exists_toeplitzForm_withSlack_neg (hκ : IsEvenSeq κ) (hE : ∀ n, 0 < levinsonErr κ n)
    (hlim : Tendsto (fun n => levinsonErr κ n) atTop (𝓝 0)) {s : ℝ} (hs : s < 0) :
    ∃ (n : ℕ) (x : Fin n → ℝ), toeplitzForm (withSlack κ s) n x < 0 := by
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (neg_pos.mpr hs))).exists
  refine ⟨n + 1, Fin.cons 1 (levinsonPred κ n), ?_⟩
  rw [toeplitzForm_withSlack, toeplitzForm_levinsonVec hκ fun k _ => (hE k).ne']
  have h2 := one_le_sum_sq_cons (levinsonPred κ n)
  nlinarith

/-- **The trichotomy of a singular lattice.** A positive evolution with margins tending to zero is the threshold of its slack
family: regular above, positive at zero with `Σ γ² = ∞`, negative below. -/
theorem lattice_trichotomy (hκ : IsEvenSeq κ) (hT : ∀ n x, 0 ≤ toeplitzForm κ n x)
    (hE : ∀ n, 0 < levinsonErr κ n) (hlim : Tendsto (fun n => levinsonErr κ n) atTop (𝓝 0)) :
    (∀ s > 0, ∀ n, s ≤ levinsonErr (withSlack κ s) n) ∧
      (∀ s > 0, Summable fun k => reflCoeff (withSlack κ s) k ^ 2) ∧
      ¬ Summable (fun k => reflCoeff κ k ^ 2) ∧
      (∀ s < 0, ∃ (n : ℕ) (x : Fin n → ℝ), toeplitzForm (withSlack κ s) n x < 0) :=
  ⟨fun _ hs n => le_levinsonErr_withSlack hκ hT hs n,
    fun _ hs => summable_reflCoeff_sq_withSlack hκ hT hs,
    (tendsto_levinsonErr_zero_iff hE).mp hlim,
    fun _ hs => exists_toeplitzForm_withSlack_neg hκ hE hlim hs⟩

/-- `T_n ≥ 0` from positive margins. -/
theorem toeplitzForm_nonneg_of_pos (hκ : IsEvenSeq κ) (hE : ∀ n, 0 < levinsonErr κ n) (n : ℕ)
    (x : Fin n → ℝ) : 0 ≤ toeplitzForm κ n x := by
  cases n with
  | zero => simp [toeplitzForm]
  | succ m =>
    by_cases hx : x = 0
    · subst hx
      exact (toeplitzForm_zero_vector κ (m + 1)).ge
    · exact ((toeplitzForm_posDef_iff hκ m).mpr fun k _ => hE k).2 x hx |>.le

/-- **RH places every lattice of `Spec ℤ` at the threshold of its slack family.** -/
theorem riemannHypothesis_iff_every_lattice_is_at_threshold :
    RiemannHypothesis ↔
      ∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h →
        (∀ n, 0 < levinsonErr (weilSeq φ h) n) ∧
          (∀ s > 0, Summable fun k => reflCoeff (withSlack (weilSeq φ h) s) k ^ 2) ∧
          ¬ Summable (fun k => reflCoeff (weilSeq φ h) k ^ 2) ∧
          ∀ s < 0, ∃ (n : ℕ) (x : Fin n → ℝ), toeplitzForm (withSlack (weilSeq φ h) s) n x < 0 := by
  constructor
  · intro hRH φ hφ hφ0 h hh
    obtain ⟨hE, hlim⟩ := (riemannHypothesis_iff_singular_lattices.mp hRH) φ hφ hφ0 h hh
    have hκ := weilSeq_isEven φ h
    obtain ⟨-, h2, h3, h4⟩ := lattice_trichotomy hκ (toeplitzForm_nonneg_of_pos hκ hE) hE hlim
    exact ⟨hE, h2, h3, h4⟩
  · intro H
    exact riemannHypothesis_iff_levinsonErr_pos.mpr fun φ hφ hφ0 h hh => (H φ hφ hφ0 h hh).1

/-! ### The first reflectors -/

/-- The Born term. -/
theorem reflCoeff_zero_eq (κ : ℤ → ℝ) : reflCoeff κ 0 = κ 1 / κ 0 := by
  simp [reflCoeff, schurParam, schurCoupling, levinsonErr_zero]

/-- **The first reflector beyond Born is the Turán–Laguerre form of the echo.** -/
theorem reflCoeff_one_eq (κ : ℤ → ℝ) (h0 : κ 0 ≠ 0) (h1 : κ 0 ^ 2 - κ 1 ^ 2 ≠ 0) :
    reflCoeff κ 1 = (κ 0 * κ 2 - κ 1 ^ 2) / (κ 0 ^ 2 - κ 1 ^ 2) := by
  have hE : levinsonErr κ 1 = κ 0 - κ 1 ^ 2 / κ 0 := by
    rw [levinsonErr_succ, levinsonErr_zero]
    congr 2
    simp [schurParam, schurCoupling]
  have hP : levinsonPred κ 1 0 = -(κ 1 / κ 0) := by
    rw [levinsonPred_succ]
    simp only [Fin.snoc]
    simp [reflCoeff_zero_eq]
  have hS : schurParam κ 1 = κ 2 - κ 1 ^ 2 / κ 0 := by
    simp only [schurParam, schurCoupling, Fin.sum_univ_one]
    have hrev : Fin.rev (0 : Fin 1) = 0 := rfl
    rw [hrev, hP]
    simp only [Fin.val_zero, Nat.cast_zero, zero_add, Nat.cast_one]
    have e2 : (1 : ℤ) + 1 = 2 := rfl
    rw [e2]
    field_simp
    ring
  rw [reflCoeff, hE, hS]
  have hd : κ 0 - κ 1 ^ 2 / κ 0 ≠ 0 := by
    intro h
    apply h1
    field_simp at h
    linarith
  field_simp
  ring

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
