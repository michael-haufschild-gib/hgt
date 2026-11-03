import GaloisForLFunctions.GrowingWindowsOfSpecZ.ACurveDegeneratesAtItsNumberOfAngles
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeHasNoSlackUnderRH
import GaloisForLFunctions.GrowingWindowsOfSpecZ.ForbiddingLatticeZeroModesIsRH

/-!
# Spec ℤ is a curve on every lattice

A lattice of step `h` folds each zero ordinate `γ_ρ` to the angle `e^{iγ_ρh}` on the unit circle.
Under RH every lattice window of Spec ℤ is exactly the window of the curve with these infinitely many
angles and multiplicities `w_ρ = m_ρ|φ̂(γ_ρ)|²`:

* **The orbit correlation is a cosine series** (`weilOrbitCorr_eq_tsum`):
  `c_φ(t) = Σ_ρ w_ρ cos(γ_ρt)`.
* **The folded zero curve** (`toeplitzForm_weilSeq_eq_tsum`):
  `T_N(x) = Σ_ρ w_ρ|Σ_k x_ke^{ikγ_ρh}|²`, the infinite-angle form of `toeplitzForm_curveData`.
* **RH is this identity** (`riemannHypothesis_iff_folded_curve`): conversely the identity at one site
  gives `Q(φ) = Σ_ρ w_ρ ≥ 0` for every test, which is RH.
* **Finite pieces of the curve bound the margins from below** (`levinsonErr_ge_of_le`,
  `toeplitzForm_truncation_le`, `levinsonErr_truncation_le`): margins are monotone in the form, and
  the window of the curve of finitely many zeros `F` lies below the window of Spec ℤ. So
  `E_n(φ, h) ≥ E_n(F)` for every finite set of zeros whose window is positive through `n`; by
  `curveData_posDef` this holds as soon as `F` folds to more than `n` distinct angles.

The finite curves of `ACurveDegeneratesAtItsNumberOfAngles` first fail at their number of angles;
Spec ℤ under RH has infinitely many and never fails, and its margins are squeezed between those of its
finite pieces and the recurrence bound `E_p ≤ Q(φ − φ(· + ph))`.
-/

noncomputable section

open Finset Complex Filter
open scoped ComplexConjugate

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis Zeta23 RHTower.WeilConditional

variable {φ : ℝ → ℝ}

/-! ### One angle -/

/-- The data of a single angle `e^{iθ}` are `cos(dθ)`. -/
theorem curveData_single (θ : ℝ) :
    curveData {cexp (θ * I)} (fun _ => 1) = fun d : ℤ => Real.cos (d * θ) := by
  funext d
  simp only [curveData, Finset.sum_singleton, Complex.ofReal_one, one_mul]
  rw [← Complex.exp_int_mul, show (d : ℂ) * (θ * I) = ((d * θ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-- `Σ_{i,j} cos((i − j)θ)x_ix_j = |Σ_k x_ke^{ikθ}|²`. -/
theorem toeplitzForm_cos (θ : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    toeplitzForm (fun d : ℤ => Real.cos (d * θ)) N x =
      ‖∑ k : Fin N, (x k : ℂ) * cexp (θ * I) ^ (k : ℕ)‖ ^ 2 := by
  rw [← curveData_single, toeplitzForm_curveData (by simp [norm_exp_ofReal_mul_I])]
  simp

/-! ### The folded zero curve -/

/-- The Weil sequence samples the orbit correlation: `κ(d) = c_φ(dh)`. -/
theorem weilSeq_eq_weilOrbitCorr (φ : ℝ → ℝ) (h : ℝ) (d : ℤ) :
    weilSeq φ h d = weilOrbitCorr φ (d * h) := by
  rw [weilSeq, latticeTranslate_eq_scaleShift', weilPair_comm, ← weilOrbitCorr_neg φ (d * h)]
  rfl

/-- Under RH, `Q(φ) = Σ_ρ w_ρ`. -/
theorem weilQuad_eq_tsum_zeroTerm (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) :
    weilQuad φ = ∑' ρ, zeroTerm (cx φ) ρ := by
  rw [LogCells.weilQuad_eq_zetaW hφ.1 hφ.2]
  exact re_W_eq_tsum_zeroTerm hRH (cx_contDiff hφ.1) (cx_hasCompactSupport hφ.2)

/-- **The orbit correlation is a cosine series** (under RH): `c_φ(t) = Σ_ρ w_ρ cos(γ_ρt)`. -/
theorem weilOrbitCorr_eq_tsum (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (t : ℝ) :
    weilOrbitCorr φ t = ∑' ρ, zeroTerm (cx φ) ρ * Real.cos ((ρ : ℂ).im * t) := by
  have hsum := summable_zeroTerm hRH (cx_contDiff hφ.1) (cx_hasCompactSupport hφ.2)
  have hcos : Summable fun ρ => zeroTerm (cx φ) ρ * Real.cos ((ρ : ℂ).im * t) :=
    hsum.of_norm_bounded fun ρ => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (zeroTerm_nonneg _ _)]
      exact mul_le_of_le_one_right (zeroTerm_nonneg _ _) (Real.abs_cos_le_one _)
  have h2 := two_mul_weilSeq_sub hφ t 1
  rw [weilQuad_frobeniusDiff_eq hRH hφ t 1, weilSeq_one] at h2
  have h0 : weilSeq φ t 0 = weilQuad φ := by rw [weilSeq, latticeTranslate_zero]; rfl
  rw [h0, weilQuad_eq_tsum_zeroTerm hRH hφ] at h2
  have hsplit : ∑' ρ, zeroTerm (cx φ) ρ * (2 * (1 - Real.cos ((ρ : ℂ).im * (((1 : ℤ) : ℝ) * t)))) =
      2 * ∑' ρ, zeroTerm (cx φ) ρ - 2 * ∑' ρ, zeroTerm (cx φ) ρ * Real.cos ((ρ : ℂ).im * t) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hsum.mul_left 2).tsum_sub (hcos.mul_left 2)]
    refine tsum_congr fun ρ => ?_
    simp only [Int.cast_one, one_mul]
    ring
  linarith

/-- **Spec ℤ is a curve on every lattice** (under RH): the lattice window of `φ` at step `h` is the
window of the folded zero curve, `T_N(x) = Σ_ρ m_ρ|φ̂(γ_ρ)|²·|Σ_k x_ke^{ikγ_ρh}|²`. -/
theorem toeplitzForm_weilSeq_eq_tsum (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (h : ℝ)
    (N : ℕ) (x : Fin N → ℝ) :
    toeplitzForm (weilSeq φ h) N x = ∑' ρ, zeroTerm (cx φ) ρ *
      ‖∑ k : Fin N, (x k : ℂ) * cexp (((ρ : ℂ).im * h : ℝ) * I) ^ (k : ℕ)‖ ^ 2 := by
  have hsum := summable_zeroTerm hRH (cx_contDiff hφ.1) (cx_hasCompactSupport hφ.2)
  set w := zeroTerm (cx φ)
  -- every entry is a cosine series
  have hseq : ∀ d : ℤ, weilSeq φ h d = ∑' ρ, w ρ * Real.cos (d * ((ρ : ℂ).im * h)) := fun d => by
    rw [weilSeq_eq_weilOrbitCorr, weilOrbitCorr_eq_tsum hRH hφ]
    exact tsum_congr fun ρ => by ring_nf
  have hs : ∀ (d : ℤ) (a : ℝ), Summable fun ρ => w ρ * (Real.cos (d * ((ρ : ℂ).im * h)) * a) :=
    fun d a => (hsum.mul_right |a|).of_norm_bounded fun ρ => by
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (zeroTerm_nonneg _ _), mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (abs_nonneg a) (Real.abs_cos_le_one _)) (zeroTerm_nonneg _ _)
  calc toeplitzForm (weilSeq φ h) N x
      = ∑ i : Fin N, ∑ j : Fin N, ∑' ρ, w ρ *
          (Real.cos (((i : ℤ) - j : ℤ) * ((ρ : ℂ).im * h)) * (x i * x j)) := by
        simp only [toeplitzForm, hseq]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [mul_assoc, ← tsum_mul_right]
        exact tsum_congr fun ρ => by ring
    _ = ∑' ρ, ∑ i : Fin N, ∑ j : Fin N, w ρ *
          (Real.cos (((i : ℤ) - j : ℤ) * ((ρ : ℂ).im * h)) * (x i * x j)) := by
        rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs _ _]
        refine sum_congr rfl fun i _ => ?_
        rw [Summable.tsum_finsetSum fun j _ => hs _ _]
    _ = _ := by
        refine tsum_congr fun ρ => ?_
        rw [← toeplitzForm_cos, toeplitzForm, Finset.mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact sum_congr rfl fun j _ => by ring

/-- **RH is the folded curve identity**: RH holds iff every lattice window of Spec ℤ is the window of
its folded zero curve. -/
theorem riemannHypothesis_iff_folded_curve :
    RiemannHypothesis ↔ ∀ φ ∈ realTests, ∀ (h : ℝ) (N : ℕ) (x : Fin N → ℝ),
      toeplitzForm (weilSeq φ h) N x = ∑' ρ, zeroTerm (cx φ) ρ *
        ‖∑ k : Fin N, (x k : ℂ) * cexp (((ρ : ℂ).im * h : ℝ) * I) ^ (k : ℕ)‖ ^ 2 := by
  refine ⟨fun hRH φ hφ h N x => toeplitzForm_weilSeq_eq_tsum hRH hφ h N x, fun H => ?_⟩
  refine ArithmeticHodgeTheoryOfDegenerations.riemannHypothesis_iff_weilQuad_nonneg.mpr
    fun g hg hgc => ?_
  have h1 := H g ⟨hg, hgc⟩ 1 1 fun _ => 1
  have hT : toeplitzForm (weilSeq g 1) 1 (fun _ => 1) = weilQuad g := by
    simp only [toeplitzForm, Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, sub_self, mul_one]
    rw [weilSeq, latticeTranslate_zero]; rfl
  rw [← hT, h1]
  exact tsum_nonneg fun ρ => mul_nonneg (zeroTerm_nonneg _ _) (sq_nonneg _)

/-! ### Finite pieces of the curve bound the margins -/

variable {κ₁ κ₂ : ℤ → ℝ}

/-- **Margins are monotone in the form.** If `T(κ₁) ≤ T(κ₂)` on size `n + 1` and the evolution of
`κ₁` is positive through `n`, then `E_n(κ₁) ≤ E_n(κ₂)`. -/
theorem levinsonErr_ge_of_le (h₁ : IsEvenSeq κ₁) (h₂ : IsEvenSeq κ₂) {n : ℕ}
    (hpd₁ : ToeplitzPosDef κ₁ n) (hne₁ : ∀ k < n, levinsonErr κ₁ k ≠ 0)
    (hne₂ : ∀ k < n, levinsonErr κ₂ k ≠ 0)
    (hle : ∀ x : Fin (n + 1) → ℝ, toeplitzForm κ₁ (n + 1) x ≤ toeplitzForm κ₂ (n + 1) x) :
    levinsonErr κ₁ n ≤ levinsonErr κ₂ n := by
  calc levinsonErr κ₁ n ≤ toeplitzForm κ₁ (n + 1) (levinsonVec κ₂ n) :=
        levinsonErr_le_toeplitzForm h₁ hpd₁ hne₁ _
    _ ≤ toeplitzForm κ₂ (n + 1) (levinsonVec κ₂ n) := hle _
    _ = levinsonErr κ₂ n := toeplitzForm_levinsonVec h₂ hne₂

/-- The data of the curve of finitely many zeros `F`: `κ_F(d) = Σ_{ρ∈F} w_ρ cos(dγ_ρh)`. -/
def truncSeq (φ : ℝ → ℝ) (h : ℝ) (F : Finset zetaZeroConfig.carrier) (d : ℤ) : ℝ :=
  ∑ ρ ∈ F, zeroTerm (cx φ) ρ * Real.cos (d * ((ρ : ℂ).im * h))

theorem truncSeq_isEven (φ : ℝ → ℝ) (h : ℝ) (F : Finset zetaZeroConfig.carrier) :
    IsEvenSeq (truncSeq φ h F) := fun d => by
  simp only [truncSeq, Int.cast_neg, neg_mul, Real.cos_neg]

theorem toeplitzForm_truncSeq (φ : ℝ → ℝ) (h : ℝ) (F : Finset zetaZeroConfig.carrier) (N : ℕ)
    (x : Fin N → ℝ) :
    toeplitzForm (truncSeq φ h F) N x = ∑ ρ ∈ F, zeroTerm (cx φ) ρ *
      ‖∑ k : Fin N, (x k : ℂ) * cexp (((ρ : ℂ).im * h : ℝ) * I) ^ (k : ℕ)‖ ^ 2 := by
  simp only [← toeplitzForm_cos, toeplitzForm, truncSeq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun ρ _ => by ring

/-- **The window of a finite piece lies below the window of Spec ℤ** (under RH). -/
theorem toeplitzForm_truncation_le (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (h : ℝ)
    (F : Finset zetaZeroConfig.carrier) (N : ℕ) (x : Fin N → ℝ) :
    toeplitzForm (truncSeq φ h F) N x ≤ toeplitzForm (weilSeq φ h) N x := by
  rw [toeplitzForm_truncSeq, toeplitzForm_weilSeq_eq_tsum hRH hφ]
  have hsum := summable_zeroTerm hRH (cx_contDiff hφ.1) (cx_hasCompactSupport hφ.2)
  refine Summable.sum_le_tsum F (fun ρ _ => mul_nonneg (zeroTerm_nonneg _ _) (sq_nonneg _)) ?_
  refine (hsum.mul_right ((∑ k : Fin N, |x k|) ^ 2)).of_nonneg_of_le
    (fun ρ => mul_nonneg (zeroTerm_nonneg _ _) (sq_nonneg _)) fun ρ => ?_
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (zeroTerm_nonneg _ _)
  refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_pow, norm_exp_ofReal_mul_I, one_pow, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- **Finite pieces bound the margins from below** (under RH): if the curve of the zeros `F` is
positive through `n`, then `E_n(F) ≤ E_n(φ, h)`. -/
theorem levinsonErr_truncation_le (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0)
    {h : ℝ} (hh : 0 < h) (F : Finset zetaZeroConfig.carrier) {n : ℕ}
    (hF : ∀ k ≤ n, 0 < levinsonErr (truncSeq φ h F) k) :
    levinsonErr (truncSeq φ h F) n ≤ levinsonErr (weilSeq φ h) n := by
  have hpos : ∀ m, 0 < levinsonErr (weilSeq φ h) m := fun m =>
    riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 h hh m
  have hpd : ToeplitzPosDef (truncSeq φ h F) n := by
    rcases n with _ | m
    · intro x hx; exact absurd (funext fun k => k.elim0) hx
    · exact (toeplitzForm_posDef_iff (truncSeq_isEven φ h F) m).mpr fun k hk => hF k (by omega)
  exact levinsonErr_ge_of_le (truncSeq_isEven φ h F) (weilSeq_isEven φ h) hpd
    (fun k hk => (hF k hk.le).ne') (fun k _ => (hpos k).ne')
    (toeplitzForm_truncation_le hRH hφ h F (n + 1))

end GaloisForLFunctions.GrowingWindowsOfSpecZ
