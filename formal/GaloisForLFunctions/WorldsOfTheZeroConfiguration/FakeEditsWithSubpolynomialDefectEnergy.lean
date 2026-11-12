import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheSignedEditFactorsThroughTheTemperedModel
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheDefectOfATwinOnTheCriticalLine
import GaloisForLFunctions.RHTower.ZetaVerticalMeanSquare

/-!
# Fake edits with subpolynomial defect energy

**Theorem I.4** (`frontier_dichotomy`).  Unconditionally, either the asymptotic abscissa law holds
(`Θ = 1`), or `Θ < 1` and for every `ρ₀ = β₀ + iγ₀` with `1/2 < β₀ < 3/2 - Θ`, `ζ(ρ₀) ≠ 0`, and
every `β_c ∈ (β₀, 1)` there is a two-sided edit of the rational primes which is an integer-norm
fake at `β_c` with density `A > 0`, whose `(s - 1) ζ_B(s)` continues to a half-plane
`Re s > σ₁`, `σ₁ < 1/2`, vanishing at `ρ₀`, and which lies in the Hamburger strip class with a
critical-line FE defect `g` satisfying, for every `ε > 0`,

`‖g(t)‖ ≤ K_ε |ζ(1/2 + 2it)| (1 + |t|)^ε`   and   `(1/2T) ∫_{-T}^{T} ‖g‖² ≤ C_ε T^ε`  (`T ≥ 2`).

**Proof.**  The signed grouped edit (`SignedEdit.sEdit`) factors as
`(s - 1) ζ_B = (s - 1) ζ · M_B`, `M_B = M · exp(H₁ + Q + R)` (`sub_one_mul_zetaSeriesC_eq`).  Right
of `Θ` the reciprocal of `ζ` is subpolynomial (`exists_invZeta_shift_data_of_zeroFree`), the
finite Euler factor is bounded on `Re s ≥ 1/2`, and `|H₁| ≤ C₁ √log(|t|+2) + C₂` with `Q`, `R`
bounded; `C₁ √L ≤ ηL + C₁²/(4η)` turns the exponential into `O((2 + |t|)^η)`
(`exists_norm_editCofactor_le`).  Lemma 1.2(1) gives the Hamburger strip, Lemma 1.2(2) with the
real symmetry of `M_B` gives `g = 2iζ Im M_B`, and the mean square of `ζ` on the critical line
(`exists_integral_normSq_zeta_critical_le`) gives the `L²` bound.
-/

open Complex Finset Filter Topology MeasureTheory Set
open RHTower RHTower.Sieve RHTower.BeurlingDeletion
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.ArithmeticPositiveDuality GaloisForLFunctions.EulerFETransportTheory
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm GaloisForLFunctions.RigidArithmeticOfCuts

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit

variable {α β : ℝ}

/-! ## Elementary bounds -/

/-- `C √L ≤ η L + C²/(4η)`. -/
theorem mul_sqrt_le {C L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) :
    C * Real.sqrt L ≤ η * L + C ^ 2 / (4 * η) := by
  have hs := Real.sq_sqrt hL
  have h : 0 ≤ (2 * η * Real.sqrt L - C) ^ 2 / (4 * η) := by positivity
  have e : η * L + C ^ 2 / (4 * η) - C * Real.sqrt L = (2 * η * Real.sqrt L - C) ^ 2 / (4 * η) := by
    field_simp
    rw [← hs]
    ring
  linarith

/-- `exp(C √log(|t|+2)) ≤ exp(C²/(4η)) (|t| + 2)^η`. -/
theorem exp_mul_sqrt_log_le {C η : ℝ} (hη : 0 < η) (t : ℝ) :
    Real.exp (C * Real.sqrt (Real.log (|t| + 2))) ≤
      Real.exp (C ^ 2 / (4 * η)) * (|t| + 2) ^ η := by
  have hL : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hpow : (|t| + 2) ^ η = Real.exp (η * Real.log (|t| + 2)) := by
    rw [Real.rpow_def_of_pos (by positivity)]; ring_nf
  rw [hpow, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith [mul_sqrt_le (C := C) hL hη])

/-! ## Subpolynomial growth of the cofactor -/

/-- The finite Euler factor of the model is bounded on `Re s ≥ 1/2`. -/
theorem exists_norm_posFiniteFactor_le (hβ : β < 1) (γ : ℝ) (k₀ : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖posFiniteFactor (2 ^ k₀ - 1) (zeroPt β γ) s‖ ≤ B := by
  set c : ℝ := (2 : ℝ) ^ (β - 3 / 2) with hc
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc0 : 0 ≤ c := by positivity
  have hinv : 0 ≤ (1 - c)⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨((1 - c)⁻¹ * (1 - c)⁻¹) ^ (smallPrimes (2 ^ k₀ - 1)).card, by positivity,
    fun s hs => ?_⟩
  have hfac : ∀ z : ℂ, ‖z‖ ≤ c → ‖(1 - z)⁻¹‖ ≤ (1 - c)⁻¹ := by
    intro z hz
    rw [norm_inv]
    have h1 : 1 - c ≤ ‖1 - z‖ := by
      have := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one] at this
      linarith
    exact inv_anti₀ (by linarith) h1
  have hpow : ∀ q : Nat.Primes, ∀ w : ℂ, w.re ≤ β - 3 / 2 → ‖((q : ℕ) : ℂ) ^ w‖ ≤ c := by
    intro q w hw
    rw [Complex.norm_natCast_cpow_of_pos q.2.pos]
    have hq2 : (2 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.2.two_le
    calc ((q : ℕ) : ℝ) ^ w.re ≤ (2 : ℝ) ^ w.re :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (by linarith)
      _ ≤ c := Real.rpow_le_rpow_of_exponent_le (by norm_num) hw
  unfold posFiniteFactor
  refine (norm_prod_le _ _).trans ?_
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hfac _ (hpow q _ (by simp [zeroPt]; linarith)))
    (hfac _ (hpow q _ (by simp [zeroPt]; linarith))) (norm_nonneg _) hinv

theorem two_add_abs_sub_le (t γ : ℝ) : 2 + |t - γ| ≤ (1 + |γ|) * (2 + |t|) := by
  have := abs_sub t γ
  nlinarith [abs_nonneg t, abs_nonneg γ]

/-- **The model cofactor is subpolynomial** on `1/2 ≤ Re s ≤ 2` when `ζ` has no zero right of
`Θ < 3/2 - β`. -/
theorem exists_norm_posCofactor_le (hβ : β < 1) (γ : ℝ) (k₀ : ℕ) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ)
    (hΘ1 : Θ ≤ 1) (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (hΘβ : Θ + β < 3 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖posCofactor (2 ^ k₀ - 1) (zeroPt β γ) s‖ ≤ K * (2 + |s.im|) ^ ε := by
  set δ : ℝ := (3 / 2 - β - Θ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  obtain ⟨Kb, hKb, -, hinv⟩ := exists_invZeta_shift_data_of_zeroFree hΘ hΘ1 hzf hδ0 hδ1
    (half_pos hε) 3
  obtain ⟨B, hB, hfin⟩ := exists_norm_posFiniteFactor_le hβ γ k₀
  refine ⟨Kb * (1 + |γ|) ^ (ε / 2) * (Kb * (1 + |γ|) ^ (ε / 2)) * B, by positivity,
    fun s hs1 hs2 => ?_⟩
  have hmem : ∀ w : ℂ, w.re = s.re + 1 - β → w ∈ GaloisForLFunctions.HTGeometry.verticalStrip (Θ + δ) 3 := by
    intro w hw
    rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip, hw]
    constructor <;> linarith
  have hb : ∀ w : ℂ, w.re = s.re + 1 - β → |w.im| ≤ |s.im - γ| ∨ |w.im| ≤ |s.im + γ| →
      ‖invZeta w‖ ≤ Kb * (1 + |γ|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2) := by
    intro w hw him
    refine (hinv w (hmem w hw)).trans ?_
    have hle : 2 + |w.im| ≤ (1 + |γ|) * (2 + |s.im|) := by
      rcases him with h | h
      · exact (by linarith : 2 + |w.im| ≤ 2 + |s.im - γ|).trans (two_add_abs_sub_le _ _)
      · have := two_add_abs_sub_le s.im (-γ)
        rw [sub_neg_eq_add, abs_neg] at this
        linarith
    calc Kb * (2 + |w.im|) ^ (ε / 2) ≤ Kb * ((1 + |γ|) * (2 + |s.im|)) ^ (ε / 2) := by
          gcongr
      _ = Kb * (1 + |γ|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  have h1 := hb (s + 1 - zeroPt β γ) (by simp [zeroPt]) (Or.inl (by simp [zeroPt]))
  have h2 := hb (s + 1 - (starRingEnd ℂ) (zeroPt β γ)) (by simp [zeroPt])
    (Or.inr (by simp [zeroPt]))
  unfold posCofactor
  rw [norm_mul, norm_mul]
  calc ‖invZeta (s + 1 - zeroPt β γ)‖ * ‖invZeta (s + 1 - (starRingEnd ℂ) (zeroPt β γ))‖ *
        ‖posFiniteFactor (2 ^ k₀ - 1) (zeroPt β γ) s‖
      ≤ (Kb * (1 + |γ|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2)) *
          (Kb * (1 + |γ|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2)) * B := by
        gcongr
        exact hfin s hs1
    _ = Kb * (1 + |γ|) ^ (ε / 2) * (Kb * (1 + |γ|) ^ (ε / 2)) * B *
          ((2 + |s.im|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2)) := by ring
    _ = _ := by
        rw [← Real.rpow_add (by positivity)]; ring_nf

/-- The exponent `H₁ + Q + R` grows at most like `√log` on `Re s ≥ 1/2`. -/
theorem exists_norm_editExponent_le (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ)
    {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖editExponent α β γ k₀ s‖ ≤ C₁ * Real.sqrt (Real.log (|s.im| + 2)) + C₂ := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hH⟩ := exists_norm_editSeries_le hα0 hα hβ γ hk₀
    (σ₀ := 1 / 2) (by linarith)
  obtain ⟨CQ, hCQ, hQ⟩ := exists_norm_editRem_le (β := β) hα0 hα γ k₀ (σ₀ := 1 / 2) (by linarith)
  obtain ⟨CR, hCR, hR⟩ := exists_norm_pairRem_le β γ k₀ (σ₀ := 1 / 2) (by linarith)
  refine ⟨C₁, C₂ + CQ + CR, hC₁, by positivity, fun s hs => ?_⟩
  unfold editExponent
  have := norm_add₃_le (editSeries α β γ k₀ s) (editRem (sEdit α β γ k₀) s) (pairRem β γ k₀ s)
  linarith [hH s hs, hQ s hs, hR s hs]

/-- **The cofactor of the edit is subpolynomial**: for every `ε > 0`,
`‖M_B(s)‖ ≤ K (2 + |Im s|)^ε` on `1/2 ≤ Re s ≤ 2`. -/
theorem exists_norm_editCofactor_le (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ)
    {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (hΘβ : Θ + β < 3 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖editCofactor α β γ k₀ s‖ ≤ K * (2 + |s.im|) ^ ε := by
  obtain ⟨KM, hKM, hM⟩ := exists_norm_posCofactor_le hβ γ k₀ hΘ hΘ1 hzf hΘβ (half_pos hε)
  obtain ⟨C₁, C₂, hC₁, hC₂, hE⟩ := exists_norm_editExponent_le hα0 hα hβ γ hk₀
  refine ⟨KM * (Real.exp C₂ * Real.exp (C₁ ^ 2 / (4 * (ε / 2)))), by positivity,
    fun s hs1 hs2 => ?_⟩
  have hexp : ‖cexp (editExponent α β γ k₀ s)‖ ≤
      Real.exp C₂ * (Real.exp (C₁ ^ 2 / (4 * (ε / 2))) * (|s.im| + 2) ^ (ε / 2)) := by
    rw [Complex.norm_exp]
    calc Real.exp (editExponent α β γ k₀ s).re ≤ Real.exp ‖editExponent α β γ k₀ s‖ :=
          Real.exp_le_exp.mpr (Complex.re_le_norm _)
      _ ≤ Real.exp (C₁ * Real.sqrt (Real.log (|s.im| + 2)) + C₂) :=
          Real.exp_le_exp.mpr (hE s hs1)
      _ = Real.exp C₂ * Real.exp (C₁ * Real.sqrt (Real.log (|s.im| + 2))) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ _ := by gcongr; exact exp_mul_sqrt_log_le (half_pos hε) s.im
  unfold editCofactor
  rw [norm_mul]
  calc ‖posCofactor (2 ^ k₀ - 1) (zeroPt β γ) s‖ * ‖cexp (editExponent α β γ k₀ s)‖
      ≤ (KM * (2 + |s.im|) ^ (ε / 2)) *
          (Real.exp C₂ * (Real.exp (C₁ ^ 2 / (4 * (ε / 2))) * (|s.im| + 2) ^ (ε / 2))) :=
        mul_le_mul (hM s hs1 hs2) hexp (norm_nonneg _) (by positivity)
    _ = KM * (Real.exp C₂ * Real.exp (C₁ ^ 2 / (4 * (ε / 2)))) *
          ((2 + |s.im|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2)) := by
        rw [add_comm (|s.im|) 2]; ring
    _ = _ := by rw [← Real.rpow_add (by positivity)]; ring_nf

/-! ## Polynomial growth of `(s - 1) ζ(s)` on the Hamburger strip -/

theorem exists_norm_zetaResidueUnit_strip_le :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      ‖zetaResidueUnit s‖ ≤ C * (1 + |s.im|) ^ N := by
  obtain ⟨Cz, Nz, hCz, hz⟩ := exists_bound_norm_riemannZeta_strip 2
  set K : Set ℂ := Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-1 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    (fun s _ => (analyticAt_zetaResidueUnit s).continuousAt.continuousWithinAt)
  refine ⟨max (max M 0) (2 * Cz), Nz + 1, by positivity, fun s hs1 hs2 => ?_⟩
  have hpow1 : (1 : ℝ) ≤ (1 + |s.im|) ^ (Nz + 1) := one_le_pow₀ (by linarith [abs_nonneg s.im])
  by_cases ht : 1 ≤ |s.im|
  · have hs1' : s ≠ 1 := fun h => by rw [h] at ht; norm_num at ht
    rw [zetaResidueUnit_of_ne hs1', norm_mul]
    have hsre : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hzs := hz s.re s.im hsre ht
    rw [← Complex.re_add_im s] at hzs ⊢
    have hn : ‖((s.re : ℂ) + (s.im : ℂ) * I) - 1‖ ≤ 2 * (1 + |s.im|) := by
      have := Complex.norm_le_abs_re_add_abs_im (((s.re : ℂ) + (s.im : ℂ) * I) - 1)
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.one_re, Complex.sub_im,
        Complex.add_im, Complex.mul_im, Complex.one_im] at this
      norm_num at this
      have : |s.re - 1| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith [abs_nonneg s.im]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one] at hzs ⊢
    have hp : |s.im| ^ Nz ≤ (1 + |s.im|) ^ Nz := pow_le_pow_left₀ (abs_nonneg _) (by linarith) Nz
    calc ‖((s.re : ℂ) + (s.im : ℂ) * I) - 1‖ * ‖riemannZeta ((s.re : ℂ) + (s.im : ℂ) * I)‖
        ≤ (2 * (1 + |s.im|)) * (Cz * (1 + |s.im|) ^ Nz) :=
          mul_le_mul hn (hzs.trans (by gcongr)) (norm_nonneg _) (by positivity)
      _ = 2 * Cz * (1 + |s.im|) ^ (Nz + 1) := by ring
      _ ≤ max (max M 0) (2 * Cz) * (1 + |s.im|) ^ (Nz + 1) := by gcongr; exact le_max_right _ _
  · push Not at ht
    have hsK : s ∈ K := by
      rw [hK, Complex.mem_reProdIm]
      exact ⟨⟨hs1, hs2⟩, (abs_le.mp ht.le)⟩
    calc ‖zetaResidueUnit s‖ ≤ max M 0 := (hM s hsK).trans (le_max_left _ _)
      _ ≤ max (max M 0) (2 * Cz) := le_max_left _ _
      _ ≤ max (max M 0) (2 * Cz) * (1 + |s.im|) ^ (Nz + 1) :=
          le_mul_of_one_le_right (by positivity) hpow1

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
