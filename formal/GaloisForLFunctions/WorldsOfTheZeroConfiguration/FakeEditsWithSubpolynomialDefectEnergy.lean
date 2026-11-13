import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheSignedEditFactorsThroughTheTemperedModel
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheDefectOfATwinOnTheCriticalLine
import GaloisForLFunctions.RHTower.ZetaVerticalMeanSquare
import GaloisForLFunctions.RHTower.ZetaSubconvexStripBound

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
  set x := Real.sqrt L
  rw [← hs]
  have h : 0 ≤ (2 * η * x - C) ^ 2 / (4 * η) := by positivity
  have e : η * x ^ 2 + C ^ 2 / (4 * η) - C * x = (2 * η * x - C) ^ 2 / (4 * η) := by
    field_simp
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
  refine (Finset.norm_prod_le _ _).trans ?_
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
theorem exists_norm_posCofactor_le (hβ0 : 0 ≤ β) (hβ : β < 1) (γ : ℝ) (k₀ : ℕ) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ)
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
  have hmem : ∀ w : ℂ, w.re = s.re + 1 - β →
      w ∈ GaloisForLFunctions.HTGeometry.verticalStrip (Θ + δ) 3 := fun w hw =>
    ⟨by rw [hw, hδ]; linarith, by rw [hw]; linarith⟩
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
  have : ‖editSeries α β γ k₀ s + editRem (sEdit α β γ k₀) s + pairRem β γ k₀ s‖ ≤
      ‖editSeries α β γ k₀ s‖ + ‖editRem (sEdit α β γ k₀) s‖ + ‖pairRem β γ k₀ s‖ :=
    norm_add₃_le
  linarith [hH s hs, hQ s hs, hR s hs]

/-- **The cofactor of the edit is subpolynomial**: for every `ε > 0`,
`‖M_B(s)‖ ≤ K (2 + |Im s|)^ε` on `1/2 ≤ Re s ≤ 2`. -/
theorem exists_norm_editCofactor_le (hα0 : 0 < α) (hα : α < 1) (hβ0 : 0 ≤ β) (hβ : β < 1) (γ : ℝ)
    {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (hΘβ : Θ + β < 3 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖editCofactor α β γ k₀ s‖ ≤ K * (2 + |s.im|) ^ ε := by
  obtain ⟨KM, hKM, hM⟩ := exists_norm_posCofactor_le hβ0 hβ γ k₀ hΘ hΘ1 hzf hΘβ (half_pos hε)
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
    rw [zetaResidueUnit_eq_of_ne hs1', norm_mul]
    have hsre : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hzs := hz s.re s.im hsre ht
    rw [Complex.re_add_im] at hzs
    have hn : ‖s - 1‖ ≤ 2 * (1 + |s.im|) := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (s - 1)
      have h2 : |(s - 1).re| ≤ 1 / 2 := by
        rw [Complex.sub_re, Complex.one_re]; exact abs_le.mpr ⟨by linarith, by linarith⟩
      have h3 : (s - 1).im = s.im := by simp
      rw [h3] at h1
      linarith [abs_nonneg s.im]
    have hp : |s.im| ^ Nz ≤ (1 + |s.im|) ^ Nz := pow_le_pow_left₀ (abs_nonneg _) (by linarith) Nz
    calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ (2 * (1 + |s.im|)) * (Cz * (1 + |s.im|) ^ Nz) :=
          mul_le_mul hn (hzs.trans (mul_le_mul_of_nonneg_left hp hCz)) (norm_nonneg _)
            (by positivity)
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

/-! ## The continuation and its zeros -/

/-- The abscissa `σ₁ = max(α/2, β - 1/2, Θ + β - 1)` of the continuation. -/
def contAbscissa (α β Θ : ℝ) : ℝ := max (max (α / 2) (β - 1 / 2)) (Θ + β - 1)

theorem contAbscissa_lt_half (hα : α < 1) (hβ : β < 1) {Θ : ℝ} (hΘβ : Θ + β < 3 / 2) :
    contAbscissa α β Θ < 1 / 2 :=
  max_lt (max_lt (by linarith) (by linarith)) (by linarith)

theorem lt_re_of_contAbscissa_lt {Θ : ℝ} {s : ℂ} (hs : contAbscissa α β Θ < s.re) :
    α / 2 < s.re ∧ β - 1 / 2 < s.re ∧ Θ + β - 1 < s.re := by
  simp only [contAbscissa, max_lt_iff] at hs
  exact ⟨hs.1.1, hs.1.2, hs.2⟩

/-- The continuation `G_B = (s - 1) ζ(s) · M_B(s)` of `(s - 1) ζ_B(s)`. -/
def editG (α β γ : ℝ) (k₀ : ℕ) (s : ℂ) : ℂ := zetaResidueUnit s * editCofactor α β γ k₀ s

theorem editG_eq (hβ : β < 1) (γ : ℝ) (k₀ : ℕ) {s : ℂ} (hs : 1 < s.re) :
    editG α β γ k₀ s = (s - 1) * (editSystem (sEdit α β γ k₀)).zetaSeriesC s :=
  (sub_one_mul_zetaSeriesC_eq hβ γ k₀ hs).symm

theorem differentiableOn_editG (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ)
    {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) :
    DifferentiableOn ℂ (editG α β γ k₀) {s : ℂ | contAbscissa α β Θ < s.re} := fun s hs =>
  (analyticAt_zetaResidueUnit s).differentiableAt.differentiableWithinAt.mul
    ((differentiableOn_editCofactor hα0 hα hβ γ hk₀ hΘ hzf).mono
      (fun _ h => lt_re_of_contAbscissa_lt h) s hs)

theorem invZeta_eq_zero_iff {Θ : ℝ} (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) {w : ℂ}
    (hw : Θ < w.re) : invZeta w = 0 ↔ w = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, invZeta_one]⟩
  by_contra hw1
  rw [invZeta_eq_inv hw1] at h
  exact inv_ne_zero (hzf w hw) h

theorem posFiniteFactor_ne_zero (γ : ℝ) (k₀ : ℕ) {s : ℂ} (hs : β - 1 < s.re) :
    posFiniteFactor (2 ^ k₀ - 1) (zeroPt β γ) s ≠ 0 := by
  unfold posFiniteFactor
  refine Finset.prod_ne_zero_iff.mpr fun q _ => mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_) <;>
  · refine one_sub_ne_zero_of_norm_lt ?_
    rw [Complex.norm_natCast_cpow_of_pos q.2.pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast q.2.one_lt)
      (by simp [zeroPt]; linarith)

/-- **The zeros of the continuation** on `Re s > σ₁` are those of `(s - 1) ζ(s)` and the pair
`{ρ₀, ρ̄₀}`. -/
theorem editG_eq_zero_iff (γ : ℝ) (k₀ : ℕ) {Θ : ℝ}
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) {s : ℂ} (hs : contAbscissa α β Θ < s.re) :
    editG α β γ k₀ s = 0 ↔
      zetaResidueUnit s = 0 ∨ s = zeroPt β γ ∨ s = (starRingEnd ℂ) (zeroPt β γ) := by
  obtain ⟨-, h2, h3⟩ := lt_re_of_contAbscissa_lt hs
  have hw1 : Θ < (s + 1 - zeroPt β γ).re := by simp [zeroPt]; linarith
  have hw2 : Θ < (s + 1 - (starRingEnd ℂ) (zeroPt β γ)).re := by simp [zeroPt]; linarith
  have hfin := posFiniteFactor_ne_zero (β := β) γ k₀ (s := s) (by linarith)
  have e1 : s + 1 - zeroPt β γ = 1 ↔ s = zeroPt β γ :=
    ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have e2 : s + 1 - (starRingEnd ℂ) (zeroPt β γ) = 1 ↔ s = (starRingEnd ℂ) (zeroPt β γ) :=
    ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  simp only [editG, editCofactor, posCofactor, mul_eq_zero, Complex.exp_ne_zero, or_false, hfin,
    invZeta_eq_zero_iff hzf hw1, invZeta_eq_zero_iff hzf hw2, e1, e2]

/-! ## The Hamburger strip and the defect -/

/-- **Lemma 1.2(1) for the edit**: `ζ_B` lies in the Hamburger strip class with defect
`g = stripDefect G_B`. -/
theorem hamburgerStripDefect_editG (hα0 : 0 < α) (hα : α < 1) (hβ0 : 0 ≤ β) (hβ : β < 1)
    (γ : ℝ) {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (hΘβ : Θ + β < 3 / 2) :
    HamburgerStripDefect (editSystem (sEdit α β γ k₀)).zetaSeriesC (editG α β γ k₀ 1 / 2)
      (stripDefect (editG α β γ k₀)) := by
  have hd := differentiableOn_editG hα0 hα hβ γ hk₀ hΘ hzf
  have hσ := contAbscissa_lt_half hα hβ hΘβ
  have hsub : GaloisForLFunctions.HTGeometry.verticalStrip (1 / 2) (3 / 2) ⊆
      {s : ℂ | contAbscissa α β Θ < s.re} := fun s hs => by
    have := (GaloisForLFunctions.HTGeometry.mem_verticalStrip.mp hs).1
    show _ < s.re
    linarith
  obtain ⟨Cz, Nz, hCz, hz⟩ := exists_norm_zetaResidueUnit_strip_le
  obtain ⟨K, hK, hM⟩ :=
    exists_norm_editCofactor_le hα0 hα hβ0 hβ γ hk₀ hΘ hΘ1 hzf hΘβ one_pos
  refine hamburgerStripDefect_of_stripContinuation (hd.mono hsub).continuousOn
    (hd.mono fun s hs => by
      simp only [Set.mem_setOf_eq] at hs ⊢
      linarith [hs.1])
    (fun s hs => editG_eq hβ γ k₀ (by rw [hs]; norm_num)) (C₀ := Cz * (2 * K)) (N₀ := Nz + 1)
    fun s hs => ?_
  obtain ⟨h1, h2⟩ := GaloisForLFunctions.HTGeometry.mem_verticalStrip.mp hs
  unfold editG
  rw [norm_mul]
  have hb : (2 + |s.im|) ^ (1 : ℝ) ≤ 2 * (1 + |s.im|) := by
    rw [Real.rpow_one]; linarith [abs_nonneg s.im]
  calc ‖zetaResidueUnit s‖ * ‖editCofactor α β γ k₀ s‖
      ≤ (Cz * (1 + |s.im|) ^ Nz) * (K * (2 * (1 + |s.im|))) :=
        mul_le_mul (hz s h1 h2) ((hM s h1 (by linarith)).trans (by gcongr)) (norm_nonneg _)
          (by positivity)
    _ = Cz * (2 * K) * (1 + |s.im|) ^ (Nz + 1) := by ring

/-- **Lemma 1.2(2) for the edit**: `g(t) = 2i ζ(1/2 + 2it) Im M_B(1/2 + 2it)`. -/
theorem stripDefect_editG (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ)
    {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (hΘβ : Θ + β < 3 / 2) (t : ℝ) :
    stripDefect (editG α β γ k₀) t = 2 * I * riemannZeta ((1 / 2 : ℂ) + (2 * t : ℝ) * I) *
      ((editCofactor α β γ k₀ ((1 / 2 : ℂ) + (2 * t : ℝ) * I)).im : ℂ) := by
  have hσ := contAbscissa_lt_half hα hβ hΘβ
  have hL : DifferentiableOn ℂ (posCofactor (2 ^ k₀ - 1) (zeroPt β γ))
      {s : ℂ | contAbscissa α β Θ < s.re} := fun s hs =>
    (differentiableAt_posCofactor_of_re_gt γ hΘ hzf (2 ^ k₀ - 1)
      (lt_re_of_contAbscissa_lt hs).2.2).differentiableWithinAt
  have hH : DifferentiableOn ℂ (editExponent α β γ k₀) {s : ℂ | contAbscissa α β Θ < s.re} :=
    (differentiableOn_editExponent hα0 hα hβ γ hk₀).mono fun s hs =>
      ⟨(lt_re_of_contAbscissa_lt hs).1, (lt_re_of_contAbscissa_lt hs).2.1⟩
  have h := FEDefect.IsFactorTwinOn.stripDefect_eq hσ hL hH (C := 1)
    (fun s hs => by rw [sub_one_mul_zetaSeriesC_eq hβ γ k₀ hs, editCofactor, one_mul]) t
  have hG : (fun s => zetaResidueUnit s * (1 * posCofactor (2 ^ k₀ - 1) (zeroPt β γ) s *
      cexp (editExponent α β γ k₀ s))) = editG α β γ k₀ :=
    funext fun s => by rw [one_mul]; rfl
  rw [hG] at h
  rw [h, editCofactor, one_mul]

/-- **The defect is `ζ` times a subpolynomial factor**: `‖g(t)‖ ≤ K ‖ζ(1/2 + 2it)‖ (1 + |t|)^ε`. -/
theorem exists_norm_stripDefect_editG_le (hα0 : 0 < α) (hα : α < 1) (hβ0 : 0 ≤ β) (hβ : β < 1)
    (γ : ℝ) {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (hΘβ : Θ + β < 3 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, ‖stripDefect (editG α β γ k₀) t‖ ≤
      K * ‖riemannZeta ((1 / 2 : ℂ) + (2 * t : ℝ) * I)‖ * (1 + |t|) ^ ε := by
  obtain ⟨K, hK, hM⟩ := exists_norm_editCofactor_le hα0 hα hβ0 hβ γ hk₀ hΘ hΘ1 hzf hΘβ hε
  refine ⟨2 * K * 2 ^ ε, by positivity, fun t => ?_⟩
  rw [stripDefect_editG hα0 hα hβ γ hk₀ hΘ hzf hΘβ t]
  set s : ℂ := (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hsim : s.im = 2 * t := by simp [hs]
  have hn : ‖(2 : ℂ) * I * riemannZeta s * ((editCofactor α β γ k₀ s).im : ℂ)‖ =
      2 * ‖riemannZeta s‖ * |(editCofactor α β γ k₀ s).im| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have him : |(editCofactor α β γ k₀ s).im| ≤ K * (2 ^ ε * (1 + |t|) ^ ε) := by
    refine (Complex.abs_im_le_norm _).trans ((hM s (by rw [hsre]) (by rw [hsre]; norm_num)).trans
      (le_of_eq ?_))
    rw [hsim, abs_mul, abs_two, show (2 : ℝ) + 2 * |t| = 2 * (1 + |t|) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  rw [hn]
  calc 2 * ‖riemannZeta s‖ * |(editCofactor α β γ k₀ s).im|
      ≤ 2 * ‖riemannZeta s‖ * (K * (2 ^ ε * (1 + |t|) ^ ε)) := by gcongr
    _ = 2 * K * 2 ^ ε * ‖riemannZeta s‖ * (1 + |t|) ^ ε := by ring

/-! ## Size of `ζ` on the critical line -/

theorem continuous_zeta_line :
    Continuous fun u : ℝ => riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hne : (1 / 2 : ℂ) + (u : ℂ) * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  exact (differentiableAt_riemannZeta hne).continuousAt.comp
    (f := fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I) (by fun_prop)

theorem continuous_zeta_double :
    Continuous fun t : ℝ => riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I) :=
  continuous_zeta_line.comp (continuous_const.mul continuous_id)

/-- **Mean square on the doubled line**: `∫_{-T}^{T} ‖ζ(1/2 + 2it)‖² dt ≤ D T^{1+η}` for `T ≥ 2`. -/
theorem exists_integral_normSq_zeta_double_le {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, 2 ≤ T →
      ∫ t in (-T)..T, ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ^ 2 ≤
        D * T ^ (1 + η) := by
  obtain ⟨D₀, hD₀, hms⟩ := exists_integral_normSq_zeta_critical_le
  have hc : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  simp only [hc] at hms
  refine ⟨2⁻¹ * D₀ * (1 + 2 / η) ^ 2 * 3 ^ (1 + η), by positivity, fun T hT => ?_⟩
  set f : ℝ → ℝ := fun u => ‖riemannZeta ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ^ 2 with hf
  have hfc : Continuous f := continuous_zeta_line.norm.pow 2
  set N : ℕ := ⌈2 * T⌉₊ with hN
  have hN4 : 4 ≤ N := by
    have : (4 : ℝ) ≤ N := (by linarith : (4 : ℝ) ≤ 2 * T).trans (Nat.le_ceil _)
    exact_mod_cast this
  have hNle : (N : ℝ) ≤ 3 * T := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hscale : ∫ t in (-T)..T, f (2 * t) = 2⁻¹ * ∫ u in (-(2 * T))..(2 * T), f u := by
    rw [intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul,
      mul_neg]
  have hmono : ∫ u in (-(2 * T))..(2 * T), f u ≤ ∫ u in (-(N : ℝ))..(N : ℝ), f u :=
    intervalIntegral.integral_mono_interval (by linarith [Nat.le_ceil (2 * T)]) (by linarith)
      (Nat.le_ceil _) (Filter.Eventually.of_forall fun u => by positivity)
      (hfc.intervalIntegrable _ _)
  have hmsN := hms hN4
  set x : ℝ := (N : ℝ) with hx
  have hx1 : 1 ≤ x := by
    have : (4 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN4
    linarith
  have hlog : Real.log x ≤ x ^ (η / 2) / (η / 2) := Real.log_le_rpow_div (by linarith) (by linarith)
  have hxη : 1 ≤ x ^ (η / 2) := Real.one_le_rpow hx1 (by linarith)
  have h1 : 1 + Real.log x ≤ (1 + 2 / η) * x ^ (η / 2) := by
    have e : x ^ (η / 2) / (η / 2) = 2 / η * x ^ (η / 2) := by field_simp
    have : 0 ≤ 2 / η := by positivity
    nlinarith
  have h2 : (1 + Real.log x) ^ 2 ≤ (1 + 2 / η) ^ 2 * x ^ η := by
    have h0 : 0 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx1]
    calc (1 + Real.log x) ^ 2 ≤ ((1 + 2 / η) * x ^ (η / 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (1 + 2 / η) ^ 2 * x ^ η := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ (η / 2)) 2, ← Real.rpow_mul (by linarith)]
          congr 2
          push_cast
          ring
  have h3 : x * x ^ η = x ^ (1 + η) := by rw [Real.rpow_add (by linarith), Real.rpow_one]
  have h4 : x ^ (1 + η) ≤ (3 * T) ^ (1 + η) := Real.rpow_le_rpow (by linarith) hNle (by linarith)
  have h5 : (3 * T) ^ (1 + η) = 3 ^ (1 + η) * T ^ (1 + η) :=
    Real.mul_rpow (by norm_num) (by linarith)
  change ∫ t in (-T)..T, f (2 * t) ≤ _
  rw [hscale]
  calc 2⁻¹ * ∫ u in (-(2 * T))..(2 * T), f u ≤ 2⁻¹ * (D₀ * x * (1 + Real.log x) ^ 2) := by
        gcongr
        exact hmono.trans hmsN
    _ ≤ 2⁻¹ * (D₀ * x * ((1 + 2 / η) ^ 2 * x ^ η)) := by gcongr
    _ = 2⁻¹ * D₀ * (1 + 2 / η) ^ 2 * (x * x ^ η) := by ring
    _ ≤ 2⁻¹ * D₀ * (1 + 2 / η) ^ 2 * (3 ^ (1 + η) * T ^ (1 + η)) := by
        rw [h3]; gcongr; exact h4.trans h5.le
    _ = _ := by ring

/-- **Weyl's exponent on the doubled line**: `‖ζ(1/2 + 2it)‖ ≤ C (1 + |t|)^{1/6+η}` for all `t`. -/
theorem exists_norm_zeta_double_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤ C * (1 + |t|) ^ (1 / 6 + η) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-4 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    continuous_zeta_double.continuousOn
  refine ⟨max (max B 0) (4200 / η * 2 ^ (1 / 6 + η)), by positivity, fun t => ?_⟩
  have hp1 : 1 ≤ (1 + |t|) ^ (1 / 6 + η) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by linarith)
  by_cases ht : 8 ≤ |2 * t|
  · have h := norm_riemannZeta_half_le_abs_rpow hη ht
    have h2 : |2 * t| ^ (1 / 6 + η) ≤ 2 ^ (1 / 6 + η) * (1 + |t|) ^ (1 / 6 + η) := by
      rw [abs_mul, abs_two, Real.mul_rpow (by norm_num) (abs_nonneg t)]
      gcongr
      linarith
    calc ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤ 4200 / η * |2 * t| ^ (1 / 6 + η) := h
      _ ≤ 4200 / η * (2 ^ (1 / 6 + η) * (1 + |t|) ^ (1 / 6 + η)) := by gcongr
      _ = 4200 / η * 2 ^ (1 / 6 + η) * (1 + |t|) ^ (1 / 6 + η) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · push Not at ht
    have hmem : t ∈ Set.Icc (-4 : ℝ) 4 := by
      rw [abs_mul, abs_two] at ht
      exact abs_le.mp (by linarith)
    calc ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤ B := hB t hmem
      _ ≤ max (max B 0) (4200 / η * 2 ^ (1 / 6 + η)) := (le_max_left _ _).trans (le_max_left _ _)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hp1

/-! ## Energy and size of the defect -/

/-- **Subpolynomial defect energy**: `∫_{-T}^{T} ‖g‖² ≤ C T^{1+ε}` for `T ≥ 2`. -/
theorem exists_integral_normSq_stripDefect_editG_le (hα0 : 0 < α) (hα : α < 1) (hβ0 : 0 ≤ β)
    (hβ : β < 1) (γ : ℝ) {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ)
    (hΘ1 : Θ ≤ 1) (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (hΘβ : Θ + β < 3 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      ∫ t in (-T)..T, ‖stripDefect (editG α β γ k₀) t‖ ^ 2 ≤ C * T ^ (1 + ε) := by
  obtain ⟨K, hK, hg⟩ := exists_norm_stripDefect_editG_le hα0 hα hβ0 hβ γ hk₀ hΘ hΘ1 hzf hΘβ
    (half_pos (half_pos hε))
  obtain ⟨D, hD, hz⟩ := exists_integral_normSq_zeta_double_le (half_pos hε)
  refine ⟨K ^ 2 * 2 ^ (ε / 2) * D, by positivity, fun T hT => ?_⟩
  have hFc : Continuous fun t : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ^ 2 :=
    continuous_zeta_double.norm.pow 2
  have hsq : ((1 + T) ^ (ε / 2 / 2)) ^ 2 = (1 + T) ^ (ε / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  have hle : ∫ t in (-T)..T, ‖stripDefect (editG α β γ k₀) t‖ ^ 2 ≤
      ∫ t in (-T)..T, K ^ 2 * (1 + T) ^ (ε / 2) *
        ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => by positivity)
      ((continuous_const.mul hFc).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have htT : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hp : (1 + |t|) ^ (ε / 2 / 2) ≤ (1 + T) ^ (ε / 2 / 2) := by gcongr
    calc ‖stripDefect (editG α β γ k₀) t‖ ^ 2
        ≤ (K * ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ * (1 + T) ^ (ε / 2 / 2)) ^ 2 := by
          gcongr
          exact (hg t).trans (by gcongr)
      _ = K ^ 2 * ((1 + T) ^ (ε / 2 / 2)) ^ 2 *
            ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ^ 2 := by ring
      _ = _ := by rw [hsq]
  rw [intervalIntegral.integral_const_mul] at hle
  have h1T : (1 + T) ^ (ε / 2) ≤ 2 ^ (ε / 2) * T ^ (ε / 2) := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    gcongr
    linarith
  have hT' : T ^ (ε / 2) * T ^ (1 + ε / 2) = T ^ (1 + ε) := by
    rw [← Real.rpow_add (by linarith)]
    congr 1
    ring
  calc ∫ t in (-T)..T, ‖stripDefect (editG α β γ k₀) t‖ ^ 2
      ≤ K ^ 2 * (1 + T) ^ (ε / 2) *
          ∫ t in (-T)..T, ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ^ 2 := hle
    _ ≤ K ^ 2 * (1 + T) ^ (ε / 2) * (D * T ^ (1 + ε / 2)) := by gcongr; exact hz T hT
    _ ≤ K ^ 2 * (2 ^ (ε / 2) * T ^ (ε / 2)) * (D * T ^ (1 + ε / 2)) := by gcongr
    _ = K ^ 2 * 2 ^ (ε / 2) * D * (T ^ (ε / 2) * T ^ (1 + ε / 2)) := by ring
    _ = _ := by rw [hT']

/-- **Pointwise size of the defect**: `‖g(t)‖ ≤ C (1 + |t|)^{1/6+ε}`. -/
theorem exists_norm_stripDefect_editG_le_weyl (hα0 : 0 < α) (hα : α < 1) (hβ0 : 0 ≤ β)
    (hβ : β < 1) (γ : ℝ) {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ)
    (hΘ1 : Θ ≤ 1) (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (hΘβ : Θ + β < 3 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖stripDefect (editG α β γ k₀) t‖ ≤ C * (1 + |t|) ^ (1 / 6 + ε) := by
  obtain ⟨K, hK, hg⟩ := exists_norm_stripDefect_editG_le hα0 hα hβ0 hβ γ hk₀ hΘ hΘ1 hzf hΘβ
    (half_pos hε)
  obtain ⟨Cz, hCz, hz⟩ := exists_norm_zeta_double_le (half_pos hε)
  refine ⟨K * Cz, by positivity, fun t => ?_⟩
  have hpos : 0 < 1 + |t| := by positivity
  calc ‖stripDefect (editG α β γ k₀) t‖
      ≤ K * ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ * (1 + |t|) ^ (ε / 2) := hg t
    _ ≤ K * (Cz * (1 + |t|) ^ (1 / 6 + ε / 2)) * (1 + |t|) ^ (ε / 2) := by gcongr; exact hz t
    _ = K * Cz * ((1 + |t|) ^ (1 / 6 + ε / 2) * (1 + |t|) ^ (ε / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add hpos]; congr 2; ring

/-! ## The fake -/

/-- **The signed edit is an integer-norm fake** at every count exponent `β_c ∈ (α, 1)`: its
continuation vanishes at `ρ₀ = β + iγ`, where `ζ` does not.  The edit is nonzero, since otherwise
`G_B = (s - 1) ζ` would be nonzero at `ρ₀`. -/
theorem isIntegerNormFakeAt_editSystem_sEdit (hα0 : 0 < α) (hα : α < 1) (hβh : 1 / 2 < β)
    (hβ : β < 1) (γ : ℝ) {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (hΘβ : Θ + β < 3 / 2)
    (hζ : riemannZeta (zeroPt β γ) ≠ 0) {β_c : ℝ} (hαc : α < β_c) (hβc : β_c < 1) :
    IsIntegerNormFakeAt (editSystem (sEdit α β γ k₀)) β_c := by
  have he := isEdit_sEdit α β γ k₀
  have hσ := contAbscissa_lt_half hα hβ hΘβ
  have hd := differentiableOn_editG hα0 hα hβ γ hk₀ hΘ hzf
  have hρre : (zeroPt β γ).re = β := by simp [zeroPt]
  have hρ1 : zeroPt β γ ≠ 1 := fun h => by
    have := congrArg Complex.re h
    rw [hρre, Complex.one_re] at this
    linarith
  have hG0 : editG α β γ k₀ (zeroPt β γ) = 0 := by
    simp [editG, editCofactor, posCofactor]
  have hρσ : contAbscissa α β Θ < (zeroPt β γ).re := by rw [hρre]; linarith
  obtain ⟨p, hp⟩ : ∃ p, sEdit α β γ k₀ p ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : sEdit α β γ k₀ = fun _ => 0 := funext h
    have heq : ∀ s : ℂ, 1 < s.re → editG α β γ k₀ s = zetaResidueUnit s := by
      intro s hs
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
      have hE : LSeries (fun k => (sEdit α β γ k₀ k : ℂ)) s + editRem (sEdit α β γ k₀) s = 0 := by
        simp [h0, editRem, LSeries, LSeries.term]
      rw [editG_eq hβ γ k₀ hs, editSystem_zetaSeriesC he hs, hE, Complex.exp_zero, mul_one,
        zetaResidueUnit_eq_of_ne hs1]
    have hid := eqOn_re_gt_of_eq_on_re_gt_one (by linarith) hd
      (fun s _ => (analyticAt_zetaResidueUnit s).differentiableAt.differentiableWithinAt) heq hρσ
    rw [hG0, zetaResidueUnit_eq_of_ne hρ1] at hid
    exact mul_ne_zero (sub_ne_zero.mpr hρ1) hζ hid.symm
  obtain ⟨A, C, hA, hC⟩ := editSystem_count (by linarith) hβc
    (summable_abs_sEdit_rpow hα0 hα γ k₀ hαc)
  exact ⟨hasIntegerNorms_editSystem _, isDiscrete_editSystem _, notNormEquivPrimes_editSystem he hp,
    ⟨A, C, hA, hC⟩, editG α β γ k₀,
    hd.mono fun s hs => show _ < s.re by have : 1 / 2 < s.re := hs; linarith,
    fun s hs => editG_eq hβ γ k₀ hs, zeroPt β γ, by rw [hρre]; exact hβh, hρ1, hG0, hζ⟩

/-! ## Theorem I.4 -/

/-- The conclusions of Theorem I.4(B) for an edit `e`, a fake zero `ρ₀` and a count exponent
`β_c`: `editSystem e` is an integer-norm fake at `β_c` of positive density whose `(s - 1) ζ_B(s)`
continues to `Re s > σ₁`, `σ₁ < 1/2`, with zeros those of `(s - 1) ζ(s)` and `{ρ₀, ρ̄₀}`; it lies
in the Hamburger strip class, and its FE defect `g` obeys `‖g(t)‖ ≤ K_ε ‖ζ(1/2 + 2it)‖ (1+|t|)^ε`,
`(2T)⁻¹ ∫_{-T}^{T} ‖g‖² ≤ C_ε T^ε` and `‖g(t)‖ ≤ C_ε (1 + |t|)^{1/6+ε}` for every `ε > 0`. -/
def IsSubpolynomialDefectFake (e : ℕ → ℤ) (ρ₀ : ℂ) (β_c : ℝ) : Prop :=
  IsEdit e ∧ IsIntegerNormFakeAt (editSystem e) β_c ∧
    (∃ A C : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x →
      |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β_c) ∧
    ∃ G : ℂ → ℂ, ∃ σ₁ : ℝ, σ₁ < 1 / 2 ∧
      DifferentiableOn ℂ G {s : ℂ | σ₁ < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
      (∀ s : ℂ, σ₁ < s.re →
        (G s = 0 ↔ zetaResidueUnit s = 0 ∨ s = ρ₀ ∨ s = (starRingEnd ℂ) ρ₀)) ∧
      HamburgerStripDefect (editSystem e).zetaSeriesC (G 1 / 2) (stripDefect G) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, ‖stripDefect G t‖ ≤
        K * ‖riemannZeta ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ * (1 + |t|) ^ ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
        (2 * T)⁻¹ * ∫ t in (-T)..T, ‖stripDefect G t‖ ^ 2 ≤ C * T ^ ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
        ‖stripDefect G t‖ ≤ C * (1 + |t|) ^ (1 / 6 + ε))

/-- The signed grouped edit with `α = (β₀ + β_c)/2` and any `k₀ ≥ 1/(α - β₀)` has all the conclusions
of Theorem I.4(B). -/
theorem isSubpolynomialDefectFake_sEdit {β₀ γ₀ β_c : ℝ} (hβ₀ : 1 / 2 < β₀)
    (hβ₀Θ : β₀ < 3 / 2 - zetaZeroAbscissa) (hζ : riemannZeta (zeroPt β₀ γ₀) ≠ 0)
    (hβc : β₀ < β_c) (hβc1 : β_c < 1) {k₀ : ℕ}
    (hk₀ : 1 ≤ (k₀ : ℝ) * ((β₀ + β_c) / 2 - β₀)) :
    IsSubpolynomialDefectFake (sEdit ((β₀ + β_c) / 2) β₀ γ₀ k₀) (zeroPt β₀ γ₀) β_c := by
  have hΘ := half_le_zetaZeroAbscissa
  have hΘ1 := zetaZeroAbscissa_le_one
  have hzf : ∀ z : ℂ, zetaZeroAbscissa < z.re → riemannZeta z ≠ 0 :=
    fun z hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz
  have hΘβ : zetaZeroAbscissa + β₀ < 3 / 2 := by linarith
  have hβ1 : β₀ < 1 := by linarith
  have hβ0 : 0 ≤ β₀ := by linarith
  set α : ℝ := (β₀ + β_c) / 2 with hαdef
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  have hαc : α < β_c := by rw [hαdef]; linarith
  have hfake := isIntegerNormFakeAt_editSystem_sEdit hα0 hα1 hβ₀ hβ1 γ₀ hk₀ hΘ hzf hΘβ hζ hαc hβc1
  obtain ⟨-, -, -, ⟨A, C, -, hC⟩, -⟩ := id hfake
  refine ⟨isEdit_sEdit α β₀ γ₀ k₀, hfake,
    ⟨A, C, pos_density_of_integerNormFakeAt_lt_one hfake hβc1 hC, hC⟩, editG α β₀ γ₀ k₀,
    contAbscissa α β₀ zetaZeroAbscissa, contAbscissa_lt_half hα1 hβ1 hΘβ,
    differentiableOn_editG hα0 hα1 hβ1 γ₀ hk₀ hΘ hzf, fun s hs => editG_eq hβ1 γ₀ k₀ hs,
    fun s hs => editG_eq_zero_iff γ₀ k₀ hzf hs,
    hamburgerStripDefect_editG hα0 hα1 hβ0 hβ1 γ₀ hk₀ hΘ hΘ1 hzf hΘβ,
    fun ε hε => exists_norm_stripDefect_editG_le hα0 hα1 hβ0 hβ1 γ₀ hk₀ hΘ hΘ1 hzf hΘβ hε,
    fun ε hε => ?_,
    fun ε hε => exists_norm_stripDefect_editG_le_weyl hα0 hα1 hβ0 hβ1 γ₀ hk₀ hΘ hΘ1 hzf hΘβ hε⟩
  obtain ⟨C', hC', hL⟩ :=
    exists_integral_normSq_stripDefect_editG_le hα0 hα1 hβ0 hβ1 γ₀ hk₀ hΘ hΘ1 hzf hΘβ hε
  refine ⟨C' / 2, by positivity, fun T hT => ?_⟩
  have hT0 : T ≠ 0 := by positivity
  have hTp : T ^ (1 + ε) = T * T ^ ε := by rw [Real.rpow_add (by linarith), Real.rpow_one]
  calc (2 * T)⁻¹ * ∫ t in (-T)..T, ‖stripDefect (editG α β₀ γ₀ k₀) t‖ ^ 2
      ≤ (2 * T)⁻¹ * (C' * T ^ (1 + ε)) := by gcongr; exact hL T hT
    _ = C' / 2 * T ^ ε := by rw [hTp]; field_simp

/-- **Theorem I.4(B), with the edit beyond any prescribed bound.**  For `1/2 < β₀ < 3/2 - Θ`
(`Θ = zetaZeroAbscissa`), `ζ(β₀ + iγ₀) ≠ 0`, `β₀ < β_c < 1` and every `P`, there is a fake edit with
subpolynomial defect energy that edits no prime `≤ P`. -/
theorem exists_subpolynomialDefectFake_beyond {β₀ γ₀ β_c : ℝ} (hβ₀ : 1 / 2 < β₀)
    (hβ₀Θ : β₀ < 3 / 2 - zetaZeroAbscissa) (hζ : riemannZeta (zeroPt β₀ γ₀) ≠ 0)
    (hβc : β₀ < β_c) (hβc1 : β_c < 1) (P : ℕ) :
    ∃ e : ℕ → ℤ, IsSubpolynomialDefectFake e (zeroPt β₀ γ₀) β_c ∧ ∀ n, e n ≠ 0 → P < n := by
  have hαβ : 0 < (β₀ + β_c) / 2 - β₀ := by linarith
  set k₀ : ℕ := max ⌈1 / ((β₀ + β_c) / 2 - β₀)⌉₊ P with hk₀def
  have hk₀ : 1 ≤ (k₀ : ℝ) * ((β₀ + β_c) / 2 - β₀) := by
    have h1 := Nat.le_ceil (1 / ((β₀ + β_c) / 2 - β₀))
    have h2 : ((⌈1 / ((β₀ + β_c) / 2 - β₀)⌉₊ : ℕ) : ℝ) ≤ k₀ := by
      exact_mod_cast le_max_left _ _
    rw [div_le_iff₀ hαβ] at h1
    nlinarith
  refine ⟨_, isSubpolynomialDefectFake_sEdit hβ₀ hβ₀Θ hζ hβc hβc1 hk₀, fun n hn => ?_⟩
  by_contra hle
  push Not at hle
  have hlt : n < 2 ^ k₀ := lt_of_le_of_lt hle (lt_of_le_of_lt (le_max_right _ _)
    (Nat.lt_two_pow_self))
  by_cases hp : n.Prime
  · exact hn (sEdit_eq_zero_of_lt γ₀ hlt)
  · exact hn ((isEdit_sEdit _ _ _ _).prime n hp)

/-- **Theorem I.4(B).** -/
theorem exists_subpolynomialDefectFake {β₀ γ₀ β_c : ℝ} (hβ₀ : 1 / 2 < β₀)
    (hβ₀Θ : β₀ < 3 / 2 - zetaZeroAbscissa) (hζ : riemannZeta (zeroPt β₀ γ₀) ≠ 0)
    (hβc : β₀ < β_c) (hβc1 : β_c < 1) :
    ∃ e : ℕ → ℤ, IsSubpolynomialDefectFake e (zeroPt β₀ γ₀) β_c :=
  let ⟨e, he, _⟩ := exists_subpolynomialDefectFake_beyond hβ₀ hβ₀Θ hζ hβc hβc1 0
  ⟨e, he⟩

/-- **Theorem I.4 (the frontier dichotomy).**  Unconditionally, either `Θ = 1` and the asymptotic
abscissa law holds, or `Θ < 1` and every admissible `(ρ₀, β_c)` carries a fake edit with
subpolynomial defect energy. -/
theorem frontier_dichotomy :
    (zetaZeroAbscissa = 1 ∧ _root_.RHTower.AsymptoticAbscissaLaw) ∨
      (zetaZeroAbscissa < 1 ∧ ∀ β₀ γ₀ β_c : ℝ, 1 / 2 < β₀ → β₀ < 3 / 2 - zetaZeroAbscissa →
        riemannZeta (zeroPt β₀ γ₀) ≠ 0 → β₀ < β_c → β_c < 1 →
          ∃ e : ℕ → ℤ, IsSubpolynomialDefectFake e (zeroPt β₀ γ₀) β_c) := by
  rcases eq_or_lt_of_le zetaZeroAbscissa_le_one with h | h
  · exact Or.inl ⟨h, asymptoticAbscissaLaw_of_zetaZeroAbscissa_eq_one h⟩
  · exact Or.inr ⟨h, fun _ _ _ h1 h2 h3 h4 h5 => exists_subpolynomialDefectFake h1 h2 h3 h4 h5⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
