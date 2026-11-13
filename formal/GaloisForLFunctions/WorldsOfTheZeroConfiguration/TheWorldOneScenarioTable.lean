import GaloisForLFunctions.WorldsOfTheZeroConfiguration.FakeEditsWithSubpolynomialDefectEnergy
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheFunctionalEquationDefectOfAFakeEdit
import GaloisForLFunctions.EulerFETransportTheory.ArbitrarilySlowDefectsOfPositiveWeightedSystems

/-!
# The World-I scenario table

**Corollary III.2.**  The three rows of the World-I table for fakes built from prime edits.

* **Row 1** (`worldOne_row_one`).  Every integer-norm fake edit with a count rate `β_c < 1` has a
  deleted prime `p₀`, and its critical-line FE defect is not Abel-sublinear, does not tend to zero,
  is not `O((1 + |t|)^{-α})`, is not bounded, and is not `≤ c √log |t|` for `c < A/(32√(π p₀))`.
  For countable Beurling systems with real norms, a defect `O((1 + |t|)^{-1/2+ε})` forces the
  rational primes (`EulerFETransportTheory.riemannZeta_eq_zero_of_decaying_defect`).
* **Row 2** (`worldOne_row_two`).  When `Θ < 1` some fake edit has a defect with no power lower
  bound in `L²`-mean: `(2T)⁻¹ ∫_{-T}^{T} ‖g‖² < c T^{2α}` for arbitrarily large `T`, for every
  `α, c > 0`.  Unconditionally (`worldOne_row_two_weighted`), a positive-real-weighted countable
  Beurling system with zeros at `1 - μ ± iγ` has `‖g(t)‖ ≤ log(1 + |t|)`, hence `‖g(t)‖ < c |t|^α`
  for all large `|t|`, for every `α, c > 0` (Theorem II.3).
* **Row 3** (`worldOne_row_three`).  When `Θ < 1` the same zero `ρ₀` is carried by fake edits whose
  least deleted prime exceeds any bound, so the floors `1/(3(p₀ + 1))` and `A²/(256 π p₀)` of
  Theorems I.2–I.3 tend to zero at fixed zero depth.
-/

open Complex Filter Topology MeasureTheory
open RHTower RHTower.HamburgerStability
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.FEDefect
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
open GaloisForLFunctions.EulerFETransportTheory GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.WorldOne

/-- **Row 1.**  The defect of an integer-norm fake edit is not small in any of the decaying senses. -/
theorem worldOne_row_one {e : ℕ → ℤ} {β_c A C : ℝ} (hβc : β_c < 1)
    (hf : IsIntegerNormFakeAt (editSystem e) β_c)
    (hcount : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β_c)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (editSystem e).zetaSeriesC β g) :
    ∃ p₀ : ℕ, p₀.Prime ∧ e p₀ = -1 ∧
      ¬ Tendsto (fun δ => δ * abelMass g δ) (𝓝[>] 0) (𝓝 0) ∧
      (¬ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R ≤ |t| → ‖g t‖ ≤ ε) ∧
      (∀ α : ℝ, 0 < α → ∀ C₁ : ℝ, ¬ ∀ t : ℝ, ‖g t‖ ≤ C₁ * (1 + |t|) ^ (-α)) ∧
      (∀ M : ℝ, ¬ ∀ t : ℝ, ‖g t‖ ≤ M) ∧
      ∀ c : ℝ, c < A / (32 * Real.sqrt (Real.pi * p₀)) → ∀ t₁ : ℝ,
        ¬ ∀ t : ℝ, t₁ ≤ |t| → ‖g t‖ ≤ c * Real.sqrt (Real.log |t|) := by
  obtain ⟨p₀, hp₀, hep₀, -⟩ := exists_least_deleted_prime hβc.le hf
  obtain ⟨h1, h2, h3⟩ := editSystem_defect_not_decaying hβc hcount hH hp₀ hep₀
  obtain ⟨h4, h5⟩ := editSystem_fake_defect_not_le_sqrt_log hβc hf hcount hH hp₀ hep₀
  exact ⟨p₀, hp₀, hep₀, h1, h2, h3, h5, h4⟩

/-- A mean square `O(T^ε)` for every `ε > 0` admits no power lower bound. -/
theorem not_power_lower_bound {F : ℝ → ℝ}
    (hF : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → F T ≤ C * T ^ ε)
    {α c : ℝ} (hα : 0 < α) (hc : 0 < c) (T₀ : ℝ) : ∃ T, T₀ ≤ T ∧ F T < c * T ^ (2 * α) := by
  obtain ⟨C, hC, hb⟩ := hF α hα
  have ht : Tendsto (fun T : ℝ => C * T ^ (-α)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hα).const_mul C
  obtain ⟨T, hT⟩ := (ht.eventually (gt_mem_nhds hc)).and
    ((eventually_ge_atTop (max T₀ 2)).and (eventually_gt_atTop 0)) |>.exists
  obtain ⟨hlt, hge, hT0⟩ := hT
  refine ⟨T, le_trans (le_max_left _ _) hge, (hb T (le_trans (le_max_right _ _) hge)).trans_lt ?_⟩
  have e : C * T ^ α = C * T ^ (-α) * T ^ (2 * α) := by
    rw [mul_assoc, ← Real.rpow_add hT0]; ring_nf
  rw [e]
  exact mul_lt_mul_of_pos_right hlt (by positivity)

/-- **Row 2.**  When `1/2 < β₀ < 3/2 - Θ` (so `Θ < 1`), some fake edit with zero `β₀ + iγ₀` has a
defect with no power lower bound in `L²`-mean. -/
theorem worldOne_row_two {β₀ γ₀ β_c : ℝ} (hβ₀ : 1 / 2 < β₀)
    (hβ₀Θ : β₀ < 3 / 2 - zetaZeroAbscissa) (hζ : riemannZeta (zeroPt β₀ γ₀) ≠ 0)
    (hβc : β₀ < β_c) (hβc1 : β_c < 1) :
    ∃ e : ℕ → ℤ, ∃ G : ℂ → ℂ, IsIntegerNormFakeAt (editSystem e) β_c ∧
      HamburgerStripDefect (editSystem e).zetaSeriesC (G 1 / 2) (stripDefect G) ∧
      ∀ α c : ℝ, 0 < α → 0 < c → ∀ T₀ : ℝ, ∃ T, T₀ ≤ T ∧
        (2 * T)⁻¹ * ∫ t in (-T)..T, ‖stripDefect G t‖ ^ 2 < c * T ^ (2 * α) := by
  obtain ⟨e, -, hf, -, G, -, -, -, -, -, hH, -, hL, -⟩ :=
    exists_subpolynomialDefectFake hβ₀ hβ₀Θ hζ hβc hβc1
  exact ⟨e, G, hf, hH, fun α c hα hc T₀ => not_power_lower_bound hL hα hc T₀⟩

/-- **Row 2, weighted systems.**  Unconditionally, some positive-real-weighted countable Beurling
system with `ℚ`-independent generator logarithms and zeros at `1 - μ ± iγ` lies in the Hamburger
strip class with a defect below every power: `‖g(t)‖ < c |t|^α` for all large `|t|`, every
`α, c > 0`.  It is Theorem II.3 with `Φ(t) = log(1 + |t|)`. -/
theorem worldOne_row_two_weighted {μ ν γ : ℝ} (hμ2 : μ < 1 / 2) (hν0 : 0 < ν)
    (hν : ν < 3 * μ - 1) :
    ∃ (ι : Type) (_ : Countable ι) (u w : ι → ℝ), (∀ i, 0 < w i) ∧ LinearIndependent ℚ u ∧
      ∃ (A : ℝ) (G : ℂ → ℂ), 0 < A ∧
        G (((1 - μ : ℝ) : ℂ) + γ * I) = 0 ∧ G (((1 - μ : ℝ) : ℂ) - γ * I) = 0 ∧
        HamburgerStripDefect
          (measureDirichlet (beurlingIntegerMeasure (Discretization.eulerPrimeMeasure u w)))
          ((A : ℂ) / 2) (stripDefect G) ∧
        ∀ α c : ℝ, 0 < α → 0 < c → ∃ T₁ : ℝ, ∀ t : ℝ, T₁ ≤ |t| →
          ‖stripDefect G t‖ < c * |t| ^ α := by
  have hΦ : Tendsto (fun t : ℝ => Real.log (1 + |t|)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ 1 tendsto_abs_atTop_atTop)
  obtain ⟨ι, hι, u, w, -, hw, -, hli, A, -, T₀, G, hA, -, -, -, -, hz1, hz2, -, hH, hg⟩ :=
    SlowDefect.exists_positiveWeighted_beurling_slow_defect (γ := γ) hΦ hμ2 hν0 hν
  refine ⟨ι, hι, u, w, hw, hli, A, G, hA, hz1, hz2, hH, fun α c hα hc => ?_⟩
  -- `log x ≤ ε x^α` eventually, `ε = c/2^{α+1}`
  have hε : 0 < c / 2 ^ (α + 1) := by positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp ((isLittleO_log_rpow_atTop hα).bound hε)
  refine ⟨max (max T₀ 1) X₀, fun t ht => ?_⟩
  have ht1 : 1 ≤ |t| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htT : T₀ ≤ |t| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have hx : X₀ ≤ 1 + |t| := by linarith [le_max_right (max T₀ 1) X₀]
  have hlog := hX₀ (1 + |t|) hx
  have hpos : 0 < |t| := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hlog
  have h2 : (1 + |t|) ^ α ≤ 2 ^ α * |t| ^ α := by
    rw [← Real.mul_rpow (by norm_num) hpos.le]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hα.le
  have hg' := hg t htT
  rw [abs_abs] at hg'
  have hta : 0 < |t| ^ α := Real.rpow_pos_of_pos hpos α
  have h2α : (2 : ℝ) ^ (α + 1) = 2 ^ α * 2 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  calc ‖stripDefect G t‖ ≤ Real.log (1 + |t|) := hg'
    _ ≤ c / 2 ^ (α + 1) * (1 + |t|) ^ α := hlog
    _ ≤ c / 2 ^ (α + 1) * (2 ^ α * |t| ^ α) := mul_le_mul_of_nonneg_left h2 hε.le
    _ = c / 2 * |t| ^ α := by
        rw [h2α]; field_simp
    _ < c * |t| ^ α := by linarith [mul_pos hc hta]

/-- **Row 3.**  When `1/2 < β₀ < 3/2 - Θ`, the zero `β₀ + iγ₀` is carried by fake edits whose least
deleted prime exceeds any prescribed `P`. -/
theorem worldOne_row_three {β₀ γ₀ β_c : ℝ} (hβ₀ : 1 / 2 < β₀)
    (hβ₀Θ : β₀ < 3 / 2 - zetaZeroAbscissa) (hζ : riemannZeta (zeroPt β₀ γ₀) ≠ 0)
    (hβc : β₀ < β_c) (hβc1 : β_c < 1) (P : ℕ) :
    ∃ e : ℕ → ℤ, IsSubpolynomialDefectFake e (zeroPt β₀ γ₀) β_c ∧
      ∃ p₀ : ℕ, p₀.Prime ∧ e p₀ = -1 ∧ P < p₀ ∧
        ∀ q : ℕ, q.Prime → e q = -1 → p₀ ≤ q := by
  obtain ⟨e, he, hP⟩ := exists_subpolynomialDefectFake_beyond hβ₀ hβ₀Θ hζ hβc hβc1 P
  obtain ⟨p₀, hp₀, hep₀, hmin⟩ := exists_least_deleted_prime hβc1.le he.2.1
  exact ⟨e, he, p₀, hp₀, hep₀, hP p₀ (by rw [hep₀]; norm_num), hmin⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.WorldOne
