import GaloisForLFunctions.SquareRootThreshold.IntervalSourceTransformsSampledOnLocallyBoundedPoints

/-!
# Sampling a transform at a free window length

A source vanishing off `[−b, b]` is sampled on points with at most `K` heights in every grid cell of
length `h = 2π/ℓ`, for any `ℓ > 2b`. Grid Parseval on a window of length `ℓ` and the power series of
the displacement give

`Σ_q |Φ(x_q + i y_q)|² ≤ e^{2(h+σ)b} K ℓ ∫|f|²`.

At `ℓ ≫ b` the factor is `1 + O(b/ℓ)`, so the constant is sharp for lattice-like point sets: `K ℓ`
is the density. At `ℓ ≍ b` the bound depends on the support length `2b` alone, not on the position
of the support, because the transform changes only by a phase and a depth factor under translation.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open GaloisForLFunctions.HTGeometry _root_.RHTower _root_.RHTower.CCMParityQuartet

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open GaloisForLFunctions.SquareRootThreshold

/-- **Sampling at a free window length.** -/
theorem sum_norm_sq_testTransform_le_of_cellCount {b ℓ : ℝ} (hb : 0 < b) (hℓ : 2 * b < ℓ)
    {f : ℝ → ℂ} (hf : IntervalSource b f) {ι : Type*} (x y : ι → ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hy : ∀ q, |y q| ≤ σ) {K : ℕ} (s : Finset ι)
    (hK : ∀ n : ℤ, (s.filter fun q => ⌊x q / (2 * π / ℓ)⌋ = n).card ≤ K) :
    ∑ q ∈ s, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
      Real.exp (2 * (2 * π / ℓ + σ) * b) * (K * (ℓ * ∫ u, ‖f u‖ ^ 2)) := by
  have hℓ0 : 0 < ℓ := by linarith only [hb, hℓ]
  obtain ⟨h, hh⟩ : ∃ h, h = 2 * π / ℓ := ⟨_, rfl⟩
  rw [← hh] at hK ⊢
  have hh0 : 0 < h := by rw [hh]; positivity
  set ρ₀ := h + σ with hρ₀
  have hρ₀0 : 0 < ρ₀ := by linarith
  set N := ∫ u, ‖f u‖ ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => by positivity
  set I₁ := ∫ u, ‖f u‖ with hI₁
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun _ => norm_nonneg _
  set g : ι → ℝ := fun q => (⌊x q / h⌋ : ℝ) * h with hg
  set B : ℕ → ι → ℝ := fun j q => ‖testTransform (momentSource f j) ((g q : ℝ) : ℂ)‖ with hB
  set D : ℕ → ℝ := fun j => ρ₀ ^ j / (j.factorial * b ^ j) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by positivity
  have hB0 : ∀ j q, 0 ≤ B j q := fun j q => norm_nonneg _
  have hBle : ∀ j q, B j q ≤ b ^ j * I₁ := fun j q => norm_testTransform_momentSource_le hf j (g q)
  have hE : ∑' j : ℕ, (ρ₀ * b) ^ j / j.factorial = Real.exp (ρ₀ * b) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hDB : ∀ j q, D j * B j q ^ 2 ≤ (ρ₀ * b) ^ j / j.factorial * I₁ ^ 2 := by
    intro j q
    calc D j * B j q ^ 2 ≤ D j * (b ^ j * I₁) ^ 2 := by
          gcongr
          exact hBle j q
      _ = (ρ₀ * b) ^ j / j.factorial * I₁ ^ 2 := by
          simp only [hD]
          rw [mul_pow (b ^ j) I₁]
          exact momentWeight_mul_sq ρ₀ b (I₁ ^ 2) j hb.ne'
  have hsummD : ∀ q, Summable fun j => D j * B j q ^ 2 := fun q =>
    Summable.of_nonneg_of_le (fun j => by positivity) (fun j => hDB j q)
      ((Real.summable_pow_div_factorial (ρ₀ * b)).mul_right _)
  -- pointwise bound through the power series and weighted Cauchy–Schwarz
  have hgx : ∀ q, |x q - g q| ≤ h := by
    intro q
    have h1 : (⌊x q / h⌋ : ℝ) ≤ x q / h := Int.floor_le _
    have h2 : x q / h < (⌊x q / h⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h1' := (le_div_iff₀ hh0).mp h1
    have h2' := (div_lt_iff₀ hh0).mp h2
    rw [abs_le]
    simp only [hg]
    constructor <;> nlinarith only [h1', h2', hh0]
  have hpt : ∀ q, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
      Real.exp (ρ₀ * b) * ∑' j, D j * B j q ^ 2 := by
    intro q
    have hw : ‖((x q : ℂ) + (y q : ℂ) * I) - (g q : ℂ)‖ ≤ ρ₀ := by
      have e : ((x q : ℂ) + (y q : ℂ) * I) - (g q : ℂ) =
          ((x q - g q : ℝ) : ℂ) + (y q : ℂ) * I := by push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      linarith [hy q, hgx q]
    have hz : ((x q : ℂ) + (y q : ℂ) * I) =
        (g q : ℂ) + (((x q : ℂ) + (y q : ℂ) * I) - (g q : ℂ)) := by ring
    have h1 := norm_testTransform_le_tsum_momentSource hf (g q) hw
    rw [← hz] at h1
    have hp : ∀ j : ℕ, 0 < (ρ₀ * b) ^ j / j.factorial := fun j => by positivity
    have hps : Summable fun j : ℕ => (ρ₀ * b) ^ j / j.factorial :=
      Real.summable_pow_div_factorial _
    have hconv : ∀ j : ℕ, (ρ₀ ^ j / j.factorial * B j q) ^ 2 / ((ρ₀ * b) ^ j / j.factorial) =
        D j * B j q ^ 2 := by
      intro j
      simp only [hD]
      exact sq_div_momentWeight ρ₀ b (B j q) j hb.ne' hρ₀0.ne'
    have hcs : Summable fun j : ℕ =>
        (ρ₀ ^ j / j.factorial * B j q) ^ 2 / ((ρ₀ * b) ^ j / j.factorial) := by
      simp only [hconv]
      exact hsummD q
    have hCS := sq_tsum_le_tsum_mul_tsum_div hp (fun j => by positivity) hps hcs
    calc ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2
        ≤ (∑' j : ℕ, ρ₀ ^ j / j.factorial * B j q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := hCS
      _ = Real.exp (ρ₀ * b) * ∑' j, D j * B j q ^ 2 := by
          rw [hE]
          congr 1
          exact tsum_congr hconv
  -- grid Parseval on a window of length `ℓ`
  have hgrid : ∀ j (t : Finset ℤ),
      ∑ n ∈ t, ‖testTransform (momentSource f j) (((n : ℝ) * h : ℝ) : ℂ)‖ ^ 2 ≤
        ℓ * ((b ^ j) ^ 2 * N) := by
    intro j t
    have hm := intervalSource_momentSource hf j
    have hsupp : ∀ u, ℓ / 2 ≤ |u| → momentSource f j u = 0 := by
      intro u hu
      apply hm.vanish
      intro hmem
      have := abs_le.mpr ⟨hmem.1, hmem.2⟩
      linarith only [this, hu, hℓ]
    have hP := hasSum_norm_sq_paperFT_grid hℓ0 hm.continuous hsupp 0 0
    -- reindex `n ↦ −n`: the grid is symmetric
    have hP' : HasSum (fun n : ℤ =>
        ‖testTransform (momentSource f j) (((n : ℝ) * h : ℝ) : ℂ)‖ ^ 2)
        (ℓ * ∫ u in (-(ℓ / 2))..(ℓ / 2), ‖momentSource f j u‖ ^ 2) := by
      have hn := (Equiv.neg ℤ).hasSum_iff.mpr hP
      convert hn using 2 with n
      simp only [Function.comp_apply, Equiv.neg_apply, testTransform, Zeta23.paperFT]
      congr 4
      rw [hh]
      push_cast
      ring_nf
    refine (sum_le_hasSum t (fun _ _ => sq_nonneg _) hP').trans ?_
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral_norm_sq_momentSource_le hf j (by linarith only [hℓ0])) hℓ0.le
  have hcell : ∀ j, ∑ q ∈ s, B j q ^ 2 ≤ K * (ℓ * ((b ^ j) ^ 2 * N)) := by
    intro j
    set G : ℤ → ℝ := fun n =>
      ‖testTransform (momentSource f j) (((n : ℝ) * h : ℝ) : ℂ)‖ ^ 2 with hG
    have hGq : ∀ q, B j q ^ 2 = G ⌊x q / h⌋ := fun q => rfl
    have hG0 : ∀ n, 0 ≤ G n := fun n => sq_nonneg _
    calc ∑ q ∈ s, B j q ^ 2 = ∑ q ∈ s, G ⌊x q / h⌋ :=
          Finset.sum_congr rfl fun q _ => hGq q
      _ = ∑ n ∈ s.image (fun q => ⌊x q / h⌋),
            (s.filter fun q => ⌊x q / h⌋ = n).card • G n :=
          Finset.sum_comp G (fun q => ⌊x q / h⌋)
      _ ≤ ∑ n ∈ s.image (fun q => ⌊x q / h⌋), K • G n :=
          Finset.sum_le_sum fun n _ => nsmul_le_nsmul_left (hG0 n) (hK n)
      _ = K • ∑ n ∈ s.image (fun q => ⌊x q / h⌋), G n := (Finset.smul_sum).symm
      _ ≤ K • (ℓ * ((b ^ j) ^ 2 * N)) := nsmul_le_nsmul_right (hgrid j _) K
      _ = K * (ℓ * ((b ^ j) ^ 2 * N)) := nsmul_eq_mul _ _
  have hterm : ∀ j : ℕ, D j * (K * (ℓ * ((b ^ j) ^ 2 * N))) =
      (ρ₀ * b) ^ j / j.factorial * (K * (ℓ * N)) := by
    intro j
    simp only [hD]
    rw [show (K : ℝ) * (ℓ * ((b ^ j) ^ 2 * N)) = (b ^ j) ^ 2 * (K * (ℓ * N)) by ring]
    exact momentWeight_mul_sq ρ₀ b (K * (ℓ * N)) j hb.ne'
  calc ∑ q ∈ s, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2
      ≤ ∑ q ∈ s, Real.exp (ρ₀ * b) * ∑' j, D j * B j q ^ 2 :=
        Finset.sum_le_sum fun q _ => hpt q
    _ = Real.exp (ρ₀ * b) * ∑' j, D j * ∑ q ∈ s, B j q ^ 2 := by
        rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun q _ => hsummD q)]
        congr 1
        refine tsum_congr fun j => ?_
        rw [Finset.mul_sum]
    _ ≤ Real.exp (ρ₀ * b) * ∑' j, D j * (K * (ℓ * ((b ^ j) ^ 2 * N))) := by
        refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun j => ?_) ?_ ?_)
          (Real.exp_pos _).le
        · exact mul_le_mul_of_nonneg_left (hcell j) (hD0 j)
        · refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
            ((Real.summable_pow_div_factorial (ρ₀ * b)).mul_right (K * (ℓ * N)))
          · exact mul_nonneg (hD0 j) (Finset.sum_nonneg fun q _ => sq_nonneg _)
          · calc D j * ∑ q ∈ s, B j q ^ 2 ≤ D j * (K * (ℓ * ((b ^ j) ^ 2 * N))) :=
                  mul_le_mul_of_nonneg_left (hcell j) (hD0 j)
              _ = (ρ₀ * b) ^ j / j.factorial * (K * (ℓ * N)) := hterm j
        · refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
            ((Real.summable_pow_div_factorial (ρ₀ * b)).mul_right (K * (ℓ * N)))
          exact le_of_eq (hterm j)
    _ = Real.exp (ρ₀ * b) * (Real.exp (ρ₀ * b) * (K * (ℓ * N))) := by
        congr 1
        rw [tsum_congr hterm, tsum_mul_right, hE]
    _ = Real.exp (2 * ρ₀ * b) * (K * (ℓ * N)) := by
        rw [← mul_assoc, ← Real.exp_add, show ρ₀ * b + ρ₀ * b = 2 * ρ₀ * b by ring]

end GaloisForLFunctions.WindowVisibilityLaw
