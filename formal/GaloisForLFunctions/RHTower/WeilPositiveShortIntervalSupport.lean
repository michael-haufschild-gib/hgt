import GaloisForLFunctions.HTGeometry.ShortBumpMellinSmoothedSums
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# Weil-positive weight systems have support in every interval of length `x^{1/2+ε}`

A real weight system `lam` on the integers is Weil-positive in Herglotz form for an archimedean
datum `A` if `Φ = A + 1/(s − 1) − Σ lam(n) n^{-s}` continues holomorphically to `Re s > 1/2` with
`Re Φ ≥ 0` there (`HerglotzWeilPositive`).  For ζ's datum `A = logDeriv Γ_ℝ + 1/s` and
`lam = Λ` this is `Φ = ξ'/ξ`, and Weil positivity of `Λ` is the Riemann hypothesis.

* Harnack on the discs `B(2 + it, 3/2)` gives `‖Φ(σ + it)‖ ≤ (1 + 3/(σ − 1/2)) ‖Φ(2 + it)‖`, so the
  regular part `E = D − 1/(s − 1) = A − Φ` is `O(log|t| / (σ − 1/2))` on the strip
  (`norm_regularPart_le`).
* Smoothed sums over `(x, x + δx)` equal `x ∫ φ_δ` up to `C x^{1/2+η} δ^{-κ}/(ηκ)`
  (`exists_const_abs_smoothedSum_sub_le`): Mellin inversion on `Re s = 2`, the pole is the main
  term, and the regular part moves to `Re s = 1/2 + η`.
* Hence every interval `(x, x + x^{1/2+ε})` meets the support of `lam`
  (`exists_weight_ne_zero_mem_Ioo_of_herglotzWeilPositive`).  A Weil-positive system supported on
  the primes forces a prime in every such interval (`exists_prime_mem_Ioo_of_herglotzWeilPositive`).
* ζ's datum has logarithmic growth on the strip (`exists_log_bound_zetaArchimedeanDatum`), so both
  statements hold for ζ's Weil cone (`exists_prime_mem_Ioo_of_zetaWeilPositive`).
-/

open Complex Metric Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **Harnack bound on the half-plane `Re s > 1/2`.**  A holomorphic function of nonnegative real
part there is controlled on the whole strip `1/2 < Re s ≤ 2` by its values on `Re s = 2`:
`‖Φ(σ + it)‖ ≤ (1 + 3/(σ − 1/2)) ‖Φ(2 + it)‖`. -/
theorem norm_le_of_re_nonneg_halfPlane {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    {σ t : ℝ} (hσ : 1 / 2 < σ) (hσ2 : σ ≤ 2) :
    ‖Φ (σ + t * I)‖ ≤ (1 + 3 / (σ - 1 / 2)) * ‖Φ (2 + t * I)‖ := by
  set c : ℂ := 2 + t * I
  set z : ℂ := σ + t * I
  have hsub : ball c (3 / 2) ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro w hw
    have h1 : |w.re - 2| ≤ ‖w - c‖ := by
      have := Complex.abs_re_le_norm (w - c)
      simpa [c] using this
    have h2 : ‖w - c‖ < 3 / 2 := mem_ball_iff_norm.mp hw
    simp only [mem_setOf_eq]
    linarith [neg_abs_le (w.re - 2)]
  have hzc : ‖z - c‖ = 2 - σ := by
    have : z - c = ((σ - 2 : ℝ) : ℂ) := by simp [z, c]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hz : z ∈ ball c (3 / 2) := by
    rw [mem_ball_iff_norm, hzc]; linarith
  have hH := norm_sub_le_of_re_nonneg_on_ball (hΦ.mono hsub)
    (fun w hw => hre w (hsub hw)) hz
  rw [hzc] at hH
  have hden : (3 : ℝ) / 2 - (2 - σ) = σ - 1 / 2 := by ring
  rw [hden] at hH
  have hpos : 0 < σ - 1 / 2 := by linarith
  have hre_le : (Φ c).re ≤ ‖Φ c‖ := Complex.re_le_norm _
  have hre0 : 0 ≤ (Φ c).re := hre c (by simp [c]; norm_num)
  have hcoef : 2 * (2 - σ) / (σ - 1 / 2) ≤ 3 / (σ - 1 / 2) :=
    div_le_div_of_nonneg_right (by linarith) hpos.le
  calc ‖Φ z‖ = ‖Φ c + (Φ z - Φ c)‖ := by ring_nf
    _ ≤ ‖Φ c‖ + ‖Φ z - Φ c‖ := norm_add_le _ _
    _ ≤ ‖Φ c‖ + 3 / (σ - 1 / 2) * ‖Φ c‖ := by
        gcongr
        calc ‖Φ z - Φ c‖ ≤ 2 * (2 - σ) / (σ - 1 / 2) * (Φ c).re := hH
          _ ≤ 3 / (σ - 1 / 2) * ‖Φ c‖ :=
            mul_le_mul hcoef hre_le hre0 (by positivity)
    _ = (1 + 3 / (σ - 1 / 2)) * ‖Φ c‖ := by ring

/-- The norm of a Dirichlet series with absolutely summable weights on `Re s = 2`. -/
theorem norm_LSeries_two_le {lam : ℕ → ℝ}
    (hsum : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ (2 : ℝ)) (t : ℝ) :
    ‖LSeries (fun n => (lam n : ℂ)) (2 + t * I)‖ ≤ ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) := by
  have hterm : ∀ n : ℕ, ‖LSeries.term (fun n => (lam n : ℂ)) (2 + t * I) n‖
      = |lam n| / (n : ℝ) ^ (2 : ℝ) := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, Complex.norm_real]
  have hs : Summable fun n : ℕ => ‖LSeries.term (fun n => (lam n : ℂ)) (2 + t * I) n‖ := by
    simpa [hterm] using hsum
  calc ‖LSeries (fun n => (lam n : ℂ)) (2 + t * I)‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n => (lam n : ℂ)) (2 + t * I) n‖ := by
        rw [LSeries]; exact norm_tsum_le_tsum_norm hs
    _ = ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) := by simp [hterm]

/-- **The regular part of a Herglotz-completed Dirichlet series grows at most like
`log|t| / (σ − 1/2)` on the strip.**  If `Φ = A + 1/(s−1) − D` on `Re s = 2`, `Φ` has nonnegative
real part on `Re s > 1/2`, and `A` grows logarithmically, then `E = A − Φ` (which equals
`D − 1/(s−1)` on `Re s = 2`) satisfies `‖E(σ + it)‖ ≤ C log(|t| + 3)/(σ − 1/2)`. -/
theorem norm_regularPart_le {lam : ℕ → ℝ} {A Φ : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hsum : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ (2 : ℝ))
    (hΦ : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    (hid : ∀ t : ℝ, Φ (2 + t * I) =
      A (2 + t * I) + 1 / (2 + t * I - 1) - LSeries (fun n => (lam n : ℂ)) (2 + t * I))
    {σ t : ℝ} (hσ : 1 / 2 < σ) (hσ2 : σ ≤ 2) :
    ‖A (σ + t * I) - Φ (σ + t * I)‖ ≤
      6 * (K + 1 + ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) * Real.log (|t| + 3) / (σ - 1 / 2) := by
  set L : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)
  have hL : 0 ≤ L := tsum_nonneg fun n => by positivity
  have hlog : 1 < Real.log (|t| + 3) := one_lt_log_abs_add_three t
  have hpos : 0 < σ - 1 / 2 := by linarith
  have hA2 : ‖A (2 + t * I)‖ ≤ K * Real.log (|t| + 3) := by
    have := hAK (2 + t * I) (by simp; norm_num) (by simp)
    simpa using this
  have hinv : ‖(1 : ℂ) / (2 + t * I - 1)‖ ≤ 1 := by
    have h1 : (2 : ℂ) + t * I - 1 = 1 + t * I := by ring
    rw [h1, norm_div, norm_one]
    have : 1 ≤ ‖(1 : ℂ) + t * I‖ := by
      have := Complex.abs_re_le_norm ((1 : ℂ) + t * I)
      simpa using this
    exact div_le_one_of_le₀ this (norm_nonneg _)
  have hΦ2 : ‖Φ (2 + t * I)‖ ≤ (K + 1 + L) * Real.log (|t| + 3) := by
    rw [hid t]
    calc ‖A (2 + t * I) + 1 / (2 + t * I - 1) - LSeries (fun n => (lam n : ℂ)) (2 + t * I)‖
        ≤ ‖A (2 + t * I)‖ + ‖(1 : ℂ) / (2 + t * I - 1)‖
            + ‖LSeries (fun n => (lam n : ℂ)) (2 + t * I)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ K * Real.log (|t| + 3) + 1 + L := by
          gcongr
          exact norm_LSeries_two_le hsum t
      _ ≤ (K + 1 + L) * Real.log (|t| + 3) := by nlinarith
  have hAσ : ‖A (σ + t * I)‖ ≤ K * Real.log (|t| + 3) := by
    have := hAK (σ + t * I) (by simpa using hσ) (by simpa using hσ2)
    simpa using this
  have hΦσ := norm_le_of_re_nonneg_halfPlane hΦ hre hσ hσ2 (t := t)
  have hone : 1 ≤ (3 / 2) / (σ - 1 / 2) := by rw [le_div_iff₀ hpos]; linarith
  have hlog0 : 0 ≤ Real.log (|t| + 3) := by linarith
  have hfinal : ‖A (σ + t * I) - Φ (σ + t * I)‖ ≤
      K * Real.log (|t| + 3) + (1 + 3 / (σ - 1 / 2)) * ((K + 1 + L) * Real.log (|t| + 3)) := by
    calc ‖A (σ + t * I) - Φ (σ + t * I)‖ ≤ ‖A (σ + t * I)‖ + ‖Φ (σ + t * I)‖ := norm_sub_le _ _
      _ ≤ _ := by
          gcongr
          exact hΦσ.trans (by gcongr)
  refine hfinal.trans ?_
  rw [le_div_iff₀ hpos]
  have h3 : (1 + 3 / (σ - 1 / 2)) * (σ - 1 / 2) = σ - 1 / 2 + 3 := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
  have hσ' : σ - 1 / 2 ≤ 3 / 2 := by linarith
  have hKL : 0 ≤ (K + 1 + L) * Real.log (|t| + 3) := by positivity
  calc (K * Real.log (|t| + 3) + (1 + 3 / (σ - 1 / 2)) * ((K + 1 + L) * Real.log (|t| + 3)))
        * (σ - 1 / 2)
      = K * Real.log (|t| + 3) * (σ - 1 / 2)
        + ((1 + 3 / (σ - 1 / 2)) * (σ - 1 / 2)) * ((K + 1 + L) * Real.log (|t| + 3)) := by ring
    _ = K * Real.log (|t| + 3) * (σ - 1 / 2)
        + (σ - 1 / 2 + 3) * ((K + 1 + L) * Real.log (|t| + 3)) := by rw [h3]
    _ ≤ 6 * (K + 1 + L) * Real.log (|t| + 3) := by
        have hK' : K * Real.log (|t| + 3) ≤ (K + 1 + L) * Real.log (|t| + 3) := by
          gcongr; linarith
        nlinarith [mul_le_mul_of_nonneg_right hσ' (by positivity : (0:ℝ) ≤ K * Real.log (|t| + 3)),
          mul_le_mul_of_nonneg_right hσ' hKL]

/-- Weil positivity in Herglotz form for the weight system `lam` with archimedean datum `A`: the
function `Φ = A + 1/(s−1) − Σ lam(n) n^{-s}`, defined on `Re s > 1`, continues holomorphically to
`Re s > 1/2` with nonnegative real part there. -/
structure HerglotzWeilPositive (lam : ℕ → ℝ) (A : ℂ → ℂ) : Prop where
  summable : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ
  herglotz : ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
    (∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) ∧
    ∀ s : ℂ, 1 < s.re → Φ s = A s + 1 / (s - 1) - LSeries (fun n => (lam n : ℂ)) s

/-- **Contour-shifted representation of smoothed sums.**  If `Φ = A + 1/(s−1) − D` on `Re s = 2`,
`Φ` has nonnegative real part on `Re s > 1/2`, and `A` grows logarithmically, then for
`0 < δ ≤ 1`, `x ≥ 1` and `1/2 < c ≤ 2`,
`Σ_n lam(n) φ_δ(n/x) − x ∫ φ_δ = (1/2π) ∫ x^{c+iy} 𝓜φ_δ(c+iy) (A − Φ)(c+iy) dy`.
Mellin inversion on `Re s = 2` gives the sum; the pole `1/(s−1)` gives exactly `x ∫ φ_δ`; the
regular part `A − Φ = D − 1/(s−1)` is then moved to `Re s = c`. -/
theorem smoothedSum_sub_eq_shifted_integral {lam : ℕ → ℝ} {A Φ : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    (hsum : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ (2 : ℝ))
    (hΦ : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid2 : ∀ t : ℝ, Φ (2 + t * I) =
      A (2 + t * I) + 1 / (2 + t * I - 1) - LSeries (fun n => (lam n : ℂ)) (2 + t * I))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx : 1 ≤ x) {c : ℝ} (hc : 1 / 2 < c)
    (hc2 : c ≤ 2) :
    ((∑' n : ℕ, lam n * shortBump δ (n / x) : ℝ) : ℂ) - ((x * ∫ u, shortBump δ u : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ, (x : ℂ) ^ ((c : ℂ) + y * I) *
        mellin (fun u => (shortBump δ u : ℂ)) ((c : ℂ) + y * I) *
          (A ((c : ℂ) + y * I) - Φ ((c : ℂ) + y * I)) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_deriv_shortBumpProfile
  set L : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)
  have hL : 0 ≤ L := tsum_nonneg fun n => by positivity
  set CE : ℝ := 6 * (K + 1 + L)
  have hCE : 0 ≤ CE := by positivity
  set E : ℂ → ℂ := fun s => A s - Φ s
  have hE : ∀ σ t : ℝ, 1 / 2 < σ → σ ≤ 2 →
      ‖E (σ + t * I)‖ ≤ CE * Real.log (|t| + 3) / (σ - 1 / 2) :=
    fun σ t hσ hσ2 => norm_regularPart_le hK hsum hΦ hre hAK hid2 hσ hσ2
  have hx0 : 0 < x := by linarith
  set η : ℝ := c - 1 / 2
  have hη : 0 < η := by simp only [η]; linarith
  set Mf : ℂ → ℂ := mellin (fun u => (shortBump δ u : ℂ))
  have hMd : Differentiable ℂ Mf := differentiable_mellin_shortBump hδ
  set G : ℂ → ℂ := fun s => (x : ℂ) ^ s * Mf s * E s
  have hstrip : ∀ {a b : ℝ}, 1 / 2 < a → GaloisForLFunctions.HTGeometry.verticalStrip a b ⊆
      {s : ℂ | 1 / 2 < s.re} := by
    intro a b ha s hs
    rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hs
    exact lt_of_lt_of_le ha hs.1
  have hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    have hxc : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
      (differentiableAt_id).const_cpow (Or.inl (by exact_mod_cast hx0.ne'))
    have hA' : DifferentiableAt ℂ A s :=
      hA.differentiableAt (isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs)
    have hΦ' : DifferentiableAt ℂ Φ s :=
      hΦ.differentiableAt (isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs)
    exact ((hxc.mul (hMd s)).mul (hA'.sub hΦ')).differentiableWithinAt
  -- pointwise bound on a line
  have hGb : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 2 → ∀ y : ℝ,
      ‖G ((σ : ℂ) + y * I)‖ ≤ x ^ σ * ((4 + 16 * M) * δ / (1 + δ ^ 2 * y ^ 2)) *
        (CE * Real.log (|y| + 3) / (σ - 1 / 2)) :=
    fun σ hσ hσ2 y => norm_shiftedIntegrand_le hE hM hδ hδ1 hx0 hσ hσ2 y
  -- integrability on a line
  have hGint : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 2 → Integrable fun y : ℝ => G ((σ : ℂ) + y * I) := by
    intro σ hσ hσ2
    obtain ⟨hI, -⟩ := integral_lorentz_rpow_le hδ hδ1 (κ := 1 / 2) (by norm_num) le_rfl
    have hσ' : 0 < σ - 1 / 2 := by linarith
    refine (hI.const_mul (x ^ σ * (4 + 16 * M) * CE * 2 / (σ - 1 / 2))).mono' ?_ ?_
    · have hcont : Continuous fun y : ℝ => G ((σ : ℂ) + y * I) := by
        have hmem : ∀ y : ℝ, ((σ : ℂ) + y * I) ∈ {s : ℂ | 1 / 2 < s.re} := fun y => by simpa using hσ
        exact hGd.continuousOn.comp_continuous (by fun_prop) hmem
      exact hcont.aestronglyMeasurable
    · refine Eventually.of_forall fun y => (hGb σ hσ hσ2 y).trans ?_
      have hlog := log_abs_add_three_le_rpow (κ := 1 / 2) (by norm_num) y
      have hden : 0 < 1 + δ ^ 2 * y ^ 2 := by positivity
      calc x ^ σ * ((4 + 16 * M) * δ / (1 + δ ^ 2 * y ^ 2)) * (CE * Real.log (|y| + 3) / (σ - 1 / 2))
          ≤ x ^ σ * ((4 + 16 * M) * δ / (1 + δ ^ 2 * y ^ 2)) *
              (CE * ((|y| + 3) ^ (1 / 2 : ℝ) / (1 / 2)) / (σ - 1 / 2)) := by gcongr
        _ = x ^ σ * (4 + 16 * M) * CE * 2 / (σ - 1 / 2) *
              (δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ (1 / 2 : ℝ)) := by field_simp
  -- horizontal edges
  have hhor : ∀ s : ℝ, s = 1 ∨ s = -1 → Tendsto (fun T : ℝ =>
      ∫ u in c..(2 : ℝ), G ((u : ℂ) + ((s * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    intro s hs
    have habs : ∀ T : ℝ, |s * T| = |T| := by
      intro T; rcases hs with rfl | rfl <;> simp
    refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun T => x ^ (2 : ℝ) * ((4 + 16 * M) * δ / (1 + δ ^ 2 * T ^ 2)) *
        (CE * Real.log (|T| + 3) / η)) (hgt := fun T => s * T) ?_ ?_
    · refine Eventually.of_forall fun T u hu => ?_
      rw [uIoc_of_le hc2] at hu
      have hu1 : 1 / 2 < u := lt_trans hc hu.1
      refine (hGb u hu1 hu.2 (s * T)).trans ?_
      have hsq : (s * T) ^ 2 = T ^ 2 := by rw [← sq_abs, habs, sq_abs]
      rw [hsq, habs]
      have hxu : x ^ u ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hu.2
      have hηu : η ≤ u - 1 / 2 := by simp only [η]; linarith [hu.1]
      have hlog0 : 0 ≤ Real.log (|T| + 3) := Real.log_nonneg (by linarith [abs_nonneg T])
      gcongr
    · -- `δ log(T+3)/(1+δ²T²) → 0`
      have hlim : Tendsto (fun T : ℝ => Real.log (|T| + 3) / (1 + δ ^ 2 * T ^ 2)) atTop (𝓝 0) := by
        have hb : Tendsto (fun T : ℝ => 4 / (δ ^ 2 * T)) atTop (𝓝 0) := by
          have h := ((tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < δ ^ 2)).inv_tendsto_atTop).const_mul 4
          simpa [div_eq_mul_inv] using h
        refine squeeze_zero' (Eventually.of_forall fun T => by
          have : 0 ≤ Real.log (|T| + 3) := Real.log_nonneg (by linarith [abs_nonneg T])
          positivity) ?_ hb
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
        have hT0 : 0 < T := by linarith
        have hlog : Real.log (|T| + 3) ≤ |T| + 3 - 1 := Real.log_le_sub_one_of_pos (by positivity)
        rw [abs_of_pos hT0] at hlog ⊢
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg T, mul_pos hT0 (by positivity : (0 : ℝ) < δ ^ 2)]
      have := (hlim.const_mul (x ^ (2 : ℝ) * (4 + 16 * M) * δ * CE / η))
      simp only [mul_zero] at this
      refine this.congr' (Eventually.of_forall fun T => ?_)
      field_simp
  have hshift := GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
    (G := G) hc2 (hGd.mono (hstrip hc)) (hGint c hc hc2) (hGint 2 (by norm_num) le_rfl)
    (by simpa using hhor (-1) (Or.inr rfl)) (by simpa using hhor 1 (Or.inl rfl))
  -- the two Mellin identities on `Re s = 2`
  have hsumId := tsum_mul_shortBump_eq_integral hsum hδ hδ1 hx0
  have hpoleId := integral_shortBump_eq_pole_integral hδ hδ1 hx
  have hMint2 : Integrable fun y : ℝ => Mf (2 + y * I) := by
    simpa using integrable_mellin_shortBump_line hδ hδ1 (σ := 2) (by norm_num) le_rfl
  have hMc2 : Continuous fun y : ℝ => Mf (2 + y * I) := by
    simpa using continuous_mellin_shortBump_line hδ 2
  have hxc : Continuous fun y : ℝ => (x : ℂ) ^ ((2 : ℂ) + y * I) :=
    continuous_const.cpow (by fun_prop) (fun _ => Or.inl (by simpa using hx0))
  have hI1 : Integrable fun y : ℝ => (x : ℂ) ^ ((2 : ℂ) + y * I) * Mf (2 + y * I) *
      LSeries (fun n => (lam n : ℂ)) (2 + y * I) := by
    refine (hMint2.norm.const_mul (x ^ (2 : ℝ) * L)).mono' ?_ (Eventually.of_forall fun y => ?_)
    · have : Continuous fun y : ℝ => LSeries (fun n => (lam n : ℂ)) (2 + y * I) := by
        have h := hid2
        have hc' : Continuous fun y : ℝ => A (2 + y * I) - Φ (2 + y * I) + 1 / (2 + y * I - 1) := by
          have hmem : ∀ y : ℝ, ((2 : ℂ) + y * I) ∈ {s : ℂ | 1 / 2 < s.re} := fun y => by
            simp; norm_num
          have hAΦ : Continuous fun y : ℝ => A (2 + y * I) - Φ (2 + y * I) :=
            ((hA.sub hΦ).continuousOn.comp_continuous (by fun_prop) hmem)
          refine hAΦ.add (continuous_const.div (by fun_prop) fun y => ?_)
          intro h0; have := congrArg Complex.re h0; norm_num at this
        refine hc'.congr fun y => ?_
        rw [h y]; ring
      exact ((hxc.mul hMc2).mul this).aestronglyMeasurable
    · rw [norm_mul, norm_mul, norm_ofReal_cpow_two_add hx0]
      have := norm_LSeries_two_le hsum y
      calc x ^ (2 : ℝ) * ‖Mf (2 + y * I)‖ * ‖LSeries (fun n => (lam n : ℂ)) (2 + y * I)‖
          ≤ x ^ (2 : ℝ) * ‖Mf (2 + y * I)‖ * L := by gcongr
        _ = x ^ (2 : ℝ) * L * ‖Mf (2 + y * I)‖ := by ring
  have hI2 : Integrable fun y : ℝ => (x : ℂ) ^ ((2 : ℂ) + y * I) * Mf (2 + y * I) *
      (1 / ((2 : ℂ) + y * I - 1)) := by
    refine (hMint2.norm.const_mul (x ^ (2 : ℝ))).mono' ?_ (Eventually.of_forall fun y => ?_)
    · have : Continuous fun y : ℝ => (1 : ℂ) / ((2 : ℂ) + y * I - 1) :=
        continuous_const.div (by fun_prop) fun y h0 => by
          have := congrArg Complex.re h0; norm_num at this
      exact ((hxc.mul hMc2).mul this).aestronglyMeasurable
    · rw [norm_mul, norm_mul, norm_ofReal_cpow_two_add hx0]
      have h1 : ‖(1 : ℂ) / ((2 : ℂ) + y * I - 1)‖ ≤ 1 := by
        rw [norm_div, norm_one]
        refine div_le_one_of_le₀ ?_ (norm_nonneg _)
        have h := Complex.abs_re_le_norm ((2 : ℂ) + y * I - 1)
        have hre1 : ((2 : ℂ) + y * I - 1).re = 1 := by simp; norm_num
        rw [hre1, abs_one] at h
        exact h
      calc x ^ (2 : ℝ) * ‖Mf (2 + y * I)‖ * ‖(1 : ℂ) / ((2 : ℂ) + y * I - 1)‖
          ≤ x ^ (2 : ℝ) * ‖Mf (2 + y * I)‖ * 1 := by gcongr
        _ = x ^ (2 : ℝ) * ‖Mf (2 + y * I)‖ := by ring
  have hdiff : ((∑' n : ℕ, lam n * shortBump δ (n / x) : ℝ) : ℂ) -
      ((x * ∫ u, shortBump δ u : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ, G ((c : ℂ) + y * I) := by
    rw [hsumId, hpoleId, ← mul_sub, ← integral_sub hI1 hI2, ← hshift]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [G, E]
    push_cast
    rw [hid2 y]
    ring
  exact hdiff

/-- **Smoothed sums of a Weil-positive system, with square-root error.**  If `lam` is
Weil-positive in Herglotz form for an archimedean datum `A` of logarithmic growth, then for
`0 < δ ≤ 1`, `x ≥ 1`, `0 < η ≤ 3/2` and `0 < κ ≤ 1/2`,
`|Σ_n lam(n) φ_δ(n/x) − x ∫ φ_δ| ≤ C x^{1/2+η} δ^{-κ} / (η κ)`.
Proof: Mellin inversion on `Re s = 2`, the pole of `D` at `1` is exactly the term `x ∫ φ_δ`, and
the regular part `E = D − 1/(s−1)` is moved to `Re s = 1/2 + η`, where the Harnack bound gives
`‖E‖ ≪ log|t| / η`. -/
theorem exists_const_abs_smoothedSum_sub_le {lam : ℕ → ℝ} {A : ℂ → ℂ} {K : ℝ}
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re}) (hK : 0 ≤ K)
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    (hW : HerglotzWeilPositive lam A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ x η κ : ℝ, 0 < δ → δ ≤ 1 → 1 ≤ x → 0 < η → η ≤ 3 / 2 → 0 < κ →
      κ ≤ 1 / 2 →
        |(∑' n : ℕ, lam n * shortBump δ (n / x)) - x * ∫ u, shortBump δ u| ≤
          C * x ^ (1 / 2 + η) * δ ^ (-κ) / (η * κ) := by
  obtain ⟨Φ, hΦ, hre, hid⟩ := hW.herglotz
  have hsum : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ (2 : ℝ) := hW.summable 2 (by norm_num)
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_deriv_shortBumpProfile
  set L : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)
  have hL : 0 ≤ L := tsum_nonneg fun n => by positivity
  set CE : ℝ := 6 * (K + 1 + L)
  have hCE : 0 ≤ CE := by positivity
  have hid2 : ∀ t : ℝ, Φ (2 + t * I) =
      A (2 + t * I) + 1 / (2 + t * I - 1) - LSeries (fun n => (lam n : ℂ)) (2 + t * I) :=
    fun t => hid _ (by simp)
  set E : ℂ → ℂ := fun s => A s - Φ s
  have hE : ∀ σ t : ℝ, 1 / 2 < σ → σ ≤ 2 →
      ‖E (σ + t * I)‖ ≤ CE * Real.log (|t| + 3) / (σ - 1 / 2) :=
    fun σ t hσ hσ2 => norm_regularPart_le hK hsum hΦ hre hAK hid2 hσ hσ2
  have hJ : 0 ≤ lorentzHalfConst := integral_nonneg fun v => by positivity
  refine ⟨(4 + 16 * M) * CE * lorentzHalfConst / (2 * Real.pi), by positivity, ?_⟩
  intro δ x η κ hδ hδ1 hx hη hη2 hκ hκ2
  have hx0 : 0 < x := by linarith
  set c : ℝ := 1 / 2 + η
  have hc : 1 / 2 < c := by simp only [c]; linarith
  have hc2 : c ≤ 2 := by simp only [c]; linarith
  set Mf : ℂ → ℂ := mellin (fun u => (shortBump δ u : ℂ))
  set G : ℂ → ℂ := fun s => (x : ℂ) ^ s * Mf s * E s
  have hGb : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 2 → ∀ y : ℝ,
      ‖G ((σ : ℂ) + y * I)‖ ≤ x ^ σ * ((4 + 16 * M) * δ / (1 + δ ^ 2 * y ^ 2)) *
        (CE * Real.log (|y| + 3) / (σ - 1 / 2)) :=
    fun σ hσ hσ2 y => norm_shiftedIntegrand_le hE hM hδ hδ1 hx0 hσ hσ2 y
  have hdiff : ((∑' n : ℕ, lam n * shortBump δ (n / x) : ℝ) : ℂ) -
      ((x * ∫ u, shortBump δ u : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ, G ((c : ℂ) + y * I) :=
    smoothedSum_sub_eq_shifted_integral hK hA hAK hsum hΦ hre hid2 hδ hδ1 hx hc hc2
  -- the final estimate
  obtain ⟨hIκ, hIκb⟩ := integral_lorentz_rpow_le hδ hδ1 hκ hκ2
  have hpt : ∀ y : ℝ, ‖G ((c : ℂ) + y * I)‖ ≤
      x ^ c * (4 + 16 * M) * CE / (η * κ) * (δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ κ) := by
    intro y
    refine (hGb c hc hc2 y).trans ?_
    have hlog := log_abs_add_three_le_rpow hκ y
    have hcη : c - 1 / 2 = η := by simp only [c]; ring
    rw [hcη]
    calc x ^ c * ((4 + 16 * M) * δ / (1 + δ ^ 2 * y ^ 2)) * (CE * Real.log (|y| + 3) / η)
        ≤ x ^ c * ((4 + 16 * M) * δ / (1 + δ ^ 2 * y ^ 2)) * (CE * ((|y| + 3) ^ κ / κ) / η) := by
          gcongr
      _ = x ^ c * (4 + 16 * M) * CE / (η * κ) * (δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ κ) := by
          field_simp
  have hnormInt : ‖∫ y : ℝ, G ((c : ℂ) + y * I)‖ ≤
      x ^ c * (4 + 16 * M) * CE / (η * κ) * (δ ^ (-κ) * lorentzHalfConst) := by
    calc ‖∫ y : ℝ, G ((c : ℂ) + y * I)‖
        ≤ ∫ y : ℝ, x ^ c * (4 + 16 * M) * CE / (η * κ) * (δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ κ) :=
          norm_integral_le_of_norm_le (hIκ.const_mul _) (Eventually.of_forall hpt)
      _ = x ^ c * (4 + 16 * M) * CE / (η * κ) *
            ∫ y : ℝ, δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ κ := integral_const_mul _ _
      _ ≤ _ := by gcongr
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hre' : |(∑' n : ℕ, lam n * shortBump δ (n / x)) - x * ∫ u, shortBump δ u| =
      ‖((∑' n : ℕ, lam n * shortBump δ (n / x) : ℝ) : ℂ) - ((x * ∫ u, shortBump δ u : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hre', hdiff, norm_mul]
  have hnπ : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]; norm_num
  rw [hnπ]
  calc 1 / (2 * Real.pi) * ‖∫ y : ℝ, G ((c : ℂ) + y * I)‖
      ≤ 1 / (2 * Real.pi) * (x ^ c * (4 + 16 * M) * CE / (η * κ) * (δ ^ (-κ) * lorentzHalfConst)) := by
        gcongr
    _ = (4 + 16 * M) * CE * lorentzHalfConst / (2 * Real.pi) * x ^ (1 / 2 + η) * δ ^ (-κ) /
          (η * κ) := by
        simp only [c]; field_simp

/-- **Short-interval law for Weil-positive systems.**  Let `lam` be Weil-positive in Herglotz form
for an archimedean datum `A` of logarithmic growth on `1/2 < Re s ≤ 2` (for instance ζ's datum
`½ψ(s/2 + 1) − ½ log π`).  Then for every `ε > 0` and all large `x`, the interval
`(x, x + x^{1/2+ε})` contains an integer `n` with `lam n ≠ 0`.

The smoothed sum of `lam` over that interval equals its length up to `O(x^{1/2+ε/2})`
(`exists_const_abs_smoothedSum_sub_le`), so it cannot vanish. -/
theorem exists_weight_ne_zero_mem_Ioo_of_herglotzWeilPositive {lam : ℕ → ℝ} {A : ℂ → ℂ} {K : ℝ}
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re}) (hK : 0 ≤ K)
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    (hW : HerglotzWeilPositive lam A) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∃ n : ℕ, x < n ∧ (n : ℝ) < x + x ^ (1 / 2 + ε) ∧ lam n ≠ 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_const_abs_smoothedSum_sub_le hA hK hAK hW
  set e : ℝ := min ε (1 / 2)
  have he : 0 < e := lt_min hε (by norm_num)
  have he2 : e ≤ 1 / 2 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  set B : ℝ := 32 * C / e ^ 2 + 1
  have hB : 0 < B := by positivity
  refine ⟨max 1 (B ^ (2 / e)), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxB : B ^ (2 / e) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  by_contra hno
  simp only [not_exists, not_and, ne_eq, not_not] at hno
  set δ : ℝ := x ^ (-(1 / 2) + e)
  have hδ : 0 < δ := Real.rpow_pos_of_pos hx0 _
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hδx : δ * x = x ^ (1 / 2 + e) := by
    rw [show (1 / 2 + e) = (-(1 / 2) + e) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
  -- the smoothed sum over `(x, x + x^{1/2+e})` vanishes
  have hterm : ∀ n : ℕ, lam n * shortBump δ (n / x) = 0 := by
    intro n
    by_cases hb : shortBump δ (n / x) = 0
    · simp [hb]
    · have hmem : (n : ℝ) / x ∈ Ioo 1 (1 + δ) := by
        by_contra h; exact hb (shortBump_eq_zero hδ h)
      have h1 : x < n := by
        have := hmem.1; rwa [lt_div_iff₀ hx0, one_mul] at this
      have h2 : (n : ℝ) < x + x ^ (1 / 2 + ε) := by
        have := hmem.2
        rw [div_lt_iff₀ hx0] at this
        have hmono : x ^ (1 / 2 + e) ≤ x ^ (1 / 2 + ε) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        nlinarith
      simp [hno n h1 h2]
  have hzero : ∑' n : ℕ, lam n * shortBump δ (n / x) = 0 := by simp [hterm]
  have hmain := hC δ x (e / 4) (e / 2) hδ hδ1 hx1 (by positivity) (by linarith) (by positivity)
    (by linarith)
  rw [hzero, zero_sub, abs_neg] at hmain
  have hlow : x ^ (1 / 2 + e) / 4 ≤ |x * ∫ u, shortBump δ u| := by
    have hint := integral_shortBump_ge hδ
    rw [← hδx]
    calc δ * x / 4 = x * (δ / 4) := by ring
      _ ≤ x * ∫ u, shortBump δ u := by gcongr
      _ ≤ |x * ∫ u, shortBump δ u| := le_abs_self _
  have hδpow : δ ^ (-(e / 2)) ≤ x ^ (e / 4) := by
    rw [← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
  have hup : C * x ^ (1 / 2 + e / 4) * δ ^ (-(e / 2)) / (e / 4 * (e / 2)) ≤
      8 * C / e ^ 2 * x ^ (1 / 2 + e / 2) := by
    have hsplit : x ^ (1 / 2 + e / 2) = x ^ (1 / 2 + e / 4) * x ^ (e / 4) := by
      rw [← Real.rpow_add hx0]; ring_nf
    rw [hsplit]
    have hxp : 0 ≤ x ^ (1 / 2 + e / 4) := by positivity
    calc C * x ^ (1 / 2 + e / 4) * δ ^ (-(e / 2)) / (e / 4 * (e / 2))
        ≤ C * x ^ (1 / 2 + e / 4) * x ^ (e / 4) / (e / 4 * (e / 2)) := by gcongr
      _ = 8 * C / e ^ 2 * (x ^ (1 / 2 + e / 4) * x ^ (e / 4)) := by field_simp; ring
  have hkey : x ^ (1 / 2 + e) / 4 ≤ 8 * C / e ^ 2 * x ^ (1 / 2 + e / 2) :=
    hlow.trans (hmain.trans hup)
  have hsplit2 : x ^ (1 / 2 + e) = x ^ (1 / 2 + e / 2) * x ^ (e / 2) := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [hsplit2] at hkey
  have hpos : 0 < x ^ (1 / 2 + e / 2) := by positivity
  have hsmall : x ^ (e / 2) ≤ 32 * C / e ^ 2 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)] at hkey
    have h' : x ^ (1 / 2 + e / 2) * x ^ (e / 2) ≤ x ^ (1 / 2 + e / 2) * (32 * C / e ^ 2) :=
      hkey.trans (le_of_eq (by ring))
    exact le_of_mul_le_mul_left h' hpos
  have hbig : B ≤ x ^ (e / 2) := by
    calc B = (B ^ (2 / e)) ^ (e / 2) := by
          rw [← Real.rpow_mul hB.le, show 2 / e * (e / 2) = 1 by field_simp, Real.rpow_one]
      _ ≤ x ^ (e / 2) := Real.rpow_le_rpow (by positivity) hxB (by positivity)
  have : B ≤ 32 * C / e ^ 2 := hbig.trans hsmall
  simp only [B] at this
  linarith

/-- **A Weil-positive system supported on the primes forces primes in every interval of length
`x^{1/2+ε}`.** -/
theorem exists_prime_mem_Ioo_of_herglotzWeilPositive {lam : ℕ → ℝ} {A : ℂ → ℂ} {K : ℝ}
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re}) (hK : 0 ≤ K)
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    (hW : HerglotzWeilPositive lam A) (hsupp : ∀ n : ℕ, lam n ≠ 0 → n.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) < x + x ^ (1 / 2 + ε) := by
  obtain ⟨x₀, hx₀⟩ := exists_weight_ne_zero_mem_Ioo_of_herglotzWeilPositive hA hK hAK hW hε
  exact ⟨x₀, fun x hx => by
    obtain ⟨n, h1, h2, h3⟩ := hx₀ x hx
    exact ⟨n, hsupp n h3, h1, h2⟩⟩

/-- **ζ's archimedean datum** `Γ̃(s) = ½ψ(s/2) − ½ log π + 1/s = ½ψ(s/2 + 1) − ½ log π`, i.e.
`logDeriv Γ_ℝ(s) + 1/s` on `Re s > 0`.  With it, `Γ̃(s) + 1/(s−1) − Σ Λ(n) n^{-s} = ξ'/ξ(s)`. -/
noncomputable def zetaArchimedeanDatum (s : ℂ) : ℂ :=
  Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s

theorem differentiableAt_digamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.digamma z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    refine (Complex.differentiableAt_Gamma w fun m h => ?_).differentiableWithinAt
    have := congrArg Complex.re h
    simp at this
    have hw' : 0 < w.re := hw
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hA := hG.analyticOnNhd hopen
  have hd : DifferentiableAt ℂ (deriv Complex.Gamma) z := (hA.deriv z hz).differentiableAt
  have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
    funext w; rw [Complex.digamma_def, logDeriv_apply]
  rw [this]
  exact hd.div (hG.differentiableAt (hopen.mem_nhds hz)) hne

theorem differentiableOn_zetaArchimedeanDatum :
    DifferentiableOn ℂ zetaArchimedeanDatum {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  have h1 : DifferentiableAt ℂ (fun s : ℂ => Complex.digamma (s / 2)) s :=
    (differentiableAt_digamma_of_re_pos (by simpa using half_pos hs')).comp s
      (differentiableAt_id.div_const 2)
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs'
  exact (((h1.div_const 2).sub_const _).add ((differentiableAt_const _).div differentiableAt_id hs0)).differentiableWithinAt

theorem norm_digamma_half_le {σ t : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖Complex.digamma (((σ : ℂ) + t * I) / 2)‖ ≤
      Real.log (|t| + 3) + GaloisForLFunctions.digammaVerticalLogConstant := by
  have hkey : ∀ τ : ℝ, 2 ≤ τ → ‖Complex.digamma (((σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ ≤
      Real.log (τ + 3) + GaloisForLFunctions.digammaVerticalLogConstant := by
    intro τ hτ
    have hσ' : 0 < σ / 2 := by positivity
    have hτ1 : 1 ≤ τ / 2 := by linarith
    have hστ : σ / 2 ≤ τ / 2 := by linarith
    have h := GaloisForLFunctions.norm_digamma_vertical_le_log hσ' hτ1 hστ
    have hl : Real.log (τ / 2) ≤ Real.log (τ + 3) := Real.log_le_log (by positivity) (by linarith)
    linarith
  rcases le_or_gt 0 t with ht0 | ht0
  · rw [abs_of_nonneg ht0] at ht ⊢
    have := hkey t ht
    convert this using 3
    push_cast; ring
  · rw [abs_of_neg ht0] at ht ⊢
    have h := hkey (-t) ht
    have hconj : ((σ : ℂ) + t * I) / 2 =
        (starRingEnd ℂ) (((σ / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * I) := by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [hconj, ReflectedDigammaAnomaly.digamma_conj, Complex.norm_conj]
    convert h using 4

/-- **ζ's archimedean datum has logarithmic growth on the strip `1/2 < Re s ≤ 2`.** -/
theorem exists_log_bound_zetaArchimedeanDatum :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 →
      ‖zetaArchimedeanDatum s‖ ≤ K * Real.log (|s.im| + 3) := by
  -- compact part `|Im s| ≤ 2`
  set Kc : Set ℂ := {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 2 ∧ -2 ≤ s.im ∧ s.im ≤ 2}
  have hKc : IsCompact Kc := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact ((isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          ((isClosed_le continuous_const Complex.continuous_im).inter
            (isClosed_le Complex.continuous_im continuous_const))))
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 4)).subset fun s hs => ?_
      rw [mem_closedBall, dist_zero_right]
      obtain ⟨h1, h2, h3, h4⟩ := hs
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 2 + 2 := by
            gcongr
            · rw [abs_le]; constructor <;> linarith
            · rw [abs_le]; constructor <;> linarith
        _ = 4 := by norm_num
  have hcont : ContinuousOn zetaArchimedeanDatum Kc :=
    differentiableOn_zetaArchimedeanDatum.continuousOn.mono fun s hs => by
      show 0 < s.re; linarith [hs.1]
  obtain ⟨C₀, hC₀⟩ := hKc.exists_bound_of_continuousOn hcont
  set c : ℝ := GaloisForLFunctions.digammaVerticalLogConstant
  have hc : 0 ≤ c := by
    simp only [c, GaloisForLFunctions.digammaVerticalLogConstant]
    have := Real.pi_pos; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  refine ⟨max C₀ 0 + c + 4, by positivity, fun s hs hs2 => ?_⟩
  have hlog : 1 < Real.log (|s.im| + 3) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9; have := abs_nonneg s.im; linarith
  rcases le_or_gt |s.im| 2 with hsmall | hbig
  · have hmem : s ∈ Kc := by
      rw [abs_le] at hsmall
      exact ⟨hs.le, hs2, hsmall.1, hsmall.2⟩
    calc ‖zetaArchimedeanDatum s‖ ≤ C₀ := hC₀ s hmem
      _ ≤ max C₀ 0 * 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ (max C₀ 0 + c + 4) * Real.log (|s.im| + 3) := by
          gcongr
          · linarith
  · have hsre : 0 < s.re := by linarith
    have hs_eq : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
    have hψ := norm_digamma_half_le hsre hs2 hbig.le
    rw [← hs_eq] at hψ
    have hinv : ‖(1 : ℂ) / s‖ ≤ 2 := by
      rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.mpr fun h => by simp [h] at hsre)]
      have := Complex.abs_re_le_norm s
      rw [abs_of_pos hsre] at this; linarith
    have hlogπ : ‖(Real.log Real.pi : ℂ) / 2‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg
        (by linarith [Real.pi_gt_three]))]
      have : Real.log Real.pi < 2 := by
        rw [Real.log_lt_iff_lt_exp Real.pi_pos]
        have := Real.pi_lt_d2
        have := Real.exp_one_gt_d9
        nlinarith [Real.add_one_le_exp 1, Real.exp_pos 1,
          show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
      simp; linarith
    have hmain : ‖zetaArchimedeanDatum s‖ ≤ (Real.log (|s.im| + 3) + c) / 2 + 1 + 2 := by
      simp only [zetaArchimedeanDatum]
      calc ‖Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s‖
          ≤ ‖Complex.digamma (s / 2) / 2‖ + ‖(Real.log Real.pi : ℂ) / 2‖ + ‖(1 : ℂ) / s‖ := by
            refine (norm_add_le _ _).trans ?_
            gcongr
            exact norm_sub_le _ _
        _ ≤ (Real.log (|s.im| + 3) + c) / 2 + 1 + 2 := by
            gcongr
            rw [norm_div]; simp only [RCLike.norm_ofNat]
            gcongr
    calc ‖zetaArchimedeanDatum s‖ ≤ (Real.log (|s.im| + 3) + c) / 2 + 1 + 2 := hmain
      _ ≤ (max C₀ 0 + c + 4) * Real.log (|s.im| + 3) := by
          have h0 : 0 ≤ max C₀ 0 := le_max_right _ _
          nlinarith

/-- **ζ's Weil cone: support in short intervals.**  A weight system that is Weil-positive for ζ's
archimedean datum meets every interval `(x, x + x^{1/2+ε})` for large `x`. -/
theorem exists_weight_ne_zero_mem_Ioo_of_zetaWeilPositive {lam : ℕ → ℝ}
    (hW : HerglotzWeilPositive lam zetaArchimedeanDatum) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∃ n : ℕ, x < n ∧ (n : ℝ) < x + x ^ (1 / 2 + ε) ∧ lam n ≠ 0 := by
  obtain ⟨K, hK, hKb⟩ := exists_log_bound_zetaArchimedeanDatum
  exact exists_weight_ne_zero_mem_Ioo_of_herglotzWeilPositive
    (differentiableOn_zetaArchimedeanDatum.mono fun s hs => by
      show 0 < s.re; have : 1 / 2 < s.re := hs; linarith) hK hKb hW hε

/-- **ζ's Weil cone: prime-supported producers give primes in short intervals.**  If a weight
system supported on the primes is Weil-positive for ζ's archimedean datum, then every interval
`(x, x + x^{1/2+ε})` with `x` large contains a prime. -/
theorem exists_prime_mem_Ioo_of_zetaWeilPositive {lam : ℕ → ℝ}
    (hW : HerglotzWeilPositive lam zetaArchimedeanDatum) (hsupp : ∀ n : ℕ, lam n ≠ 0 → n.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) < x + x ^ (1 / 2 + ε) := by
  obtain ⟨x₀, hx₀⟩ := exists_weight_ne_zero_mem_Ioo_of_zetaWeilPositive hW hε
  exact ⟨x₀, fun x hx => by
    obtain ⟨n, h1, h2, h3⟩ := hx₀ x hx
    exact ⟨n, hsupp n h3, h1, h2⟩⟩

end RHTower
