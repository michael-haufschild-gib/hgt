import GaloisForLFunctions.HTGeometry.HermiteGeneratingFunction
import GaloisForLFunctions.RHTower.XiSliceHeatedOffLineDetection

/-!
# The Hermite window: the slice at a real point as a Hermite sum of heated coefficients

Let `T_N = T_N(λ, 0, t)` be the heated slice coefficients and `p_N = λ^{N/2} He_N(δ/√λ)` the Hermite
weights (`sliceHermiteWeight`).

**Hermite identity** (`hasSum_hermiteWeight_mul_xiSliceHeatTransfer`).  For `λ > 0` and real `δ`,

  `S(t, δ) = Σ_N p_N T_N(λ, 0, t)`.

In the kernel, `e^{δy} = e^{λy²/2} Σ_N p_N yᴺ/N!` (`y = u − v`, the Hermite generating function), and
the absolute series is at most `e^{λy² + |δ||y|}`, which `Φ(u)Φ(v)` integrates.

**The window** (`hermiteWeight_ge`).  For `N ≤ δ²/(4λ)` the weights are positive: `p_N ≥ (δ/2)ᴺ`,
because `δ/√λ ≥ 2√N` puts `He_N` beyond its zeros.  Also `|p_N| ≤ (δ + 2√(λN))ᴺ`
(`abs_hermiteWeight_le`).  So in `S(t, δ) = Σ p_N T_N` the heated coefficients of order `≤ δ²/(4λ)`
enter with positive weights.

**Hermite-window detection** (`exists_re_xiSliceHeatTransfer_neg_of_hermiteWindow`).  At the
horizontal offset `δ` of an off-line zero `S(γ, δ) = 0`.  If `‖S(γ, z)‖ ≤ c₀ e^{K + A‖z‖ + B‖z‖²}`,
`c₀ = S(γ, 0)`, `768Bλ ≤ 1` and `6 e^{K + 50A²λ + 4Aδ + 64Bδ²} max(1, 4(A + √B + 1)√λ e^{(K+6)/2}) <
2^{⌊δ²/(4λ)⌋}`, then some `T_N(λ, 0, γ)` with `N ≤ δ²/(4λ)` is negative.  Proof: if not, the window
terms give `0 = S(γ, δ) ≥ T_0 − Σ_{N > n₀} |p_N T_N|`.  Each tail term is `≤ √2 c₀ e^{K+50A²λ+4Aδ+64Bδ²}
2^{−N}` (Cauchy at radius `4(δ + 2√(λN))`, `abs_hermiteWeight_mul_re_le`), while
`√(2π) T_0 ≥ e^{−1/2} c₀ min(1, e^{−(K+6)/2}/(4(A + √B + 1)√λ))` (`re_xiSliceHeatTransfer_zero_ge`).
The condition is logarithmic in the envelope, so detection holds for
`λ ≍ min(δ/A, δ²/(K + Bδ² + 1))`.

* Product envelope (`exists_re_xiSliceHeatTransfer_neg_of_hermiteWindow_mass`): `K = 0`, `A = 2m/δ`,
  `B = S` give detection for `λ ≍ min(δ²/(m + Sδ² + log(2 + S)), 1/S)`.  The perturbative bound of
  `XiSliceHeatedOffLineDetection` needed `λ ≤ δ² e^{−8δ²S}/C`.
* An envelope with `A ≍ log γ`, `B ≈ 0` and local constant `K` gives the Ki–Kim–Lee scale `λ ≍ δ/log γ`.
-/

open Complex MeasureTheory Filter Topology Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- The Hermite weights `p_N = λ^{N/2} He_N(δ/√λ)`. -/
def sliceHermiteWeight (lam δ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt lam ^ N * aeval (δ / Real.sqrt lam) (hermite N)

/-- `Σ_N p_N yᴺ/N! = e^{δy − λy²/2}`. -/
theorem hasSum_hermiteWeight_mul_pow {lam : ℝ} (hlam : 0 < lam) (δ y : ℝ) :
    HasSum (fun N : ℕ => sliceHermiteWeight lam δ N * y ^ N / (N.factorial : ℝ))
      (Real.exp (δ * y - lam * y ^ 2 / 2)) := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have h := hasSum_aeval_hermite_mul_pow_div_factorial (δ / Real.sqrt lam) (Real.sqrt lam * y)
  have e : δ / Real.sqrt lam * (Real.sqrt lam * y) - (Real.sqrt lam * y) ^ 2 / 2
      = δ * y - lam * y ^ 2 / 2 := by
    rw [mul_pow, Real.sq_sqrt hlam.le]; field_simp
  rw [e] at h
  refine h.congr_fun fun N => ?_
  simp only [sliceHermiteWeight, mul_pow]
  ring

/-- `Σ_N |p_N| |y|ᴺ/N! ≤ e^{|δ||y| + λy²/2}`. -/
theorem summable_abs_hermiteWeight_mul_pow {lam : ℝ} (hlam : 0 < lam) (δ y : ℝ) :
    Summable (fun N : ℕ => |sliceHermiteWeight lam δ N| * |y| ^ N / (N.factorial : ℝ)) ∧
      ∑' N : ℕ, |sliceHermiteWeight lam δ N| * |y| ^ N / (N.factorial : ℝ)
        ≤ Real.exp (|δ| * |y| + lam * y ^ 2 / 2) := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  obtain ⟨h1, h2⟩ := summable_abs_aeval_hermite_le (δ / Real.sqrt lam) (Real.sqrt lam * y)
  have e : ∀ N : ℕ, |sliceHermiteWeight lam δ N| * |y| ^ N / (N.factorial : ℝ)
      = |aeval (δ / Real.sqrt lam) (hermite N)| * |Real.sqrt lam * y| ^ N / (N.factorial : ℝ) := by
    intro N
    simp only [sliceHermiteWeight, abs_mul, abs_pow, abs_of_pos hs, mul_pow]
    ring
  have e2 : |δ / Real.sqrt lam| * |Real.sqrt lam * y| + (Real.sqrt lam * y) ^ 2 / 2
      = |δ| * |y| + lam * y ^ 2 / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hs, mul_pow, Real.sq_sqrt hlam.le]; field_simp
  simp only [e]
  exact ⟨h1, e2 ▸ h2⟩

/-- **The window.**  For `δ ≥ 0` and `4λN ≤ δ²`, `p_N ≥ (δ/2)ᴺ`. -/
theorem hermiteWeight_ge {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 ≤ δ) {N : ℕ}
    (hN : 4 * lam * N ≤ δ ^ 2) : (δ / 2) ^ N ≤ sliceHermiteWeight lam δ N := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hx : 2 * Real.sqrt N ≤ δ / Real.sqrt lam := by
    rw [le_div_iff₀ hs]
    have h1 : (2 * Real.sqrt N * Real.sqrt lam) ^ 2 ≤ δ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), Real.sq_sqrt hlam.le]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hδ (by norm_num)).mp h1
  have h := (pow_half_le_aeval_hermite hx N le_rfl).1
  unfold sliceHermiteWeight
  calc (δ / 2) ^ N = Real.sqrt lam ^ N * (δ / Real.sqrt lam / 2) ^ N := by
        rw [← mul_pow]; congr 1; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

/-- `|p_N| ≤ (|δ| + 2√(λN))ᴺ`. -/
theorem abs_hermiteWeight_le {lam : ℝ} (hlam : 0 < lam) (δ : ℝ) (N : ℕ) :
    |sliceHermiteWeight lam δ N| ≤ (|δ| + 2 * Real.sqrt (lam * N)) ^ N := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have h := (abs_aeval_hermite_le (n := N) (δ / Real.sqrt lam) N le_rfl).1
  unfold sliceHermiteWeight
  rw [abs_mul, abs_pow, abs_of_pos hs]
  calc Real.sqrt lam ^ N * |aeval (δ / Real.sqrt lam) (hermite N)|
      ≤ Real.sqrt lam ^ N * (|δ / Real.sqrt lam| + 2 * Real.sqrt N) ^ N :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (|δ| + 2 * Real.sqrt (lam * N)) ^ N := by
        rw [← mul_pow, Real.sqrt_mul hlam.le, abs_div, abs_of_pos hs]
        congr 1; field_simp

/-- **The Hermite identity.**  `S(t, δ) = Σ_N p_N T_N(λ, 0, t)` for `λ > 0`. -/
theorem hasSum_hermiteWeight_mul_xiSliceHeatTransfer {lam : ℝ} (hlam : 0 < lam) (t δ : ℝ) :
    HasSum (fun N : ℕ => (sliceHermiteWeight lam δ N : ℂ) * xiSliceHeatTransfer lam 0 t N)
      (xiSliceProduct t δ) := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set F : ℕ → ℝ × ℝ → ℂ := fun N p =>
    ((Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
      (sliceHermiteWeight lam δ N * (p.1 - p.2) ^ N / N.factorial) : ℝ) : ℂ)
        * cexp (I * t * (p.1 + p.2)) with hF
  set D : ℝ × ℝ → ℝ := fun p =>
    Φ p.1 * Real.exp ((2 * lam) * p.1 ^ 2) * Real.exp ((|δ| + 1) * |p.1|) *
      (Φ p.2 * Real.exp ((2 * lam) * p.2 ^ 2) * Real.exp ((|δ| + 1) * |p.2|)) with hD
  have hDi : Integrable D := by
    have h := integrable_prod_majorant (riemannKernel_superExp.mul_exp_sq
      (by positivity : (0 : ℝ) ≤ 2 * lam)) (|δ| + 1)
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [hD, hΦ]
  have hnormF : ∀ N p, ‖F N p‖ = Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
      (|sliceHermiteWeight lam δ N| * |p.1 - p.2| ^ N / N.factorial) := by
    intro N p
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add,
      mul_one, abs_div, abs_pow, Nat.abs_cast, abs_mul, abs_of_nonneg (hΦ0 _),
      abs_of_pos (Real.exp_pos _)]
  have hbound : ∀ M : ℕ, ∀ p : ℝ × ℝ, ∑ N ∈ Finset.range M, ‖F N p‖ ≤ D p := by
    intro M p
    simp only [hnormF]
    rw [← Finset.mul_sum]
    obtain ⟨hsum, hle⟩ := summable_abs_hermiteWeight_mul_pow hlam δ (p.1 - p.2)
    have hpart : ∑ N ∈ Finset.range M, |sliceHermiteWeight lam δ N| * |p.1 - p.2| ^ N / N.factorial
        ≤ Real.exp (|δ| * |p.1 - p.2| + lam * (p.1 - p.2) ^ 2 / 2) :=
      le_trans (hsum.sum_le_tsum _ fun N _ => by positivity) hle
    have hΦΦ : 0 ≤ Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) := by
      have := hΦ0 p.1; have := hΦ0 p.2; positivity
    have hexp : Real.exp (lam * (p.1 - p.2) ^ 2 / 2)
        * Real.exp (|δ| * |p.1 - p.2| + lam * (p.1 - p.2) ^ 2 / 2)
        ≤ Real.exp ((2 * lam) * p.1 ^ 2) * Real.exp ((|δ| + 1) * |p.1|)
          * (Real.exp ((2 * lam) * p.2 ^ 2) * Real.exp ((|δ| + 1) * |p.2|)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : |p.1 - p.2| ≤ |p.1| + |p.2| := abs_sub _ _
      have h2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg δ)
      have h3 : (p.1 - p.2) ^ 2 ≤ 2 * p.1 ^ 2 + 2 * p.2 ^ 2 := by nlinarith [sq_nonneg (p.1 + p.2)]
      have h4 := mul_le_mul_of_nonneg_left h3 hlam.le
      nlinarith [abs_nonneg p.1, abs_nonneg p.2]
    calc Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
          ∑ N ∈ Finset.range M, |sliceHermiteWeight lam δ N| * |p.1 - p.2| ^ N / N.factorial
        ≤ Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
            Real.exp (|δ| * |p.1 - p.2| + lam * (p.1 - p.2) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hpart hΦΦ
      _ = Φ p.1 * Φ p.2 * (Real.exp (lam * (p.1 - p.2) ^ 2 / 2)
            * Real.exp (|δ| * |p.1 - p.2| + lam * (p.1 - p.2) ^ 2 / 2)) := by ring
      _ ≤ Φ p.1 * Φ p.2 * (Real.exp ((2 * lam) * p.1 ^ 2) * Real.exp ((|δ| + 1) * |p.1|)
            * (Real.exp ((2 * lam) * p.2 ^ 2) * Real.exp ((|δ| + 1) * |p.2|))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg (hΦ0 _) (hΦ0 _))
      _ = D p := by simp only [hD]; ring
  have hmeas : ∀ N, AEStronglyMeasurable (F N) := by
    intro N
    refine Continuous.aestronglyMeasurable ?_
    have := continuous_riemannKernelReal
    simp only [hF, hΦ]
    fun_prop
  have hint : ∀ N, Integrable (F N) := by
    intro N
    refine hDi.mono' (hmeas N) (Eventually.of_forall fun p => ?_)
    have := hbound (N + 1) p
    rw [Finset.sum_range_succ] at this
    have hnn : 0 ≤ ∑ i ∈ Finset.range N, ‖F i p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hsum : Summable (fun N => ∫ p, ‖F N p‖) := by
    refine summable_of_sum_range_le (c := ∫ p, D p)
      (fun N => integral_nonneg fun p => norm_nonneg _) fun M => ?_
    rw [← integral_finsetSum _ (fun N _ => (hint N).norm)]
    exact integral_mono (integrable_finsetSum _ fun N _ => (hint N).norm) hDi (hbound M)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ p : ℝ × ℝ, ∑' N, F N p =
      ((Φ p.1 * Φ p.2 * Real.exp (δ * (p.1 - p.2)) * ((p.1 - p.2) ^ 0 / (0 : ℕ).factorial) : ℝ) : ℂ)
        * cexp (I * t * (p.1 + p.2)) := by
    intro p
    have hR := (hasSum_hermiteWeight_mul_pow hlam δ (p.1 - p.2)).mul_left
      (Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2))
    have hC := (Complex.hasSum_ofReal.mpr hR).mul_right (cexp (I * t * (p.1 + p.2)))
    refine (hC.congr_fun fun N => ?_).tsum_eq.trans ?_
    · simp only [hF]
    · have e : Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * Real.exp (δ * (p.1 - p.2) - lam * (p.1 - p.2) ^ 2 / 2)
          = Real.exp (δ * (p.1 - p.2)) := by rw [← Real.exp_add]; ring_nf
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
      rw [← e]; push_cast; ring
  simp_rw [htsum] at h
  have hslice : xiSliceProduct t δ = kernelSliceMoment Φ δ t 0 := by
    rw [kernelSliceMoment_eq_iteratedDeriv riemannKernel_superExp, cosTransform_riemannKernel_slice]
    simp
  rw [hslice]
  refine h.congr_fun fun N => ?_
  simp only [hF, xiSliceHeatTransfer]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [zero_mul, Real.exp_zero, mul_one]
  push_cast
  ring

/-- The envelope `c₀ e^{K + Aρ + Bρ²}`. -/
def sliceExpEnvelope (c₀ K A B : ℝ) (ρ : ℝ) : ℝ := c₀ * Real.exp (K + A * ρ + B * ρ ^ 2)

theorem expEnvelope_mono {c₀ K A B : ℝ} (hc₀ : 0 ≤ c₀) (hA : 0 ≤ A) (hB : 0 ≤ B) {ρ ρ' : ℝ}
    (hρ : 0 ≤ ρ) (hρρ : ρ ≤ ρ') : sliceExpEnvelope c₀ K A B ρ ≤ sliceExpEnvelope c₀ K A B ρ' := by
  unfold sliceExpEnvelope
  have h2 : ρ ^ 2 ≤ ρ' ^ 2 := pow_le_pow_left₀ hρ hρρ 2
  gcongr

/-- **Gaussian average of the envelope.**  For `16 B λ ≤ 1`,
`∫ e^{−w²/2} c₀ e^{K + A(√λ|w| + r) + B(√λ|w| + r)²} dw ≤ √(4π) c₀ e^{K + Ar + 2Br² + 2A²λ}`. -/
theorem integral_gauss_mul_expEnvelope_le {c₀ K A B lam r : ℝ} (hc₀ : 0 ≤ c₀)
    (hB : 0 ≤ B) (hlam : 0 < lam) (hBlam : 16 * B * lam ≤ 1) :
    Integrable (fun w : ℝ => Real.exp (-(w ^ 2 / 2)) * sliceExpEnvelope c₀ K A B (Real.sqrt lam * |w| + r))
      ∧ ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * sliceExpEnvelope c₀ K A B (Real.sqrt lam * |w| + r)
        ≤ Real.sqrt (4 * Real.pi) * (c₀ * Real.exp (K + A * r + 2 * B * r ^ 2 + 2 * A ^ 2 * lam)) := by
  set C := c₀ * Real.exp (K + A * r + 2 * B * r ^ 2 + 2 * A ^ 2 * lam) with hC
  have hpt : ∀ w : ℝ, Real.exp (-(w ^ 2 / 2)) * sliceExpEnvelope c₀ K A B (Real.sqrt lam * |w| + r)
      ≤ C * Real.exp (-(1 / 4) * w ^ 2) := by
    intro w
    unfold sliceExpEnvelope
    rw [hC, mul_left_comm, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc₀
    have hs2 : (Real.sqrt lam * |w|) ^ 2 = lam * w ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hlam.le, sq_abs]
    have h1 : B * (Real.sqrt lam * |w| + r) ^ 2 ≤ 2 * B * (lam * w ^ 2) + 2 * B * r ^ 2 := by
      have := mul_le_mul_of_nonneg_left
        (show (Real.sqrt lam * |w| + r) ^ 2 ≤ 2 * (Real.sqrt lam * |w|) ^ 2 + 2 * r ^ 2 by
          nlinarith [sq_nonneg (Real.sqrt lam * |w| - r)]) hB
      rw [hs2] at this; linarith
    have h2 : 2 * B * (lam * w ^ 2) ≤ w ^ 2 / 8 := by
      have := mul_le_mul_of_nonneg_right hBlam (sq_nonneg w); nlinarith
    have h3 : A * (Real.sqrt lam * |w|) ≤ w ^ 2 / 8 + 2 * A ^ 2 * lam := by
      have ha2 : (A * Real.sqrt lam) ^ 2 = A ^ 2 * lam := by rw [mul_pow, Real.sq_sqrt hlam.le]
      have e : A * (Real.sqrt lam * |w|) = (A * Real.sqrt lam) * |w| := by ring
      rw [e]
      nlinarith [sq_nonneg (|w| - 4 * (A * Real.sqrt lam)), sq_abs w]
    nlinarith
  have hcont : Continuous fun w : ℝ =>
      Real.exp (-(w ^ 2 / 2)) * sliceExpEnvelope c₀ K A B (Real.sqrt lam * |w| + r) := by
    unfold sliceExpEnvelope; fun_prop
  have hgi : Integrable fun w : ℝ => C * Real.exp (-(1 / 4) * w ^ 2) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  have hint : Integrable fun w : ℝ =>
      Real.exp (-(w ^ 2 / 2)) * sliceExpEnvelope c₀ K A B (Real.sqrt lam * |w| + r) :=
    hgi.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold sliceExpEnvelope; positivity)]
      exact hpt w)
  refine ⟨hint, ?_⟩
  calc ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * sliceExpEnvelope c₀ K A B (Real.sqrt lam * |w| + r)
      ≤ ∫ w : ℝ, C * Real.exp (-(1 / 4) * w ^ 2) := integral_mono hint hgi hpt
    _ = Real.sqrt (4 * Real.pi) * C := by
        rw [integral_const_mul, integral_gaussian, mul_comm]
        congr 2; ring

/-- **Cauchy bound for the heated coefficients.**  If `‖S(t, z)‖ ≤ E(‖z‖)` with `E` monotone, then
`√(2π) ‖T_N(λ, 0, t)‖ ≤ r^{−N} ∫ e^{−w²/2} E(√λ|w| + r) dw` for every `r > 0`. -/
theorem norm_xiSliceHeatTransfer_le_of_envelope {t lam : ℝ} (hlam : 0 ≤ lam) {E : ℝ → ℝ}
    (hEmono : ∀ ρ ρ', 0 ≤ ρ → ρ ≤ ρ' → E ρ ≤ E ρ') (hE : ∀ z, ‖xiSliceProduct t z‖ ≤ E ‖z‖)
    {r : ℝ} (hr : 0 < r)
    (hint : Integrable fun w : ℝ => Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + r)) (N : ℕ) :
    Real.sqrt (2 * Real.pi) * ‖xiSliceHeatTransfer lam 0 t N‖
      ≤ (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + r)) / r ^ N := by
  have hrep := xiSliceHeatTransfer_eq_integral_iteratedDeriv hlam t N
  have hsq : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hn : Real.sqrt (2 * Real.pi) * ‖xiSliceHeatTransfer lam 0 t N‖
      = ‖((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 t N‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsq]
  rw [hn, hrep]
  have hfac : ∀ n : ℕ, (0 : ℝ) < n.factorial := fun n => by exact_mod_cast Nat.factorial_pos n
  have hpt : ∀ w : ℝ, ‖((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
      * (iteratedDeriv N (xiSliceProduct t) ((Real.sqrt lam * w : ℝ) : ℂ) / N.factorial)‖
        ≤ Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + r) / r ^ N := by
    intro w
    have hx : ‖((Real.sqrt lam * w : ℝ) : ℂ)‖ = Real.sqrt lam * |w| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hc := norm_iteratedDeriv_xiSliceProduct_le t N (x := ((Real.sqrt lam * w : ℝ) : ℂ))
      (r := r) (M := E (Real.sqrt lam * |w| + r)) hr fun z hz => by
        refine le_trans (hE z) (hEmono _ _ (norm_nonneg _) ?_)
        have := norm_sub_norm_le z ((Real.sqrt lam * w : ℝ) : ℂ)
        rw [mem_sphere_iff_norm.mp hz, hx] at this
        linarith
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_natCast]
    calc Real.exp (-(w ^ 2 / 2)) * (‖iteratedDeriv N (xiSliceProduct t)
          ((Real.sqrt lam * w : ℝ) : ℂ)‖ / N.factorial)
        ≤ Real.exp (-(w ^ 2 / 2)) * ((N.factorial * E (Real.sqrt lam * |w| + r) / r ^ N)
            / N.factorial) := by gcongr
      _ = Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + r) / r ^ N := by
          field_simp
  calc ‖∫ w : ℝ, ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
        * (iteratedDeriv N (xiSliceProduct t) ((Real.sqrt lam * w : ℝ) : ℂ) / N.factorial)‖
      ≤ ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + r) / r ^ N :=
        norm_integral_le_of_norm_le (hint.div_const _) (Eventually.of_forall hpt)
    _ = (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * E (Real.sqrt lam * |w| + r)) / r ^ N :=
        integral_div _ _

/-- **Lower bound for the zeroth heated coefficient.**  If `‖S(t, z)‖ ≤ c₀ e^{K + A‖z‖ + B‖z‖²}` with
`c₀ = S(t, 0) > 0`, then `√(2π) Re T_0(λ, 0, t) ≥ e^{−1/2} c₀ min(a, 1)` with
`a = e^{−(K+6)/2}/(4(A + √B + 1)√λ)`. -/
theorem re_xiSliceHeatTransfer_zero_ge {t lam K A B : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hc₀ : 0 < (xiSliceCoeff t 0).re)
    (hE : ∀ z, ‖xiSliceProduct t z‖ ≤ sliceExpEnvelope (xiSliceCoeff t 0).re K A B ‖z‖) :
    Real.exp (-(1 / 2)) * (xiSliceCoeff t 0).re
        * min (Real.exp (-((K + 6) / 2)) / (4 * (A + Real.sqrt B + 1) * Real.sqrt lam)) 1
      ≤ Real.sqrt (2 * Real.pi) * (xiSliceHeatTransfer lam 0 t 0).re := by
  set c₀ := (xiSliceCoeff t 0).re with hc₀def
  set r := 1 / (A + Real.sqrt B + 1) with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hAr : A * r ≤ 1 := by
    rw [hrdef, mul_one_div, div_le_one (by positivity)]; linarith [Real.sqrt_nonneg B]
  have hBr : B * r ^ 2 ≤ 1 := by
    have h1 : Real.sqrt B * r ≤ 1 := by
      rw [hrdef, mul_one_div, div_le_one (by positivity)]; linarith
    have h2 : (Real.sqrt B * r) ^ 2 ≤ 1 := by nlinarith [mul_nonneg (Real.sqrt_nonneg B) hr0.le]
    rw [mul_pow, Real.sq_sqrt hB] at h2; exact h2
  set ρ := r * Real.exp (-((K + 6) / 2)) / 4 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hρr : ρ ≤ r := by
    rw [hρdef]
    have : Real.exp (-((K + 6) / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  -- the slice is at least `c₀/2` on `|x| ≤ ρ`
  have hEmono : ∀ x y, 0 ≤ x → x ≤ y → sliceExpEnvelope c₀ K A B x ≤ sliceExpEnvelope c₀ K A B y :=
    fun x y hx hxy => expEnvelope_mono hc₀.le hA hB hx hxy
  have hS0eq : xiSliceProduct t 0 = ((c₀ : ℝ) : ℂ) := by
    have h1 : xiSliceCoeff t 0 = xiSliceProduct t 0 := by simp [xiSliceCoeff]
    rw [← h1]
    exact Complex.ext (by simp [hc₀def]) (by simp [xiSliceCoeff_im_eq_zero])
  have hlow : ∀ x : ℝ, |x| ≤ ρ → c₀ / 2 ≤ xiSliceReal t x := by
    intro x hx
    have h := norm_xiSliceProduct_sub_le_of_deriv_eq_zero hEmono hE
      (iteratedDeriv_one_xiSliceProduct_zero t) hr0 ((x : ℝ) : ℂ)
    rw [zero_add, hS0eq, norm_zero, zero_add, Complex.norm_real, Real.norm_eq_abs,
      xiSliceProduct_ofReal_eq_xiSliceReal, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    have hEb : sliceExpEnvelope c₀ K A B (r + |x|) ≤ c₀ * Real.exp (K + 6) := by
      have h1 := hEmono (r + |x|) (2 * r) (by positivity) (by linarith)
      refine le_trans h1 ?_
      unfold sliceExpEnvelope
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc₀.le
      nlinarith
    have hq : (|x| / r) ^ 2 ≤ Real.exp (-(K + 6)) / 16 := by
      have h1 : |x| / r ≤ Real.exp (-((K + 6) / 2)) / 4 := by
        rw [div_le_iff₀ hr0]; rw [hρdef] at hx; linarith
      have h2 : (Real.exp (-((K + 6) / 2)) / 4) ^ 2 = Real.exp (-(K + 6)) / 16 := by
        have h3 : (Real.exp (-((K + 6) / 2))) ^ 2 = Real.exp (-(K + 6)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [div_pow, h3]; norm_num
      calc (|x| / r) ^ 2 ≤ (Real.exp (-((K + 6) / 2)) / 4) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h1 2
        _ = _ := h2
    have hprod : 8 * (|x| / r) ^ 2 * sliceExpEnvelope c₀ K A B (r + |x|) ≤ c₀ / 2 := by
      have h1 : Real.exp (-(K + 6)) * Real.exp (K + 6) = 1 := by
        rw [← Real.exp_add]; simp
      calc 8 * (|x| / r) ^ 2 * sliceExpEnvelope c₀ K A B (r + |x|)
          ≤ 8 * (Real.exp (-(K + 6)) / 16) * (c₀ * Real.exp (K + 6)) := by
            gcongr
            unfold sliceExpEnvelope; positivity
        _ = c₀ / 2 := by rw [show 8 * (Real.exp (-(K + 6)) / 16) * (c₀ * Real.exp (K + 6))
              = c₀ / 2 * (Real.exp (-(K + 6)) * Real.exp (K + 6)) by ring, h1, mul_one]
    have := le_trans h hprod
    rw [abs_le] at this
    linarith [this.1]
  -- the Gaussian average
  have hrep := xiSliceHeatTransfer_eq_integral_iteratedDeriv hlam.le t 0
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hrep
  have hreal : (fun w : ℝ => ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
      * xiSliceProduct t ((Real.sqrt lam * w : ℝ) : ℂ))
      = fun w => ((Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w) : ℝ) : ℂ) := by
    funext w; rw [xiSliceProduct_ofReal_eq_xiSliceReal]; push_cast; ring
  rw [hreal, integral_complex_ofReal] at hrep
  have hT0 : Real.sqrt (2 * Real.pi) * (xiSliceHeatTransfer lam 0 t 0).re
      = ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w) := by
    have := congrArg Complex.re hrep
    rw [Complex.re_ofReal_mul, Complex.ofReal_re] at this
    exact this
  rw [hT0]
  have hintc := integrable_gauss_mul_iteratedDeriv_xiSliceProduct hlam.le t 0
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hintc
  rw [hreal] at hintc
  have hint : Integrable fun w : ℝ => Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w) := by
    refine hintc.re.congr (Eventually.of_forall fun w => ?_)
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
  set a := min (Real.exp (-((K + 6) / 2)) / (4 * (A + Real.sqrt B + 1) * Real.sqrt lam)) 1 with ha
  have ha0 : 0 ≤ a := le_min (by positivity) zero_le_one
  have ha1 : a ≤ 1 := min_le_right _ _
  have haρ : Real.sqrt lam * a ≤ ρ := by
    have h1 : a ≤ Real.exp (-((K + 6) / 2)) / (4 * (A + Real.sqrt B + 1) * Real.sqrt lam) :=
      min_le_left _ _
    have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    rw [le_div_iff₀ (by positivity)] at h1
    rw [hρdef, hrdef]
    rw [show 1 / (A + Real.sqrt B + 1) * Real.exp (-((K + 6) / 2)) / 4
      = Real.exp (-((K + 6) / 2)) / (4 * (A + Real.sqrt B + 1)) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hpt : ∀ w : ℝ, (Set.Icc (-a) a).indicator (fun _ => Real.exp (-(1 / 2)) * (c₀ / 2)) w
      ≤ Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w) := by
    intro w
    by_cases hw : w ∈ Set.Icc (-a) a
    · rw [Set.indicator_of_mem hw]
      have hwa : |w| ≤ a := abs_le.mpr ⟨hw.1, hw.2⟩
      have hw1 : w ^ 2 ≤ 1 := by
        have := abs_le.mp (le_trans hwa ha1); nlinarith
      have hx : |Real.sqrt lam * w| ≤ ρ := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact le_trans (mul_le_mul_of_nonneg_left hwa (Real.sqrt_nonneg _)) haρ
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hlow _ hx) (by positivity)
        (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem hw]
      exact mul_nonneg (Real.exp_pos _).le (xiSliceReal_nonneg t _)
  have hind : Integrable ((Set.Icc (-a) a).indicator (fun _ : ℝ => Real.exp (-(1 / 2)) * (c₀ / 2))) :=
    (integrableOn_const (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
  have hmono := integral_mono hind hint hpt
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
    smul_eq_mul] at hmono
  calc Real.exp (-(1 / 2)) * c₀ * a ≤ (a - -a) * (Real.exp (-(1 / 2)) * (c₀ / 2)) := by
        nlinarith [Real.exp_pos (-(1 / 2))]
    _ ≤ _ := hmono

theorem sqrt_two_pi_mul_sqrt_two_mul_exp_half_le_six :
    Real.sqrt (2 * Real.pi) * Real.sqrt 2 * Real.exp (1 / 2) ≤ 6 := by
  have hπ := Real.pi_lt_d2
  have he := Real.exp_one_lt_d9
  have h1 : Real.sqrt (2 * Real.pi) * Real.sqrt 2 = Real.sqrt (4 * Real.pi) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  have h2 : Real.exp (1 / 2) = Real.sqrt (Real.exp 1) := by
    rw [← Real.exp_half]
  rw [h1, h2, ← Real.sqrt_mul (by positivity)]
  rw [show (6 : ℝ) = Real.sqrt 36 by rw [show (36 : ℝ) = 6 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]]
  have h3 : 4 * Real.pi * Real.exp 1 ≤ 4 * 3.15 * 2.7182818286 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hπ.le (by norm_num)) he.le (Real.exp_pos 1).le
      (by norm_num)
  have h4 : (4 : ℝ) * 3.15 * 2.7182818286 ≤ 36 := by norm_num
  exact Real.sqrt_le_sqrt (le_trans h3 h4)

/-- The final arithmetic of the Hermite-window detection. -/
theorem two_pow_le_of_hermite_key {e c m E Q : ℝ} {n : ℕ} (hm : 0 < m) (he : 0 < e)
    (hc : c * e ≤ 6) (hkey : e⁻¹ * m ≤ c * E * (1 / 2) ^ n) (hmax : 1 / m ≤ Q) (hE0 : 0 ≤ E) :
    (2 : ℝ) ^ n ≤ 6 * E * Q := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h1 : m ≤ c * e * E * (1 / 2) ^ n := by
    have := mul_le_mul_of_nonneg_left hkey he.le
    rw [← mul_assoc, mul_inv_cancel₀ he.ne', one_mul] at this
    linarith [show e * (c * E * (1 / 2) ^ n) = c * e * E * (1 / 2) ^ n by ring]
  have h2 : m * 2 ^ n ≤ 6 * E := by
    have h3 : c * e * E * (1 / 2) ^ n * 2 ^ n = c * e * E := by
      rw [mul_assoc, ← mul_pow]; norm_num
    have h4 := mul_le_mul_of_nonneg_right h1 h2n.le
    rw [h3] at h4
    exact le_trans h4 (mul_le_mul_of_nonneg_right hc hE0)
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hmax
  calc (2 : ℝ) ^ n = (1 / m) * (m * 2 ^ n) := by field_simp
    _ ≤ (1 / m) * (6 * E) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ Q * (6 * E) := mul_le_mul_of_nonneg_right hmax (by positivity)
    _ = 6 * E * Q := by ring

/-- **One term beyond the window.**  Under the envelope, with `E = e^{K + 50A²λ + 4Aδ + 64Bδ²}`,
`|p_N Re T_N(λ, 0, t)| ≤ √2 c₀ E 2^{−N}`. -/
theorem abs_hermiteWeight_mul_re_le {t δ lam K A B : ℝ} (hlam : 0 < lam) (hδ : 0 < δ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc₀ : 0 < (xiSliceCoeff t 0).re)
    (hE : ∀ z, ‖xiSliceProduct t z‖ ≤ sliceExpEnvelope (xiSliceCoeff t 0).re K A B ‖z‖)
    (hBlam : 768 * B * lam ≤ 1) (N : ℕ) :
    |sliceHermiteWeight lam δ N * (xiSliceHeatTransfer lam 0 t N).re|
      ≤ Real.sqrt 2 * (xiSliceCoeff t 0).re
        * Real.exp (K + 50 * A ^ 2 * lam + 4 * A * δ + 64 * B * δ ^ 2) * (1 / 2) ^ N := by
  set c₀ := (xiSliceCoeff t 0).re with hc₀def
  set E := Real.exp (K + 50 * A ^ 2 * lam + 4 * A * δ + 64 * B * δ ^ 2) with hEdef
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have he23 : Real.exp (2 / 3) ≤ 2 :=
    le_trans (Real.exp_le_exp.mpr hlog2) (le_of_eq (Real.exp_log (by norm_num)))
  set rN := 4 * (δ + 2 * Real.sqrt (lam * N)) with hrN
  have hrN0 : 0 < rN := by rw [hrN]; positivity
  obtain ⟨hint, hI⟩ := integral_gauss_mul_expEnvelope_le (K := K) (A := A) (r := rN) hc₀.le hB
    hlam (by linarith)
  have hT := norm_xiSliceHeatTransfer_le_of_envelope hlam.le
    (fun x y hx hxy => expEnvelope_mono hc₀.le hA hB hx hxy) hE hrN0 hint N
  have hp := abs_hermiteWeight_le hlam δ N
  rw [abs_of_pos hδ] at hp
  have hsq2 : Real.sqrt (4 * Real.pi) = Real.sqrt 2 * Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hs2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hTn : ‖xiSliceHeatTransfer lam 0 t N‖
      ≤ Real.sqrt 2 * (c₀ * Real.exp (K + A * rN + 2 * B * rN ^ 2 + 2 * A ^ 2 * lam)) / rN ^ N := by
    have h1 := le_trans hT (div_le_div_of_nonneg_right hI (by positivity))
    rw [hsq2] at h1
    have h2 : Real.sqrt (2 * Real.pi) * ‖xiSliceHeatTransfer lam 0 t N‖
        ≤ Real.sqrt (2 * Real.pi) * (Real.sqrt 2 * (c₀ * Real.exp (K + A * rN
          + 2 * B * rN ^ 2 + 2 * A ^ 2 * lam)) / rN ^ N) := by
      calc _ ≤ _ := h1
        _ = _ := by ring
    exact le_of_mul_le_mul_left h2 hs2π
  -- the exponent
  have hexp : A * rN + 2 * B * rN ^ 2 + 2 * A ^ 2 * lam
      ≤ 4 * A * δ + 64 * B * δ ^ 2 + 50 * A ^ 2 * lam + 2 / 3 * N := by
    have hsl : Real.sqrt (lam * N) ^ 2 = lam * N := Real.sq_sqrt (by positivity)
    have h1 : 8 * A * Real.sqrt (lam * N) ≤ N / 3 + 48 * A ^ 2 * lam := by
      have h0 : 0 ≤ 3 * lam * (N / 3 + 48 * A ^ 2 * lam - 8 * A * Real.sqrt (lam * N)) := by
        nlinarith [sq_nonneg (Real.sqrt (lam * N) - 12 * A * lam), hsl]
      have := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 3 * lam)).mp h0
      linarith
    have hrsq : rN ^ 2 ≤ 32 * δ ^ 2 + 128 * (lam * N) := by
      rw [hrN]; nlinarith [sq_nonneg (δ - 2 * Real.sqrt (lam * N)), hsl]
    have h2 : 2 * B * rN ^ 2 ≤ 64 * B * δ ^ 2 + 256 * B * (lam * N) := by
      have := mul_le_mul_of_nonneg_left hrsq (by positivity : (0 : ℝ) ≤ 2 * B)
      linarith
    have h3 : 256 * B * (lam * N) ≤ N / 3 := by
      have := mul_le_mul_of_nonneg_right hBlam (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      linarith
    have hArN : A * rN = 4 * A * δ + 8 * A * Real.sqrt (lam * N) := by rw [hrN]; ring
    linarith only [hArN, h1, h2, h3]
  have hpN : |sliceHermiteWeight lam δ N| ≤ (rN / 4) ^ N := by
    have e : rN / 4 = δ + 2 * Real.sqrt (lam * N) := by rw [hrN]; ring
    rw [e]; exact hp
  obtain ⟨X, hX⟩ : ∃ X, X = Real.exp (K + A * rN + 2 * B * rN ^ 2 + 2 * A ^ 2 * lam) := ⟨_, rfl⟩
  rw [← hX] at hTn
  have hXle : X ≤ E * Real.exp (2 / 3) ^ N := by
    rw [hX, hEdef, ← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hrNN : 0 < rN ^ N := by positivity
  calc |sliceHermiteWeight lam δ N * (xiSliceHeatTransfer lam 0 t N).re|
        = |sliceHermiteWeight lam δ N| * |(xiSliceHeatTransfer lam 0 t N).re| := abs_mul _ _
    _ ≤ (rN / 4) ^ N * ‖xiSliceHeatTransfer lam 0 t N‖ :=
        mul_le_mul hpN (Complex.abs_re_le_norm _) (abs_nonneg _) (by positivity)
    _ ≤ (rN / 4) ^ N * (Real.sqrt 2 * (c₀ * X) / rN ^ N) := by gcongr
    _ = Real.sqrt 2 * c₀ * X * (1 / 4) ^ N := by
        rw [div_pow, one_div_pow]; field_simp
    _ ≤ Real.sqrt 2 * c₀ * (E * Real.exp (2 / 3) ^ N) * (1 / 4) ^ N := by gcongr
    _ = Real.sqrt 2 * c₀ * E * (Real.exp (2 / 3) / 4) ^ N := by
        rw [div_pow, div_pow, one_pow]; ring
    _ ≤ Real.sqrt 2 * c₀ * E * (1 / 2) ^ N := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ N) (by positivity)
        linarith [he23]

/-- **Hermite-window detection.**  Let `ρ` be an off-line zero, `γ = Im ρ`, `δ = |Re ρ − ½|`,
`Ξ(γ) ≠ 0`, `c₀ = S(γ, 0)`, and let `‖S(γ, z)‖ ≤ c₀ e^{K + A‖z‖ + B‖z‖²}` for all `z`.  For `λ > 0` with
`768 B λ ≤ 1` and `n₀ = ⌊δ²/(4λ)⌋`, if

  `6 e^{K + 50A²λ + 4Aδ + 64Bδ²} · max(1, 4(A + √B + 1)√λ e^{(K+6)/2}) < 2^{n₀}`,

then some heated coefficient `T_N(λ, 0, γ)` with `N ≤ n₀` has negative real part. -/
theorem exists_re_xiSliceHeatTransfer_neg_of_hermiteWindow {ρ : ℂ} (hρ : xi ρ = 0)
    (hne : ρ.re ≠ 1 / 2) (hΞ : XiC ρ.im ≠ 0) {K A B : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : ∀ z, ‖xiSliceProduct ρ.im z‖ ≤ sliceExpEnvelope (xiSliceCoeff ρ.im 0).re K A B ‖z‖)
    {lam : ℝ} (hlam : 0 < lam) (hBlam : 768 * B * lam ≤ 1)
    (hcond : 6 * Real.exp (K + 50 * A ^ 2 * lam + 4 * A * |ρ.re - 1 / 2|
        + 64 * B * |ρ.re - 1 / 2| ^ 2)
        * max 1 (4 * (A + Real.sqrt B + 1) * Real.sqrt lam * Real.exp ((K + 6) / 2))
      < 2 ^ ⌊|ρ.re - 1 / 2| ^ 2 / (4 * lam)⌋₊) :
    ∃ N ≤ ⌊|ρ.re - 1 / 2| ^ 2 / (4 * lam)⌋₊, (xiSliceHeatTransfer lam 0 ρ.im N).re < 0 := by
  classical
  set t : ℝ := ρ.im with htdef
  set δ : ℝ := |ρ.re - 1 / 2| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  set c₀ := (xiSliceCoeff t 0).re with hc₀def
  have hc₀ : 0 < c₀ := by simpa using xiSliceCoeff_zero_re_pos hΞ
  set n₀ := ⌊δ ^ 2 / (4 * lam)⌋₊ with hn₀
  set E := Real.exp (K + 50 * A ^ 2 * lam + 4 * A * δ + 64 * B * δ ^ 2) with hEdef
  by_contra hcon
  push Not at hcon
  -- the Hermite identity at the offset, where the slice vanishes
  have hH := hasSum_hermiteWeight_mul_xiSliceHeatTransfer hlam t δ
  rw [(xiSliceProduct_offset_eq_zero hρ).1] at hH
  have hHre := Complex.hasSum_re hH
  simp only [Complex.re_ofReal_mul, Complex.zero_re] at hHre
  set a : ℕ → ℝ := fun N => sliceHermiteWeight lam δ N * (xiSliceHeatTransfer lam 0 t N).re with hadef
  -- window terms are nonnegative
  have hwin : ∀ N ≤ n₀, 0 ≤ a N := by
    intro N hN
    have hNr : (N : ℝ) ≤ δ ^ 2 / (4 * lam) :=
      le_trans (by exact_mod_cast hN) (Nat.floor_le (by positivity))
    have h4 : 4 * lam * N ≤ δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at hNr; linarith
    have hp := hermiteWeight_ge hlam hδ.le h4
    exact mul_nonneg (le_trans (by positivity) hp) (hcon N hN)
  have hp0 : sliceHermiteWeight lam δ 0 = 1 := by simp [sliceHermiteWeight]
  have hhead : (xiSliceHeatTransfer lam 0 t 0).re ≤ ∑ N ∈ Finset.range (n₀ + 1), a N := by
    have h := Finset.single_le_sum (f := a) (fun N hN => hwin N
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hN))) (Finset.mem_range.mpr (Nat.succ_pos n₀))
    simpa [hadef, hp0] using h
  -- the tail beyond the window
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have he23 : Real.exp (2 / 3) ≤ 2 :=
    le_trans (Real.exp_le_exp.mpr hlog2) (le_of_eq (Real.exp_log (by norm_num)))
  have hterm : ∀ N : ℕ, |a N| ≤ Real.sqrt 2 * c₀ * E * (1 / 2) ^ N := fun N =>
    abs_hermiteWeight_mul_re_le hlam hδ hA hB hc₀ hE hBlam N
  have hsplit := (hasSum_nat_add_iff' (n₀ + 1)).mpr hHre
  have hgeo : HasSum (fun k : ℕ => Real.sqrt 2 * c₀ * E * (1 / 2) ^ (k + (n₀ + 1)))
      (Real.sqrt 2 * c₀ * E * (1 / 2) ^ n₀) := by
    have h := hasSum_geometric_two.mul_left (Real.sqrt 2 * c₀ * E * (1 / 2) ^ (n₀ + 1))
    have hv : Real.sqrt 2 * c₀ * E * (1 / 2) ^ (n₀ + 1) * 2 = Real.sqrt 2 * c₀ * E * (1 / 2) ^ n₀ := by
      rw [pow_succ]; ring
    rw [hv] at h
    exact h.congr_fun fun k => by rw [pow_add]; ring
  have htail := hsplit.norm_le_of_bounded hgeo fun k => by
    rw [Real.norm_eq_abs]; exact hterm (k + (n₀ + 1))
  rw [Real.norm_eq_abs, zero_sub, abs_neg] at htail
  have hT0le : (xiSliceHeatTransfer lam 0 t 0).re ≤ Real.sqrt 2 * c₀ * E * (1 / 2) ^ n₀ :=
    le_trans hhead (le_trans (le_abs_self _) htail)
  have hT0ge := re_xiSliceHeatTransfer_zero_ge (t := t) hlam hK hA hB hc₀ hE
  -- the contradiction
  set m := min (Real.exp (-((K + 6) / 2)) / (4 * (A + Real.sqrt B + 1) * Real.sqrt lam)) 1 with hm
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  have hs2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hkey : Real.exp (-(1 / 2)) * m ≤ Real.sqrt (2 * Real.pi) * Real.sqrt 2 * E * (1 / 2) ^ n₀ := by
    have h1 := le_trans hT0ge (mul_le_mul_of_nonneg_left hT0le hs2π.le)
    have h2 : Real.exp (-(1 / 2)) * c₀ * m = c₀ * (Real.exp (-(1 / 2)) * m) := by ring
    have h3 : Real.sqrt (2 * Real.pi) * (Real.sqrt 2 * c₀ * E * (1 / 2) ^ n₀)
        = c₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt 2 * E * (1 / 2) ^ n₀) := by ring
    rw [h2, h3] at h1
    exact le_of_mul_le_mul_left h1 hc₀
  have hconst := sqrt_two_pi_mul_sqrt_two_mul_exp_half_le_six
  have hmax : 1 / m ≤ max 1 (4 * (A + Real.sqrt B + 1) * Real.sqrt lam * Real.exp ((K + 6) / 2)) := by
    rcases le_total (Real.exp (-((K + 6) / 2)) / (4 * (A + Real.sqrt B + 1) * Real.sqrt lam)) 1
      with h | h
    · rw [hm, min_eq_left h, one_div_div]
      refine le_trans (le_of_eq ?_) (le_max_right _ _)
      rw [Real.exp_neg]; field_simp
    · rw [hm, min_eq_right h, div_one]; exact le_max_left _ _
  have hfinal := two_pow_le_of_hermite_key (n := n₀) hm0 (Real.exp_pos (1 / 2)) hconst
    (by rw [← Real.exp_neg]; exact hkey) hmax (Real.exp_pos _).le
  linarith

/-- The product envelope is an exponential envelope with `K = 0`, `A = 2m/δ`, `B = S`. -/
theorem sliceEnvelope_le_expEnvelope {c₀ δ S : ℝ} (hc₀ : 0 ≤ c₀) (hδ : 0 < δ) (m : ℕ) {r : ℝ}
    (hr : 0 ≤ r) : sliceEnvelope c₀ δ S m r ≤ sliceExpEnvelope c₀ 0 (2 * m / δ) S r := by
  unfold sliceEnvelope sliceExpEnvelope
  have hu : 0 ≤ r / δ := div_nonneg hr hδ.le
  have h1 : 1 + r ^ 2 / δ ^ 2 ≤ Real.exp (2 * (r / δ)) := by
    have h := Real.add_one_le_exp (r / δ)
    have h2 : Real.exp (2 * (r / δ)) = Real.exp (r / δ) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [h2, show r ^ 2 / δ ^ 2 = (r / δ) ^ 2 by rw [div_pow]]
    nlinarith
  have h3 : (1 + r ^ 2 / δ ^ 2) ^ m ≤ Real.exp (2 * m / δ * r) := by
    calc (1 + r ^ 2 / δ ^ 2) ^ m ≤ Real.exp (2 * (r / δ)) ^ m :=
          pow_le_pow_left₀ (by positivity) h1 m
      _ = Real.exp (2 * m / δ * r) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  calc c₀ * ((1 + r ^ 2 / δ ^ 2) ^ m * Real.exp (r ^ 2 * S))
      ≤ c₀ * (Real.exp (2 * m / δ * r) * Real.exp (r ^ 2 * S)) := by gcongr
    _ = c₀ * Real.exp (0 + 2 * m / δ * r + S * r ^ 2) := by
        rw [← Real.exp_add]; ring_nf

/-- **Hermite-window detection with the product envelope.**  For an off-line zero with at most `m`
copies at `γ ± iδ` and other copies of inverse-square mass `≤ S`: if `768 S λ ≤ 1` and
`6 e^{200m²λ/δ² + 8m + 64Sδ²} · max(1, 4(2m/δ + √S + 1)√λ e³) < 2^{⌊δ²/(4λ)⌋}`, some heated coefficient
of order `≤ δ²/(4λ)` is negative.  The condition holds for `λ ≍ min(δ²/(m + Sδ² + log(2 + S)), 1/S)`. -/
theorem exists_re_xiSliceHeatTransfer_neg_of_hermiteWindow_mass {ρ : ℂ} (hρ : xi ρ = 0)
    (hne : ρ.re ≠ 1 / 2) (hΞ : XiC ρ.im ≠ 0) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I)) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S)
    {lam : ℝ} (hlam : 0 < lam) (hSlam : 768 * S * lam ≤ 1)
    (hcond : 6 * Real.exp (0 + 50 * (2 * m / |ρ.re - 1 / 2|) ^ 2 * lam
        + 4 * (2 * m / |ρ.re - 1 / 2|) * |ρ.re - 1 / 2| + 64 * S * |ρ.re - 1 / 2| ^ 2)
        * max 1 (4 * (2 * m / |ρ.re - 1 / 2| + Real.sqrt S + 1) * Real.sqrt lam
          * Real.exp ((0 + 6) / 2))
      < 2 ^ ⌊|ρ.re - 1 / 2| ^ 2 / (4 * lam)⌋₊) :
    ∃ N ≤ ⌊|ρ.re - 1 / 2| ^ 2 / (4 * lam)⌋₊, (xiSliceHeatTransfer lam 0 ρ.im N).re < 0 := by
  have hδ : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hS0 : 0 ≤ S := by simpa using hS ∅ (by simp)
  have hc₀ : 0 < (xiSliceCoeff ρ.im 0).re := by simpa using xiSliceCoeff_zero_re_pos hΞ
  refine exists_re_xiSliceHeatTransfer_neg_of_hermiteWindow hρ hne hΞ le_rfl (by positivity) hS0
    (fun z => le_trans (norm_xiSliceProduct_le_envelope hne hΞ hown hS z)
      (sliceEnvelope_le_expEnvelope hc₀.le hδ m (norm_nonneg z))) hlam hSlam hcond

end

end RHTower.DeBruijn
