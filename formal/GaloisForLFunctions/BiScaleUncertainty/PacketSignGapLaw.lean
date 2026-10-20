import GaloisForLFunctions.BiScaleUncertainty.SimpleZeroPacketCriterion

/-!
# Bounded sign gaps of compact packets

Packet persistence (`PacketPersistenceLaw`) says a nonzero compact packet exceeds `±c` at arbitrarily
large shifts. When the packet is bounded above this holds in **every window of a fixed length**.

**Sign gap law** (`packet_sign_changes_in_every_window`). For a nonzero real compact `C²` source
whose packet is eventually bounded above there are `c, ℓ > 0` and `T₀` such that every window
`[x, x + ℓ]`, `x ≥ T₀`, contains a shift with `P_f > c` and one with `P_f < −c`. Under RH this holds
for every nonzero compact source (`packet_sign_changes_in_every_window_of_riemannHypothesis`): the
smoothed prime–polar discrepancy changes sign in every multiplicative interval `[X, e^ℓ X]`.

**Mechanism.** Beyond the support `P_f = B − G` with `B → 0` and `G` the critical almost periodic
series. For an absolutely convergent series the window means are uniform in the position of the
window: over `[x, x + ℓ]` the mean of `G` is at most `Σ|a_i| |χ_ℓ(γ_i)|` and the mean of `|G|²`
differs from `Σ|a_i|²` by at most `Σ_{i≠j} |a_i||a_j| |χ_ℓ(γ_i − γ_j)|`, with
`χ_ℓ(Δ) = ℓ⁻¹∫_0^ℓ e^{iΔs} ds` (`norm_window_mean_apSeries_le`, `window_meanSq_apSeries_ge`); both
bounds tend to `0` as `ℓ → ∞` because the frequencies are nonzero and distinct. If `−M ≤ P_f ≤ c` on
a window then `P_f² ≤ (c − M)P_f + Mc` there (`window_energy_le`), which averages to
`E(f) ≤ Mc` up to small errors: impossible for `c = E(f)/(4(M + 1))`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## Window means of absolutely convergent almost periodic series -/

section Window

variable {ι : Type*} [Countable ι]

/-- The series `Σ_i a_i e^{iγ_i τ}`. -/
def apSeries (a : ι → ℂ) (γ : ι → ℝ) (τ : ℝ) : ℂ := ∑' i, a i * cexp ((γ i * τ : ℝ) * I)

omit [Countable ι] in
theorem apSeries_add (a : ι → ℂ) (γ : ι → ℝ) (x s : ℝ) :
    apSeries a γ (x + s) = apSeries (fun i => a i * cexp ((γ i * x : ℝ) * I)) γ s := by
  unfold apSeries
  refine tsum_congr fun i => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

omit [Countable ι] in
theorem norm_shift_coeff (a : ι → ℂ) (γ : ι → ℝ) (x : ℝ) (i : ι) :
    ‖a i * cexp ((γ i * x : ℝ) * I)‖ = ‖a i‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem mean_apSeries_eq {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) (γ : ι → ℝ) (L : ℝ) :
    (∫ τ in (0 : ℝ)..L, apSeries a γ τ) / L = ∑' i, a i * characterMean (γ i) L := by
  have hn : ∀ i (τ : ℝ), ‖a i * cexp ((γ i * τ : ℝ) * I)‖ = ‖a i‖ := fun i τ =>
    norm_shift_coeff a γ τ i
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := L) (F := fun i τ => a i * cexp ((γ i * τ : ℝ) * I))
    (f := fun τ => ∑' i, a i * cexp ((γ i * τ : ℝ) * I))
    (fun (i : ι) (_ : ℝ) => ‖a i‖)
    (fun i => (Continuous.aestronglyMeasurable (by fun_prop)))
    (fun i => Eventually.of_forall fun τ _ => (hn i τ).le)
    (Eventually.of_forall fun τ _ => ha)
    intervalIntegrable_const
    (Eventually.of_forall fun τ _ =>
      (Summable.of_norm (ha.congr fun i => (hn i τ).symm)).hasSum)
  unfold apSeries
  rw [← hsum.tsum_eq, ← tsum_div_const]
  exact tsum_congr fun i => by rw [intervalIntegral.integral_const_mul, characterMean, mul_div_assoc]

theorem mean_normSq_apSeries_eq {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) (γ : ι → ℝ)
    (L : ℝ) :
    (((∫ τ in (0 : ℝ)..L, ‖apSeries a γ τ‖ ^ 2) / L : ℝ) : ℂ) =
      ∑' ij : ι × ι, a ij.1 * conj (a ij.2) * characterMean (γ ij.1 - γ ij.2) L := by
  set e : ι → ℝ → ℂ := fun i τ => a i * cexp ((γ i * τ : ℝ) * I)
  have hne : ∀ i τ, ‖e i τ‖ = ‖a i‖ := fun i τ => norm_shift_coeff a γ τ i
  have hes : ∀ τ, Summable fun i => ‖e i τ‖ := fun τ => by simpa [hne] using ha
  set p : ι × ι → ℝ → ℂ := fun ij τ =>
    a ij.1 * conj (a ij.2) * cexp (((γ ij.1 - γ ij.2) * τ : ℝ) * I)
  have hpn : ∀ ij τ, ‖p ij τ‖ = ‖a ij.1‖ * ‖a ij.2‖ := fun ij τ => by
    simp only [p]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_conj]
  have hps : Summable fun ij : ι × ι => ‖a ij.1‖ * ‖a ij.2‖ := by
    simpa [norm_mul] using Summable.mul_norm ha ha
  have hsq : ∀ τ : ℝ, ((‖apSeries a γ τ‖ ^ 2 : ℝ) : ℂ) = ∑' ij : ι × ι, p ij τ := by
    intro τ
    have hs1 : Summable fun i => ‖a i * cexp ((γ i * τ : ℝ) * I)‖ :=
      ha.congr fun i => (norm_shift_coeff a γ τ i).symm
    rw [Complex.ofReal_pow, ← Complex.mul_conj', apSeries, Complex.conj_tsum,
      tsum_mul_tsum_of_summable_norm hs1 (by simpa [Complex.norm_conj] using hs1)]
    refine tsum_congr fun ij => ?_
    simp only [p, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := L) (F := p) (f := fun τ => ∑' ij : ι × ι, p ij τ)
    (fun (ij : ι × ι) (_ : ℝ) => ‖a ij.1‖ * ‖a ij.2‖)
    (fun ij => (Continuous.aestronglyMeasurable (by simp only [p]; fun_prop)))
    (fun ij => Eventually.of_forall fun τ _ => (hpn ij τ).le)
    (Eventually.of_forall fun τ _ => hps)
    intervalIntegrable_const
    (Eventually.of_forall fun τ _ => (Summable.of_norm (by simpa [hpn] using hps)).hasSum)
  rw [Complex.ofReal_div, ← intervalIntegral.integral_ofReal]
  simp_rw [hsq]
  rw [← hsum.tsum_eq, ← tsum_div_const]
  refine tsum_congr fun ij => ?_
  simp only [p]
  rw [intervalIntegral.integral_const_mul, characterMean, mul_div_assoc]

open Classical in
/-- The off-diagonal remainder `Σ_{i≠j} |a_i||a_j||χ_L(γ_i − γ_j)|`. -/
def offDiagRemainder (a : ι → ℂ) (γ : ι → ℝ) (L : ℝ) : ℝ :=
  ∑' ij : ι × ι, if ij.1 = ij.2 then 0 else
    ‖a ij.1‖ * ‖a ij.2‖ * ‖characterMean (γ ij.1 - γ ij.2) L‖

/-- The mean remainder `Σ_i |a_i||χ_L(γ_i)|`. -/
def meanRemainder (a : ι → ℂ) (γ : ι → ℝ) (L : ℝ) : ℝ :=
  ∑' i, ‖a i‖ * ‖characterMean (γ i) L‖

theorem abs_mean_normSq_apSeries_sub_le {a : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    (γ : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    |(∫ τ in (0 : ℝ)..L, ‖apSeries a γ τ‖ ^ 2) / L - ∑' i, ‖a i‖ ^ 2| ≤
      offDiagRemainder a γ L := by
  classical
  have hps : Summable fun ij : ι × ι => ‖a ij.1‖ * ‖a ij.2‖ := by
    simpa [norm_mul] using Summable.mul_norm ha ha
  have hcm : ∀ Δ : ℝ, ‖characterMean Δ L‖ ≤ 1 := fun Δ => norm_characterMean_le Δ hL
  have h1 : Summable fun ij : ι × ι => a ij.1 * conj (a ij.2) *
      characterMean (γ ij.1 - γ ij.2) L :=
    Summable.of_norm_bounded hps fun ij => by
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_of_le_one_right (by positivity) (hcm _)
  have h2 : Summable fun ij : ι × ι => if ij.1 = ij.2 then a ij.1 * conj (a ij.2) else 0 :=
    Summable.of_norm_bounded hps fun ij => by
      split_ifs
      · rw [norm_mul, Complex.norm_conj]
      · rw [norm_zero]; positivity
  have hdiag : ((∑' i, ‖a i‖ ^ 2 : ℝ) : ℂ) =
      ∑' ij : ι × ι, if ij.1 = ij.2 then a ij.1 * conj (a ij.2) else 0 := by
    rw [h2.tsum_prod, Complex.ofReal_tsum]
    refine tsum_congr fun i => ?_
    rw [tsum_eq_single i fun j hj => if_neg (Ne.symm hj), if_pos rfl, Complex.mul_conj']
    push_cast
    ring
  have hdiff : ((((∫ τ in (0 : ℝ)..L, ‖apSeries a γ τ‖ ^ 2) / L - ∑' i, ‖a i‖ ^ 2) : ℝ) : ℂ) =
      ∑' ij : ι × ι, if ij.1 = ij.2 then 0 else
        a ij.1 * conj (a ij.2) * characterMean (γ ij.1 - γ ij.2) L := by
    rw [Complex.ofReal_sub, mean_normSq_apSeries_eq ha γ L, hdiag, ← h1.tsum_sub h2]
    refine tsum_congr fun ij => ?_
    split_ifs with h
    · rw [h, sub_self, characterMean_zero hL, mul_one, sub_self]
    · rw [sub_zero]
  have hs3 : Summable fun ij : ι × ι => (if ij.1 = ij.2 then 0 else
      ‖a ij.1‖ * ‖a ij.2‖ * ‖characterMean (γ ij.1 - γ ij.2) L‖) :=
    hps.of_nonneg_of_le (fun ij => by split_ifs <;> positivity) fun ij => by
      split_ifs
      · positivity
      · exact mul_le_of_le_one_right (by positivity) (hcm _)
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff, offDiagRemainder]
  refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum (fun ij => ?_) ?_ hs3)
  · refine hs3.of_nonneg_of_le (fun _ => norm_nonneg _) fun ij => ?_
    split_ifs
    · simp
    · rw [norm_mul, norm_mul, Complex.norm_conj]
  · split_ifs
    · simp
    · rw [norm_mul, norm_mul, Complex.norm_conj]
  · refine hs3.of_nonneg_of_le (fun _ => norm_nonneg _) fun ij => ?_
    split_ifs
    · simp
    · rw [norm_mul, norm_mul, Complex.norm_conj]

omit [Countable ι] in
theorem tendsto_offDiagRemainder {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) {γ : ι → ℝ}
    (hγ : Function.Injective γ) : Tendsto (offDiagRemainder a γ) atTop (𝓝 0) := by
  classical
  have hps : Summable fun ij : ι × ι => ‖a ij.1‖ * ‖a ij.2‖ := by
    simpa [norm_mul] using Summable.mul_norm ha ha
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (bound := fun ij : ι × ι => ‖a ij.1‖ * ‖a ij.2‖) hps
    (f := fun L ij => if ij.1 = ij.2 then 0 else
      ‖a ij.1‖ * ‖a ij.2‖ * ‖characterMean (γ ij.1 - γ ij.2) L‖) (g := fun _ => 0)
    (fun ij => by
      by_cases hij : ij.1 = ij.2
      · simp only [hij, if_true]
        exact tendsto_const_nhds
      · simp only [hij, if_false]
        have := ((tendsto_characterMean (sub_ne_zero.mpr fun h => hij (hγ h))).norm).const_mul
          (‖a ij.1‖ * ‖a ij.2‖)
        simpa using this)
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL ij
      split_ifs
      · simp only [norm_zero]; positivity
      · rw [Real.norm_of_nonneg (by positivity)]
        exact mul_le_of_le_one_right (by positivity) (norm_characterMean_le _ hL))
  rw [tsum_zero] at h
  exact h

omit [Countable ι] in
theorem tendsto_meanRemainder {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) {γ : ι → ℝ}
    (hγ : ∀ i, γ i ≠ 0) : Tendsto (meanRemainder a γ) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (bound := fun i => ‖a i‖) ha
    (f := fun L i => ‖a i‖ * ‖characterMean (γ i) L‖) (g := fun _ => 0)
    (fun i => by simpa using ((tendsto_characterMean (hγ i)).norm).const_mul ‖a i‖)
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL i
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_characterMean_le _ hL))
  rw [tsum_zero] at h
  exact h

omit [Countable ι] in
/-- Shifting a window replaces the coefficients by unimodular multiples. -/
theorem integral_window_apSeries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ι → ℂ) (γ : ι → ℝ) (F : ℂ → E) (x L : ℝ) :
    ∫ τ in x..x + L, F (apSeries a γ τ) =
      ∫ s in (0 : ℝ)..L, F (apSeries (fun i => a i * cexp ((γ i * x : ℝ) * I)) γ s) := by
  have h := intervalIntegral.integral_comp_add_left (fun τ => F (apSeries a γ τ)) x
    (a := 0) (b := L)
  rw [add_zero] at h
  rw [← h]
  exact intervalIntegral.integral_congr fun s _ => by simp only [apSeries_add]

/-- **Uniform window mean.** Over every window `[x, x + L]` the mean of the series is at most the
mean remainder. -/
theorem norm_window_mean_apSeries_le {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) (γ : ι → ℝ)
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ‖(∫ τ in x..x + L, apSeries a γ τ) / L‖ ≤ meanRemainder a γ L := by
  set a' := fun i => a i * cexp ((γ i * x : ℝ) * I)
  have ha' : Summable fun i => ‖a' i‖ := ha.congr fun i => (norm_shift_coeff a γ x i).symm
  have hw := integral_window_apSeries a γ (fun z => z) x L
  rw [hw, mean_apSeries_eq ha' γ L, meanRemainder]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun i => ?_))
  · exact (ha.mul_right 1).of_nonneg_of_le (fun _ => norm_nonneg _) fun i => by
      rw [norm_mul, norm_shift_coeff, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_characterMean_le _ hL)
  · rw [norm_mul, norm_shift_coeff]

/-- **Uniform window mean square.** Over every window `[x, x + L]` the mean square of the series is
at least `Σ|a_i|²` minus the off-diagonal remainder. -/
theorem window_meanSq_apSeries_ge {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) (γ : ι → ℝ)
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∑' i, ‖a i‖ ^ 2 - offDiagRemainder a γ L ≤
      (∫ τ in x..x + L, ‖apSeries a γ τ‖ ^ 2) / L := by
  set a' := fun i => a i * cexp ((γ i * x : ℝ) * I)
  have ha' : Summable fun i => ‖a' i‖ := ha.congr fun i => (norm_shift_coeff a γ x i).symm
  have hnorm : ∀ i, ‖a' i‖ = ‖a i‖ := norm_shift_coeff a γ x
  have hrem : offDiagRemainder a' γ L = offDiagRemainder a γ L := by
    simp only [offDiagRemainder, hnorm]
  have hsq : ∑' i, ‖a' i‖ ^ 2 = ∑' i, ‖a i‖ ^ 2 := by simp only [hnorm]
  have h := abs_mean_normSq_apSeries_sub_le ha' γ hL
  rw [hrem, hsq] at h
  have hw := integral_window_apSeries a γ (fun z => ‖z‖ ^ 2) x L
  rw [hw]
  linarith [(abs_le.mp h).1]

end Window

/-! ## The window energy inequality -/

/-- On a window where `q = Re(B − G)` stays in `[−M, c]` and `|B| ≤ η`, the window mean square of
`G` is at most `(M + c)(η + ρ₁) + Mc + η(2M + η)`, where `ρ₁` bounds the window mean of `G`. -/
theorem window_energy_le {q : ℝ → ℝ} {B G : ℝ → ℂ} (hG : Continuous G)
    {x ℓ c M η E ρ₁ ρ₂ : ℝ} (hℓ : 0 < ℓ) (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hqBG : ∀ τ ∈ Icc x (x + ℓ), (q τ : ℂ) = B τ - G τ)
    (hqc : ∀ τ ∈ Icc x (x + ℓ), q τ ≤ c) (hqM : ∀ τ ∈ Icc x (x + ℓ), |q τ| ≤ M)
    (hBη : ∀ τ ∈ Icc x (x + ℓ), ‖B τ‖ ≤ η)
    (h1 : ‖(∫ τ in x..x + ℓ, G τ) / ℓ‖ ≤ ρ₁)
    (h2 : E - ρ₂ ≤ (∫ τ in x..x + ℓ, ‖G τ‖ ^ 2) / ℓ) :
    E - ρ₂ - η * (2 * M + η) ≤ (M + c) * (η + ρ₁) + M * c := by
  have hx : x ∈ Icc x (x + ℓ) := ⟨le_rfl, by linarith⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hqM x hx)
  have hρ₁ : 0 ≤ ρ₁ := (norm_nonneg _).trans h1
  -- pointwise inequality on the window
  have hpt : ∀ τ ∈ Icc x (x + ℓ), ‖G τ‖ ^ 2 - η * (2 * M + η) ≤
      ((M + c) * η + M * c) - (c - M) * (G τ).re := by
    intro τ hτ
    have hq := hqBG τ hτ
    have hqc' := hqc τ hτ
    have hqM' := abs_le.mp (hqM τ hτ)
    have hB := hBη τ hτ
    have hGle : ‖G τ‖ ≤ |q τ| + η := by
      have : G τ = B τ - (q τ : ℂ) := by rw [hq]; ring
      rw [this]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith
    have hre : (G τ).re = (B τ).re - q τ := by
      have := congrArg Complex.re hq
      simp only [ofReal_re, sub_re] at this
      linarith
    have hBre : |(B τ).re| ≤ η := (Complex.abs_re_le_norm _).trans hB
    have hquad : q τ ^ 2 ≤ (c - M) * q τ + M * c := by nlinarith
    have hGsq : ‖G τ‖ ^ 2 ≤ q τ ^ 2 + η * (2 * M + η) := by
      have habs : |q τ| ≤ M := hqM τ hτ
      have h5 : ‖G τ‖ ^ 2 ≤ (|q τ| + η) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hGle 2
      have h6 : (|q τ| + η) ^ 2 ≤ q τ ^ 2 + η * (2 * M + η) := by
        rw [add_sq, sq_abs]
        nlinarith [mul_le_mul_of_nonneg_right habs hη]
      linarith
    rw [hre]
    have : (c - M) * ((B τ).re - q τ) ≤ (M + c) * η - (c - M) * q τ := by
      have h3 : (c - M) * (B τ).re ≤ (M + c) * η := by
        have := abs_mul (c - M) (B τ).re
        have h4 : |c - M| ≤ M + c := by rw [abs_le]; constructor <;> linarith
        nlinarith [le_abs_self ((c - M) * (B τ).re), abs_nonneg (B τ).re, abs_nonneg (c - M)]
      linarith
    linarith
  -- integrate and average
  have hGc : Continuous fun τ => ‖G τ‖ ^ 2 := by fun_prop
  have hGre : Continuous fun τ => (G τ).re := Complex.continuous_re.comp hG
  have hint : ∫ τ in x..x + ℓ, (‖G τ‖ ^ 2 - η * (2 * M + η)) ≤
      ∫ τ in x..x + ℓ, (((M + c) * η + M * c) - (c - M) * (G τ).re) :=
    intervalIntegral.integral_mono_on (by linarith)
      ((hGc.sub continuous_const).intervalIntegrable _ _)
      ((continuous_const.sub (continuous_const.mul hGre)).intervalIntegrable _ _) hpt
  have e1 : ∫ τ in x..x + ℓ, (‖G τ‖ ^ 2 - η * (2 * M + η)) =
      (∫ τ in x..x + ℓ, ‖G τ‖ ^ 2) - η * (2 * M + η) * ℓ := by
    rw [intervalIntegral.integral_sub (f := fun τ => ‖G τ‖ ^ 2) (g := fun _ => η * (2 * M + η))
      (hGc.intervalIntegrable _ _) intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul]
    ring
  have e2 : ∫ τ in x..x + ℓ, (((M + c) * η + M * c) - (c - M) * (G τ).re) =
      ((M + c) * η + M * c) * ℓ - (c - M) * ∫ τ in x..x + ℓ, (G τ).re := by
    rw [intervalIntegral.integral_sub (f := fun _ => (M + c) * η + M * c)
      (g := fun τ => (c - M) * (G τ).re) intervalIntegrable_const
      ((continuous_const.mul hGre).intervalIntegrable _ _), intervalIntegral.integral_const,
      smul_eq_mul, intervalIntegral.integral_const_mul]
    ring
  rw [e1, e2] at hint
  have hreint : ∫ τ in x..x + ℓ, (G τ).re = (∫ τ in x..x + ℓ, G τ).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm ((hG.intervalIntegrable (μ := volume) x (x + ℓ)))
    simpa using this
  have hmean : |(∫ τ in x..x + ℓ, (G τ).re) / ℓ| ≤ ρ₁ := by
    rw [hreint, abs_div, abs_of_pos hℓ]
    have := (Complex.abs_re_le_norm (∫ τ in x..x + ℓ, G τ))
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ] at h1
    calc |(∫ τ in x..x + ℓ, G τ).re| / ℓ ≤ ‖∫ τ in x..x + ℓ, G τ‖ / ℓ :=
          div_le_div_of_nonneg_right this hℓ.le
      _ ≤ ρ₁ := h1
  have hdiv : (∫ τ in x..x + ℓ, ‖G τ‖ ^ 2) / ℓ - η * (2 * M + η) ≤
      ((M + c) * η + M * c) - (c - M) * ((∫ τ in x..x + ℓ, (G τ).re) / ℓ) := by
    have k1 : (∫ τ in x..x + ℓ, ‖G τ‖ ^ 2) / ℓ - η * (2 * M + η) =
        ((∫ τ in x..x + ℓ, ‖G τ‖ ^ 2) - η * (2 * M + η) * ℓ) / ℓ := by
      field_simp
    have k2 : ((M + c) * η + M * c) - (c - M) * ((∫ τ in x..x + ℓ, (G τ).re) / ℓ) =
        (((M + c) * η + M * c) * ℓ - (c - M) * ∫ τ in x..x + ℓ, (G τ).re) / ℓ := by
      field_simp
    rw [k1, k2]
    exact div_le_div_of_nonneg_right hint hℓ.le
  have hcm : -(c - M) * ((∫ τ in x..x + ℓ, (G τ).re) / ℓ) ≤ (M + c) * ρ₁ := by
    have h4 : |c - M| ≤ M + c := by rw [abs_le]; constructor <;> linarith
    have := abs_mul (c - M) ((∫ τ in x..x + ℓ, (G τ).re) / ℓ)
    nlinarith [neg_abs_le ((c - M) * ((∫ τ in x..x + ℓ, (G τ).re) / ℓ)),
      abs_nonneg (c - M), abs_nonneg ((∫ τ in x..x + ℓ, (G τ).re) / ℓ)]
  nlinarith

/-! ## Bounded sign gaps -/

/-- **Sign gap law.** A nonzero real compact `C²` source whose packet is eventually bounded above
has `c, ℓ > 0` and `T₀` such that every window `[x, x + ℓ]`, `x ≥ T₀`, contains shifts with
`P_f > c` and with `P_f < −c`. -/
theorem packet_sign_changes_in_every_window {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hne : f ≠ 0)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K) :
    ∃ c ℓ T₀ : ℝ, 0 < c ∧ 0 < ℓ ∧ ∀ x : ℝ, T₀ ≤ x →
      (∃ τ ∈ Icc x (x + ℓ), c < stationaryPacket f τ) ∧
        ∃ τ ∈ Icc x (x + ℓ), stationaryPacket f τ < -c := by
  -- blindness, boundedness and the critical decomposition
  have hup_iff := packet_upper_iff hf hfc le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one] at hup_iff
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 :=
    fun ρ hρ => hup_iff.mp hup ρ (by linarith)
  obtain ⟨w, hw, hwf⟩ := hfc.exists_pos_le_norm
  have hwz : ∀ v : ℝ, w < |v| → f v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  obtain ⟨T₀, M, hM⟩ := (packet_bounded_iff_blind hf hfc).mpr hblind
  obtain ⟨B, hBc, hB0, hEF⟩ := exists_packet_eq_sub_criticalSeries hf hfc hw.le hwz hblind
  -- the critical series as an almost periodic series
  haveI : Countable 𝒵 := (countable_carrier _).to_subtype
  set a : criticalZeros → ℂ := fun ρ => packetCoeff f ρ
  set γ : criticalZeros → ℝ := fun ρ => ((ρ : 𝒵) : ℂ).im
  have ha : Summable fun ρ => ‖a ρ‖ := (summable_norm_packetCoeff hf hfc).subtype _
  have hG : criticalSeries f = apSeries a γ := rfl
  have hγinj : Function.Injective γ := fun ρ ρ' h => eq_of_im_eq_critical h
  have hE : ∑' ρ, ‖a ρ‖ ^ 2 = criticalPacketEnergy f := by
    refine tsum_congr fun ρ => ?_
    simp only [a, packetCoeff, norm_mul, Complex.norm_natCast, mul_pow,
      gammaOf_of_mem_critical ρ.2]
  set E := criticalPacketEnergy f
  have hEpos : 0 < E := criticalPacketEnergy_pos hf hfc hne
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM T₀ le_rfl)
  set c := E / (4 * (M + 1))
  have hc0 : 0 < c := by positivity
  have hMc : M * c ≤ E / 4 := by
    simp only [c]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- choose the window length and the decay threshold
  have hK : 0 < M + c := by linarith
  obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.mp ((tendsto_offDiagRemainder ha hγinj).eventually
    (gt_mem_nhds (show (0 : ℝ) < E / 8 by positivity)))
  obtain ⟨ℓ₂, hℓ₂⟩ := eventually_atTop.mp ((tendsto_meanRemainder ha
    (fun ρ => im_ne_zero_of_mem_critical ρ)).eventually
    (gt_mem_nhds (show (0 : ℝ) < E / (16 * (M + c)) by positivity)))
  set ℓ := max (max ℓ₁ ℓ₂) 1
  have hℓ : 0 < ℓ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : offDiagRemainder a γ ℓ < E / 8 := hℓ₁ ℓ ((le_max_left _ _).trans (le_max_left _ _))
  have hR₁ : meanRemainder a γ ℓ < E / (16 * (M + c)) :=
    hℓ₂ ℓ ((le_max_right _ _).trans (le_max_left _ _))
  set η := min 1 (E / (16 * (2 * M + 1 + (M + c))))
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηE : η * (2 * M + η) + (M + c) * η ≤ E / 16 := by
    have h1 : η ≤ E / (16 * (2 * M + 1 + (M + c))) := min_le_right _ _
    have h2 : η * (2 * M + η) + (M + c) * η ≤ η * (2 * M + 1 + (M + c)) := by nlinarith
    calc _ ≤ η * (2 * M + 1 + (M + c)) := h2
      _ ≤ E / (16 * (2 * M + 1 + (M + c))) * (2 * M + 1 + (M + c)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = E / 16 := by field_simp
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hB0.norm.eventually
    (ge_mem_nhds (show ‖(0 : ℂ)‖ < η by simpa using hη0)))
  refine ⟨c, ℓ, max (max T₀ T₁) (w + 1), hc0, hℓ, fun x hx => ?_⟩
  have hxT₀ : T₀ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxT₁ : T₁ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxw : w + 1 ≤ x := (le_max_right _ _).trans hx
  -- the window data
  have hmem : ∀ τ ∈ Icc x (x + ℓ), w < τ ∧ T₀ ≤ τ ∧ T₁ ≤ τ := fun τ hτ =>
    ⟨by linarith [hτ.1], hxT₀.trans hτ.1, hxT₁.trans hτ.1⟩
  set p : ℝ → ℝ := fun τ => (B τ - criticalSeries f τ).re
  have hpP : ∀ τ, w < τ → p τ = stationaryPacket f τ := fun τ hτ => by
    simp only [p]; rw [← hEF τ hτ, ofReal_re]
  have hpBG : ∀ τ, w < τ → (p τ : ℂ) = B τ - criticalSeries f τ := fun τ hτ => by
    rw [hpP τ hτ, hEF τ hτ]
  have hGc : Continuous (criticalSeries f) := continuous_criticalSeries hf hfc
  have h1 := norm_window_mean_apSeries_le ha γ hℓ x
  have h2 := window_meanSq_apSeries_ge ha γ hℓ x
  rw [hE] at h2
  rw [← hG] at h1 h2
  have hBη : ∀ τ ∈ Icc x (x + ℓ), ‖B τ‖ ≤ η := fun τ hτ => by
    exact hT₁ τ (hmem τ hτ).2.2
  -- the final contradiction, for either sign
  have key : ∀ (s : ℝ), |s| = 1 → ¬ ∀ τ ∈ Icc x (x + ℓ), s * stationaryPacket f τ ≤ c := by
    intro s hs hle
    have hss : s * s = 1 := by rw [← abs_mul_abs_self, hs, one_mul]
    have hqBG : ∀ τ ∈ Icc x (x + ℓ), ((s * p τ : ℝ) : ℂ) =
        (s : ℂ) * B τ - (s : ℂ) * criticalSeries f τ := fun τ hτ => by
      push_cast
      rw [hpBG τ (hmem τ hτ).1]
      ring
    have hqc : ∀ τ ∈ Icc x (x + ℓ), s * p τ ≤ c := fun τ hτ => by
      rw [hpP τ (hmem τ hτ).1]; exact hle τ hτ
    have hqM : ∀ τ ∈ Icc x (x + ℓ), |s * p τ| ≤ M := fun τ hτ => by
      rw [abs_mul, hs, one_mul, hpP τ (hmem τ hτ).1]; exact hM τ (hmem τ hτ).2.1
    have hBs : ∀ τ ∈ Icc x (x + ℓ), ‖(s : ℂ) * B τ‖ ≤ η := fun τ hτ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hs, one_mul]; exact hBη τ hτ
    have hsG : ∀ τ, ‖(s : ℂ) * criticalSeries f τ‖ = ‖criticalSeries f τ‖ := fun τ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hs, one_mul]
    have h1' : ‖(∫ τ in x..x + ℓ, (s : ℂ) * criticalSeries f τ) / ℓ‖ ≤
        meanRemainder a γ ℓ := by
      rw [intervalIntegral.integral_const_mul, mul_div_assoc, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, hs, one_mul]
      exact h1
    have h2' : E - offDiagRemainder a γ ℓ ≤
        (∫ τ in x..x + ℓ, ‖(s : ℂ) * criticalSeries f τ‖ ^ 2) / ℓ := by
      simp only [hsG]; exact h2
    have hW := window_energy_le (q := fun τ => s * p τ) (B := fun τ => (s : ℂ) * B τ)
      (G := fun τ => (s : ℂ) * criticalSeries f τ) (continuous_const.mul hGc) hℓ hc0.le hη0.le
      hqBG hqc hqM hBs h1' h2'
    have hR₁' : (M + c) * meanRemainder a γ ℓ ≤ E / 16 := by
      have h := (lt_div_iff₀ (by positivity)).mp hR₁
      linarith
    nlinarith
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    exact key 1 (by simp) fun τ hτ => by rw [one_mul]; exact h τ hτ
  · by_contra h
    push Not at h
    exact key (-1) (by simp) fun τ hτ => by linarith [h τ hτ]

/-- **Under RH every nonzero compact packet changes sign in every window of a fixed length.** -/
theorem packet_sign_changes_in_every_window_of_riemannHypothesis (hRH : RiemannHypothesis)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hne : f ≠ 0) :
    ∃ c ℓ T₀ : ℝ, 0 < c ∧ 0 < ℓ ∧ ∀ x : ℝ, T₀ ≤ x →
      (∃ τ ∈ Icc x (x + ℓ), c < stationaryPacket f τ) ∧
        ∃ τ ∈ Icc x (x + ℓ), stationaryPacket f τ < -c := by
  refine packet_sign_changes_in_every_window hf hfc hne ?_
  have h := (packet_upper_iff hf hfc le_rfl).mpr fun ρ hρ => by
    rw [re_eq_half_of_mem hRH ρ] at hρ
    norm_num at hρ
  obtain ⟨T, K, hK⟩ := h
  exact ⟨T, K, fun τ hτ => by simpa using hK τ hτ⟩

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
