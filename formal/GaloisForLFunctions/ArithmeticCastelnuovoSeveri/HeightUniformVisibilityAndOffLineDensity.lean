import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfRightZeros
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger
import GaloisForLFunctions.SquareRootThreshold.TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster
import GaloisForLFunctions.SquareRootThreshold.TheWidthBoundsTheEnergyNormalisedWeilFloor
import GaloisForLFunctions.SquareRootThreshold.ZetaNearTopZerosAreVisibleAtAPolylogarithmicLag
import GaloisForLFunctions.RHTower.OffLineClusterWeilUnbounded

/-!
# Height-Uniform Visibility Degree and Local Off-Line Density

In `TheVisibilityDegreeOfRightZeros`, the degree at which `n` right zeros of a tempered configuration
become visible is given in terms of the on-line mass `onLineMass Z b`, a local on-line zero count, or
a logarithmic zero count `N(t, t + 1] ≤ A₀ log(|t| + 3)` together with a height cutoff `|Im ρ| ≤ H_m`.
In `SquareRootThreshold`, every near-top zero of `ζ` at height `γ₀` is visible by an explicit lag
`V_w(γ₀, δ₀) ≍ (log γ₀)² log log γ₀ / δ₀`, where the height `γ₀` enters through the local window
count `P = ⌈80 log(180 Γ)⌉`, while the ground-energy rate equals the zero width `zetaZeroWidth`
unless the off-line zeros cluster without bound in unit height windows (`OffLineCopiesLocallyBounded M`
or `OffLineDepthLocallyBounded W`).

This module establishes the height-uniform visibility degree and Castelnuovo–Severi degree-defect
laws governed by local off-line density:

1. **Height-uniform visibility degree of `n` separated right zeros under bounded local count**
   (`uniformVisibleMargin`, `re_W_visible_combination_le_of_uniform_count`,
   `card_le_hodgeDefectAt_of_uniform_window_count`, `one_le_hodgeDefectAt_of_isolated_cluster`):
   Because the modulated odd test `modulatedTest ρ.im (sinhTest a δ)` has translation-invariant
   Sobolev norm `testNorm (sinhTest a δ)` and deep-pair integral `∫ sinhTest a δ(u) sinh(δ u)`, a
   uniform unit-window count `N(t, t + 1] ≤ D` bounds both the diagonal tail and the off-diagonal
   Gram entries independently of the heights `Im ρ`. Any finite set `T` of `2R`-separated,
   `R`-isolated right zeros of depth `≥ δ` at arbitrary heights satisfies `|T| ≤ hodgeDefectAt Z a`
   as soon as `0 < uniformVisibleMargin D a δ R`. In a logarithmic background
   `N(t, t + 1] ≤ A₀ log(|t| + 3)`, an isolated right zero at arbitrary height `γ₀` is visible at a
   fixed degree `a` whenever its off-line multiplicity matches the local `log(|γ₀| + 3)` factor.

2. **Near-top zero visibility of `ζ` with height-uniform companion count under bounded off-line copies**
   (`sum_mult_offLine_window_le_of_offLineCopiesLocallyBounded`,
   `mult_offLine_zeta_le_of_offLineCopiesLocallyBounded`,
   `card_offLine_window_le_of_offLineCopiesLocallyBounded`,
   `offLineDensityBound_zeta_of_offLineCopiesLocallyBounded`,
   `norm_evenCoeff_modScaledBump_le_of_offLineCopiesLocallyBounded`,
   `zeta_near_top_cluster_collapse_of_offLineCopiesLocallyBounded`,
   `zeta_near_top_visible_of_offLineCopiesLocallyBounded`):
   The companion set around a Legendre record of `ζ` consists exclusively of strictly off-line zeros
   (`Re ρ ≥ ½ + Re z₀ / 4 > ½`) in a unit-radius height window `|Im ρ − Im z₁| ≤ 1`. Under
   `OffLineCopiesLocallyBounded M`, every unit-radius window carries at most `M` off-line zeros (counted
   with multiplicity), so the companion count `P = M`, the off-line coefficient bound
   `2 M (e^{w/2} B_w)²`, the phase-coherence scale `H₀`, the coherence product `c`, the annulus gap `G`,
   the loose-factor ratio `q`, and the record depth offset are all uniform in the height `γ₀`.

3. **Height-uniform Castelnuovo–Severi degree-defect floor and zero-width equivalence**
   (`scalingSubsurface_defect_ge_of_offLineDensityBound`,
   `scalingSubsurface_defect_ge_of_offLineCopiesLocallyBounded`,
   `exists_scalingSubsurface_defect_floor_of_offLineDensityBound`,
   `zetaZeroWidth_le_iff_scalingSubsurface_odd_defect_floor_of_offLineDensityBound`,
   `zetaZeroWidth_le_iff_scalingSubsurface_odd_defect_floor_of_offLineCopiesLocallyBounded`):
   On-line zeros have nonnegative Weil summands `m_ρ ‖h_f(γ_ρ)‖² ≥ 0` and drop out of the defect
   lower bound. Under `OffLineDensityBound zetaZeroConfig D` (or `OffLineCopiesLocallyBounded M`),
   the Castelnuovo–Severi defect on `scalingSubsurface` is bounded below at rate
   `2 zetaZeroWidth` uniformly in the heights of all zeros, and the defect-floor rate is
   unconditionally equivalent to `zetaZeroWidth ≤ σ`.

4. **The unconditional clustering alternative on the scaling surface**
   (`scalingSurface_defectRate_eq_zetaZeroWidth_or_offLine_cluster`,
   `exists_scalingSubsurface_defect_floor_and_groundEnergy_bounds_of_finite_offLine`):
   Unconditionally for `ζ`, either the Castelnuovo–Severi degree-defect rate on
   `scalingSubsurface (oddRealTestsAt r)` and `polarGroundEnergyRate` both equal `zetaZeroWidth`,
   or the off-line divisor copies of `ξ` cluster without bound in unit height windows (forcing
   infinitely many off-line divisor copies of `ξ`). When the off-line divisor copies of `ξ` are
   finite and nonempty, the Castelnuovo–Severi defect floor holds at every rate above
   `zetaZeroWidth` and the ground energy obeys two-sided exponential bounds at rate
   `2 zetaZeroWidth` from an explicit threshold aperture `A`.
-/

open Complex MeasureTheory Real Set Filter Topology Finset Matrix
open scoped Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.SquareRootThreshold
  GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity
  _root_.RHTower.CCMParityQuartet _root_.RHTower.CCMParityTopLayer

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Height-uniform visibility degree of `n` separated right zeros under bounded local count -/

/-- Under a uniform unit-window count `N(t, t + 1] ≤ D`, the inverse-square and inverse-cube height
sums `Σ_ρ m_ρ / (1 + |γ_ρ − γ₀|)²` and `Σ_ρ m_ρ / (1 + |γ_ρ − γ₀|)³` are bounded by `10 D`
uniformly in the center height `γ₀ ∈ ℝ`. -/
theorem window_tsum_inv_sq_and_cube_le_of_uniform_count (Z : ZeroConfig) {D : ℝ}
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ D) (γ₀ : ℝ) :
    (Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 2) ∧
      ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 2 ≤ 10 * D) ∧
    (Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) ∧
      ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 ≤ 10 * D) := by
  classical
  have hwin : ∀ t : ℝ, ∀ s : Finset Z.carrier,
      (∀ ρ ∈ s, t < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ t + 1) → ∑ ρ ∈ s, (Z.mult ρ : ℝ) ≤ D := by
    intro t s hs
    refine le_trans ?_ (hloc t)
    have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨ρ, hρ, rfl⟩ := hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2, hs ρ hρ⟩
    have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
    rw [Finset.sum_map] at h
    exact_mod_cast h
  obtain ⟨hsum2, hle2⟩ := RHTower.window_tsum_inv_sq_le (fun ρ : Z.carrier => (ρ : ℂ).im)
    (g := fun ρ : Z.carrier => (Z.mult ρ : ℝ)) (fun _ => Nat.cast_nonneg _) hwin γ₀
  have hpt : ∀ ρ : Z.carrier,
      (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 ≤
        (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 2 := by
    intro ρ
    have h1 : 1 ≤ 1 + |(ρ : ℂ).im - γ₀| := by linarith [abs_nonneg ((ρ : ℂ).im - γ₀)]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      (pow_le_pow_right₀ h1 (by omega))
  have hsum3 : Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) :=
    Summable.of_nonneg_of_le (fun _ => div_nonneg (Nat.cast_nonneg _) (by positivity)) hpt hsum2
  exact ⟨⟨hsum2, hle2⟩, ⟨hsum3, (Summable.tsum_le_tsum hpt hsum3 hsum2).trans hle2⟩⟩

/-- **Height-uniform isolation inequality.** Under a uniform unit-window count `N(t, t + 1] ≤ D`,
for any zero `ρ₀ = ½ + δ + iγ₀` (`δ > 0`) at arbitrary height `γ₀ ∈ ℝ` that is `R`-isolated from
other off-line zeros, and any real odd `C²` test `s` supported in `[−a, a]`,
`Re W(e^{-iγ₀u}s, e^{-iγ₀u}s) ≤ −2 m_{ρ₀} (∫ s(u) sinh(δu))² + 160 D testNorm(s)² (1 + e^a/(1 + R))`. -/
theorem re_W_modulatedTest_le_of_isolated_uniform_count (Z : ZeroConfig) {D : ℝ}
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ D)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hiso : ∀ ρ ∈ Z.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.im - ρ₀.im| ≤ R → ρ.re = 1 / 2)
    {s : ℝ → ℝ} (hs : ContDiff ℝ 2 s) (hodd : ∀ u, s (-u) = -s u)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) :
    (Z.W (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s)).re ≤
      -2 * Z.mult ρ₀ * (∫ u, s u * Real.sinh (δ * u)) ^ 2 +
        160 * D * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) := by
  classical
  obtain ⟨-, hwsum, hwle⟩ := window_tsum_inv_sq_and_cube_le_of_uniform_count Z hloc ρ₀.im
  have hsumm : Summable (fun ρ : Z.carrier =>
      Z.Wsummand (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s) ρ) :=
    Summable.of_norm_bounded (hwsum.mul_left _) fun ρ =>
      norm_Wsummand_modulatedTest_le_weight Z ρ₀.im ha hs hsupp ρ.2
  obtain ⟨hval0, hval1⟩ := Wsummand_modulatedTest_deep_pair Z hρ₀ hre hs.continuous hsupp hodd
  set Q : ℝ := (Z.mult ρ₀ : ℝ) * (∫ u, s u * Real.sinh (δ * u)) ^ 2 with hQ
  set ρ₀ₛ : Z.carrier := ⟨ρ₀, hρ₀⟩ with hρ₀ₛ
  set ρ₁ₛ : Z.carrier := ⟨reflect ρ₀, Z.reflect_mem ρ₀ hρ₀⟩ with hρ₁ₛ
  have hne : ρ₁ₛ ≠ ρ₀ₛ := by
    intro h
    have := congrArg (fun x : Z.carrier => (x : ℂ).re) h
    simp only [hρ₀ₛ, hρ₁ₛ, reflect, Complex.sub_re, Complex.one_re, Complex.conj_re, hre] at this
    linarith
  set F : Z.carrier → ℝ := fun ρ =>
    (Z.Wsummand (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s) ρ).re with hF
  set c : Z.carrier → ℝ := fun ρ =>
    16 * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) *
      ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ρ₀.im|) ^ 3) with hc
  have hN := testNorm_nonneg s
  have hc0 : ∀ ρ, 0 ≤ c ρ := fun ρ => by
    have : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    simp only [hc]; positivity
  have hgc : ∀ ρ, F ρ + (if ρ = ρ₀ₛ then Q else 0) + (if ρ = ρ₁ₛ then Q else 0) ≤ c ρ := by
    intro ρ
    by_cases h0 : ρ = ρ₀ₛ
    · rw [h0, if_pos rfl, if_neg hne.symm]
      simp only [hF]
      rw [show ((ρ₀ₛ : Z.carrier) : ℂ) = ρ₀ from rfl, hval0, Complex.ofReal_re]
      linarith [hc0 ρ₀ₛ]
    by_cases h1 : ρ = ρ₁ₛ
    · rw [h1, if_neg hne, if_pos rfl]
      simp only [hF]
      rw [show ((ρ₁ₛ : Z.carrier) : ℂ) = reflect ρ₀ from rfl, hval1, Complex.ofReal_re]
      linarith [hc0 ρ₁ₛ]
    rw [if_neg h0, if_neg h1, add_zero, add_zero]
    have hρ0 : (ρ : ℂ) ≠ ρ₀ := fun h => h0 (Subtype.ext h)
    have hρ1 : (ρ : ℂ) ≠ reflect ρ₀ := fun h => h1 (Subtype.ext h)
    exact (Complex.re_le_norm _).trans (norm_Wsummand_modulatedTest_le_isolated Z ρ₀.im ha hR
      hs hsupp ρ.2 (hiso ρ ρ.2 hρ0 hρ1))
  have hre_sum : Summable F := (Complex.hasSum_re hsumm.hasSum).summable
  have hi0 := hasSum_ite_eq ρ₀ₛ Q
  have hi1 := hasSum_ite_eq ρ₁ₛ Q
  have hgsum : Summable (fun ρ => F ρ + (if ρ = ρ₀ₛ then Q else 0) +
      (if ρ = ρ₁ₛ then Q else 0)) := (hre_sum.add hi0.summable).add hi1.summable
  have hcsum : Summable c := hwsum.mul_left _
  have htg : ∑' ρ, (F ρ + (if ρ = ρ₀ₛ then Q else 0) + (if ρ = ρ₁ₛ then Q else 0)) =
      (∑' ρ, F ρ) + Q + Q := by
    rw [Summable.tsum_add (hre_sum.add hi0.summable) hi1.summable,
      Summable.tsum_add hre_sum hi0.summable, hi0.tsum_eq, hi1.tsum_eq]
  have htc : ∑' ρ, c ρ ≤ 16 * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) * (10 * D) := by
    rw [hc, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hwle (by positivity)
  have hle := Summable.tsum_le_tsum hgc hgsum hcsum
  have hW : (Z.W (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s)).re = ∑' ρ, F ρ := by
    rw [ZeroConfig.W, Complex.re_tsum hsumm]
  rw [hW]
  have : ∑' ρ, F ρ ≤ -2 * Q + 16 * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) * (10 * D) := by
    linarith
  calc ∑' ρ, F ρ ≤ -2 * Q + 16 * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) * (10 * D) := this
    _ = -2 * Z.mult ρ₀ * (∫ u, s u * Real.sinh (δ * u)) ^ 2 +
        160 * D * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) := by
        rw [hQ]; ring

/-- Off-diagonal Gram bound for two modulated tests under a uniform unit-window count `D`,
completely independent of the center heights `γ₁, γ₂`. -/
theorem norm_W_modulatedTest_pair_le_of_uniform_count (Z : ZeroConfig) {D : ℝ}
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ D) (γ₁ γ₂ : ℝ) {s : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hs : ContDiff ℝ 2 s) (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) :
    Summable (fun ρ : Z.carrier => Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ) ∧
      ‖Z.W (modulatedTest γ₁ s) (modulatedTest γ₂ s)‖ ≤
        64 * Real.exp a * testNorm s ^ 2 * (20 * D) / (1 + |γ₁ - γ₂|) ^ 2 := by
  obtain ⟨⟨hs₁, ht₁⟩, -⟩ := window_tsum_inv_sq_and_cube_le_of_uniform_count Z hloc γ₁
  obtain ⟨⟨hs₂, ht₂⟩, -⟩ := window_tsum_inv_sq_and_cube_le_of_uniform_count Z hloc γ₂
  set K := 64 * Real.exp a * testNorm s ^ 2 / (1 + |γ₁ - γ₂|) ^ 2 with hK
  have hK0 : 0 ≤ K := by have := testNorm_nonneg s; positivity
  have hb : ∀ ρ : Z.carrier, ‖Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ‖ ≤
      K * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₁|) ^ 2 +
        (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₂|) ^ 2) := fun ρ =>
    norm_Wsummand_modulatedTest_pair_le Z γ₁ γ₂ ha hs hsupp ρ.2
  have hbs : Summable (fun ρ : Z.carrier => K * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₁|) ^ 2 +
      (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₂|) ^ 2)) := (hs₁.add hs₂).mul_left K
  have hsum := Summable.of_norm_bounded hbs hb
  refine ⟨hsum, ?_⟩
  rw [ZeroConfig.W]
  have hns : Summable (fun ρ : Z.carrier =>
      ‖Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hbs
  calc ‖∑' ρ : Z.carrier, Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ‖
      ≤ ∑' ρ : Z.carrier, ‖Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ‖ :=
        norm_tsum_le_tsum_norm hns
    _ ≤ ∑' ρ : Z.carrier, K * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₁|) ^ 2 +
          (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₂|) ^ 2) := Summable.tsum_le_tsum hb hns hbs
    _ = K * (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₁|) ^ 2 +
          ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₂|) ^ 2) := by
        rw [tsum_mul_left, Summable.tsum_add hs₁ hs₂]
    _ ≤ K * (10 * D + 10 * D) := mul_le_mul_of_nonneg_left (add_le_add ht₁ ht₂) hK0
    _ = 64 * Real.exp a * testNorm s ^ 2 * (20 * D) / (1 + |γ₁ - γ₂|) ^ 2 := by rw [hK]; ring

/-- The height-independent visibility margin for separated `R`-isolated right zeros of depth `≥ δ`
at degree `a` under a uniform unit-window count `D`. -/
def uniformVisibleMargin (D a δ R : ℝ) : ℝ :=
  2 * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 -
    (160 * D * testNorm (sinhTest a δ) ^ 2 * (1 + Real.exp a / (1 + R)) +
      64 * Real.exp a * testNorm (sinhTest a δ) ^ 2 * (20 * D) * (10 / R ^ 2))

/-- **Height-uniform quadratic bound for separated visible pairs.** Let `Z` have unit-window count
`N(t, t + 1] ≤ D`, and let `T` be a finite set of right zeros of depth `≥ δ > 0` at arbitrary
heights (no height bound `|Im ρ| ≤ H_m`), pairwise `2R`-separated (`R ≥ 1`) and `R`-isolated from
other off-line zeros. Then every linear combination of the modulated sinh-tests at the heights of `T`
has Weil form at most `−uniformVisibleMargin D a δ R · Σ_{ρ ∈ T} |c_ρ|²`. -/
theorem re_W_visible_combination_le_of_uniform_count (Z : ZeroConfig) {D : ℝ}
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ D) {a δ R : ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (hR : 1 ≤ R) (T : Finset ℂ)
    (hT : ∀ ρ ∈ T, ρ ∈ Z.carrier ∧ 1 / 2 + δ ≤ ρ.re)
    (hsep : ∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|)
    (hiso : ∀ ρ ∈ T, ∀ σ ∈ Z.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R → σ.re = 1 / 2)
    (c : ℂ → ℂ) :
    (Z.W (fun u => ∑ ρ ∈ T, c ρ * modulatedTest ρ.im (sinhTest a δ) u)
      (fun u => ∑ ρ ∈ T, c ρ * modulatedTest ρ.im (sinhTest a δ) u)).re ≤
      -uniformVisibleMargin D a δ R * ∑ ρ ∈ T, ‖c ρ‖ ^ 2 := by
  classical
  have hD0 : 0 ≤ D := le_trans (Nat.cast_nonneg _) (hloc 0)
  set s := sinhTest a δ with hsdef
  set N := testNorm s with hN
  set P := ∫ u, s u * Real.sinh (δ * u) with hP
  set f : ℂ → ℝ → ℂ := fun ρ => modulatedTest ρ.im s with hf
  have hs := sinhTest_contDiff a δ
  have hsupp : ∀ u, s u ≠ 0 → |u| ≤ a := sinhTest_supp ha
  have hfc : ∀ ρ, Continuous (f ρ) := fun ρ => continuous_modulatedTest _ hs.continuous
  have hfcs : ∀ ρ, HasCompactSupport (f ρ) := fun ρ => hasCompactSupport_modulatedTest _ hsupp
  have hpair := fun ρ σ : ℂ =>
    norm_W_modulatedTest_pair_le_of_uniform_count Z hloc ρ.im σ.im ha hs hsupp
  have hexp := W_finset_sum Z T c hfc hfcs (fun ρ σ => (hpair ρ σ).1)
  rw [hexp, Complex.re_sum]
  set Ed := 160 * D * N ^ 2 * (1 + Real.exp a / (1 + R)) with hEd
  set K := 64 * Real.exp a * N ^ 2 * (20 * D) with hKdef
  have hK0 : 0 ≤ K := by positivity
  set κ : ℂ → ℂ → ℝ := fun ρ σ => if ρ = σ then 0 else K / (1 + |ρ.im - σ.im|) ^ 2 with hκ
  have hκ0 : ∀ ρ σ, 0 ≤ κ ρ σ := fun ρ σ => by simp only [hκ]; split_ifs <;> positivity
  have hdiag : ∀ ρ ∈ T, (Z.W (f ρ) (f ρ)).re ≤ -2 * P ^ 2 + Ed := by
    intro ρ hρ
    set δ' := ρ.re - 1 / 2 with hδ'
    have hδ'0 : 0 < δ' := by linarith [(hT ρ hρ).2]
    have hmaster := re_W_modulatedTest_le_of_isolated_uniform_count Z hloc (hT ρ hρ).1 hδ'0
      (by rw [hδ']; ring) ha (by linarith) (hiso ρ hρ) hs (sinhTest_odd a δ) hsupp
    have hP0 : 0 ≤ P := by
      refine integral_nonneg fun u => ?_
      show 0 ≤ sinhTest a δ u * Real.sinh (δ * u)
      simp only [sinhTest]
      have := mul_nonneg (mul_self_nonneg (Real.sinh (δ * u))) (sinhTestWeight_nonneg a u)
      nlinarith
    have hmono := integral_sinhTest_mul_sinh_mono (a := a) ha hδ.le
      (show δ ≤ δ' by linarith [(hT ρ hρ).2])
    have hsq : P ^ 2 ≤ (∫ u, sinhTest a δ u * Real.sinh (δ' * u)) ^ 2 :=
      pow_le_pow_left₀ hP0 hmono 2
    have hm : (1 : ℝ) ≤ Z.mult ρ := by exact_mod_cast Z.one_le_mult ρ (hT ρ hρ).1
    have h1 : -2 * (Z.mult ρ : ℝ) * (∫ u, sinhTest a δ u * Real.sinh (δ' * u)) ^ 2 ≤
        -2 * P ^ 2 := by
      have := sq_nonneg (∫ u, sinhTest a δ u * Real.sinh (δ' * u))
      nlinarith
    linarith
  have hterm : ∀ ρ ∈ T, ∀ σ ∈ T, (c ρ * conj (c σ) * Z.W (f ρ) (f σ)).re ≤
      (if ρ = σ then ‖c ρ‖ ^ 2 * (-2 * P ^ 2 + Ed) else 0) +
        1 * 1 * (‖c ρ‖ * ‖c σ‖) * κ ρ σ := by
    intro ρ hρ σ hσ
    by_cases hrs : ρ = σ
    · subst hrs
      rw [if_pos rfl]
      simp only [hκ, if_pos rfl, mul_zero, add_zero]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul]
      exact mul_le_mul_of_nonneg_left (hdiag ρ hρ) (sq_nonneg _)
    · rw [if_neg hrs, zero_add]
      simp only [hκ, if_neg hrs, one_mul]
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hpair ρ σ).2 (by positivity)
  have hrow : ∀ ρ ∈ T, ∑ σ ∈ T, (1 : ℝ) * κ ρ σ ≤ K * (10 / R ^ 2) := by
    intro ρ hρ
    have e : ∑ σ ∈ T, (1 : ℝ) * κ ρ σ = K * ∑ σ ∈ T.erase ρ, 1 / (1 + |ρ.im - σ.im|) ^ 2 := by
      rw [← Finset.add_sum_erase T _ hρ]
      simp only [hκ, if_pos rfl, one_mul, zero_add]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ hσ => ?_
      rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hσ))]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (sum_separated_inv_sq_le hR hsep hρ) hK0
  have hcol : ∀ σ ∈ T, ∑ ρ ∈ T, (1 : ℝ) * κ ρ σ ≤ K * (10 / R ^ 2) := by
    intro σ hσ
    have e : ∑ ρ ∈ T, (1 : ℝ) * κ ρ σ = K * ∑ ρ ∈ T.erase σ, 1 / (1 + |σ.im - ρ.im|) ^ 2 := by
      rw [← Finset.add_sum_erase T _ hσ]
      simp only [hκ, if_pos rfl, one_mul, zero_add]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      rw [if_neg (Finset.ne_of_mem_erase hρ), abs_sub_comm]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (sum_separated_inv_sq_le hR hsep hσ) hK0
  have hschur := double_sum_le_of_row_col T (m := fun _ => (1 : ℝ)) (x := fun ρ => ‖c ρ‖)
    (fun _ => zero_le_one) hκ0 hrow hcol
  have hsum_le : ∑ ρ ∈ T, (∑ σ ∈ T, c ρ * conj (c σ) * Z.W (f ρ) (f σ)).re ≤
      ∑ ρ ∈ T, ∑ σ ∈ T, ((if ρ = σ then ‖c ρ‖ ^ 2 * (-2 * P ^ 2 + Ed) else 0) +
        1 * 1 * (‖c ρ‖ * ‖c σ‖) * κ ρ σ) := by
    refine Finset.sum_le_sum fun ρ hρ => ?_
    rw [Complex.re_sum]
    exact Finset.sum_le_sum fun σ hσ => hterm ρ hρ σ hσ
  have hsplit : ∑ ρ ∈ T, ∑ σ ∈ T, ((if ρ = σ then ‖c ρ‖ ^ 2 * (-2 * P ^ 2 + Ed) else 0) +
        1 * 1 * (‖c ρ‖ * ‖c σ‖) * κ ρ σ) =
      (∑ ρ ∈ T, ‖c ρ‖ ^ 2) * (-2 * P ^ 2 + Ed) +
        ∑ ρ ∈ T, ∑ σ ∈ T, 1 * 1 * (‖c ρ‖ * ‖c σ‖) * κ ρ σ := by
    simp_rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun ρ hρ => by rw [if_pos hρ]
  have hS' : ∑ σ ∈ T, (1 : ℝ) * ‖c σ‖ ^ 2 = ∑ ρ ∈ T, ‖c ρ‖ ^ 2 := by simp
  rw [hS'] at hschur
  calc ∑ ρ ∈ T, (∑ σ ∈ T, c ρ * conj (c σ) * Z.W (f ρ) (f σ)).re
      ≤ (∑ ρ ∈ T, ‖c ρ‖ ^ 2) * (-2 * P ^ 2 + Ed) +
          ∑ ρ ∈ T, ∑ σ ∈ T, 1 * 1 * (‖c ρ‖ * ‖c σ‖) * κ ρ σ := hsum_le.trans (le_of_eq hsplit)
    _ ≤ (∑ ρ ∈ T, ‖c ρ‖ ^ 2) * (-2 * P ^ 2 + Ed) + K * (10 / R ^ 2) * ∑ ρ ∈ T, ‖c ρ‖ ^ 2 := by
        linarith
    _ = -uniformVisibleMargin D a δ R * ∑ ρ ∈ T, ‖c ρ‖ ^ 2 := by
        rw [uniformVisibleMargin, ← hP, ← hN, hEd, hKdef]; ring

/-- **Height-uniform visibility degree of `n` separated right zeros under bounded local count.**
Let `Z` be a tempered configuration with unit-window zero count `N(t, t + 1] ≤ D`, and let `T` be a
finite set of right zeros of depth `≥ δ > 0` at arbitrary heights (no height cutoff `H_m`), pairwise
`2R`-separated (`R ≥ 1`) and `R`-isolated from other off-line zeros. Whenever
`0 < uniformVisibleMargin D a δ R`, the modulated sinh-tests at the heights of `T` span a
`|T|`-dimensional negative subspace of `zeroGram Z` at degree `a`, so `(|T| : ℕ∞) ≤ hodgeDefectAt Z a`. -/
theorem card_le_hodgeDefectAt_of_uniform_window_count (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {D : ℝ} (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ D)
    {a δ R : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hR : 1 ≤ R) (T : Finset ℂ)
    (hT : ∀ ρ ∈ T, ρ ∈ Z.carrier ∧ 1 / 2 + δ ≤ ρ.re)
    (hsep : ∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|)
    (hiso : ∀ ρ ∈ T, ∀ σ ∈ Z.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R → σ.re = 1 / 2)
    (hvis : 0 < uniformVisibleMargin D a δ R) :
    (T.card : ℕ∞) ≤ hodgeDefectAt Z a ∧
      ∃ f : Fin T.card → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧
        (∀ i, tsupport (f i) ⊆ Icc (-a) a) ∧ T.card ≤ hermNegIndex (zeroGram Z f) := by
  classical
  set e := T.equivFin
  set s := RHTower.sinhTest a δ
  set f : Fin T.card → ℝ → ℂ := fun i => RHTower.modulatedTest (e.symm i : ℂ).im s
  have hs : ContDiff ℝ 2 s := RHTower.sinhTest_contDiff a δ
  have hsupp : ∀ u, s u ≠ 0 → |u| ≤ a := RHTower.sinhTest_supp ha
  have hfd : ∀ i, ContDiff ℝ 2 (f i) := fun i => RHTower.modulatedTest_contDiff _ hs
  have hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a := fun i =>
    RHTower.tsupport_modulatedTest_subset _ hsupp
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hfs i)
  have hpd : IsPosDefOn (-(zeroGram Z f)) ⊤ := by
    intro x _ hx0
    rw [hermQuad_neg, hermQuad_zeroGram_of_tempered Z hZ f hfd hfc]
    set c : T → ℂ := fun ρ => conj (x (e ρ))
    have hc0 : c ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
      intro h
      apply hi
      have h1 : c (e.symm i) = 0 := congrFun h (e.symm i)
      simp only [c, Equiv.apply_symm_apply, map_eq_zero] at h1
      exact h1
    have hfun : (∑ i, conj (x i) • f i) =
        fun u => ∑ ρ ∈ T, RHTower.extendCoeff T c ρ * RHTower.modulatedTest ρ.im s u := by
      rw [← RHTower.visibleCombination_eq]
      funext u
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RHTower.visibleCombination]
      rw [← Equiv.sum_comp e (fun i => conj (x i) * f i u)]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp [f, c]
    rw [hfun]
    obtain ⟨ρ₀, hρ₀T, hρ₀ne⟩ := RHTower.exists_extendCoeff_ne hc0
    have hpos : 0 < ∑ ρ ∈ T, ‖RHTower.extendCoeff T c ρ‖ ^ 2 :=
      lt_of_lt_of_le (by positivity)
        (Finset.single_le_sum (f := fun ρ => ‖RHTower.extendCoeff T c ρ‖ ^ 2)
          (fun _ _ => sq_nonneg _) hρ₀T)
    have hle := re_W_visible_combination_le_of_uniform_count Z hloc ha hδ hR T hT hsep hiso
      (RHTower.extendCoeff T c)
    have hneg : -uniformVisibleMargin D a δ R * ∑ ρ ∈ T, ‖RHTower.extendCoeff T c ρ‖ ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (neg_lt_zero.mpr hvis) hpos
    linarith
  have hneg : T.card ≤ hermNegIndex (zeroGram Z f) := by
    have h1 := finrank_le_posIndex hpd
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    rw [hermNegIndex]
    exact h1
  exact ⟨(ENat.coe_le_coe.mpr hneg).trans (le_hodgeDefectAt Z f fun i => ⟨hfd i, hfs i⟩),
    f, hfd, hfs, hneg⟩

/-- **Height-uniform visibility of an off-line cluster in a logarithmic background.** In any
tempered configuration `Z` with local count `N(t, t + 1] ≤ A₀ log(|t| + 3)`, an `R`-isolated right
zero `ρ₀ = ½ + δ + iγ₀` (`δ > 0`) at arbitrary height `γ₀` produces `1 ≤ hodgeDefectAt Z a` at a
fixed degree `a` as soon as its off-line multiplicity `Z.mult ρ₀` beats the local logarithmic count:
`384 A₀ log(|γ₀| + 3) testNorm(sinhTest a δ)² (1 + e^a/(1 + R)) < 2 m_{ρ₀} (∫ sinhTest a δ(u) sinh(δu))²`. -/
theorem one_le_hodgeDefectAt_of_isolated_cluster (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {A₀ : ℝ} (hA₀ : 1 ≤ A₀) (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hiso : ∀ ρ ∈ Z.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.im - ρ₀.im| ≤ R → ρ.re = 1 / 2)
    (hmult : 384 * A₀ * Real.log (|ρ₀.im| + 3) * testNorm (sinhTest a δ) ^ 2 *
        (1 + Real.exp a / (1 + R)) <
      2 * Z.mult ρ₀ * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2) :
    1 ≤ hodgeDefectAt Z a := by
  set f : Fin 1 → ℝ → ℂ := fun _ => modulatedTest ρ₀.im (sinhTest a δ)
  have hs := sinhTest_contDiff a δ
  have hsupp : ∀ u, sinhTest a δ u ≠ 0 → |u| ≤ a := sinhTest_supp ha
  have hfd : ∀ i, ContDiff ℝ 2 (f i) := fun _ => modulatedTest_contDiff _ hs
  have hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a := fun _ => tsupport_modulatedTest_subset _ hsupp
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hfs i)
  have hmaster := re_W_modulatedTest_le_of_isolated Z hA₀ hloc hρ₀ hδ hre ha hR hiso
    hs (sinhTest_odd a δ) hsupp
  have hpd : IsPosDefOn (-(zeroGram Z f)) ⊤ := by
    intro x _ hx0
    rw [hermQuad_neg, hermQuad_zeroGram_of_tempered Z hZ f hfd hfc, Fin.sum_univ_one]
    have hx : x 0 ≠ 0 := fun h => hx0 (Subsingleton.elim x 0 |>.trans (by simp [h]))
    have hnorm : 0 < ‖conj (x 0)‖ ^ 2 := by simp [hx]
    have hW : (Z.W (conj (x 0) • f 0) (conj (x 0) • f 0)).re =
        ‖conj (x 0)‖ ^ 2 * (Z.W (f 0) (f 0)).re := by
      have h1 : ∀ ρ, Z.Wsummand (conj (x 0) • f 0) (conj (x 0) • f 0) ρ =
          ((‖conj (x 0)‖ ^ 2 : ℝ) : ℂ) * Z.Wsummand (f 0) (f 0) ρ := fun ρ => by
        unfold ZeroConfig.Wsummand
        have hft : ∀ z, paperFT (conj (x 0) • f 0) z = conj (x 0) * paperFT (f 0) z := fun z => by
          rw [paperFT_def, paperFT_def, ← integral_const_mul]
          congr 1 with u; simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
        rw [hft, hft, map_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        ring
      rw [ZeroConfig.W, ZeroConfig.W]
      simp_rw [h1]
      rw [tsum_mul_left, Complex.re_ofReal_mul]
    rw [hW]
    have hneg : (Z.W (f 0) (f 0)).re < 0 := by simp only [f]; linarith
    nlinarith
  have hneg : 1 ≤ hermNegIndex (zeroGram Z f) := by
    have h1 := finrank_le_posIndex hpd
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    rw [hermNegIndex]
    exact h1
  exact (ENat.coe_le_coe.mpr hneg).trans (le_hodgeDefectAt Z f fun i => ⟨hfd i, hfs i⟩)

/-! ### 2. Near-top zero visibility of `ζ` with height-uniform companion count under bounded off-line copies -/

/-- **Off-line multiplicity sum in a unit-radius height window.** Under
`OffLineCopiesLocallyBounded M`, any finite set `S` of off-line zeros of `ζ` (`Re ρ ≠ ½`) in a
unit-radius window `|Im ρ − T₀| ≤ 1` has total multiplicity `Σ_{ρ ∈ S} mult(ρ) ≤ M`, uniformly in
the window center `T₀ ∈ ℝ`. -/
theorem sum_mult_offLine_window_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) (T₀ : ℝ) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier ∧ ρ.re ≠ 1 / 2 ∧ |ρ.im - T₀| ≤ 1) :
    ∑ ρ ∈ S, zetaZeroConfig.mult ρ ≤ M := by
  classical
  set d : S → XiDivisorSupport := fun ρ => xiDivisorZetaCarrierEquiv.symm ⟨ρ, (hS ρ ρ.2).1⟩ with hd
  have hdv : ∀ ρ : S, ((d ρ : XiDivisorSupport) : ℂ) = ρ := fun _ => rfl
  have hdm : ∀ ρ : S, (MeromorphicOn.divisor xi Set.univ ((d ρ : XiDivisorSupport) : ℂ)).toNat =
      zetaZeroConfig.mult ρ := fun ρ => by
    rw [xiDivisorZetaCarrierEquiv_multiplicity, hd]; simp only [Equiv.apply_symm_apply]
  have hinj : Function.Injective d := fun a b h => by
    have := congrArg (fun x : XiDivisorSupport => (x : ℂ)) h
    simp only [hdv] at this
    exact Subtype.ext this
  set W : Finset XiDivisorSupport := S.attach.image d with hW
  set Q : Finset XiZeroCopy := W.sigma (fun δ =>
    (Finset.univ : Finset (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (δ : ℂ)))))) with hQ
  have hQcard : Q.card = ∑ ρ ∈ S, zetaZeroConfig.mult ρ := by
    calc Q.card
        = ∑ δ ∈ W, (MeromorphicOn.divisor xi Set.univ (δ : ℂ)).toNat := by
            rw [hQ, Finset.card_sigma]
            refine Finset.sum_congr rfl fun δ _ => ?_
            simp
      _ = ∑ ρ ∈ S.attach, (MeromorphicOn.divisor xi Set.univ ((d ρ : XiDivisorSupport) : ℂ)).toNat := by
            rw [hW, Finset.sum_image fun a _ b _ h => hinj h]
      _ = ∑ ρ ∈ S.attach, zetaZeroConfig.mult ρ := Finset.sum_congr rfl fun ρ _ => hdm ρ
      _ = ∑ ρ ∈ S, zetaZeroConfig.mult ρ := Finset.sum_attach S _
  have hsub : (Q : Set XiZeroCopy) ⊆
      {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0 ∧ |(xiSpectralPoint q).re - T₀| ≤ 1} := by
    intro q hq
    rw [Finset.mem_coe, hQ, Finset.mem_sigma] at hq
    obtain ⟨hqW, -⟩ := hq
    rw [hW, Finset.mem_image] at hqW
    obtain ⟨ρ, -, hρq⟩ := hqW
    have hval : (q.1 : ℂ) = (ρ : ℂ) := by rw [← hρq, hdv]
    have him : (xiSpectralPoint q).im = 1 / 2 - (ρ : ℂ).re := by
      rw [xiSpectralPoint_im_eq, hval]
    have hre : (xiSpectralPoint q).re = (ρ : ℂ).im := by
      simp [xiSpectralPoint, hval]
    refine ⟨?_, ?_⟩
    · rw [him, sub_ne_zero]
      exact (hS ρ ρ.2).2.1.symm
    · rw [hre]
      exact (hS ρ ρ.2).2.2
  have henc := (Set.encard_le_encard hsub).trans (hM T₀)
  rw [Set.encard_coe_eq_coe_finsetCard, hQcard] at henc
  exact_mod_cast henc

/-- **Height-uniform multiplicity bound for off-line zeros of `ζ`.** Under
`OffLineCopiesLocallyBounded M`, every off-line zero `ρ` of `ζ` (`Re ρ ≠ ½`) has multiplicity at
most `M`, independent of `Im ρ`. -/
theorem mult_offLine_zeta_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier)
    (hoff : ρ.re ≠ 1 / 2) :
    zetaZeroConfig.mult ρ ≤ M := by
  simpa using sum_mult_offLine_window_le_of_offLineCopiesLocallyBounded hM ρ.im {ρ}
    (fun σ hσ => by
      rw [Finset.mem_singleton] at hσ
      subst hσ
      exact ⟨hρ, hoff, by simp⟩)

/-- **Height-uniform cardinality bound for off-line exponents in a unit-radius window.** Under
`OffLineCopiesLocallyBounded M`, any finite set `T` of off-line exponents (`Re z ≠ 0`,
`½ + z ∈ zetaZeroConfig.carrier`) in a unit-radius window `|Im z − T₀| ≤ 1` has `|T| ≤ M`,
independent of the window height `T₀`. -/
theorem card_offLine_window_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) (T₀ : ℝ) (T : Finset ℂ)
    (hT : ∀ z ∈ T, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ z.re ≠ 0 ∧ |z.im - T₀| ≤ 1) :
    T.card ≤ M := by
  classical
  have hinj : Function.Injective (fun z : ℂ => 1 / 2 + z) := fun a b h => by simpa using h
  have hS : ∀ ρ ∈ T.image (fun z : ℂ => 1 / 2 + z),
      ρ ∈ zetaZeroConfig.carrier ∧ ρ.re ≠ 1 / 2 ∧ |ρ.im - T₀| ≤ 1 := by
    intro ρ hρ
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨hm, hre, him⟩ := hT z hz
    refine ⟨hm, ?_, ?_⟩
    · intro h
      apply hre
      have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
      linarith
    · simpa using him
  calc T.card
      = (T.image (fun z : ℂ => 1 / 2 + z)).card := (Finset.card_image_of_injective T hinj).symm
    _ = ∑ _ρ ∈ T.image (fun z : ℂ => 1 / 2 + z), 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ ρ ∈ T.image (fun z : ℂ => 1 / 2 + z), zetaZeroConfig.mult ρ :=
        Finset.sum_le_sum fun ρ hρ => zetaZeroConfig.one_le_mult ρ (hS ρ hρ).1
    _ ≤ M := sum_mult_offLine_window_le_of_offLineCopiesLocallyBounded hM T₀ _ hS

/-- **Bridge between the two local off-line density hypotheses.** `OffLineCopiesLocallyBounded M`
from `SquareRootThreshold` implies `RHTower.OffLineDensityBound zetaZeroConfig M`: every unit window
`(t, t + 1]` lies inside the unit-radius window `[t + ½ − 1, t + ½ + 1]`. -/
theorem offLineDensityBound_zeta_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) :
    RHTower.OffLineDensityBound zetaZeroConfig M := by
  classical
  intro t s hs
  set s' := s.filter (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).re ≠ 1 / 2) with hs'
  have hsum_eq : ∑ ρ ∈ s, RHTower.offLineMult zetaZeroConfig ρ =
      ∑ ρ ∈ s', (zetaZeroConfig.mult ρ : ℝ) := by
    rw [hs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases h : (ρ : ℂ).re = 1 / 2 <;> simp [RHTower.offLineMult, h]
  rw [hsum_eq]
  have hinj : Function.Injective (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ)) := Subtype.val_injective
  have hS : ∀ ρ ∈ s'.image (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ)),
      ρ ∈ zetaZeroConfig.carrier ∧ ρ.re ≠ 1 / 2 ∧ |ρ.im - (t + 1 / 2)| ≤ 1 := by
    intro ρ hρ
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hρ
    rw [hs', Finset.mem_filter] at hσ
    have hw := hs σ hσ.1
    refine ⟨σ.2, hσ.2, ?_⟩
    rw [abs_le]
    constructor <;> linarith [hw.1, hw.2]
  have hle := sum_mult_offLine_window_le_of_offLineCopiesLocallyBounded hM (t + 1 / 2)
    (s'.image (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ))) hS
  rw [Finset.sum_image fun a _ b _ h => hinj h] at hle
  exact_mod_cast hle

/-- **Height-uniform bound for off-line modulated coefficients.** Under
`OffLineCopiesLocallyBounded M`, every off-line exponent `z` (`Re z ≠ 0`) has
`‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤ 2 M (e^{w/2} B_w)²`, completely independent of
the height `Im z` and the modulation center `c`. -/
theorem norm_evenCoeff_modScaledBump_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) (c : ℝ) {z : ℂ} (hz : z.re ≠ 0) :
    ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      2 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := by
  set K := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 : ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤ M * K := by
    by_cases hc : (1 / 2 + z) ∈ zetaZeroConfig.carrier
    · have hle := norm_lagCoeff_modScaledBump_le zetaZeroConfig hw c hc
      have hm : (zetaZeroConfig.mult (1 / 2 + z) : ℝ) ≤ M := by
        exact_mod_cast mult_offLine_zeta_le_of_offLineCopiesLocallyBounded hM hc (by
          intro h; apply hz; have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
          linarith)
      have hden : 1 ≤ (1 + |z.im - c|) ^ 4 := one_le_pow₀ (by linarith [abs_nonneg (z.im - c)])
      calc ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖
          ≤ (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * K / (1 + |z.im - c|) ^ 4 := hle
        _ ≤ (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * K := div_le_self (by positivity) hden
        _ ≤ M * K := mul_le_mul_of_nonneg_right hm hK0
    · rw [lagCoeff, Set.indicator_of_notMem hc, norm_zero]; positivity
  have h2 : ‖lagCoeff zetaZeroConfig (modScaledBump w c) (conj z)‖ ≤ M * K := by
    by_cases hc : (1 / 2 + conj z) ∈ zetaZeroConfig.carrier
    · have hle := norm_lagCoeff_modScaledBump_le zetaZeroConfig hw c hc
      have hm : (zetaZeroConfig.mult (1 / 2 + conj z) : ℝ) ≤ M := by
        exact_mod_cast mult_offLine_zeta_le_of_offLineCopiesLocallyBounded hM hc (by
          intro h; apply hz; have e : (1 / 2 + conj z).re = 1 / 2 + z.re := by simp
          linarith)
      have hden : 1 ≤ (1 + |(conj z).im - c|) ^ 4 :=
        one_le_pow₀ (by linarith [abs_nonneg ((conj z).im - c)])
      calc ‖lagCoeff zetaZeroConfig (modScaledBump w c) (conj z)‖
          ≤ (zetaZeroConfig.mult (1 / 2 + conj z) : ℝ) * K / (1 + |(conj z).im - c|) ^ 4 := hle
        _ ≤ (zetaZeroConfig.mult (1 / 2 + conj z) : ℝ) * K := div_le_self (by positivity) hden
        _ ≤ M * K := mul_le_mul_of_nonneg_right hm hK0
    · rw [lagCoeff, Set.indicator_of_notMem hc, norm_zero]; positivity
  calc ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖
      ≤ ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ +
          ‖conj (lagCoeff zetaZeroConfig (modScaledBump w c) (conj z))‖ := by
        rw [evenCoeff]; exact norm_add_le _ _
    _ = ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ +
          ‖lagCoeff zetaZeroConfig (modScaledBump w c) (conj z)‖ := by rw [Complex.norm_conj]
    _ ≤ M * K + M * K := add_le_add h1 h2
    _ = 2 * M * K := by ring

/-- **Near-top cluster collapse with height-uniform companion count `M`.** Under
`OffLineCopiesLocallyBounded M`, the local companion count `P` in `zeta_near_top_cluster_collapse` is
replaced by the height-independent constant `M` (requiring no `80 log(180 Γ) ≤ P` hypothesis):
every companion in `T` is a strictly off-line zero (`Re ρ ≥ ½ + Re z₀ / 4 > ½`) in the unit-radius
window `|Im ρ − Im z₁| ≤ 1`, so `|C| ≤ M` uniformly in `γ₀ = Im z₀`. -/
theorem zeta_near_top_cluster_collapse_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im) {V : ℝ} (hV : 0 < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hneg : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re)
    {κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀)
    (hV2 : 2 * Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + M : ℕ) ≤ V)
    (hVr : 4 * π * (k + M : ℕ) ≤ V * (z₀.re / 8)) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      |z₁.im| ≤ recordHeightEnvelope w z₀.im ∧
      (∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V)) ∧
      ∃ C : Finset ℂ, z₁ ∉ C ∧ C.card ≤ M ∧
        (∀ z ∈ C, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
          ‖z - z₁‖ ≤ z₀.re / 8 + 2 * κ₀ / V) ∧
        (∀ z, z ≠ z₁ → evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 →
          ‖z - z₁‖ ≤ z₀.re / 8 - 2 * κ₀ / V → z ∈ C) ∧
        (∏ z ∈ C, ‖z - z₁‖) * (κ₀ / (2 * (M + 1))) ^ C.card * V ^ (2 * k + C.card + 1) *
            (z₀.re / 8) ^ (2 * k + 1) ≤ clusterCollapseBound w z₀.im κ₀ k C.card := by
  classical
  set b := modScaledBump w z₀.im with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set Γ := recordHeightEnvelope w z₀.im with hΓdef
  set r : ℝ := z₀.re / 8 with hr
  have hpos₀ : 0 < z₀.im := lt_of_lt_of_le (by unfold nearTopHeight; positivity) hTw
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1' : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith [hre₀1']
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · exact h
    · have := conj_mem_zetaZeroConfig h
      have e : conj (1 / 2 + conj x) = 1 / 2 + x := by apply Complex.ext <;> simp
      rwa [e] at this
  have htop' : ∀ z, D z ≠ 0 → z.re ≤ z₀.re + 1 / V := fun z hz => by
    have := htop _ (hmem z hz)
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    linarith
  obtain ⟨z₁, hz₁, hre₁, hlow, hup, hD₁, hrec⟩ :=
    near_top_record_facts hw hV hz₀ hre₀ hTw htop' hV2
  refine ⟨z₁, hz₁, hre₁, hup, hrec, ?_⟩
  have hκ₀0 : 0 < κ₀ := by linarith
  have h2κ : 2 * κ₀ / V ≤ r / 2 := by rw [hr]; linarith
  set R₀ : ℝ := r + 2 * κ₀ / V with hR₀
  set T : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b z₁ R₀).toFinset.erase z₁ with hT
  have hTcard : T.card ≤ M := by
    refine card_offLine_window_le_of_offLineCopiesLocallyBounded hM z₁.im T fun z hz => ?_
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset] at hz
    obtain ⟨-, hDz, hzr⟩ := hz
    refine ⟨hmem z hDz, ?_, ?_⟩
    · have h1 := Complex.abs_re_le_norm (z - z₁)
      rw [Complex.sub_re] at h1
      have h2 := neg_abs_le (z.re - z₁.re)
      have h3 : R₀ ≤ z₀.re / 4 := by rw [hR₀, hr]; linarith
      intro h0
      linarith
    · have h1 := Complex.abs_im_le_norm (z - z₁)
      rw [Complex.sub_im] at h1
      have h2 : R₀ ≤ 1 := by rw [hR₀]; linarith
      linarith
  obtain ⟨κ, hκ1, hκ2, hmirror⟩ := exists_depth_avoiding_mirrors T z₁ hTcard hκ₀0 hV
  set ε : ℝ := κ₀ / (2 * (M + 1) * V) with hε
  have hκ0 : 0 < κ := by linarith
  have hκV' : κ / V ≤ 2 * κ₀ / V := div_le_div_of_nonneg_right hκ2 hV.le
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hz₁s : ‖z₁ - s‖ = κ / V := by
    have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hκ0 hV)]
  set S : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b s r).toFinset with hS
  have hz₁S : z₁ ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]; exact ⟨hz₁, by rw [hz₁s]; linarith⟩
  have hSr : ∀ z ∈ S, ‖z - s‖ ≤ r := fun z hz => by
    rw [hS, Set.Finite.mem_toFinset] at hz; exact hz.2
  have hiso : ∀ z, z ∉ S → D z ≠ 0 → r ≤ ‖z - s‖ := fun z hz hDz => by
    rw [hS, Set.Finite.mem_toFinset] at hz
    by_contra h; push Not at h; exact hz ⟨hDz, h.le⟩
  have hST : S.erase z₁ ⊆ T := fun z hz => by
    rw [Finset.mem_erase] at hz
    have hzS := hz.2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset]
    refine ⟨hz.1, hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    have := hSr z hz.2
    rw [hR₀]; linarith
  set p := (S.erase z₁).card with hp
  have hpP : p ≤ M := (Finset.card_le_card hST).trans hTcard
  have hpP' : ((k + p : ℕ) : ℝ) ≤ (k + M : ℕ) := by exact_mod_cast (by omega : k + p ≤ k + M)
  have hrσ : r ≤ z₁.re - κ / V := by rw [hr] at h2κ ⊢; linarith
  have hεz : ∀ z ∈ S.erase z₁, ε ≤ ‖(z - s) + ((κ / V : ℝ) : ℂ)‖ := fun z hz => by
    have e : (z - s) + ((κ / V : ℝ) : ℂ) = (z - z₁) + ((2 * κ / V : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [hs]; ring
      · simp [hs]
    rw [e]; exact hmirror z (hST hz)
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hcol := zeta_full_cluster_collapse (contDiff_modScaledBump_two w _)
    (modScaledBump_support hw _) hneg hz₁ hrec hκ0 hr0 hr1 hrσ hk S hz₁S hSr hiso
    (le_trans (mul_le_mul_of_nonneg_left hpP' Real.pi_pos.le) hVk)
    (le_trans (mul_le_mul_of_nonneg_left hpP' (by positivity)) hVr) hε0 hεz
  rw [← hp] at hcol
  refine ⟨S.erase z₁, Finset.notMem_erase z₁ S, hpP, fun z hz => ?_, fun z hz1 hDz hzr => ?_, ?_⟩
  · have hzS := (Finset.mem_erase.mp hz).2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    refine ⟨hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    linarith [hzS.2]
  · refine Finset.mem_erase.mpr ⟨hz1, ?_⟩
    rw [hS, Set.Finite.mem_toFinset]
    refine ⟨hDz, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z z₁ s
    rw [hz₁s] at h1
    linarith
  rw [← hp]
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (180 * (|z₁.im| + 6)) := ⟨_, rfl⟩
  obtain ⟨LΓ, hLΓ⟩ : ∃ LΓ : ℝ, LΓ = Real.log (180 * (Γ + 6)) := ⟨_, rfl⟩
  have hθ0 : 0 < κ / V := div_pos hκ0 hV
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : ℝ, Q₂ = (4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (2 * (k + p)).factorial * (π / V) ^ (2 * (k + p)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos Real.pi_pos hV) _)
  have hbase : ∀ t : ℝ, 0 < t → 0 < t ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := fun t ht =>
    add_pos_of_pos_of_nonneg (pow_pos ht 2)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg π)) (sq_nonneg _))
  have hQ0 : 0 < Q := by rw [hQ]; exact pow_pos (hbase κ hκ0) _
  have hK : u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q) ≤
      ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (norm_fejerPowWin_ofReal_ge hV (k + p) hθ0)
    have hVne : V ≠ 0 := hV.ne'
    have hκne : κ ≠ 0 := hκ0.ne'
    have e : (κ / V) ^ 2 + (2 * π * ((k + p : ℕ) : ℝ) / V) ^ 2 =
        (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) / V ^ 2 := by
      field_simp; ring
    rw [e, div_mul_cancel₀ κ hVne, hu, hQ, div_pow, div_pow, ← pow_mul V 2 (k + p), pow_succ]
    field_simp
  rw [← hu] at hcol
  have hMW := mass_le_of_record_height hw hpos₀ hlow
  rw [← hL] at hMW hcol
  have hL0 : 0 ≤ L := by
    rw [hL]; exact Real.log_nonneg (by have := abs_nonneg z₁.im; linarith only [this])
  have hLL : L ≤ LΓ := by
    rw [hL, hLΓ]
    exact Real.log_le_log (by have := abs_nonneg z₁.im; positivity) (by linarith only [hup])
  have hκ1' : 1 ≤ κ := hκ₀.trans hκ1
  have hΞ := xi_ratio_le hw hκ1' hD₁ hL0 hMW
  have hQQ : κ * Q ≤ 2 * κ₀ * Q₂ := by
    have hq : Q ≤ Q₂ := by
      rw [hQ, hQ₂]
      refine pow_le_pow_left₀ (hbase κ hκ0).le ?_ _
      have h2 : κ ^ 2 ≤ (2 * κ₀) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [h2, e]
    exact mul_le_mul hκ2 hq hQ0.le (by linarith only [hκ₀0])
  have hA0 := twinTightConstant_nonneg hw
  have hE : 0 < Real.exp κ - 1 := by linarith only [Real.add_one_lt_exp hκ0.ne', hκ0]
  have hc0 : (0 : ℝ) ≤ (8 / 3) ^ p * (4 / 3) ^ k :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have hPr0 : 0 ≤ ∏ z ∈ S.erase z₁, ‖z - z₁‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hfin := cluster_log_arith (D := ‖D z₁‖) (u := u) (E := Real.exp κ - 1)
    (norm_pos_iff.mpr hz₁) hu0 hE hε0 hPr0 hr0 hV (mul_pos hκ0 hQ0) hcol hK hΞ hc0 hQQ
    (mul_nonneg hA0 hL0) (p := p) (m := 2 * (k + p) + 1) (k := k)
  have e : ε ^ p * V ^ (2 * (k + p) + 1) = (κ₀ / (2 * (M + 1))) ^ p * V ^ (2 * k + p + 1) := by
    have hVne : V ≠ 0 := hV.ne'
    rw [hε, show 2 * (k + p) + 1 = (2 * k + p + 1) + p by ring, pow_add, div_pow, div_pow, mul_pow]
    field_simp
  have hQ₂0 : 0 ≤ Q₂ := by
    rw [hQ₂]
    have : 0 < 4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := by
      have := hbase (2 * κ₀) (by linarith only [hκ₀0])
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [this, e]
    exact (pow_pos this _).le
  have h1 : twinTightConstant w * L ≤ twinTightConstant w * LΓ := mul_le_mul_of_nonneg_left hLL hA0
  have h2 : 0 ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) :=
    mul_nonneg hc0 (mul_nonneg (by linarith only [hκ₀0]) hQ₂0)
  calc (∏ z ∈ S.erase z₁, ‖z - z₁‖) * (κ₀ / (2 * (M + 1))) ^ p * V ^ (2 * k + p + 1) * r ^ (2 * k + 1)
      = (∏ z ∈ S.erase z₁, ‖z - z₁‖) * ε ^ p * V ^ (2 * (k + p) + 1) * r ^ (2 * k + 1) := by
        rw [mul_assoc (∏ z ∈ S.erase z₁, ‖z - z₁‖), ← e]; ring
    _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (twinTightConstant w * L) := hfin
    _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (twinTightConstant w * LΓ) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = clusterCollapseBound w z₀.im κ₀ k p := by
        rw [clusterCollapseBound, ← hΓdef, ← hLΓ, ← hQ₂]; ring

/-- **Near-top visibility with height-uniform companion count `M` and height-uniform core mass.**
Under `OffLineCopiesLocallyBounded M`, the companion count `P` in `zeta_near_top_visible` is
replaced by the height-independent constant `M` and the core mass bound by the height-independent
constant `2 M (e^{w/2} B_w)²`. -/
theorem zeta_near_top_visible_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im) {V : ℝ} (hV : 0 < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    {κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀)
    (hV2 : 2 * Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + M : ℕ) ≤ V)
    (hVr : 4 * π * (k + M : ℕ) ≤ V * (z₀.re / 8)) {H₀ : ℝ} (hH₀ : 0 < H₀)
    (hH : H₀ ^ 2 ≤ centerAmplitude w ^ 2 / (2 * Real.exp 1) /
        (40 * Real.log (180 * recordHeightEnvelope w z₀.im)) -
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4)
    (hK : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4 ≤ H₀ ^ 2 / 16)
    {ρ G : ℝ} (hρ : 0 < ρ) (hG : 1 ≤ G) (hρV : ρ * V ≤ 1) (hρw : w * ρ ≤ 1)
    (hρL : 8 * w * Real.exp (w / 2) * bumpMass w * ρ ≤ H₀) (hρr : ρ ≤ z₀.re / 16)
    (hη : ((1 + coreFactorPerturbation M κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation M κ₀ V ρ G) * ((M + 1) * (2 * M *
          (Real.exp (w / 2) * scaledBumpDecay w) ^ 2)) ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) / 2)
    (hmain : ∀ p : ℕ, p ≤ M → 2 * clusterCollapseBound w z₀.im κ₀ k p <
      (ρ * κ₀ / (2 * (M + 1) * G ^ M)) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1)) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re < 0 := by
  by_contra hneg
  push Not at hneg
  classical
  set b := modScaledBump w z₀.im with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set Γ := recordHeightEnvelope w z₀.im with hΓdef
  set r : ℝ := z₀.re / 8 with hr
  have hpos₀ : 0 < z₀.im := lt_of_lt_of_le (by unfold nearTopHeight; positivity) hTw
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1' : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith [hre₀1']
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · exact h
    · have := conj_mem_zetaZeroConfig h
      have e : conj (1 / 2 + conj x) = 1 / 2 + x := by apply Complex.ext <;> simp
      rwa [e] at this
  have htop' : ∀ z, D z ≠ 0 → z.re ≤ z₀.re + 1 / V := fun z hz => by
    have := htop _ (hmem z hz)
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    linarith
  obtain ⟨z₁, hz₁, hre₁, hlow, hup, hD₁, hrec⟩ :=
    near_top_record_facts hw hV hz₀ hre₀ hTw htop' hV2
  have hκ₀0 : 0 < κ₀ := by linarith
  have h2κ : 2 * κ₀ / V ≤ r / 2 := by rw [hr]; linarith
  set R₀ : ℝ := r + 2 * κ₀ / V with hR₀
  set T : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b z₁ R₀).toFinset.erase z₁ with hT
  have hTcard : T.card ≤ M := by
    refine card_offLine_window_le_of_offLineCopiesLocallyBounded hM z₁.im T fun z hz => ?_
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset] at hz
    obtain ⟨-, hDz, hzr⟩ := hz
    refine ⟨hmem z hDz, ?_, ?_⟩
    · have h1 := Complex.abs_re_le_norm (z - z₁)
      rw [Complex.sub_re] at h1
      have h2 := neg_abs_le (z.re - z₁.re)
      have h3 : R₀ ≤ z₀.re / 4 := by rw [hR₀, hr]; linarith
      intro h0
      linarith
    · have h1 := Complex.abs_im_le_norm (z - z₁)
      rw [Complex.sub_im] at h1
      have h2 : R₀ ≤ 1 := by rw [hR₀]; linarith
      linarith
  obtain ⟨κ, hκ1, hκ2, hmirror⟩ := exists_depth_avoiding_mirrors T z₁ hTcard hκ₀0 hV
  set ε : ℝ := κ₀ / (2 * (M + 1) * V) with hε
  have hκ0 : 0 < κ := by linarith
  have hκV' : κ / V ≤ 2 * κ₀ / V := div_le_div_of_nonneg_right hκ2 hV.le
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hz₁s : ‖z₁ - s‖ = κ / V := by
    have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hκ0 hV)]
  set S : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b s r).toFinset with hS
  have hz₁S : z₁ ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]; exact ⟨hz₁, by rw [hz₁s]; linarith⟩
  have hSr : ∀ z ∈ S, ‖z - s‖ ≤ r := fun z hz => by
    rw [hS, Set.Finite.mem_toFinset] at hz; exact hz.2
  have hiso : ∀ z, z ∉ S → D z ≠ 0 → r ≤ ‖z - s‖ := fun z hz hDz => by
    rw [hS, Set.Finite.mem_toFinset] at hz
    by_contra h; push Not at h; exact hz ⟨hDz, h.le⟩
  have hST : S.erase z₁ ⊆ T := fun z hz => by
    rw [Finset.mem_erase] at hz
    have hzS := hz.2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset]
    refine ⟨hz.1, hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    have := hSr z hz.2
    rw [hR₀]; linarith
  have hrσ : r ≤ z₁.re - κ / V := by rw [hr] at h2κ ⊢; linarith
  obtain ⟨j, hjP, hann⟩ := exists_empty_annulus T z₁ hTcard hρ hG
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = ρ / G ^ (j + 1) := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = ρ / G ^ j := ⟨_, rfl⟩
  rw [← hρ₀, ← hρ₁] at hann
  have hG0 : 0 < G := by linarith only [hG]
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hρ₀ρ : ρ₀ ≤ ρ := by rw [hρ₀]; exact div_le_self hρ.le (one_le_pow₀ hG)
  have hρ₁ρ₀ : ρ₁ = G * ρ₀ := by rw [hρ₁, hρ₀, pow_succ]; field_simp
  have hρ₁P : ρ / G ^ M ≤ ρ₁ := by
    rw [hρ₁]; exact div_le_div_of_nonneg_left hρ.le (by positivity) (pow_le_pow_right₀ hG hjP)
  obtain ⟨SL, hSL⟩ : ∃ SL : Finset ℂ, SL = (S.erase z₁).filter fun z => ρ₁ < ‖z - z₁‖ :=
    ⟨_, rfl⟩
  have hSLmem : ∀ z, z ∈ SL ↔ (z ≠ z₁ ∧ z ∈ S) ∧ ρ₁ < ‖z - z₁‖ := fun z => by
    rw [hSL, Finset.mem_filter, Finset.mem_erase]
  have hSLS : SL ⊆ S := fun z hz => ((hSLmem z).mp hz).1.2
  have hSLT : SL ⊆ T := fun z hz => hST (Finset.mem_erase.mpr ((hSLmem z).mp hz).1)
  have hpP : SL.card ≤ M := (Finset.card_le_card hSLT).trans hTcard
  have hpP' : ((k + SL.card : ℕ) : ℝ) ≤ (k + M : ℕ) := by exact_mod_cast (by omega : k + SL.card ≤ k + M)
  have hPE := zeta_partial_elimination_le (contDiff_modScaledBump_two w _)
    (modScaledBump_support hw _) hneg hz₁ hrec hκ0 hr0 hr1 hrσ hk S SL hSLS hSr hiso
    (le_trans (mul_le_mul_of_nonneg_left hpP' Real.pi_pos.le) hVk)
    (le_trans (mul_le_mul_of_nonneg_left hpP' (by positivity)) hVr)
  rw [← hs] at hPE
  have hz₁C : z₁ ∈ S.filter fun z => z ∉ SL :=
    Finset.mem_filter.mpr ⟨hz₁S, fun h => ((hSLmem z₁).mp h).1.1 rfl⟩
  have hcρ₀ : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖c - z₁‖ ≤ ρ₀ := fun c hc => by
    obtain ⟨hcS, hcL⟩ := Finset.mem_filter.mp hc
    by_cases hne : c = z₁
    · rw [hne, sub_self, norm_zero]; exact hρ₀0.le
    · rcases hann c (hST (Finset.mem_erase.mpr ⟨hne, hcS⟩)) with h | h
      · exact h
      · exact absurd ((hSLmem c).mpr ⟨⟨hne, hcS⟩, h⟩) hcL
  have hcρ : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖c - z₁‖ ≤ ρ := fun c hc => (hcρ₀ c hc).trans hρ₀ρ
  have hθc : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
  have hε0' : 0 < ε := by rw [hε]; positivity
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁ρ₀]; positivity
  have hbig : ∀ y ∈ SL, ρ₁ * ε ≤ ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖ := fun y hy => by
    have e : (y - s) ^ 2 - (z₁ - s) ^ 2 = (y - z₁) * ((y - z₁) + ((2 * κ / V : ℝ) : ℂ)) := by
      have e1 : y - s = (y - z₁) + ((κ / V : ℝ) : ℂ) := by rw [← hθc]; ring
      rw [e1, hθc]; push_cast; ring
    rw [e, norm_mul]
    exact mul_le_mul ((hSLmem y).mp hy).2.le (hmirror y (hSLT hy)) hε0'.le (norm_nonneg _)
  have hγ₀1 : 1 ≤ z₀.im := le_trans (by
    unfold nearTopHeight
    have : 0 ≤ 700000 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2 := by
      positivity
    linarith only [this]) hTw
  have hDS : ∀ c ∈ S, D c ≠ 0 := fun c hc => by
    rw [hS, Set.Finite.mem_toFinset] at hc; exact hc.1
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hcoh : ∀ c ∈ S.filter (fun z => z ∉ SL), 0 ≤ (D c * conj (D z₁)).re := fun c hc => by
    have hcS := (Finset.mem_filter.mp hc).1
    have hcz := hcρ c hc
    exact re_twin_mul_conj_nonneg hw hγ₀1 (hmem z₁ hz₁) (hmem c (hDS c hcS)) hlow
      (by linarith only [hcz, hρr, hre₀1']) hH₀ hup hD₁ hH hK
      (le_trans (mul_le_mul_of_nonneg_left hcz (mul_nonneg (by positivity) hJ0)) hρL)
      (le_trans (mul_le_mul_of_nonneg_left hcz hw.le) hρw)
  obtain ⟨Dm, hDm⟩ : ∃ Dm : ℝ,
      Dm = 2 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := ⟨_, rfl⟩
  rw [← hDm] at hη
  have hDc : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤ Dm := fun c hc => by
    have hcz := hcρ c hc
    have h1 := Complex.abs_re_le_norm (c - z₁)
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (c.re - z₁.re)
    have hcre : c.re ≠ 0 := by intro h0; linarith
    rw [hDm]
    exact norm_evenCoeff_modScaledBump_le_of_offLineCopiesLocallyBounded hM hw z₀.im hcre
  have hCcard : (S.filter fun z => z ∉ SL).card ≤ M + 1 :=
    (Finset.card_filter_le _ _).trans (by
      rw [← Finset.card_erase_add_one hz₁S]
      exact Nat.succ_le_succ ((Finset.card_le_card hST).trans hTcard))
  have hsumD : ∑ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤ (M + 1) * Dm := by
    have h := Finset.sum_le_card_nsmul _ (fun c => ‖D c‖) Dm hDc
    rw [nsmul_eq_mul] at h
    have hD0 : 0 ≤ Dm := le_trans (norm_nonneg _) (hDc z₁ hz₁C)
    have hc : ((S.filter fun z => z ∉ SL).card : ℝ) ≤ M + 1 := by exact_mod_cast hCcard
    exact h.trans (mul_le_mul_of_nonneg_right hc hD0)
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = (4 * κ₀ / V + ρ) * (2 * (M + 1) * V) / (G * κ₀) := ⟨_, rfl⟩
  have ht₀0 : 0 ≤ t₀ := by rw [ht₀]; positivity
  have hτ : (1 + t₀) ^ SL.card - 1 ≤ coreFactorPerturbation M κ₀ V ρ G := by
    rw [coreFactorPerturbation, ← ht₀]
    have := pow_le_pow_right₀ (by linarith only [ht₀0] : (1 : ℝ) ≤ 1 + t₀) hpP
    linarith only [this]
  have hτ0 : 0 ≤ coreFactorPerturbation M κ₀ V ρ G := by
    have := one_le_pow₀ (n := SL.card) (by linarith only [ht₀0] : (1 : ℝ) ≤ 1 + t₀)
    linarith only [this, hτ]
  have hmass : ((1 + coreFactorPerturbation M κ₀ V ρ G) * (2 * (ρ * V)) +
      coreFactorPerturbation M κ₀ V ρ G) * ∑ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤
        ‖D z₁‖ / 2 := by
    have hη0 : 0 ≤ (1 + coreFactorPerturbation M κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation M κ₀ V ρ G := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsumD hη0
    linarith only [h1, hη, hD₁]
  have hgap : ρ₀ * (2 * (κ / V) + ρ₀) ≤ t₀ * (ρ₁ * ε) := by
    rw [ht₀, hρ₁ρ₀, hε]
    exact core_gap_arith hρ₀0.le hρ₀ρ hG0 hκ₀0 hV (Nat.cast_nonneg M) hκ2
  have hθ0 : 0 < κ / V := div_pos hκ0 hV
  have hcore_ge := eliminated_core_ge hz₁C D (k + SL.card) hV hθc hθ0.le hρ₀0.le
    (mul_pos hρ₁0 hε0') hbig hcρ₀ hgap hτ (mul_le_mul_of_nonneg_right hρ₀ρ hV.le) hρV hcoh hmass
  have hcol := hcore_ge.trans hPE
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = SL.card := ⟨_, rfl⟩
  rw [← hp] at hcol hpP
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (180 * (|z₁.im| + 6)) := ⟨_, rfl⟩
  obtain ⟨LΓ, hLΓ⟩ : ∃ LΓ : ℝ, LΓ = Real.log (180 * (Γ + 6)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : ℝ, Q₂ = (4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (2 * (k + p)).factorial * (π / V) ^ (2 * (k + p)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos Real.pi_pos hV) _)
  have hbase : ∀ t : ℝ, 0 < t → 0 < t ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := fun t ht =>
    add_pos_of_pos_of_nonneg (pow_pos ht 2)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg π)) (sq_nonneg _))
  have hQ0 : 0 < Q := by rw [hQ]; exact pow_pos (hbase κ hκ0) _
  have hKlow : u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q) ≤
      ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (norm_fejerPowWin_ofReal_ge hV (k + p) hθ0)
    have hVne : V ≠ 0 := hV.ne'
    have hκne : κ ≠ 0 := hκ0.ne'
    have e : (κ / V) ^ 2 + (2 * π * ((k + p : ℕ) : ℝ) / V) ^ 2 =
        (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) / V ^ 2 := by
      field_simp; ring
    rw [e, div_mul_cancel₀ κ hVne, hu, hQ, div_pow, div_pow, ← pow_mul V 2 (k + p), pow_succ]
    field_simp
  rw [← hu] at hcol
  have hMW := mass_le_of_record_height hw hpos₀ hlow
  rw [← hL] at hMW hcol
  have hL0 : 0 ≤ L := by
    rw [hL]; exact Real.log_nonneg (by have := abs_nonneg z₁.im; linarith only [this])
  have hLL : L ≤ LΓ := by
    rw [hL, hLΓ]
    exact Real.log_le_log (by have := abs_nonneg z₁.im; positivity) (by linarith only [hup])
  have hκ1' : 1 ≤ κ := hκ₀.trans hκ1
  have hΞ := xi_ratio_le hw hκ1' hD₁ hL0 hMW
  have hQQ : κ * Q ≤ 2 * κ₀ * Q₂ := by
    have hq : Q ≤ Q₂ := by
      rw [hQ, hQ₂]
      refine pow_le_pow_left₀ (hbase κ hκ0).le ?_ _
      have h2 : κ ^ 2 ≤ (2 * κ₀) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [h2, e]
    exact mul_le_mul hκ2 hq hQ0.le (by linarith only [hκ₀0])
  have hA0 := twinTightConstant_nonneg hw
  have hE : 0 < Real.exp κ - 1 := by linarith only [Real.add_one_lt_exp hκ0.ne', hκ0]
  have hc0 : (0 : ℝ) ≤ (8 / 3) ^ p * (4 / 3) ^ k :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have hPr0 : 0 ≤ ρ₁ ^ p / 2 := by positivity
  have hcol' : ‖D z₁‖ * (ρ₁ ^ p / 2) * ε ^ p * ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ ≤
      u * ((8 / 3) ^ p * (4 / 3) ^ k *
        (4 * |2 * (lagStructure zetaZeroConfig b 0).re| + 4 * (∑' z : ℂ, ‖D z‖) +
          3840 * L * ‖D z₁‖ * Real.exp κ) / r ^ (2 * k + 1)) :=
    le_trans (le_of_eq (by rw [mul_pow]; ring)) hcol
  have hfin := cluster_log_arith (D := ‖D z₁‖) (u := u) (E := Real.exp κ - 1)
    (norm_pos_iff.mpr hz₁) hu0 hE hε0'.le hPr0 hr0 hV (mul_pos hκ0 hQ0) hcol' hKlow hΞ hc0 hQQ
    (mul_nonneg hA0 hL0) (p := p) (m := 2 * (k + p) + 1) (k := k)
  have e : ε ^ p * V ^ (2 * (k + p) + 1) = (κ₀ / (2 * (M + 1))) ^ p * V ^ (2 * k + p + 1) := by
    have hVne : V ≠ 0 := hV.ne'
    rw [hε, show 2 * (k + p) + 1 = (2 * k + p + 1) + p by ring, pow_add, div_pow, div_pow, mul_pow]
    field_simp
  have hQ₂0 : 0 ≤ Q₂ := by
    rw [hQ₂]
    have : 0 < 4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := by
      have := hbase (2 * κ₀) (by linarith only [hκ₀0])
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [this, e]
    exact (pow_pos this _).le
  have h1 : twinTightConstant w * L ≤ twinTightConstant w * LΓ := mul_le_mul_of_nonneg_left hLL hA0
  have h2 : 0 ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) :=
    mul_nonneg hc0 (mul_nonneg (by linarith only [hκ₀0]) hQ₂0)
  have hb : (ρ₁ ^ p * (κ₀ / (2 * (M + 1))) ^ p) / 2 * (V ^ (2 * k + p + 1) * r ^ (2 * k + 1)) ≤
      clusterCollapseBound w z₀.im κ₀ k p :=
    calc (ρ₁ ^ p * (κ₀ / (2 * (M + 1))) ^ p) / 2 * (V ^ (2 * k + p + 1) * r ^ (2 * k + 1))
        = ρ₁ ^ p / 2 * (ε ^ p * V ^ (2 * (k + p) + 1)) * r ^ (2 * k + 1) := by rw [e]; ring
      _ = ρ₁ ^ p / 2 * ε ^ p * V ^ (2 * (k + p) + 1) * r ^ (2 * k + 1) := by ring
      _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (twinTightConstant w * L) := hfin
      _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (twinTightConstant w * LΓ) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = clusterCollapseBound w z₀.im κ₀ k p := by
          rw [clusterCollapseBound, ← hΓdef, ← hLΓ, ← hQ₂]; ring
  have hab : (ρ * κ₀ / (2 * (M + 1) * G ^ M)) ^ p ≤ ρ₁ ^ p * (κ₀ / (2 * (M + 1))) ^ p := by
    rw [← mul_pow]
    have e2 : ρ * κ₀ / (2 * (M + 1) * G ^ M) = ρ / G ^ M * (κ₀ / (2 * (M + 1))) := by
      field_simp
    refine pow_le_pow_left₀ (by positivity) ?_ p
    rw [e2]
    exact mul_le_mul_of_nonneg_right hρ₁P (by positivity)
  exact visible_final_arith hab (by positivity) hb (hmain p hpP)

/-! ### 3. Height-uniform Castelnuovo–Severi degree-defect floor and zero-width equivalence -/

/-- **Castelnuovo–Severi defect floor under `OffLineDensityBound`.** On `scalingSurface`, every
on-line zero of `ζ` contributes a nonnegative square `m_ρ ‖h_f(γ_ρ)‖² ≥ 0` to the Weil form, so
only off-line zeros can make the Castelnuovo–Severi defect negative. Under
`OffLineDensityBound zetaZeroConfig D`, for every degree `r ≥ 0`, every subspace `V ≤ realTestsAt r`
(both even and odd cycles), and every cycle `x : ℝ × ℝ × V`,
`−3500 (2r + 3) D e^{2·zetaZeroWidth·(r + 2)} ∫ f² ≤ (scalingSubsurface V).defect x x`. -/
theorem scalingSubsurface_defect_ge_of_offLineDensityBound {D r : ℝ}
    (hD : RHTower.OffLineDensityBound zetaZeroConfig D) (hr : 0 ≤ r)
    (V : Submodule ℝ realTests) (hV : V ≤ realTestsAt r) (x : ℝ × ℝ × V) :
    -(3500 * (2 * r + 3) * D * Real.exp (2 * zetaZeroWidth * (r + 2)) *
        ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
      (scalingSubsurface V).defect x x := by
  rw [scalingSubsurface_defect_self, weilPair_self_eq_zeta_W_re x.2.2.1.2.1 x.2.2.1.2.2,
    ← integral_norm_cx_sq]
  have hη : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ zetaZeroWidth := fun _ hρ =>
    abs_re_sub_half_le_zetaZeroWidth hρ
  have hf : Continuous (cx (x.2.2.1 : ℝ → ℝ)) := (cx_contDiff x.2.2.1.2.1).continuous
  have hsupp : ∀ u : ℝ, cx (x.2.2.1 : ℝ → ℝ) u ≠ 0 → |u| ≤ r := by
    intro u hu
    have hu' : (x.2.2.1 : ℝ → ℝ) u ≠ 0 := by
      simp only [cx, ne_eq, Complex.ofReal_eq_zero] at hu
      exact hu
    exact abs_le.mpr (hV x.2.2.2 (subset_tsupport _ hu'))
  exact RHTower.re_W_ge_of_depth_offLineDensity zetaZeroConfig zetaZeroWidth_nonneg hη hD hr
    hf hsupp

/-- **Castelnuovo–Severi defect floor under `OffLineCopiesLocallyBounded`.** Under
`OffLineCopiesLocallyBounded M`, for every degree `r ≥ 0`, every subspace `V ≤ realTestsAt r`, and
every cycle `x : ℝ × ℝ × V`,
`−3500 (2r + 3) M e^{2·zetaZeroWidth·(r + 2)} ∫ f² ≤ (scalingSubsurface V).defect x x`. -/
theorem scalingSubsurface_defect_ge_of_offLineCopiesLocallyBounded {M : ℕ} {r : ℝ}
    (hM : OffLineCopiesLocallyBounded M) (hr : 0 ≤ r)
    (V : Submodule ℝ realTests) (hV : V ≤ realTestsAt r) (x : ℝ × ℝ × V) :
    -(3500 * (2 * r + 3) * M * Real.exp (2 * zetaZeroWidth * (r + 2)) *
        ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
      (scalingSubsurface V).defect x x :=
  scalingSubsurface_defect_ge_of_offLineDensityBound
    (offLineDensityBound_zeta_of_offLineCopiesLocallyBounded hM) hr V hV x

/-- **Pure exponential Castelnuovo–Severi defect floor at every rate `θ > zetaZeroWidth` under
`OffLineDensityBound`.** -/
theorem exists_scalingSubsurface_defect_floor_of_offLineDensityBound {D : ℝ}
    (hD : RHTower.OffLineDensityBound zetaZeroConfig D) {θ : ℝ} (hθ : zetaZeroWidth < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ V : Submodule ℝ realTests, V ≤ realTestsAt r →
      ∀ x : ℝ × ℝ × V,
        -(C * Real.exp (2 * θ * r) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
          (scalingSubsurface V).defect x x := by
  set ε := θ - zetaZeroWidth with hε
  have hε0 : 0 < ε := by linarith
  have hD0 : 0 ≤ D := hD.nonneg
  refine ⟨3500 * (1 / ε + 3) * D * Real.exp (4 * zetaZeroWidth), by positivity,
    fun r hr V hV x => ?_⟩
  refine le_trans ?_ (scalingSubsurface_defect_ge_of_offLineDensityBound hD hr.le V hV x)
  apply neg_le_neg
  have hI0 : 0 ≤ ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hexp1 : 2 * ε * r + 1 ≤ Real.exp (2 * ε * r) := Real.add_one_le_exp _
  have hexp2 : 1 ≤ Real.exp (2 * ε * r) := Real.one_le_exp (by positivity)
  have hlin : 2 * r + 3 ≤ (1 / ε + 3) * Real.exp (2 * ε * r) := by
    have h1 : 2 * r ≤ 1 / ε * Real.exp (2 * ε * r) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hε0]
      nlinarith
    nlinarith
  have hsplit : Real.exp (2 * θ * r) = Real.exp (2 * ε * r) * Real.exp (2 * zetaZeroWidth * r) := by
    rw [← Real.exp_add]; congr 1; rw [hε]; ring
  have hsplit2 : Real.exp (2 * zetaZeroWidth * (r + 2)) =
      Real.exp (4 * zetaZeroWidth) * Real.exp (2 * zetaZeroWidth * r) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, hsplit2]
  calc 3500 * (2 * r + 3) * D *
        (Real.exp (4 * zetaZeroWidth) * Real.exp (2 * zetaZeroWidth * r)) *
        ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2
      ≤ 3500 * ((1 / ε + 3) * Real.exp (2 * ε * r)) * D *
          (Real.exp (4 * zetaZeroWidth) * Real.exp (2 * zetaZeroWidth * r)) *
          ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 := by gcongr
    _ = 3500 * (1 / ε + 3) * D * Real.exp (4 * zetaZeroWidth) *
          (Real.exp (2 * ε * r) * Real.exp (2 * zetaZeroWidth * r)) *
          ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2 := by ring

/-- **Height-Uniform Castelnuovo–Severi Zero-Width Equivalence under `OffLineDensityBound`.**
Under `OffLineDensityBound zetaZeroConfig D`, for every `σ ≥ 0`, `zetaZeroWidth ≤ σ` holds if and
only if for every `θ > σ` there is a constant `C` such that
`δ(x, x) ≥ −C e^{2θr} ∫ f²` on `scalingSubsurface (oddRealTestsAt r)` at every degree `r > 0`. -/
theorem zetaZeroWidth_le_iff_scalingSubsurface_odd_defect_floor_of_offLineDensityBound {D : ℝ}
    (hD : RHTower.OffLineDensityBound zetaZeroConfig D) {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔
      ∀ θ : ℝ, σ < θ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
        -(C * Real.exp (2 * θ * r) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
          (scalingSubsurface (oddRealTestsAt r)).defect x x := by
  constructor
  · intro hle θ hθ
    obtain ⟨C, -, hC⟩ :=
      exists_scalingSubsurface_defect_floor_of_offLineDensityBound hD (lt_of_le_of_lt hle hθ)
    exact ⟨C, fun r hr x => hC r hr (oddRealTestsAt r) (fun _ hf => hf.1) x⟩
  · intro hfloor
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, hC⟩ := hfloor (σ + ε) (by linarith)
    exact zetaZeroWidth_le_of_scalingSubsurface_odd_defect_floor (by linarith) hC

/-- **Height-Uniform Castelnuovo–Severi Zero-Width Equivalence under
`OffLineCopiesLocallyBounded`.** -/
theorem zetaZeroWidth_le_iff_scalingSubsurface_odd_defect_floor_of_offLineCopiesLocallyBounded
    {M : ℕ} (hM : OffLineCopiesLocallyBounded M) {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔
      ∀ θ : ℝ, σ < θ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
        -(C * Real.exp (2 * θ * r) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
          (scalingSubsurface (oddRealTestsAt r)).defect x x :=
  zetaZeroWidth_le_iff_scalingSubsurface_odd_defect_floor_of_offLineDensityBound
    (offLineDensityBound_zeta_of_offLineCopiesLocallyBounded hM) hσ

/-! ### 4. The unconditional clustering alternative on the scaling surface -/

/-- **Unconditional Clustering Alternative on the Scaling Surface.** For the scaling surface of
`ℤ`, either:
1. the Castelnuovo–Severi degree-defect exponent on `scalingSubsurface (oddRealTestsAt r)` and the
   polar ground-energy exponent `polarGroundEnergyRate` both equal `zetaZeroWidth`, or
2. the off-line divisor copies of `ξ` cluster without bound in unit height windows
   (`∀ M, ¬ OffLineCopiesLocallyBounded M`), which forces infinitely many off-line divisor copies of
   `ξ`. -/
theorem scalingSurface_defectRate_eq_zetaZeroWidth_or_offLine_cluster :
    ((polarGroundEnergyRate = zetaZeroWidth ∧
      ∀ θ : ℝ, zetaZeroWidth < θ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
        -(C * Real.exp (2 * θ * r) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
          (scalingSubsurface (oddRealTestsAt r)).defect x x) ∨
    ((∀ M : ℕ, ¬ OffLineCopiesLocallyBounded M) ∧
      {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Infinite)) := by
  by_cases hM : ∃ M : ℕ, OffLineCopiesLocallyBounded M
  · obtain ⟨M, hM⟩ := hM
    left
    exact ⟨polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded hM,
      (zetaZeroWidth_le_iff_scalingSubsurface_odd_defect_floor_of_offLineCopiesLocallyBounded hM
        zetaZeroWidth_nonneg).mp le_rfl⟩
  · right
    push Not at hM
    exact ⟨hM, fun hfin => hM _ (offLineCopiesLocallyBounded_of_finite hfin)⟩

/-- **Finite off-line regime on the scaling surface.** When the off-line divisor copies of `ξ` are
finite and nonempty, `polarGroundEnergyRate = zetaZeroWidth`, the Castelnuovo–Severi degree-defect
floor holds at every rate `θ > zetaZeroWidth`, and there is a threshold aperture `A` beyond which
the restricted Weil ground energy obeys two-sided exponential bounds
`c e^{2·zetaZeroWidth·a} ≤ −μ(a) ≤ C e^{2·zetaZeroWidth·a}` (`c > 0`). -/
theorem exists_scalingSubsurface_defect_floor_and_groundEnergy_bounds_of_finite_offLine
    (h : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite)
    (hne : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Nonempty) :
    polarGroundEnergyRate = zetaZeroWidth ∧
      (∀ θ : ℝ, zetaZeroWidth < θ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
        -(C * Real.exp (2 * θ * r) * ∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) ≤
          (scalingSubsurface (oddRealTestsAt r)).defect x x) ∧
      ∃ c C A : ℝ, 0 < c ∧ ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
        c * Real.exp (2 * zetaZeroWidth * a.1) ≤ -ccmRestrictedWeilGroundEnergy a ∧
          -ccmRestrictedWeilGroundEnergy a ≤ C * Real.exp (2 * zetaZeroWidth * a.1) := by
  have hM := offLineCopiesLocallyBounded_of_finite h
  exact ⟨polarGroundEnergyRate_eq_zetaZeroWidth_of_finite_offLine h,
    (zetaZeroWidth_le_iff_scalingSubsurface_odd_defect_floor_of_offLineCopiesLocallyBounded hM
      zetaZeroWidth_nonneg).mp le_rfl,
    exists_groundEnergy_exponential_bounds_of_finite_offLine h hne⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
