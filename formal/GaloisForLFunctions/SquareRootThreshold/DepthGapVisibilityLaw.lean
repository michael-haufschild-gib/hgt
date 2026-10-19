import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw

/-!
# The depth-gap visibility law

Let `Z` be a zero configuration with local count `N(t, t+1] ≤ A₀ log(|t| + 3)`, and let
`ρ₀ = ½ + δ + iγ₀` be a zero of depth `δ > 0`. Suppose every other zero `ρ ≠ ρ₀, 1 − ρ̄₀` with
`|γ_ρ − γ₀| ≤ R` has depth at most `δ'`. Test with `e^{−iγ₀u} s(u)`, where `s` is real, odd,
`C²` and supported in `[-a, a]`. Then
`Re W ≤ −2 m_{ρ₀} P² + 384 A₀ log(|γ₀| + 3) N² (e^{2δ'a} + e^a/(1 + R))`,
with `P = ∫ s(u) sinh(δu)` and `N = ‖s‖₁ + ‖s''‖₁` (`re_W_modulatedTest_le_of_depthGap`).

For the explicit test `sinh(δu)(a² − u²)₊^{5/2}`: `P ≍ e^{2δa}` and `N² ≍ e^{2δa}`, up to powers of
`a`. So the zero becomes visible as soon as the depth gap satisfies
`2(δ − δ')a ≳ log(A₀ log γ₀) + O(log a)` (`exists_re_W_neg_of_depthGap_deep_zero`).

**Consequences.**
* `δ' = 0` is the isolated law `RHTower.re_W_modulatedTest_le_of_isolated`.
* The off-line lattice pair, which is invisible below the Nyquist aperture, is the case
  `δ' = δ`: there is no gap.
* Contrapositively (`zeta_weil_positive_forces_deep_companion`), if `ζ` is Weil-nonnegative at
  aperture `a`, then every zero of depth `δ` has a companion within ordinate distance `R`, other
  than its reflection, of depth greater than `δ'`. This holds whenever the size condition holds.
  Positivity tolerates off-line zeros only in clusters of comparable depth.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- Weight bound for the zeros other than the deep pair, under a depth gap. -/
theorem norm_Wsummand_modulatedTest_le_depthGap (Z : ZeroConfig) (γ₀ : ℝ) {s : ℝ → ℝ}
    {a R δ' : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (hs : ContDiff ℝ 2 s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hgap : |ρ.im - γ₀| ≤ R → |ρ.re - 1 / 2| ≤ δ') :
    ‖Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) ρ‖ ≤
      16 * testNorm s ^ 2 * (Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R)) *
        ((Z.mult ρ : ℝ) / (1 + |ρ.im - γ₀|) ^ 3) := by
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hN := testNorm_nonneg s
  set K := Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R) with hK
  have hR0 : 0 < 1 + R := by linarith
  set D := 1 + |ρ.im - γ₀| with hD
  have hD1 : 1 ≤ D := by linarith [abs_nonneg (ρ.im - γ₀)]
  have hD0 : 0 < D := by linarith
  refine (norm_Wsummand_modulatedTest_le Z γ₀ hs hsupp ρ).trans ?_
  rw [div_le_iff₀ (by positivity)]
  rcases le_or_gt |ρ.im - γ₀| R with hnear | hfar
  · have hdep : |1 / 2 - ρ.re| ≤ δ' := by rw [abs_sub_comm]; exact hgap hnear
    have hE : Real.exp (|1 / 2 - ρ.re| * a) ^ 2 ≤ K := by
      have h1 : Real.exp (|1 / 2 - ρ.re| * a) ^ 2 ≤ Real.exp (δ' * a) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdep ha)) 2
      have h2 : 0 ≤ Real.exp a / (1 + R) := by positivity
      rw [hK]
      linarith
    have hD34 : D ^ 3 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
    have h3' : 0 ≤ (Z.mult ρ : ℝ) / D ^ 3 := by positivity
    calc (Z.mult ρ : ℝ) * (Real.exp (|1 / 2 - ρ.re| * a) ^ 2 * (16 * testNorm s ^ 2))
        ≤ (Z.mult ρ : ℝ) * (K * (16 * testNorm s ^ 2)) := by gcongr
      _ = 16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / D ^ 3) * D ^ 3 := by
          field_simp
      _ ≤ 16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / D ^ 3) * D ^ 4 := by gcongr
  · have hE := exp_abs_half_sub_sq_le (Z.strip ρ hρ) ha
    have hDR : 1 + R ≤ D := by rw [hD]; linarith
    have h1' : Real.exp a / (1 + R) ≤ K := by
      rw [hK]
      linarith [pow_nonneg (Real.exp_pos (δ' * a)).le 2]
    have h3' : 0 ≤ (Z.mult ρ : ℝ) / D ^ 3 := by positivity
    calc (Z.mult ρ : ℝ) * (Real.exp (|1 / 2 - ρ.re| * a) ^ 2 * (16 * testNorm s ^ 2))
        ≤ (Z.mult ρ : ℝ) * (Real.exp a * (16 * testNorm s ^ 2)) := by gcongr
      _ = 16 * testNorm s ^ 2 * (Real.exp a / (1 + R)) * ((Z.mult ρ : ℝ) / D ^ 3) *
            ((1 + R) * D ^ 3) := by
          field_simp
      _ ≤ 16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / D ^ 3) * ((1 + R) * D ^ 3) := by
          gcongr
      _ ≤ 16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / D ^ 3) * (D * D ^ 3) := by
          gcongr
      _ = 16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / D ^ 3) * D ^ 4 := by ring

/-- **The depth-gap inequality.** If every zero other than `ρ₀, 1 − ρ̄₀` within ordinate distance
`R` of `ρ₀` has depth at most `δ'`, then
`Re W ≤ −2 m_{ρ₀} P² + 384 A₀ log(|γ₀| + 3) N² (e^{2δ'a} + e^a/(1 + R))`. -/
theorem re_W_modulatedTest_le_of_depthGap (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {a R δ' : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hgap : ∀ ρ ∈ Z.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.im - ρ₀.im| ≤ R →
      |ρ.re - 1 / 2| ≤ δ')
    {s : ℝ → ℝ} (hs : ContDiff ℝ 2 s) (hodd : ∀ u, s (-u) = -s u)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) :
    (Z.W (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s)).re ≤
      -2 * Z.mult ρ₀ * (∫ u, s u * Real.sinh (δ * u)) ^ 2 +
        384 * A₀ * Real.log (|ρ₀.im| + 3) * testNorm s ^ 2 *
          (Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R)) := by
  classical
  obtain ⟨hwsum, hwle⟩ := window_tsum_le Z hA₀ hloc ρ₀.im
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
  set K := Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R) with hK
  set F : Z.carrier → ℝ := fun ρ =>
    (Z.Wsummand (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s) ρ).re with hF
  set c : Z.carrier → ℝ := fun ρ =>
    16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ρ₀.im|) ^ 3) with hc
  have hN := testNorm_nonneg s
  have hR0 : 0 < 1 + R := by linarith
  have hK0 : 0 ≤ K := by positivity
  have hc0 : ∀ ρ, 0 ≤ c ρ := fun ρ => by
    have : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    simp only [hc]
    positivity
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
    exact (Complex.re_le_norm _).trans (norm_Wsummand_modulatedTest_le_depthGap Z ρ₀.im ha hR
      hs hsupp ρ.2 (hgap ρ ρ.2 hρ0 hρ1))
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
  have htc : ∑' ρ, c ρ ≤ 16 * testNorm s ^ 2 * K * (24 * A₀ * Real.log (|ρ₀.im| + 3)) := by
    rw [hc, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hwle (by positivity)
  have hle := Summable.tsum_le_tsum hgc hgsum hcsum
  have hW : (Z.W (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s)).re = ∑' ρ, F ρ := by
    rw [ZeroConfig.W, Complex.re_tsum hsumm]
  rw [hW]
  have : ∑' ρ, F ρ ≤ -2 * Q + 16 * testNorm s ^ 2 * K * (24 * A₀ * Real.log (|ρ₀.im| + 3)) := by
    linarith
  calc ∑' ρ, F ρ ≤ -2 * Q + 16 * testNorm s ^ 2 * K * (24 * A₀ * Real.log (|ρ₀.im| + 3)) := this
    _ = -2 * Z.mult ρ₀ * (∫ u, s u * Real.sinh (δ * u)) ^ 2 +
        384 * A₀ * Real.log (|ρ₀.im| + 3) * testNorm s ^ 2 * K := by
        rw [hQ]; ring

/-- **A zero with a depth gap violates Weil positivity at aperture `a`.** Suppose every zero
other than `ρ₀, 1 − ρ̄₀` within ordinate distance `R` has depth at most `δ'`, and for some
`0 < w ≤ a/4`, `384 A₀ log(|γ₀| + 3) N_b² (e^{2δ'a} + e^a/(1 + R)) < 2 P_b²`, with
`N_b = 2a cosh(δa)(a⁵ + δ²a⁵ + 10δa⁴ + 20a³)` and `P_b = w (wa)^{5/2} sinh²(δ(a − 2w))`. Then a `C²`
test supported in `[-a, a]` has negative Weil form. -/
theorem exists_re_W_neg_of_depthGap_deep_zero (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {a R w δ' : ℝ} (hR : 0 ≤ R) (hw : 0 < w) (hwa : w ≤ a / 4)
    (hgap : ∀ ρ ∈ Z.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.im - ρ₀.im| ≤ R →
      |ρ.re - 1 / 2| ≤ δ')
    (hbig : 384 * A₀ * Real.log (|ρ₀.im| + 3) *
        (2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R)) <
      2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ (Z.W f f).re < 0 := by
  have ha : 0 < a := by linarith
  refine ⟨modulatedTest ρ₀.im (sinhTest a δ), modulatedTest_contDiff _ (sinhTest_contDiff a δ),
    tsupport_modulatedTest_subset _ (sinhTest_supp ha.le), ?_⟩
  have hmaster := re_W_modulatedTest_le_of_depthGap Z hA₀ hloc hρ₀ hδ hre ha.le hR hgap
    (sinhTest_contDiff a δ) (sinhTest_odd a δ) (sinhTest_supp ha.le)
  have hP := sinhTest_energy_ge (a := a) hδ hw hwa
  have hN := testNorm_sinhTest_le ha.le hδ.le
  have hN0 := testNorm_nonneg (sinhTest a δ)
  have hm : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  have hPl0 : 0 ≤ w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2 := by positivity
  have hL : 0 ≤ 384 * A₀ * Real.log (|ρ₀.im| + 3) := by
    have := one_le_log_abs_add_three ρ₀.im
    positivity
  have hK : 0 ≤ Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R) := by positivity
  have hP2 := pow_le_pow_left₀ hPl0 hP 2
  have hN2 := pow_le_pow_left₀ hN0 hN 2
  have h1 : -2 * (Z.mult ρ₀ : ℝ) * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 ≤
      -2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (∫ u, sinhTest a δ u * Real.sinh (δ * u))]
  have h2 : 384 * A₀ * Real.log (|ρ₀.im| + 3) * testNorm (sinhTest a δ) ^ 2 *
        (Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R)) ≤
      384 * A₀ * Real.log (|ρ₀.im| + 3) *
        (2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R)) := by
    gcongr
  linarith

/-- **Weil positivity forces a deep companion.** If the Weil form is nonnegative on all `C²`
tests supported in `[-a, a]`, then every zero `ρ₀` of depth `δ` satisfying the size condition of
`exists_re_W_neg_of_depthGap_deep_zero` has a zero `ρ ≠ ρ₀, 1 − ρ̄₀` within ordinate distance `R`
of depth greater than `δ'`. -/
theorem exists_deep_companion_of_weil_positive (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a : ℝ}
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {R w δ' : ℝ} (hR : 0 ≤ R) (hw : 0 < w) (hwa : w ≤ a / 4)
    (hbig : 384 * A₀ * Real.log (|ρ₀.im| + 3) *
        (2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R)) <
      2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2) :
    ∃ ρ ∈ Z.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧ |ρ.im - ρ₀.im| ≤ R ∧ δ' < |ρ.re - 1 / 2| := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  obtain ⟨f, hf, hfs, hneg⟩ :=
    exists_re_W_neg_of_depthGap_deep_zero Z hA₀ hloc hρ₀ hδ hre hR hw hwa h hbig
  exact absurd (hpos f hf hfs) (not_le.mpr hneg)

/-- **The deep-companion law for `ζ`**, with the unconditional local zero count. -/
theorem zeta_weil_positive_forces_deep_companion :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a : ℝ,
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ (zetaZeroConfig.W f f).re) →
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, ∀ δ : ℝ, 0 < δ → ρ₀.re = 1 / 2 + δ →
      ∀ R w δ' : ℝ, 0 ≤ R → 0 < w → w ≤ a / 4 →
        384 * A₀ * Real.log (|ρ₀.im| + 3) *
            (2 * a * Real.cosh (δ * a) *
              (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
            (Real.exp (δ' * a) ^ 2 + Real.exp a / (1 + R)) <
          2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 →
        ∃ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧ |ρ.im - ρ₀.im| ≤ R ∧
          δ' < |ρ.re - 1 / 2| := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, hA₀, fun a hpos ρ₀ hρ₀ δ hδ hre R w δ' hR hw hwa hbig =>
    exists_deep_companion_of_weil_positive zetaZeroConfig hA₀ hloc hpos hρ₀ hδ hre hR hw hwa
      hbig⟩

end GaloisForLFunctions.SquareRootThreshold
