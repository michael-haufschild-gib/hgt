/-
Residues of the rational source adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.RationalSourceProjection

/-!
# Residues of the rational source

Clearing analytic Whittaker factors transfers initial Gauss-series relations to the actual
residues `rationalSourceResidualFourierCoefficient`. They satisfy the prime recurrence with
coefficient `1 + N(p)⁻¹`, and the rational source projection has the cubic Eisenstein residue
as an eigenvector of the variational resolvent.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource

/-- Clearing analytic height factors transfers a scalar relation from the initial half-plane to residues. -/
theorem cuspScalarResidue_relation {ι : Type*} (T H : ι → ℂ → ℂ) (R : ι → ℂ)
    (hT : ∀ i, AnalyticOnNhd ℂ (T i) {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hH : ∀ i, AnalyticOnNhd ℂ (H i) {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hHc : ∀ i, ContinuousAt (H i) (4 / 3 : ℂ))
    (hR : ∀ i, Tendsto (fun s : ℂ => (s - 4 / 3) * T i s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (R i)))
    (hHne : ∀ i, H i (4 / 3) ≠ 0) (i0 i1 i2 : ι) (A B : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hB : AnalyticOnNhd ℂ B {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hAc : ContinuousAt A (4 / 3 : ℂ)) (hBc : ContinuousAt B (4 / 3 : ℂ))
    (hrel : ∀ s : ℂ, 4 < s.re → 0 < s.im →
      T i0 s * H i1 s * H i2 s =
        A s * T i1 s * H i0 s * H i2 s + B s * T i2 s * H i0 s * H i1 s) :
    R i0 / H i0 (4 / 3) = A (4 / 3) * (R i1 / H i1 (4 / 3)) +
      B (4 / 3) * (R i2 / H i2 (4 / 3)) := by
  let D : Set ℂ := {s | 1 < s.re ∧ 0 < s.im}
  let f : ℂ → ℂ := fun s => T i0 s * H i1 s * H i2 s
  let g : ℂ → ℂ := fun s => A s * T i1 s * H i0 s * H i2 s + B s * T i2 s * H i0 s * H i1 s
  have hf : AnalyticOnNhd ℂ f D := fun s hs => ((hT i0 s hs).mul (hH i1 s hs)).mul (hH i2 s hs)
  have hg : AnalyticOnNhd ℂ g D := fun s hs =>
    ((((hA s hs).mul (hT i1 s hs)).mul (hH i0 s hs)).mul (hH i2 s hs)).add
      ((((hB s hs).mul (hT i2 s hs)).mul (hH i0 s hs)).mul (hH i1 s hs))
  have hconvex : Convex ℝ D :=
    ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f =ᶠ[𝓝 (5 + Complex.I : ℂ)] g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact hrel s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected
    (by norm_num [D] : (5 + Complex.I : ℂ) ∈ D) hev
  have hlimH (i : ι) : Tendsto (H i) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (H i (4 / 3))) :=
    (hHc i).tendsto.mono_left nhdsWithin_le_nhds
  have hl := (((hR i0).mul (hlimH i1)).mul (hlimH i2)).comp thetaApproach_tendsto_complex_punctured
  have hrightA := (((hAc.tendsto.mono_left nhdsWithin_le_nhds).mul (hR i1)).mul (hlimH i0)).mul (hlimH i2)
  have hrightB := (((hBc.tendsto.mono_left nhdsWithin_le_nhds).mul (hR i2)).mul (hlimH i0)).mul (hlimH i1)
  have hr := (hrightA.add hrightB).comp thetaApproach_tendsto_complex_punctured
  have hcross : R i0 * H i1 (4 / 3) * H i2 (4 / 3) =
      A (4 / 3) * R i1 * H i0 (4 / 3) * H i2 (4 / 3) +
      B (4 / 3) * R i2 * H i0 (4 / 3) * H i1 (4 / 3) := by
    apply tendsto_nhds_unique_of_eventuallyEq hl hr
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have htD : (4 / 3 : ℂ) + (t : ℂ) + (t : ℂ) * Complex.I ∈ D := by
      constructor
      · norm_num
        linarith
      · simpa using ht
    have hc := heq htD
    dsimp only [Function.comp_def, f, g] at *
    linear_combination (((4 / 3 : ℂ) + (t : ℂ) + (t : ℂ) * Complex.I) - 4 / 3) * hc
  field_simp [hHne i0, hHne i1, hHne i2]
  linear_combination hcross

/-- Analytic uniqueness transfers an initial Gauss-series relation to the actual residues.
Multiplying by the three Whittaker factors avoids dividing at their possible zeros. -/
theorem unramifiedGaussResidue_of_initial_relation (h0 h1 h2 : O) (A B : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hB : AnalyticOnNhd ℂ B {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hAc : ContinuousAt A (4 / 3 : ℂ)) (hBc : ContinuousAt B (4 / 3 : ℂ))
    (hrel : ∀ s : ℂ, 4 < s.re → 0 < s.im → unramifiedCubicGaussSeries s h0 =
      A s * unramifiedCubicGaussSeries s h1 + B s * unramifiedCubicGaussSeries s h2) :
    unramifiedGaussResidue h0 = A (4 / 3) * unramifiedGaussResidue h1 +
      B (4 / 3) * unramifiedGaussResidue h2 := by
  unfold unramifiedGaussResidue
  apply cuspScalarResidue_relation
    (fun h => rationalCuspFamily (3 * h) oppositeSource 2 3 (by norm_num) (by norm_num))
    (fun h s => cuspWhittakerHeightFactor s (3 * h))
    (fun h => rationalCuspFourier (3 * h) oppositeSource cubicEisensteinResidue)
    (fun h s hs => rationalCuspFamily_analyticAt_nonreal (3 * h) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
    (fun h s hs => cuspWhittakerHeightFactor_analyticAt (3 * h) s hs.1)
    (fun h => (cuspWhittakerHeightFactor_analyticAt (3 * h) (4 / 3) (by norm_num)).continuousAt)
    (fun h => rationalCuspFamily_residue_limit (3 * h) oppositeSource 2 3 (by norm_num) (by norm_num))
    (fun h => cuspWhittakerHeightFactor_center_ne_zero (3 * h)) h0 h1 h2 A B hA hB hAc hBc
  intro s hs hi
  rw [rationalCuspFamily_opposite_initial h0 s hs hi,
    rationalCuspFamily_opposite_initial h1 s hs hi,
    rationalCuspFamily_opposite_initial h2 s hs hi, hrel s hs hi]
  ring

lemma gaussPrimeWeight_analytic (p : O) (hp : Prime p) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-z)) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall fun z => (differentiableAt_id.neg).const_cpow (Or.inl
    (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))))

lemma gaussPrimeWeight_center (p : O) (hp : Prime p) :
    (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 *
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3 =
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ := by
  have hq : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast _ 3, ← Complex.cpow_add _ _ hq]
  convert Complex.cpow_neg_one (Ideal.absNorm (Ideal.span {p}) : ℂ) using 1
  congr 1
  norm_num

/-- The residue satisfies the exact prime recurrence with coefficient `1+N(p)⁻¹`. -/
theorem unramifiedGaussResidue_prime_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    unramifiedGaussResidue (h * p ^ 3) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * unramifiedGaussResidue h -
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) * primeCubicGauss p hp hprimary 1 h *
        unramifiedGaussResidue (h * p) := by
  let A : ℂ → ℂ := fun s => 1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 *
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s)) ^ 3
  let B : ℂ → ℂ := fun s => -((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s) * primeCubicGauss p hp hprimary 1 h)
  have hA (s : ℂ) : AnalyticAt ℂ A s := analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have hB (s : ℂ) : AnalyticAt ℂ B s := ((gaussPrimeWeight_analytic p hp s).mul analyticAt_const).neg
  have hgood : primaryIdealGenerator (Ideal.span {p}) ≠ 0 := by
    rw [primaryIdealGenerator_span p hp.ne_zero hprimary]
    exact hp.ne_zero
  have he := unramifiedGaussResidue_of_initial_relation (h * p ^ 3) h (h * p) A B
    (fun s _ => hA s) (fun s _ => hB s) (hA _).continuousAt (hB _).continuousAt (by
      intro s hs hi
      have hh := unramifiedCubicGaussSeries_prime_recurrence p hp hprimary s (by linarith) h hph
      rw [unramifiedNormWeight_of_good s _ hgood] at hh
      simpa only [A, B, neg_mul, sub_eq_add_neg] using hh)
  dsimp only [A, B] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [neg_mul, sub_eq_add_neg] using he

theorem unramifiedGaussResidue_cube_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) :
    unramifiedGaussResidue (h * p ^ 6) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * unramifiedGaussResidue (h * p ^ 3) -
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * unramifiedGaussResidue h := by
  let A : ℂ → ℂ := fun s => 1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 *
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s)) ^ 3
  let B : ℂ → ℂ := fun s => -((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 *
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s)) ^ 3)
  have hA (s : ℂ) : AnalyticAt ℂ A s := analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have hB (s : ℂ) : AnalyticAt ℂ B s :=
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3)).neg
  have hgood : primaryIdealGenerator (Ideal.span {p}) ≠ 0 := by
    rw [primaryIdealGenerator_span p hp.ne_zero hprimary]
    exact hp.ne_zero
  have he := unramifiedGaussResidue_of_initial_relation (h * p ^ 6) (h * p ^ 3) h A B
    (fun s _ => hA s) (fun s _ => hB s) (hA _).continuousAt (hB _).continuousAt (by
      intro s hs hi
      have hh := unramifiedCubicGaussSeries_cube_recurrence p hp hprimary s (by linarith) h
      rw [unramifiedNormWeight_of_good s _ hgood] at hh
      simpa only [A, B, neg_mul, sub_eq_add_neg] using hh)
  dsimp only [A, B] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [neg_mul, sub_eq_add_neg] using he

theorem unramifiedGaussResidue_square_cube (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    unramifiedGaussResidue (h * p ^ 5) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * unramifiedGaussResidue (h * p ^ 2) := by
  let A : ℂ → ℂ := fun s => 1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 *
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s)) ^ 3
  have hA (s : ℂ) : AnalyticAt ℂ A s := analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have hgood : primaryIdealGenerator (Ideal.span {p}) ≠ 0 := by
    rw [primaryIdealGenerator_span p hp.ne_zero hprimary]
    exact hp.ne_zero
  have he := unramifiedGaussResidue_of_initial_relation (h * p ^ 5) (h * p ^ 2) 0 A (fun _ => 0)
    (fun s _ => hA s) (fun _ _ => analyticAt_const) (hA _).continuousAt continuousAt_const (by
      intro s hs hi
      have hh := unramifiedCubicGaussSeries_square_cube p hp hprimary s (by linarith) h hph
      rw [unramifiedNormWeight_of_good s _ hgood] at hh
      simpa only [A, zero_mul, add_zero] using hh)
  dsimp only [A] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [zero_mul, add_zero] using he

/-- An admissible cube has trivial cubic character in the ramified Fourier sum. -/
lemma arithmeticResidueSum_frequency_cube (h c t : O) (hc : c ≠ 0) (hlevel : (3 : O) ∣ c)
    (ht : lambda ^ 2 ∣ t - 1) (hct : IsCoprime c t) :
    arithmeticResidueSum (h * t ^ 3) c = arithmeticResidueSum h c := by
  have he := arithmeticResidueSum_frequency_twist h c (t ^ 3) hc hlevel
    ⟨hct.pow_right, three_dvd_primary_sub_one _ (primary_pow_congruence t ht 3)⟩
  rw [symbol_pow_denominator, symbol_cube_of_isCoprime c t ht hct, map_one, one_mul] at he
  exact he

lemma ramified_prime_frequency_not_dvd (h p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (hph : ¬ p ∣ h) (u : Oˣ) (n : ℕ) :
    ¬ p ∣ 9 * h * ((u : O) * lambda ^ n) := by
  have hc := ramified_primary_coprime u n p hprimary
  have h9 : IsCoprime (9 * ((u : O) * lambda ^ n)) p := by
    rw [show (9 : O) = 3 * 3 by norm_num]
    exact (hc.of_mul_left_left.mul_left hc.of_mul_left_left).mul_left hc.of_mul_left_right
  have hn := hp.coprime_iff_not_dvd.mp h9.symm
  rw [show 9 * h * ((u : O) * lambda ^ n) = (9 * ((u : O) * lambda ^ n)) * h by ring]
  intro hd
  exact (hp.dvd_mul.mp hd).elim hn hph

/-- Any common cutoff above the ramified support can be used in the finite decomposition. -/
theorem arithmeticDirichletSeries_finite_gauss_of_bound (s : ℂ) (hs : 2 < s.re)
    (h : O) (hh : h ≠ 0) (N : ℕ) (hN : ramifiedFrequencyBound h + 1 ≤ N) :
    arithmeticDirichletSeries s h =
      ∑' u : Oˣ, ∑ n ∈ Finset.range N,
        (((3 ^ (n + 2) : ℕ) : ℂ) ^ (-s) * arithmeticResidueSum h ((u : O) * lambda ^ (n + 2))) *
          unramifiedCubicGaussSeries s (9 * h * ((u : O) * lambda ^ (n + 2))) := by
  rw [arithmeticDirichletSeries_ramified_reindex s hs h]
  apply tsum_congr
  intro u
  have hz (n : ℕ) (hn : n ∉ Finset.range N) :
      (∑' I : GoodIdeal, arithmeticDirichletTerm s h (ramifiedLowerMap (u, n, I)).1) = 0 := by
    have hlarge : ramifiedFrequencyBound h < n + 2 := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    have he (I : GoodIdeal) : arithmeticDirichletTerm s h (ramifiedLowerMap (u, n, I)).1 = 0 :=
      arithmeticDirichletTerm_ramified_vanish s h hh u (n + 2) (by omega)
        (primaryIdealGenerator I.1) (primaryIdealGenerator_spec I.1 I.2).2 hlarge
    simp only [he, tsum_zero]
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro n hn
  rw [unramifiedCubicGaussSeries, ← tsum_mul_left]
  exact tsum_congr (fun I => arithmeticDirichletTerm_ramified_gauss s h u n I)

lemma cubic_units_finite : Finite Oˣ := by
  letI : Fintype {z : O // ‖ringComplex z‖ ≤ 1} := (finite_norm_sublevel 1).fintype
  have hn (u : Oˣ) : ‖ringComplex (u : O)‖ ≤ 1 := by
    have he := ramifiedElement_absNorm u 0
    simp only [pow_zero, mul_one] at he
    have hs := ringComplex_norm_sq_eq_absNorm_span (u : O)
    rw [he, Nat.cast_one] at hs
    nlinarith only [hs, norm_nonneg (ringComplex (u : O))]
  exact Finite.of_injective (fun u : Oˣ => (⟨u, hn u⟩ : {z : O // ‖ringComplex z‖ ≤ 1}))
    (fun u v h => Units.ext (congrArg Subtype.val h))

def ramifiedGaussTerm (s : ℂ) (h : O) (u : Oˣ) (n : ℕ) : ℂ :=
  (((3 ^ (n + 2) : ℕ) : ℂ) ^ (-s) * arithmeticResidueSum h ((u : O) * lambda ^ (n + 2))) *
    unramifiedCubicGaussSeries s (9 * h * ((u : O) * lambda ^ (n + 2)))

/-- The ramified character cancels the frequency twist in the unramified prime factor. -/
lemma ramifiedGaussTerm_prime_recurrence (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (s : ℂ) (hs : 2 < s.re) (h : O) (hph : ¬ p ∣ h) (u : Oˣ) (n : ℕ) :
    ramifiedGaussTerm s (h * p ^ 3) u n =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        ramifiedGaussTerm s h u n -
      unramifiedNormWeight s (Ideal.span {p}) * cubicUnitGaussSum (9 * h) p *
        ramifiedGaussTerm s (h * p) u n := by
  let c : O := (u : O) * lambda ^ (n + 2)
  have hc : c ≠ 0 := ramifiedElement_ne_zero u (n + 2)
  have hlevel : (3 : O) ∣ c := ramifiedElement_level u (n + 2) (by omega)
  have hcop : IsCoprime c p := (ramified_primary_coprime u (n + 2) p hprimary).of_mul_left_right
  have ha := arithmeticResidueSum_frequency_cube h c p hc hlevel hprimary hcop
  have ht := arithmeticResidueSum_frequency_twist h c p hc hlevel
    ⟨hcop, three_dvd_primary_sub_one p hprimary⟩
  have hg := cubicUnitGaussSum_frequency_twist (9 * h) p c hp.ne_zero hcop.symm
  have hcub := unramifiedCubicGaussSeries_prime_recurrence p hp hprimary s hs (9 * h * c)
    (ramified_prime_frequency_not_dvd h p hp hprimary hph u (n + 2))
  rw [primeCubicGauss_one_eq] at hcub
  have hcancel : arithmeticResidueSum h c * cubicUnitGaussSum (9 * h * c) p =
      cubicUnitGaussSum (9 * h) p * arithmeticResidueSum (h * p) c := by
    rw [← ht]
    calc
      _ = (ringComplex (symbol c p) * cubicUnitGaussSum (9 * h * c) p) *
          arithmeticResidueSum (h * p) c := by ring
      _ = _ := by rw [hg]
  change (_ * arithmeticResidueSum (h * p ^ 3) c) * unramifiedCubicGaussSeries s (9 * (h * p ^ 3) * c) =
    _ * ((_ * arithmeticResidueSum h c) * unramifiedCubicGaussSeries s (9 * h * c)) -
    _ * ((_ * arithmeticResidueSum (h * p) c) * unramifiedCubicGaussSeries s (9 * (h * p) * c))
  rw [ha, show 9 * (h * p ^ 3) * c = (9 * h * c) * p ^ 3 by ring, hcub,
    show 9 * (h * p) * c = (9 * h * c) * p by ring]
  linear_combination -unramifiedNormWeight s (Ideal.span {p}) * ((3 ^ (n + 2) : ℕ) : ℂ) ^ (-s) *
    unramifiedCubicGaussSeries s ((9 * h * c) * p) * hcancel

theorem arithmeticDirichletSeries_prime_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) (hph : ¬ p ∣ h) :
    arithmeticDirichletSeries s (h * p ^ 3) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        arithmeticDirichletSeries s h -
      unramifiedNormWeight s (Ideal.span {p}) * cubicUnitGaussSum (9 * h) p *
        arithmeticDirichletSeries s (h * p) := by
  letI : Finite Oˣ := cubic_units_finite
  letI : Fintype Oˣ := Fintype.ofFinite _
  have hh : h ≠ 0 := fun hz => hph (hz ▸ dvd_zero p)
  let N := max (ramifiedFrequencyBound (h * p ^ 3) + 1)
    (max (ramifiedFrequencyBound h + 1) (ramifiedFrequencyBound (h * p) + 1))
  rw [arithmeticDirichletSeries_finite_gauss_of_bound s hs (h * p ^ 3)
      (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    arithmeticDirichletSeries_finite_gauss_of_bound s hs h hh N ((le_max_left _ _).trans (le_max_right _ _)),
    arithmeticDirichletSeries_finite_gauss_of_bound s hs (h * p)
      (mul_ne_zero hh hp.ne_zero) N ((le_max_right _ _).trans (le_max_right _ _))]
  change (∑' u : Oˣ, ∑ n ∈ Finset.range N, ramifiedGaussTerm s (h * p ^ 3) u n) =
    _ * (∑' u : Oˣ, ∑ n ∈ Finset.range N, ramifiedGaussTerm s h u n) -
    _ * (∑' u : Oˣ, ∑ n ∈ Finset.range N, ramifiedGaussTerm s (h * p) u n)
  simp_rw [ramifiedGaussTerm_prime_recurrence p hp hprimary s hs h hph,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [tsum_fintype, Finset.sum_sub_distrib, Finset.mul_sum]

lemma ramifiedGaussTerm_cube_recurrence (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (s : ℂ) (hs : 2 < s.re) (h : O) (u : Oˣ) (n : ℕ) :
    ramifiedGaussTerm s (h * p ^ 6) u n =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        ramifiedGaussTerm s (h * p ^ 3) u n -
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3 *
        ramifiedGaussTerm s h u n := by
  let c : O := (u : O) * lambda ^ (n + 2)
  have ha (k : O) : arithmeticResidueSum (k * p ^ 3) c = arithmeticResidueSum k c :=
    arithmeticResidueSum_frequency_cube k c p (ramifiedElement_ne_zero u (n + 2))
      (ramifiedElement_level u (n + 2) (by omega)) hprimary
      (ramified_primary_coprime u (n + 2) p hprimary).of_mul_left_right
  have ha6 : arithmeticResidueSum (h * p ^ 6) c = arithmeticResidueSum h c := by
    rw [show h * p ^ 6 = (h * p ^ 3) * p ^ 3 by ring, ha, ha]
  have he := unramifiedCubicGaussSeries_cube_recurrence p hp hprimary s hs (9 * h * c)
  change (_ * arithmeticResidueSum (h * p ^ 6) c) * unramifiedCubicGaussSeries s (9 * (h * p ^ 6) * c) =
    _ * ((_ * arithmeticResidueSum (h * p ^ 3) c) * unramifiedCubicGaussSeries s (9 * (h * p ^ 3) * c)) -
    _ * ((_ * arithmeticResidueSum h c) * unramifiedCubicGaussSeries s (9 * h * c))
  rw [ha6, ha, show 9 * (h * p ^ 6) * c = (9 * h * c) * p ^ 6 by ring,
    show 9 * (h * p ^ 3) * c = (9 * h * c) * p ^ 3 by ring, he]
  ring

theorem arithmeticDirichletSeries_cube_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) (hh : h ≠ 0) :
    arithmeticDirichletSeries s (h * p ^ 6) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        arithmeticDirichletSeries s (h * p ^ 3) -
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3 *
        arithmeticDirichletSeries s h := by
  letI : Finite Oˣ := cubic_units_finite
  letI : Fintype Oˣ := Fintype.ofFinite _
  let N := max (ramifiedFrequencyBound (h * p ^ 6) + 1)
    (max (ramifiedFrequencyBound (h * p ^ 3) + 1) (ramifiedFrequencyBound h + 1))
  rw [arithmeticDirichletSeries_finite_gauss_of_bound s hs (h * p ^ 6)
      (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    arithmeticDirichletSeries_finite_gauss_of_bound s hs (h * p ^ 3)
      (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N ((le_max_left _ _).trans (le_max_right _ _)),
    arithmeticDirichletSeries_finite_gauss_of_bound s hs h hh N ((le_max_right _ _).trans (le_max_right _ _))]
  change (∑' u : Oˣ, ∑ n ∈ Finset.range N, ramifiedGaussTerm s (h * p ^ 6) u n) =
    _ * (∑' u : Oˣ, ∑ n ∈ Finset.range N, ramifiedGaussTerm s (h * p ^ 3) u n) -
    _ * (∑' u : Oˣ, ∑ n ∈ Finset.range N, ramifiedGaussTerm s h u n)
  simp_rw [ramifiedGaussTerm_cube_recurrence p hp hprimary s hs h,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [tsum_fintype, Finset.sum_sub_distrib, Finset.mul_sum]

lemma ramifiedGaussTerm_square_cube (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (s : ℂ) (hs : 2 < s.re) (h : O) (hph : ¬ p ∣ h) (u : Oˣ) (n : ℕ) :
    ramifiedGaussTerm s (h * p ^ 5) u n =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        ramifiedGaussTerm s (h * p ^ 2) u n := by
  let c : O := (u : O) * lambda ^ (n + 2)
  have ha := arithmeticResidueSum_frequency_cube (h * p ^ 2) c p
    (ramifiedElement_ne_zero u (n + 2)) (ramifiedElement_level u (n + 2) (by omega)) hprimary
    (ramified_primary_coprime u (n + 2) p hprimary).of_mul_left_right
  rw [show (h * p ^ 2) * p ^ 3 = h * p ^ 5 by ring] at ha
  have he := unramifiedCubicGaussSeries_square_cube p hp hprimary s hs (9 * h * c)
    (ramified_prime_frequency_not_dvd h p hp hprimary hph u (n + 2))
  change (_ * arithmeticResidueSum (h * p ^ 5) c) * unramifiedCubicGaussSeries s (9 * (h * p ^ 5) * c) =
    _ * ((_ * arithmeticResidueSum (h * p ^ 2) c) * unramifiedCubicGaussSeries s (9 * (h * p ^ 2) * c))
  rw [ha, show 9 * (h * p ^ 5) * c = (9 * h * c) * p ^ 5 by ring,
    show 9 * (h * p ^ 2) * c = (9 * h * c) * p ^ 2 by ring, he]
  ring

theorem arithmeticDirichletSeries_square_cube (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) (hph : ¬ p ∣ h) :
    arithmeticDirichletSeries s (h * p ^ 5) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        arithmeticDirichletSeries s (h * p ^ 2) := by
  have hh : h ≠ 0 := fun hz => hph (hz ▸ dvd_zero p)
  let N := max (ramifiedFrequencyBound (h * p ^ 5) + 1) (ramifiedFrequencyBound (h * p ^ 2) + 1)
  rw [arithmeticDirichletSeries_finite_gauss_of_bound s hs (h * p ^ 5)
      (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    arithmeticDirichletSeries_finite_gauss_of_bound s hs (h * p ^ 2)
      (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_right _ _)]
  change (∑' u : Oˣ, ∑ n ∈ Finset.range N, ramifiedGaussTerm s (h * p ^ 5) u n) =
    _ * (∑' u : Oˣ, ∑ n ∈ Finset.range N, ramifiedGaussTerm s (h * p ^ 2) u n)
  simp_rw [ramifiedGaussTerm_square_cube p hp hprimary s hs h hph, ← Finset.mul_sum]
  exact tsum_mul_left

theorem nonzeroScatteringResidue_of_initial_relation (h0 h1 h2 : O)
    (hh0 : h0 ≠ 0) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0) (A B : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hB : AnalyticOnNhd ℂ B {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hAc : ContinuousAt A (4 / 3 : ℂ)) (hBc : ContinuousAt B (4 / 3 : ℂ))
    (hrel : ∀ s : ℂ, 4 < s.re → 0 < s.im → scatteringCoefficient s h0 =
      A s * scatteringCoefficient s h1 + B s * scatteringCoefficient s h2) :
    nonzeroScatteringResidue h0 = A (4 / 3) * nonzeroScatteringResidue h1 +
      B (4 / 3) * nonzeroScatteringResidue h2 := by
  unfold nonzeroScatteringResidue
  apply cuspScalarResidue_relation
    (ι := {h : O // h ≠ 0})
    (fun h => kernelCuspFourierFamily h.1 2 3 (by norm_num) (by norm_num))
    (fun h s => ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * cuspWhittakerHeightFactor s h.1)
    (fun h => kernelCuspFourier h.1 cubicEisensteinResidue)
    (fun h s hs => kernelCuspFourierFamily_analyticAt_nonreal h.1 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
    (fun h s hs => analyticAt_const.mul (cuspWhittakerHeightFactor_analyticAt h.1 s hs.1))
    (fun h => continuousAt_const.mul
      (cuspWhittakerHeightFactor_analyticAt h.1 (4 / 3) (by norm_num)).continuousAt)
    (fun h => kernelCuspFourierFamily_residue_limit h.1 2 3 (by norm_num) (by norm_num))
    (fun h => mul_ne_zero cusp_volume_ne_zero (cuspWhittakerHeightFactor_center_ne_zero h.1))
    ⟨h0, hh0⟩ ⟨h1, hh1⟩ ⟨h2, hh2⟩ A B hA hB hAc hBc
  intro s hs hi
  rw [kernelCuspFourierFamily_eq_upper h0 hh0 ⟨by linarith, hi⟩,
    kernelCuspFourierFamily_eq_upper h1 hh1 ⟨by linarith, hi⟩,
    kernelCuspFourierFamily_eq_upper h2 hh2 ⟨by linarith, hi⟩]
  dsimp only
  rw [hrel s hs hi]
  ring

/-- The actual nonconstant scattering residues inherit the prime recurrence. -/
theorem nonzeroScatteringResidue_prime_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    nonzeroScatteringResidue (h * p ^ 3) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * nonzeroScatteringResidue h -
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) * cubicUnitGaussSum (9 * h) p *
        nonzeroScatteringResidue (h * p) := by
  let A : ℂ → ℂ := fun s => 1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 *
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s)) ^ 3
  let B : ℂ → ℂ := fun s => -((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s) * cubicUnitGaussSum (9 * h) p)
  have hA (s : ℂ) : AnalyticAt ℂ A s := analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have hB (s : ℂ) : AnalyticAt ℂ B s := ((gaussPrimeWeight_analytic p hp s).mul analyticAt_const).neg
  have hh : h ≠ 0 := fun hz => hph (hz ▸ dvd_zero p)
  have hgood : primaryIdealGenerator (Ideal.span {p}) ≠ 0 := by
    rw [primaryIdealGenerator_span p hp.ne_zero hprimary]
    exact hp.ne_zero
  have he := nonzeroScatteringResidue_of_initial_relation (h * p ^ 3) h (h * p)
    (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) hh (mul_ne_zero hh hp.ne_zero) A B
    (fun s _ => hA s) (fun s _ => hB s) (hA _).continuousAt (hB _).continuousAt (by
      intro s hs hi
      have hr := arithmeticDirichletSeries_prime_recurrence p hp hprimary s (by linarith) h hph
      rw [unramifiedNormWeight_of_good s _ hgood] at hr
      unfold scatteringCoefficient
      rw [hr]
      dsimp only [A, B]
      ring)
  dsimp only [A, B] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [neg_mul, sub_eq_add_neg] using he

theorem nonzeroScatteringResidue_cube_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hh : h ≠ 0) :
    nonzeroScatteringResidue (h * p ^ 6) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * nonzeroScatteringResidue (h * p ^ 3) -
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * nonzeroScatteringResidue h := by
  let A : ℂ → ℂ := fun s => 1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 *
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s)) ^ 3
  let B : ℂ → ℂ := fun s => -((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 *
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s)) ^ 3)
  have hA (s : ℂ) : AnalyticAt ℂ A s := analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have hB (s : ℂ) : AnalyticAt ℂ B s :=
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3)).neg
  have hgood : primaryIdealGenerator (Ideal.span {p}) ≠ 0 := by
    rw [primaryIdealGenerator_span p hp.ne_zero hprimary]
    exact hp.ne_zero
  have he := nonzeroScatteringResidue_of_initial_relation (h * p ^ 6) (h * p ^ 3) h
    (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) hh A B
    (fun s _ => hA s) (fun s _ => hB s) (hA _).continuousAt (hB _).continuousAt (by
      intro s hs hi
      have hr := arithmeticDirichletSeries_cube_recurrence p hp hprimary s (by linarith) h hh
      rw [unramifiedNormWeight_of_good s _ hgood] at hr
      unfold scatteringCoefficient
      rw [hr]
      dsimp only [A, B]
      ring)
  dsimp only [A, B] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [neg_mul, sub_eq_add_neg] using he

theorem nonzeroScatteringResidue_square_cube (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    nonzeroScatteringResidue (h * p ^ 5) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * nonzeroScatteringResidue (h * p ^ 2) := by
  let A : ℂ → ℂ := fun s => 1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 *
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s)) ^ 3
  have hA (s : ℂ) : AnalyticAt ℂ A s := analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have hh : h ≠ 0 := fun hz => hph (hz ▸ dvd_zero p)
  have hgood : primaryIdealGenerator (Ideal.span {p}) ≠ 0 := by
    rw [primaryIdealGenerator_span p hp.ne_zero hprimary]
    exact hp.ne_zero
  have he := nonzeroScatteringResidue_of_initial_relation (h * p ^ 5) (h * p ^ 2) h
    (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) hh A (fun _ => 0)
    (fun s _ => hA s) (fun _ _ => analyticAt_const) (hA _).continuousAt continuousAt_const (by
      intro s hs hi
      have hr := arithmeticDirichletSeries_square_cube p hp hprimary s (by linarith) h hph
      rw [unramifiedNormWeight_of_good s _ hgood] at hr
      unfold scatteringCoefficient
      rw [hr]
      dsimp only [A]
      ring)
  dsimp only [A] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [zero_mul, add_zero] using he

/-- Rational matrices acting on hyperbolic space through the Eisenstein embedding. -/
def rationalComplex : SL(2, ℤ) →* SL(2, ℂ) := integralComplexMatrix.comp rationalEmbedding

lemma rational_translate_congr (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (r s : SL(2, ℤ)) (he : rationalSourceQuotient r = rationalSourceQuotient s)
    (w : HyperbolicSpace) : f (rationalComplex r • w) = f (rationalComplex s • w) := by
  have hm : rationalEmbedding (r * s⁻¹) ∈ levelThree := by
    apply (QuotientGroup.eq_one_iff (N := levelThreeInRationalExtension)
      (rationalSourceLift (r * s⁻¹))).mp
    change rationalSourceQuotient (r * s⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have h := hf ⟨rationalEmbedding (r * s⁻¹), hm⟩ (rationalComplex s • w)
  rw [complexCharacter_rational_intersection, one_mul] at h
  change f (rationalComplex (r * s⁻¹) • (rationalComplex s • w)) = _ at h
  simpa only [map_mul, map_inv, mul_smul, inv_smul_smul] using h

/-- Left translation permutes the rational averaging classes. -/
lemma rationalSourceProjection_left_invariant (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    rationalSourceProjection (fun v => f (rationalComplex r • v)) w = rationalSourceProjection f w := by
  have he (q : rationalExtension ⧸ levelThreeInRationalExtension) :
      f (rationalComplex r • (rationalComplex (rationalSourceSection q) • w)) =
        f (rationalComplex (rationalSourceSection (rationalSourceQuotient r * q)) • w) := by
    rw [← mul_smul, ← map_mul]
    apply rational_translate_congr f hf
    rw [map_mul, rationalSourceSection_spec, rationalSourceSection_spec]
  change _ * (∑ q, f (rationalComplex r • (rationalComplex (rationalSourceSection q) • w))) =
    _ * (∑ q, f (rationalComplex (rationalSourceSection q) • w))
  simp_rw [he]
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective (rationalSourceQuotient r))
    (fun q => f (rationalComplex (rationalSourceSection q) • w))]

lemma rational_translate_automorphy (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (r : SL(2, ℤ)) (n : levelThree) (w : HyperbolicSpace) :
    f (rationalComplex r • (complexMatrix n • w)) =
      complexCharacter n * f (rationalComplex r • w) := by
  have he : rationalEmbedding r * (n : SL(2, O)) =
      (levelThreeConjugate (rationalEmbedding r) n : SL(2, O)) * rationalEmbedding r := by
    change _ = (rationalEmbedding r * (n : SL(2, O)) * (rationalEmbedding r)⁻¹) * rationalEmbedding r
    group
  change f (integralComplexMatrix (rationalEmbedding r) •
    (integralComplexMatrix (n : SL(2, O)) • w)) = _
  rw [← mul_smul, ← map_mul, he, map_mul, integralComplexMatrix_levelThree, mul_smul,
    hf, complexCharacter_conjugate_rational]
  rfl

lemma rationalUnipotent_add (a b : ℤ) : rationalUnipotent (a + b) = rationalUnipotent a * rationalUnipotent b := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalUnipotent, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma rationalUnipotent_nat (n : ℕ) : rationalUnipotent (n : ℤ) = ModularGroup.T ^ n := by
  induction n with
  | zero =>
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [rationalUnipotent]
  | succ n ih =>
    rw [Nat.cast_succ, rationalUnipotent_add, ih, pow_succ]
    rfl

lemma rational_T_cube_levelThree : rationalEmbedding (ModularGroup.T ^ 3) ∈ levelThree := by
  rw [← rationalUnipotent_nat]
  change Matrix.SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (Ideal.span {(3 : O)}))
    (rationalEmbedding (rationalUnipotent 3)) = 1
  have hz : Ideal.Quotient.mk (Ideal.span {(3 : O)}) 3 = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, rationalUnipotent_embedding]
  fin_cases i <;> fin_cases j <;> simp [hz]

lemma rational_translate_T_cube (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    f (rationalComplex (r * ModularGroup.T ^ 3) • w) = f (rationalComplex r • w) := by
  have he := rational_translate_automorphy f hf r
    ⟨rationalEmbedding (ModularGroup.T ^ 3), rational_T_cube_levelThree⟩ w
  rw [complexCharacter_rational_intersection, one_mul] at he
  change f (rationalComplex r • (rationalComplex (ModularGroup.T ^ 3) • w)) = _ at he
  simpa only [map_mul, mul_smul] using he

/-- The four rational cusps; translation invariance collapses each parabolic fiber. -/
def fourCuspAverage (f : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  (4 : ℂ)⁻¹ * (f w + f (rationalComplex ModularGroup.S • w) +
    f (rationalComplex (ModularGroup.S * ModularGroup.T) • w) +
    f (rationalComplex (ModularGroup.S * ModularGroup.T ^ 2) • w))

lemma fourCuspAverage_automorphy (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (n : levelThree) (w : HyperbolicSpace) :
    fourCuspAverage f (complexMatrix n • w) = complexCharacter n * fourCuspAverage f w := by
  simp only [fourCuspAverage, hf, rational_translate_automorphy f hf]
  ring

lemma fourCuspAverage_T (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (hT : ∀ w, f (rationalComplex ModularGroup.T • w) = f w) (w : HyperbolicSpace) :
    fourCuspAverage f (rationalComplex ModularGroup.T • w) = fourCuspAverage f w := by
  have h2 : ModularGroup.S * ModularGroup.T * ModularGroup.T = ModularGroup.S * ModularGroup.T ^ 2 := by rw [pow_two, mul_assoc]
  have h3 : ModularGroup.S * ModularGroup.T ^ 2 * ModularGroup.T = ModularGroup.S * ModularGroup.T ^ 3 := by group
  simp only [fourCuspAverage, hT, ← mul_smul, ← map_mul, h2, h3, rational_translate_T_cube f hf]
  ring

lemma rational_STS : ModularGroup.S * ModularGroup.T * ModularGroup.S =
    ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_S, ModularGroup.coe_T, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma rational_STTS : ModularGroup.S * ModularGroup.T ^ 2 * ModularGroup.S =
    (ModularGroup.S * ModularGroup.T ^ 3 * ModularGroup.S⁻¹) *
      (ModularGroup.S ^ 2 * ModularGroup.T * ModularGroup.S * ModularGroup.T) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_S, ModularGroup.coe_T, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma fourCuspAverage_S (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (hT : ∀ w, f (rationalComplex ModularGroup.T • w) = f w)
    (hSS : ∀ w, f (rationalComplex (ModularGroup.S ^ 2) • w) = f w) (w : HyperbolicSpace) :
    fourCuspAverage f (rationalComplex ModularGroup.S • w) = fourCuspAverage f w := by
  have hTi (v : HyperbolicSpace) : f (rationalComplex ModularGroup.T⁻¹ • v) = f v := by
    have he := hT (rationalComplex ModularGroup.T⁻¹ • v)
    simpa only [map_inv, smul_inv_smul] using he.symm
  have hSTS : f (rationalComplex (ModularGroup.S * ModularGroup.T * ModularGroup.S) • w) =
      f (rationalComplex (ModularGroup.S * ModularGroup.T ^ 2) • w) := by
    rw [rational_STS, map_mul, map_mul, mul_smul, mul_smul, hTi]
    have he := rational_translate_T_cube f hf (ModularGroup.S * ModularGroup.T⁻¹) w
    have hg : (ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T ^ 3 =
        ModularGroup.S * ModularGroup.T ^ 2 := by group
    rw [hg] at he
    simpa only [map_mul, mul_smul] using he.symm
  have hconj : rationalEmbedding (ModularGroup.S * ModularGroup.T ^ 3 * ModularGroup.S⁻¹) ∈ levelThree := by
    simpa only [levelThreeConjugate, map_mul, map_inv] using
      (levelThreeConjugate (rationalEmbedding ModularGroup.S)
        ⟨rationalEmbedding (ModularGroup.T ^ 3), rational_T_cube_levelThree⟩).property
  have hSTTS : f (rationalComplex (ModularGroup.S * ModularGroup.T ^ 2 * ModularGroup.S) • w) =
      f (rationalComplex (ModularGroup.S * ModularGroup.T) • w) := by
    rw [rational_STTS, map_mul, mul_smul]
    have he := hf ⟨_, hconj⟩ (rationalComplex
      (ModularGroup.S ^ 2 * ModularGroup.T * ModularGroup.S * ModularGroup.T) • w)
    rw [complexCharacter_rational_intersection, one_mul] at he
    change f (rationalComplex _ • _) = _ at he
    rw [he]
    simp only [map_mul, mul_smul, hSS, hT]
  simp only [fourCuspAverage, ← mul_smul, ← map_mul,
    show ModularGroup.S * ModularGroup.S = ModularGroup.S ^ 2 by rw [pow_two], hSS, hSTS, hSTTS]
  ring

def rationalFunctionStabilizer (f : HyperbolicSpace → ℂ) : Subgroup (SL(2, ℤ)) where
  carrier r := ∀ w, f (rationalComplex r • w) = f w
  one_mem' w := by rw [map_one, one_smul]
  mul_mem' hr hs w := by rw [map_mul, mul_smul, hr, hs]
  inv_mem' {r} hr w := by
    have he := hr (rationalComplex r⁻¹ • w)
    simpa only [map_inv, smul_inv_smul] using he.symm

lemma fourCuspAverage_rational (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (hT : ∀ w, f (rationalComplex ModularGroup.T • w) = f w)
    (hSS : ∀ w, f (rationalComplex (ModularGroup.S ^ 2) • w) = f w)
    (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    fourCuspAverage f (rationalComplex r • w) = fourCuspAverage f w := by
  have htop : rationalFunctionStabilizer (fourCuspAverage f) = ⊤ := by
    apply top_unique
    rw [← SpecialLinearGroup.SL2Z_generators]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with (rfl | rfl)
    · exact fourCuspAverage_S f hf hT hSS
    · exact fourCuspAverage_T f hf hT
  have hr : r ∈ rationalFunctionStabilizer (fourCuspAverage f) := by rw [htop]; trivial
  exact hr w

/-- Generator relations give the four-cusp formula without enumerating the finite quotient. -/
theorem rationalSourceProjection_four_cusps (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (hT : ∀ w, f (rationalComplex ModularGroup.T • w) = f w)
    (hSS : ∀ w, f (rationalComplex (ModularGroup.S ^ 2) • w) = f w)
    (w : HyperbolicSpace) : rationalSourceProjection f w = fourCuspAverage f w := by
  have hfixed : rationalSourceProjection (fourCuspAverage f) w = fourCuspAverage f w := by
    apply rationalSourceProjection_fixed
    intro g v
    obtain ⟨n, r, hr⟩ := g.property
    rw [← hr, map_mul, integralComplexMatrix_levelThree, mul_smul,
      fourCuspAverage_automorphy f hf]
    change complexCharacter n * fourCuspAverage f (rationalComplex r • v) = _
    rw [fourCuspAverage_rational f hf hT hSS]
    have he : extendedComplexCharacter g = complexCharacter n :=
      rationalExtensionValue_of_product g n r hr
    rw [he]
  have havg : rationalSourceProjection (fourCuspAverage f) w = rationalSourceProjection f w := by
    have hS := rationalSourceProjection_left_invariant f hf ModularGroup.S w
    have hST := rationalSourceProjection_left_invariant f hf (ModularGroup.S * ModularGroup.T) w
    have hSTT := rationalSourceProjection_left_invariant f hf (ModularGroup.S * ModularGroup.T ^ 2) w
    unfold rationalSourceProjection fourCuspAverage
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    unfold rationalSourceProjection at hS hST hSTT
    linear_combination (1 / 4 : ℂ) * hS + (1 / 4 : ℂ) * hST + (1 / 4 : ℂ) * hSTT
  exact havg.symm.trans hfixed

lemma rationalComplex_S_sq_row (v : Fin 2 → ℂ) :
    rowOperator (rationalComplex (ModularGroup.S ^ 2)) v = -v := by
  have hS : ((ModularGroup.S ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_two, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hC : (rationalComplex (ModularGroup.S ^ 2) : Matrix (Fin 2) (Fin 2) ℂ) = !![-1, 0; 0, -1] := by
    ext i j
    change ringComplex ((Int.castRingHom O) ((ModularGroup.S ^ 2 : SL(2, ℤ)) i j)) = _
    rw [congrFun (congrFun hS i) j]
    fin_cases i <;> fin_cases j <;> simp
  rw [rowOperator_apply, hC]
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma hyperbolicEisenstein_S_sq (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.S ^ 2) • w) = hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    change eisenstein (rationalComplex (ModularGroup.S ^ 2) * g) s = eisenstein g s
    apply tsum_congr
    intro x
    unfold summand
    rw [← rowOperator_mul, rationalComplex_S_sq_row, map_neg]
    simp [rowEnergy]

lemma hyperbolicEisenstein_T_pow (s : ℂ) (n : ℕ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.T ^ n) • w) = hyperbolicEisenstein s w := by
  simpa only [rationalUnipotent_nat, rationalComplex, MonoidHom.comp_apply] using
    hyperbolicEisenstein_unipotent (n : ℤ) s w

/-- The Eisenstein family averaged over the rational extension of the cubic group. -/
def rationalSourceEisenstein (s : ℂ) : HyperbolicSpace → ℂ :=
  rationalSourceProjection (hyperbolicEisenstein s)

theorem rationalSourceEisenstein_four_cusps (s : ℂ) (hs : 2 < s.re) (w : HyperbolicSpace) :
    rationalSourceEisenstein s w = fourCuspAverage (hyperbolicEisenstein s) w := by
  exact rationalSourceProjection_four_cusps (hyperbolicEisenstein s)
    (fun n v => hyperbolicEisenstein_automorphy n s hs v)
    (fun v => by simpa only [pow_one] using hyperbolicEisenstein_T_pow s 1 v)
    (hyperbolicEisenstein_S_sq s) w

lemma cosetHeight_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight x (rationalComplex (rationalUnipotent t) • w) =
      cosetHeight (cuspUnipotentEquiv t x) w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    change (rowEnergy (rowOperator (rationalComplex (rationalUnipotent t) * g) (embeddedRow x)))⁻¹ =
      (rowEnergy (rowOperator g (embeddedRow (cuspUnipotentEquiv t x))))⁻¹
    rw [embeddedRow_cuspUnipotentEquiv, ← rowOperator_apply, rowOperator_mul]
    rfl

lemma cuspCutoffCorrection_unipotent (t : ℤ) (Y : ℝ) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection Y F (rationalComplex (rationalUnipotent t) • w) = cuspCutoffCorrection Y F w := by
  have he (x : CuspCosets) :
      cuspCutoffTerm Y F x (rationalComplex (rationalUnipotent t) • w) =
        cuspCutoffTerm Y F (cuspUnipotentEquiv t x) w := by
    simp only [cuspCutoffTerm, cosetHeight_cuspUnipotentEquiv, cosetCharacter_cuspUnipotentEquiv]
  unfold cuspCutoffCorrection
  simp_rw [he]
  exact (cuspUnipotentEquiv t).tsum_eq (fun x => cuspCutoffTerm Y F x w)

lemma cosetHeight_S_sq (x : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight x (rationalComplex (ModularGroup.S ^ 2) • w) = cosetHeight x w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    change (rowEnergy (rowOperator (rationalComplex (ModularGroup.S ^ 2) * g) (embeddedRow x)))⁻¹ = _
    rw [← rowOperator_mul, rationalComplex_S_sq_row, map_neg]
    simp [rowEnergy, cosetHeight]

lemma cuspCutoffCorrection_S_sq (Y : ℝ) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection Y F (rationalComplex (ModularGroup.S ^ 2) • w) = cuspCutoffCorrection Y F w := by
  simp only [cuspCutoffCorrection, cuspCutoffTerm, cosetHeight_S_sq]

/-- A symmetry of the initial Eisenstein family and its cutoff survives the residue limit. -/
theorem cubicEisensteinResidue_rational_symmetry (r : SL(2, ℤ))
    (hE : ∀ s : ℂ, 2 < s.re → ∀ w,
      hyperbolicEisenstein s (rationalComplex r • w) = hyperbolicEisenstein s w)
    (hseed : ∀ s : ℂ, ∀ w,
      smoothCuspSeed 2 3 s (rationalComplex r • w) = smoothCuspSeed 2 3 s w) :
    kernelRationalPullback (rationalSourceLift r) cubicEisensteinResidue = cubicEisensteinResidue := by
  let P := kernelRationalPullback (rationalSourceLift r)
  let F := kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num)
  have hc : AnalyticOnNhd ℂ F cuspUpperParameterRegion := fun s hs =>
    kernelEisensteinL2Correction_analyticAt_nonreal 2 3 (by norm_num) (by norm_num)
      s (by linarith [hs.1]) hs.2.ne'
  have hl : AnalyticOnNhd ℂ (fun s => P (F s)) cuspUpperParameterRegion := fun s hs =>
    (ContinuousLinearMap.analyticAt (𝕜 := ℂ) P.toContinuousLinearMap _).comp_of_eq (hc s hs) rfl
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s => P (F s)) =ᶠ[𝓝 (5 + Complex.I : ℂ)] F := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    have hF := kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs.1 hs.2
    have hcomp := (kernelRationalAction_measurePreserving (rationalSourceLift r)).quasiMeasurePreserving.ae_eq_comp hF
    have hpoint (q : KernelQuotient) :
        kernelQuotientEisenstein s (by linarith [hs.1]) (kernelRationalAction (rationalSourceLift r) q) -
          kernelQuotientSeed 2 3 s (kernelRationalAction (rationalSourceLift r) q) =
        kernelQuotientEisenstein s (by linarith [hs.1]) q - kernelQuotientSeed 2 3 s q := by
      induction q using Quotient.inductionOn with
      | _ w => exact congrArg₂ (fun a b : ℂ => a - b) (hE s (by linarith [hs.1]) w) (hseed s w)
    apply Lp.ext
    filter_upwards [kernelRationalPullback_ae (rationalSourceLift r) (F s), hcomp, hF] with q hp hq hf
    exact hp.trans (hq.trans ((hpoint q).trans hf.symm))
  have heq := hl.eqOn_of_preconnected_of_eventuallyEq hc cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion]) hev
  have hlim := (kernelEisensteinResidueVector_limit 2 3 (by norm_num) (by norm_num)).comp
    thetaApproach_tendsto_complex_punctured
  have hp := P.continuous.continuousAt.tendsto.comp hlim
  apply tendsto_nhds_unique_of_eventuallyEq hp hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have htD : (4 / 3 : ℂ) + (t : ℂ) + (t : ℂ) * Complex.I ∈ cuspUpperParameterRegion := by
    constructor
    · norm_num
      linarith
    · simpa using ht
  change P (_ • F _) = _ • F _
  rw [map_smul]
  exact congrArg (fun u : KernelQuotientL2 =>
    ((4 / 3 : ℂ) + (t : ℂ) + (t : ℂ) * Complex.I - 4 / 3) • u) (heq htD)

theorem cubicResidualFunction_rational_symmetry (r : SL(2, ℤ))
    (hr : kernelRationalPullback (rationalSourceLift r) cubicEisensteinResidue = cubicEisensteinResidue)
    (w : HyperbolicSpace) : cubicResidualFunction (rationalComplex r • w) = cubicResidualFunction w := by
  have he : (fun q => cubicEisensteinResidue (kernelRationalAction (rationalSourceLift r) q))
      =ᵐ[integralQuotientVolume globalKubotaKernel] cubicEisensteinResidue := by
    filter_upwards [kernelRationalPullback_ae (rationalSourceLift r) cubicEisensteinResidue] with q hq
    rw [hr] at hq
    exact hq.symm
  have hl := kernelProjection_quasiMeasurePreserving.ae_eq_comp he
  have hrep := cubicEisensteinResidue_continuous_representative
  have hcomp := (measurePreserving_smul (rationalComplex r)
    hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp hrep
  have hae : (fun p : HyperbolicSpace => cubicResidualFunction (rationalComplex r • p))
      =ᵐ[hyperbolicVolume] cubicResidualFunction := by
    filter_upwards [hcomp, hl, hrep] with p hp hc hq
    exact hp.symm.trans (hc.trans hq)
  exact congrFun (Measure.eq_of_ae_eq hae
    (cubicResidualFunction_continuous.comp (continuous_hyperbolic_action (rationalComplex r)))
    cubicResidualFunction_continuous) w

lemma cubicResidualFunction_T (w : HyperbolicSpace) :
    cubicResidualFunction (rationalComplex ModularGroup.T • w) = cubicResidualFunction w := by
  apply cubicResidualFunction_rational_symmetry
  apply cubicEisensteinResidue_rational_symmetry
  · intro s hs v
    simpa only [pow_one] using hyperbolicEisenstein_T_pow s 1 v
  · intro s v
    have he : rationalUnipotent (1 : ℤ) = ModularGroup.T := by
      simpa only [Nat.cast_one, pow_one] using rationalUnipotent_nat 1
    simpa only [he, smoothCuspSeed] using cuspCutoffCorrection_unipotent 1 1 (cuspSeedProfile 2 3 s) v

lemma cubicResidualFunction_S_sq (w : HyperbolicSpace) :
    cubicResidualFunction (rationalComplex (ModularGroup.S ^ 2) • w) = cubicResidualFunction w := by
  apply cubicResidualFunction_rational_symmetry
  apply cubicEisensteinResidue_rational_symmetry
  · exact fun s _ v => hyperbolicEisenstein_S_sq s v
  · exact fun s v => cuspCutoffCorrection_S_sq 1 (cuspSeedProfile 2 3 s) v

/-- The actual residual source is the average of its four rational cusp translates. -/
theorem cubicSourceResidualFunction_four_cusps (w : HyperbolicSpace) :
    cubicSourceResidualFunction w = fourCuspAverage cubicResidualFunction w :=
  rationalSourceProjection_four_cusps cubicResidualFunction cubicResidualFunction_automorphy
    cubicResidualFunction_T cubicResidualFunction_S_sq w

lemma rationalUnipotent_action (t : ℤ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    rationalComplex (rationalUnipotent t) • upperPoint z v hv = upperPoint (z + (t : ℂ)) v hv := by
  have he : rationalEmbedding (rationalUnipotent t) = integralTranslation (t : O) := by
    apply Subtype.ext
    exact rationalUnipotent_embedding t
  change integralComplexMatrix (rationalEmbedding (rationalUnipotent t)) • upperPoint z v hv = _
  rw [he, integralTranslation_action, map_intCast]

lemma rational_T_pow_action (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    rationalComplex (ModularGroup.T ^ n) • upperPoint z v hv = upperPoint (z + (n : ℂ)) v hv := by
  simpa only [rationalUnipotent_nat, Int.cast_natCast] using rationalUnipotent_action (n : ℤ) z v hv

lemma rational_translate_period (f : HyperbolicSpace → ℂ)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (r : SL(2, ℤ)) (v : ℝ) (hv : 0 < v) (n : O) (z : ℂ) :
    f (rationalComplex r • upperPoint (z + 3 * ringComplex n) v hv) =
      f (rationalComplex r • upperPoint z v hv) := by
  obtain ⟨hn, hchar⟩ := (globalKubotaKernel_mem _).mp (integralTranslation_three_mem_kernel n)
  have he := rational_translate_automorphy f hf r ⟨integralTranslation (3 * n), hn⟩ (upperPoint z v hv)
  rw [hchar, one_mul] at he
  change f (rationalComplex r •
    (integralComplexMatrix (integralTranslation (3 * n)) • upperPoint z v hv)) = _ at he
  simpa only [integralTranslation_action, map_mul, map_ofNat] using he

/-- Translation of a periodic function multiplies its Fourier coefficient by the dual character. -/
lemma period_fourier_translation (f : ℂ → ℂ)
    (hf : ∀ (n : O) (z : ℂ), f (z + 3 * ringComplex n) = f z) (h : O) (b : ℂ) :
    (∫ z in periodDomain, f (z + b) * tracePhase (-cuspFrequency h * z)) =
      tracePhase (cuspFrequency h * b) * ∫ z in periodDomain, f z * tracePhase (-cuspFrequency h * z) := by
  have hperiod (n : O) (z : ℂ) :
      f (z + 3 * ringComplex n) * tracePhase (-cuspFrequency h * (z + 3 * ringComplex n)) =
        f z * tracePhase (-cuspFrequency h * z) := by
    rw [hf, cuspFrequency_negative_period]
  have he (z : ℂ) : f (z + b) * tracePhase (-cuspFrequency h * z) =
      tracePhase (cuspFrequency h * b) * (f (b + z) * tracePhase (-cuspFrequency h * (b + z))) := by
    rw [mul_left_comm, ← AddChar.map_add_eq_mul]
    rw [show cuspFrequency h * b + -cuspFrequency h * (b + z) = -cuspFrequency h * z by ring,
      add_comm b z]
  simp_rw [he]
  rw [integral_const_mul]
  exact congrArg (fun z : ℂ => tracePhase (cuspFrequency h * b) * z)
    (period_integral_translation (fun z => f z * tracePhase (-cuspFrequency h * z)) hperiod b)

def rationalCuspPhaseSum (h : O) : ℂ :=
  1 + tracePhase (cuspFrequency h) + tracePhase (cuspFrequency h * 2)

lemma fourCuspAverage_fourier (f : HyperbolicSpace → ℂ) (hc : Continuous f)
    (hf : ∀ n : levelThree, ∀ w, f (complexMatrix n • w) = complexCharacter n * f w)
    (v : ℝ) (hv : 0 < v) (h : O) :
    (∫ z in periodDomain, fourCuspAverage f (upperPoint z v hv) * tracePhase (-cuspFrequency h * z)) =
      (4 : ℂ)⁻¹ * ((∫ z in periodDomain, f (upperPoint z v hv) * tracePhase (-cuspFrequency h * z)) +
        rationalCuspPhaseSum h * ∫ z in periodDomain,
          f (rationalComplex ModularGroup.S • upperPoint z v hv) * tracePhase (-cuspFrequency h * z)) := by
  let A : ℂ → ℂ := fun z => f (upperPoint z v hv)
  let B : ℂ → ℂ := fun z => f (rationalComplex ModularGroup.S • upperPoint z v hv)
  let P : ℂ → ℂ := fun z => tracePhase (-cuspFrequency h * z)
  have hcoord : Continuous (fun z : ℂ => (⟨(z, v), hv⟩ : UpperCoordinates)) := by fun_prop
  have hu : Continuous (fun z : ℂ => upperPoint z v hv) :=
    upperCoordinatesHomeomorph.continuous.comp hcoord
  have hA : Continuous A := hc.comp hu
  have hB : Continuous B := hc.comp ((continuous_hyperbolic_action _).comp hu)
  have hP : Continuous P := tracePhase_continuous.comp (continuous_const.mul continuous_id)
  have hiA : IntegrableOn (fun z => A z * P z) periodDomain :=
    periodDomain_continuous_integrable _ (hA.mul hP)
  have hiB (b : ℂ) : IntegrableOn (fun z => B (z + b) * P z) periodDomain :=
    periodDomain_continuous_integrable _ ((hB.comp (continuous_id.add continuous_const)).mul hP)
  have hiB0 : IntegrableOn (fun z => B z * P z) periodDomain := by simpa only [add_zero] using hiB 0
  have hiAB : IntegrableOn (fun z => A z * P z + B z * P z) periodDomain := hiA.add hiB0
  have hiAB1 : IntegrableOn (fun z => A z * P z + B z * P z + B (z + 1) * P z) periodDomain :=
    hiAB.add (hiB 1)
  have hshift (b : ℂ) : (∫ z in periodDomain, B (z + b) * P z) =
      tracePhase (cuspFrequency h * b) * ∫ z in periodDomain, B z * P z :=
    period_fourier_translation B (rational_translate_period f hf ModularGroup.S v hv) h b
  have he (z : ℂ) : fourCuspAverage f (upperPoint z v hv) * P z =
      (4 : ℂ)⁻¹ * (A z * P z + B z * P z + B (z + 1) * P z + B (z + 2) * P z) := by
    have h1 := rational_T_pow_action 1 z v hv
    simp only [pow_one, Nat.cast_one] at h1
    have h2 := rational_T_pow_action 2 z v hv
    simp only [Nat.cast_ofNat] at h2
    simp only [fourCuspAverage, map_mul, mul_smul, h1, h2, A, B]
    ring
  change (∫ z in periodDomain, fourCuspAverage f (upperPoint z v hv) * P z) = _
  simp_rw [he]
  rw [integral_const_mul, integral_add hiAB1 (hiB 2),
    integral_add hiAB (hiB 1), integral_add hiA hiB0, hshift 1, hshift 2]
  dsimp only [rationalCuspPhaseSum, A, B, P]
  simp only [mul_one]
  ring

/-- The source Fourier series combines the original scattering series and the opposite-cusp Gauss series. -/
theorem rationalSourceEisenstein_fourier (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    (∫ z in periodDomain, rationalSourceEisenstein s (upperPoint z v hv) * tracePhase (-cuspFrequency h * z)) =
      (4 : ℂ)⁻¹ * ((v : ℂ) ^ s * (if h = 0 then ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) else 0) +
        ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
          (arithmeticDirichletSeries s h + rationalCuspPhaseSum h * unramifiedCubicGaussSeries s (9 * h))) := by
  simp_rw [rationalSourceEisenstein_four_cusps s hs]
  rw [fourCuspAverage_fourier _ (hyperbolicEisenstein_continuous s hs)
    (fun n w => hyperbolicEisenstein_automorphy n s hs w)]
  rw [show rationalComplex ModularGroup.S = oppositeMatrix from oppositeSource_matrix]
  change (4 : ℂ)⁻¹ * ((∫ z in periodDomain, upperEisenstein z v hv s * tracePhase (-cuspFrequency h * z)) +
    rationalCuspPhaseSum h * ∫ z in periodDomain, oppositeEisenstein z v hv s * tracePhase (-cuspFrequency h * z)) = _
  rw [integral_upperEisenstein_arithmetic v hv s hs h, oppositeEisenstein_fourier v hv s hs h]
  ring

lemma tracePhase_primary_frequency (h p k : O) (hprimary : lambda ^ 2 ∣ p - 1) :
    tracePhase (cuspFrequency (h * p) * ringComplex k) = tracePhase (cuspFrequency h * ringComplex k) := by
  obtain ⟨t, ht⟩ := three_dvd_lambda_sq.trans hprimary
  have hp : h * p = h + 3 * (h * t) := by linear_combination h * ht
  have he : cuspFrequency (h * p) * ringComplex k =
      cuspFrequency h * ringComplex k + ringComplex (h * t * k) / ringComplex traceLambda := by
    rw [hp]
    simp only [cuspFrequency, map_add, map_mul, map_ofNat]
    field_simp
  rw [he, AddChar.map_add_eq_mul, tracePhase_embedding_div_traceLambda, mul_one]

lemma rationalCuspPhaseSum_primary_mul (h p : O) (hprimary : lambda ^ 2 ∣ p - 1) :
    rationalCuspPhaseSum (h * p) = rationalCuspPhaseSum h := by
  have h1 := tracePhase_primary_frequency h p 1 hprimary
  have h2 := tracePhase_primary_frequency h p 2 hprimary
  simp only [map_one, mul_one] at h1
  simp only [map_ofNat] at h2
  rw [rationalCuspPhaseSum, rationalCuspPhaseSum, h1, h2]

/-- Arithmetic factor in the nonconstant Fourier modes of the rationally averaged source. -/
def rationalSourceArithmeticSeries (s : ℂ) (h : O) : ℂ :=
  (4 : ℂ)⁻¹ * (arithmeticDirichletSeries s h + rationalCuspPhaseSum h * unramifiedCubicGaussSeries s (9 * h))

lemma primary_prime_not_dvd_nine_frequency (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) : ¬ p ∣ 9 * h := by
  simpa only [Units.val_one, pow_zero, mul_one] using
    ramified_prime_frequency_not_dvd h p hp hprimary hph 1 0

theorem rationalSourceArithmeticSeries_prime_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) (hph : ¬ p ∣ h) :
    rationalSourceArithmeticSeries s (h * p ^ 3) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        rationalSourceArithmeticSeries s h -
      unramifiedNormWeight s (Ideal.span {p}) * cubicUnitGaussSum (9 * h) p *
        rationalSourceArithmeticSeries s (h * p) := by
  have hg := unramifiedCubicGaussSeries_prime_recurrence p hp hprimary s hs (9 * h)
    (primary_prime_not_dvd_nine_frequency p hp hprimary h hph)
  rw [primeCubicGauss_one_eq] at hg
  unfold rationalSourceArithmeticSeries
  rw [rationalCuspPhaseSum_primary_mul h (p ^ 3) (primary_pow_congruence p hprimary 3),
    rationalCuspPhaseSum_primary_mul h p hprimary, arithmeticDirichletSeries_prime_recurrence p hp hprimary s hs h hph,
    show 9 * (h * p ^ 3) = (9 * h) * p ^ 3 by ring, hg,
    show 9 * (h * p) = (9 * h) * p by ring]
  ring

theorem rationalSourceArithmeticSeries_cube_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) (hh : h ≠ 0) :
    rationalSourceArithmeticSeries s (h * p ^ 6) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        rationalSourceArithmeticSeries s (h * p ^ 3) -
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3 *
        rationalSourceArithmeticSeries s h := by
  unfold rationalSourceArithmeticSeries
  rw [rationalCuspPhaseSum_primary_mul h (p ^ 6) (primary_pow_congruence p hprimary 6),
    rationalCuspPhaseSum_primary_mul h (p ^ 3) (primary_pow_congruence p hprimary 3),
    arithmeticDirichletSeries_cube_recurrence p hp hprimary s hs h hh,
    show 9 * (h * p ^ 6) = (9 * h) * p ^ 6 by ring,
    show 9 * (h * p ^ 3) = (9 * h) * p ^ 3 by ring,
    unramifiedCubicGaussSeries_cube_recurrence p hp hprimary s hs (9 * h)]
  ring

theorem rationalSourceArithmeticSeries_square_cube (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (s : ℂ) (hs : 2 < s.re) (h : O) (hph : ¬ p ∣ h) :
    rationalSourceArithmeticSeries s (h * p ^ 5) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 3 * unramifiedNormWeight s (Ideal.span {p}) ^ 3) *
        rationalSourceArithmeticSeries s (h * p ^ 2) := by
  unfold rationalSourceArithmeticSeries
  rw [rationalCuspPhaseSum_primary_mul h (p ^ 5) (primary_pow_congruence p hprimary 5),
    rationalCuspPhaseSum_primary_mul h (p ^ 2) (primary_pow_congruence p hprimary 2),
    arithmeticDirichletSeries_square_cube p hp hprimary s hs h hph,
    show 9 * (h * p ^ 5) = (9 * h) * p ^ 5 by ring,
    show 9 * (h * p ^ 2) = (9 * h) * p ^ 2 by ring,
    unramifiedCubicGaussSeries_square_cube p hp hprimary s hs (9 * h)
      (primary_prime_not_dvd_nine_frequency p hp hprimary h hph)]
  ring

/-- Compact translated support for a Fourier test on an arbitrary positive height interval. -/
def rationalIntervalCompact (a b : ℝ) (g : rationalExtension) : Set KernelQuotient :=
  kernelRationalAction g '' kernelCuspIntervalCompact a b

lemma rationalIntervalCompact_isCompact (a b : ℝ) (ha : 0 < a) (g : rationalExtension) :
    IsCompact (rationalIntervalCompact a b g) :=
  (kernelCuspIntervalCompact_isCompact a b ha).image (kernelRationalAction_continuous g)

def rationalIntervalFourier (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) (g : rationalExtension) : KernelQuotientL2 →L[ℂ] ℂ :=
  (kernelCuspIntervalFourier a b ha ρ h).comp (kernelRationalPullback g).toContinuousLinearMap

lemma rationalIntervalFourier_integral (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) (g : rationalExtension) (F : KernelQuotientL2) :
    rationalIntervalFourier a b ha ρ h g F = ∫ w in cuspPeriodStrip a b,
      F (kernelRationalAction g (integralOrbitProjection globalKubotaKernel w)) *
        cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  rw [rationalIntervalFourier, ContinuousLinearMap.comp_apply, kernelCuspIntervalFourier_integral]
  have he := (kernelCuspInterval_projection_quasiMeasurePreserving a b ha).ae_eq_comp
    (kernelRationalPullback_ae g F)
  exact integral_congr_ae (he.mul (Eventually.of_forall (fun _ => rfl)))

lemma rationalIntervalFourier_restrict (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) (g : rationalExtension) (F : KernelQuotientL2) :
    rationalIntervalFourier a b ha ρ h g (kernelMassRestrictionCLM (rationalIntervalCompact a b g)
      (rationalIntervalCompact_isCompact a b ha g).measurableSet F) = rationalIntervalFourier a b ha ρ h g F := by
  rw [rationalIntervalFourier_integral, rationalIntervalFourier_integral]
  have hsource := (kernelRationalAction_measurePreserving g).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe _ (rationalIntervalCompact_isCompact a b ha g).measurableSet F)
  have he := (kernelCuspInterval_projection_quasiMeasurePreserving a b ha).ae_eq_comp hsource
  apply integral_congr_ae
  filter_upwards [he, ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  have hm : kernelRationalAction g (integralOrbitProjection globalKubotaKernel w) ∈ rationalIntervalCompact a b g :=
    Set.mem_image_of_mem _ (Set.mem_image_of_mem _ (cuspPeriodStrip_subset_intervalHull a b hwm))
  exact congrArg (fun z : ℂ => z * cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem hm _))

def rationalIntervalFamily (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) (g : rationalExtension) (s : ℂ) : ℂ :=
  rationalIntervalFourier a b ha ρ h g
    (kernelLocalCorrectedSeed (rationalIntervalCompact a b g) (rationalIntervalCompact_isCompact a b ha g)
      2 3 (by norm_num) (by norm_num) s)

lemma rationalIntervalFamily_analyticAt (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) (g : rationalExtension) (s : ℂ) (hs : 1 < s.re) (hi : 0 < s.im) :
    AnalyticAt ℂ (rationalIntervalFamily a b ha ρ h g) s :=
  (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (rationalIntervalFourier a b ha ρ h g) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (rationalIntervalCompact_isCompact a b ha g)
        2 3 (by norm_num) (by norm_num) s hs.ne' hi.ne') rfl

lemma rationalIntervalFamily_residue_limit (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) (g : rationalExtension) :
    Tendsto (fun s : ℂ => (s - 4 / 3) * rationalIntervalFamily a b ha ρ h g s)
      (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (rationalIntervalFourier a b ha ρ h g cubicEisensteinResidue)) := by
  have he := (rationalIntervalFourier a b ha ρ h g).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (rationalIntervalCompact_isCompact a b ha g))
  simpa only [Function.comp_def, map_smul, smul_eq_mul, rationalIntervalFourier_restrict,
    rationalIntervalFamily] using he

lemma rationalIntervalFamily_initial (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) (g : rationalExtension) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    rationalIntervalFamily a b ha ρ h g s = ∫ w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (integralComplexMatrix (g : SL(2, O)) • w) *
        cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  rw [rationalIntervalFamily, rationalIntervalFourier_integral]
  have hsource := (kernelRationalAction_measurePreserving g).quasiMeasurePreserving.ae_eq_comp
    (cubicEisensteinLocalFamily_initial_ae _ (rationalIntervalCompact_isCompact a b ha g) s hs hi)
  have he := (kernelCuspInterval_projection_quasiMeasurePreserving a b ha).ae_eq_comp hsource
  apply integral_congr_ae
  filter_upwards [he, ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  have hm : kernelRationalAction g (integralOrbitProjection globalKubotaKernel w) ∈ rationalIntervalCompact a b g :=
    Set.mem_image_of_mem _ (Set.mem_image_of_mem _ (cuspPeriodStrip_subset_intervalHull a b hwm))
  dsimp only [Function.comp_def] at hw
  rw [hw, Set.indicator_of_mem hm, kernelRationalAction_mk, kernelQuotientEisenstein_mk]

lemma rationalIntervalFamily_opposite_initial (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    rationalIntervalFamily a b ha ρ h oppositeSource s =
      unramifiedCubicGaussSeries s (9 * h) * cuspIntervalWhittakerFactor a b ρ s h := by
  rw [rationalIntervalFamily_initial a b ha ρ h oppositeSource s hs hi]
  let g : HyperbolicSpace → ℂ := fun w =>
    hyperbolicEisenstein s (integralComplexMatrix (oppositeSource : SL(2, O)) • w) * cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s (by linarith)).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspInterval_integral_coordinates a b ha g hg.aestronglyMeasurable
    (cuspInterval_continuous_integrable a b ha g hg)]
  have hinner (v : ℝ) (hv : 0 < v) : (∫ z in periodDomain, g (cuspCoordinateLift (v, z))) =
      ρ v * (((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
        unramifiedCubicGaussSeries s (9 * h)) := by
    simp_rw [g, cuspCoordinateLift_positive v _ hv, hyperbolicEisenstein_opposite_upper,
      cuspWeightedFourierPhase, hyperbolicHeight_upperPoint, cuspFourierPhase, hyperbolicHorizontal_upperPoint]
    rw [← oppositeEisenstein_fourier v hv s (by linarith) h, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall (fun z => by ring))
  rw [cuspIntervalWhittakerFactor, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne'
  dsimp only
  rw [hinner v (ha.trans_le hv.1)]
  have hp : (v : ℂ) ^ (-s - 1) = (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
    rw [show -s - 1 = (2 - s) - 3 by ring, Complex.cpow_sub _ _ hv0]
    congr 1
    exact Complex.cpow_natCast _ 3
  rw [hp]
  ring

/-- Cross multiplication continues a Fourier factorization even when a weighted height factor vanishes. -/
theorem cuspScalarResidue_cross (T0 T1 H0 H1 : ℂ → ℂ) (R0 R1 : ℂ)
    (hT0 : AnalyticOnNhd ℂ T0 {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hT1 : AnalyticOnNhd ℂ T1 {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hH0 : AnalyticOnNhd ℂ H0 {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hH1 : AnalyticOnNhd ℂ H1 {s : ℂ | 1 < s.re ∧ 0 < s.im})
    (hH0c : ContinuousAt H0 (4 / 3 : ℂ)) (hH1c : ContinuousAt H1 (4 / 3 : ℂ))
    (hR0 : Tendsto (fun s : ℂ => (s - 4 / 3) * T0 s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 R0))
    (hR1 : Tendsto (fun s : ℂ => (s - 4 / 3) * T1 s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 R1))
    (hrel : ∀ s : ℂ, 4 < s.re → 0 < s.im → T0 s * H1 s = T1 s * H0 s) :
    R0 * H1 (4 / 3) = R1 * H0 (4 / 3) := by
  have hl : AnalyticOnNhd ℂ (fun s => T0 s * H1 s) {s : ℂ | 1 < s.re ∧ 0 < s.im} :=
    fun s hs => (hT0 s hs).mul (hH1 s hs)
  have hr : AnalyticOnNhd ℂ (fun s => T1 s * H0 s) {s : ℂ | 1 < s.re ∧ 0 < s.im} :=
    fun s hs => (hT1 s hs).mul (hH0 s hs)
  have hconvex : Convex ℝ {s : ℂ | 1 < s.re ∧ 0 < s.im} :=
    ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s => T0 s * H1 s) =ᶠ[𝓝 (5 + Complex.I : ℂ)] (fun s => T1 s * H0 s) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact hrel s hs.1 hs.2
  have heq := hl.eqOn_of_preconnected_of_eventuallyEq hr hconvex.isPreconnected (by norm_num) hev
  have hlim0 := (hR0.mul (hH1c.tendsto.mono_left nhdsWithin_le_nhds)).comp thetaApproach_tendsto_complex_punctured
  have hlim1 := (hR1.mul (hH0c.tendsto.mono_left nhdsWithin_le_nhds)).comp thetaApproach_tendsto_complex_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hlim0 hlim1
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have htD : (4 / 3 : ℂ) + (t : ℂ) + (t : ℂ) * Complex.I ∈ {s : ℂ | 1 < s.re ∧ 0 < s.im} := by
    constructor
    · norm_num
      linarith
    · simpa using ht
  simpa only [Function.comp_def, mul_assoc] using congrArg
    (fun z : ℂ => ((4 / 3 : ℂ) + (t : ℂ) + (t : ℂ) * Complex.I - 4 / 3) * z) (heq htD)

lemma rationalCuspFamily_opposite_all_initial (h : O) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    rationalCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s =
      unramifiedCubicGaussSeries s (9 * h) * cuspWhittakerHeightFactor s h := by
  rw [rationalCuspFamily_initial h oppositeSource 2 3
    (by norm_num) (by norm_num) (by norm_num) s hs hi, opposite_cusp_fourier_average s (by linarith)]

def oppositeCuspResidue (h : O) : ℂ :=
  rationalCuspFourier h oppositeSource cubicEisensteinResidue / cuspWhittakerHeightFactor (4 / 3) h

/-- Every positive height interval sees the same opposite-cusp residue, including the constant mode. -/
theorem rationalIntervalFourier_opposite_residue (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) : rationalIntervalFourier a b ha ρ h oppositeSource cubicEisensteinResidue =
      oppositeCuspResidue h * cuspIntervalWhittakerFactor a b ρ (4 / 3) h := by
  have he := cuspScalarResidue_cross
    (rationalIntervalFamily a b ha ρ h oppositeSource)
    (rationalCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num))
    (fun s => cuspIntervalWhittakerFactor a b ρ s h) (fun s => cuspWhittakerHeightFactor s h)
    (rationalIntervalFourier a b ha ρ h oppositeSource cubicEisensteinResidue)
    (rationalCuspFourier h oppositeSource cubicEisensteinResidue)
    (fun s hs => rationalIntervalFamily_analyticAt a b ha ρ h oppositeSource s hs.1 hs.2)
    (fun s hs => rationalCuspFamily_analyticAt_nonreal h oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
    (fun s hs => cuspIntervalWhittakerFactor_analyticAt a b ha ρ h s hs.1)
    (fun s hs => cuspWhittakerHeightFactor_analyticAt h s hs.1)
    (cuspIntervalWhittakerFactor_analyticAt a b ha ρ h (4 / 3) (by norm_num)).continuousAt
    (cuspWhittakerHeightFactor_analyticAt h (4 / 3) (by norm_num)).continuousAt
    (rationalIntervalFamily_residue_limit a b ha ρ h oppositeSource)
    (rationalCuspFamily_residue_limit h oppositeSource 2 3 (by norm_num) (by norm_num)) (by
      intro s hs hi
      rw [rationalIntervalFamily_opposite_initial a b ha ρ h s hs hi,
        rationalCuspFamily_opposite_all_initial h s hs hi]
      ring)
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero h)
  rw [he, oppositeCuspResidue]
  field_simp [cuspWhittakerHeightFactor_center_ne_zero h]

theorem oppositeCuspResidue_eq_unramified (h : O) : oppositeCuspResidue h = unramifiedGaussResidue (9 * h) := by
  have he := cuspScalarResidue_cross
    (rationalCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num))
    (rationalCuspFamily (3 * (9 * h)) oppositeSource 2 3 (by norm_num) (by norm_num))
    (fun s => cuspWhittakerHeightFactor s h) (fun s => cuspWhittakerHeightFactor s (3 * (9 * h)))
    (rationalCuspFourier h oppositeSource cubicEisensteinResidue)
    (rationalCuspFourier (3 * (9 * h)) oppositeSource cubicEisensteinResidue)
    (fun s hs => rationalCuspFamily_analyticAt_nonreal h oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
    (fun s hs => rationalCuspFamily_analyticAt_nonreal (3 * (9 * h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
    (fun s hs => cuspWhittakerHeightFactor_analyticAt h s hs.1)
    (fun s hs => cuspWhittakerHeightFactor_analyticAt (3 * (9 * h)) s hs.1)
    (cuspWhittakerHeightFactor_analyticAt h (4 / 3) (by norm_num)).continuousAt
    (cuspWhittakerHeightFactor_analyticAt (3 * (9 * h)) (4 / 3) (by norm_num)).continuousAt
    (rationalCuspFamily_residue_limit h oppositeSource 2 3 (by norm_num) (by norm_num))
    (rationalCuspFamily_residue_limit (3 * (9 * h)) oppositeSource 2 3 (by norm_num) (by norm_num)) (by
      intro s hs hi
      rw [rationalCuspFamily_opposite_all_initial h s hs hi,
        rationalCuspFamily_opposite_initial (9 * h) s hs hi]
      ring)
  unfold oppositeCuspResidue unramifiedGaussResidue
  exact (div_eq_div_iff (cuspWhittakerHeightFactor_center_ne_zero h)
    (cuspWhittakerHeightFactor_center_ne_zero (3 * (9 * h)))).mpr he

lemma cuspIntervalWhittakerFactor_center_bessel (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (hh : h ≠ 0) :
    cuspIntervalWhittakerFactor a b ρ (4 / 3) h =
      ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
        (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ)) *
      ∫ v in Set.Icc a b, ρ v *
        (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2) := by
  rw [cuspIntervalWhittakerFactor, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  rw [sourceFourierKernel_residual_height h hh v (ha.trans_le hv.1)]
  ring

/-- Bessel coefficient of the residual function at the opposite cusp. -/
def oppositeResidualFourierCoefficient (h : O) : ℂ :=
  (oppositeCuspResidue h / ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) *
    ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
      (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ))

theorem rationalIntervalFourier_opposite_bessel (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (hh : h ≠ 0) :
    rationalIntervalFourier a b ha ρ h oppositeSource cubicEisensteinResidue =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * oppositeResidualFourierCoefficient h *
        ∫ v in Set.Icc a b, ρ v *
          (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2) := by
  rw [rationalIntervalFourier_opposite_residue,
    cuspIntervalWhittakerFactor_center_bessel a b ha ρ h hh, oppositeResidualFourierCoefficient]
  field_simp [cusp_volume_ne_zero]

/-- Rational pullback preserves the uniform Fourier-test bound. -/
theorem rationalIntervalFourier_uniform_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : BoundedContinuousFunction ℝ ℂ) (h : O)
      (g : rationalExtension) (F : KernelQuotientL2),
      ‖rationalIntervalFourier a b ha ρ h g F‖ ≤ C * ‖ρ‖ * ‖F‖ := by
  obtain ⟨C, hC, hbound⟩ := kernelCuspIntervalFourier_uniform_bound a b ha
  refine ⟨C, hC, ?_⟩
  intro ρ h g F
  change ‖kernelCuspIntervalFourier a b ha ρ h (kernelRationalPullback g F)‖ ≤ _
  simpa only [LinearIsometry.norm_map] using hbound ρ h (kernelRationalPullback g F)

lemma oppositeResidualFourierCoefficient_interval_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖oppositeResidualFourierCoefficient h‖ * ‖∫ v in Set.Icc a b,
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := rationalIntervalFourier_uniform_bound a b ha
  let area : ℂ := ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)
  have harea : 0 < ‖area‖ := norm_pos_iff.mpr cusp_volume_ne_zero
  refine ⟨C * ‖BoundedContinuousFunction.const ℝ (1 : ℂ)‖ * ‖cubicEisensteinResidue‖ / ‖area‖,
    by positivity, ?_⟩
  intro h hh
  have hb := hbound (BoundedContinuousFunction.const ℝ 1) h oppositeSource cubicEisensteinResidue
  rw [rationalIntervalFourier_opposite_bessel a b ha _ h hh] at hb
  simp only [BoundedContinuousFunction.const_apply, one_mul, norm_mul] at hb
  apply (le_div_iff₀ harea).mpr
  calc
    _ = ‖area‖ * ‖oppositeResidualFourierCoefficient h‖ * ‖∫ v in Set.Icc a b,
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2‖ := by ring
    _ ≤ _ := hb

theorem oppositeResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖oppositeResidualFourierCoefficient h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) :=
  cubicBesselCoefficient_subexponential oppositeResidualFourierCoefficient
    oppositeResidualFourierCoefficient_interval_bound ε hε

lemma rationalCuspPhaseSum_norm_le (h : O) : ‖rationalCuspPhaseSum h‖ ≤ 3 := by
  calc
    _ ≤ ‖(1 : ℂ) + tracePhase (cuspFrequency h)‖ + ‖tracePhase (cuspFrequency h * 2)‖ := norm_add_le _ _
    _ ≤ (‖(1 : ℂ)‖ + ‖tracePhase (cuspFrequency h)‖) + ‖tracePhase (cuspFrequency h * 2)‖ :=
      add_le_add (norm_add_le (1 : ℂ) (tracePhase (cuspFrequency h))) le_rfl
    _ = 3 := by rw [norm_one, tracePhase_norm, tracePhase_norm]; norm_num

def rationalSourceResidualFourierCoefficient (h : O) : ℂ :=
  (4 : ℂ)⁻¹ * (cubicResidualFourierCoefficient h + rationalCuspPhaseSum h * oppositeResidualFourierCoefficient h)

theorem rationalSourceResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖rationalSourceResidualFourierCoefficient h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) := by
  obtain ⟨C, hC, hboundC⟩ := cubicResidualFourierCoefficient_subexponential ε hε
  obtain ⟨D, hD, hboundD⟩ := oppositeResidualFourierCoefficient_subexponential ε hε
  refine ⟨(4 : ℝ)⁻¹ * (C + 3 * D), by positivity, ?_⟩
  intro h hh
  have hsum : ‖cubicResidualFourierCoefficient h + rationalCuspPhaseSum h * oppositeResidualFourierCoefficient h‖ ≤
      ‖cubicResidualFourierCoefficient h‖ + 3 * ‖oppositeResidualFourierCoefficient h‖ := by
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (rationalCuspPhaseSum_norm_le h)
      (norm_nonneg (oppositeResidualFourierCoefficient h)))
  rw [rationalSourceResidualFourierCoefficient, norm_mul]
  have hnorm : ‖(4 : ℂ)⁻¹‖ = (4 : ℝ)⁻¹ := by norm_num
  rw [hnorm]
  calc
    _ ≤ (4 : ℝ)⁻¹ * (‖cubicResidualFourierCoefficient h‖ + 3 * ‖oppositeResidualFourierCoefficient h‖) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (4 : ℝ)⁻¹ * (C * Real.exp (ε * ‖cuspFrequency h‖) + 3 * (D * Real.exp (ε * ‖cuspFrequency h‖))) :=
      mul_le_mul_of_nonneg_left (add_le_add (hboundC h hh)
        (mul_le_mul_of_nonneg_left (hboundD h hh) (by norm_num))) (by positivity)
    _ = _ := by ring

lemma cuspFourier_continuous_log_height (f : HyperbolicSpace → ℂ) (hf : Continuous f) (h : O) :
    Continuous (fun t : ℝ => ∫ z in periodDomain,
      f (upperPoint z (Real.exp t) (Real.exp_pos t)) * tracePhase (-cuspFrequency h * z)) := by
  let F : ℝ → ℂ → ℂ := fun t z =>
    f (upperPoint z (Real.exp t) (Real.exp_pos t)) * tracePhase (-cuspFrequency h * z)
  have hcoord : Continuous (fun p : ℝ × ℂ =>
      (⟨(p.2, Real.exp p.1), Real.exp_pos p.1⟩ : UpperCoordinates)) := by fun_prop
  have hF : Continuous F.uncurry :=
    (hf.comp (upperCoordinatesHomeomorph.continuous.comp hcoord)).mul
      (tracePhase_continuous.comp (continuous_const.mul continuous_snd))
  let K : Set ℂ := Metric.closedBall 0 (∑ i, ‖periodBasis i‖)
  have hsub : periodDomain ⊆ K := by
    intro z hz
    simpa only [K, Metric.mem_closedBall, dist_zero_right] using norm_mem_periodDomain z hz
  have hμ : (volume.restrict periodDomain).restrict K = (volume : Measure ℂ).restrict periodDomain := by
    rw [Measure.restrict_restrict (isCompact_closedBall 0 (∑ i, ‖periodBasis i‖)).measurableSet, inter_eq_right.mpr hsub]
  letI : IsFiniteMeasure ((volume : Measure ℂ).restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  have hc := continuous_parametric_integral_of_continuous (μ := volume.restrict periodDomain) hF
    (isCompact_closedBall 0 (∑ i, ‖periodBasis i‖))
  change Continuous (fun t => ∫ z, F t z ∂(volume.restrict periodDomain).restrict K) at hc
  rw [hμ] at hc
  exact hc

def continuousCuspSlice (f : HyperbolicSpace → ℂ) (h : O) (v : ℝ) : ℂ :=
  (∫ z in periodDomain, f (cuspCoordinateLift (v, z)) * tracePhase (-cuspFrequency h * z)) / (v : ℂ) ^ 3

lemma continuousCuspSlice_continuousOn (f : HyperbolicSpace → ℂ) (hf : Continuous f) (h : O) :
    ContinuousOn (continuousCuspSlice f h) (Ioi 0) := by
  let J : ℝ → ℂ := fun t => ∫ z in periodDomain,
    f (upperPoint z (Real.exp t) (Real.exp_pos t)) * tracePhase (-cuspFrequency h * z)
  have hJ : Continuous J := cuspFourier_continuous_log_height f hf h
  have hc : ContinuousOn (fun v : ℝ => J (Real.log v) / (v : ℂ) ^ 3) (Ioi 0) := by
    intro v hv
    exact ((hJ.continuousAt.comp (Real.continuousAt_log hv.ne')).div
      ((Complex.continuous_ofReal.pow 3).continuousAt)
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hv.ne'))).continuousWithinAt
  apply hc.congr
  intro v hv
  simp only [continuousCuspSlice, J, cuspCoordinateLift_positive v _ hv, Real.exp_log hv]

lemma continuousCuspSlice_weighted_integral (f : HyperbolicSpace → ℂ) (hf : Continuous f)
    (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    (∫ w in cuspPeriodStrip a b, f w * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume) =
      ∫ v in Set.Icc a b, ρ v * continuousCuspSlice f h v := by
  let g : HyperbolicSpace → ℂ := fun w => f w * cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := hf.mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspInterval_integral_coordinates a b ha g hg.aestronglyMeasurable
    (cuspInterval_continuous_integrable a b ha g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos := ha.trans_le hv.1
  change (∫ z in periodDomain, g (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 =
    ρ v * ((∫ z in periodDomain,
      f (cuspCoordinateLift (v, z)) * tracePhase (-cuspFrequency h * z)) / (v : ℂ) ^ 3)
  rw [← mul_div_assoc]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [g]
    rw [cuspWeightedFourierPhase, cuspFourierPhase, cuspCoordinateLift_positive v z hpos,
      hyperbolicHeight_upperPoint, hyperbolicHorizontal_upperPoint]
    ring)

/-- Continuous Fourier slices are determined at every positive height by bounded interval tests. -/
theorem continuousCuspSlice_eq_of_interval_tests (f : HyperbolicSpace → ℂ) (hf : Continuous f)
    (h : O) (D : ℝ → ℂ) (hD : ContinuousOn D (Set.Ioi 0))
    (htest : ∀ a b : ℝ, ∀ _ha : 0 < a, ∀ ρ : BoundedContinuousFunction ℝ ℂ,
      (∫ w in cuspPeriodStrip a b, f w * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume) =
        ∫ v in Set.Icc a b, ρ v * D v)
    (v : ℝ) (hv : 0 < v) : continuousCuspSlice f h v = D v := by
  let a := v / 2
  let b := 2 * v
  have ha : 0 < a := half_pos hv
  have hs : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => ha.trans_le hx.1
  have hc := (continuousCuspSlice_continuousOn f hf h).mono hs
  have hd := hD.mono hs
  have he : continuousCuspSlice f h =ᵐ[volume.restrict (Set.Icc a b)] D := by
    apply interval_ae_eq_of_boundedContinuous_tests a b _ _ hc.integrableOn_Icc hd.integrableOn_Icc
    intro ρ
    rw [← continuousCuspSlice_weighted_integral f hf a b ha ρ h]
    exact htest a b ha ρ
  have he' := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self he
  exact Measure.eqOn_Ioo_of_ae_eq volume he' (hc.mono Ioo_subset_Icc_self)
    (hd.mono Ioo_subset_Icc_self) (by constructor <;> dsimp [a, b] <;> linarith)

lemma rationalIntervalFourier_residual_integral (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) (g : rationalExtension) :
    rationalIntervalFourier a b ha ρ h g cubicEisensteinResidue = ∫ w in cuspPeriodStrip a b,
      cubicResidualFunction (integralComplexMatrix (g : SL(2, O)) • w) *
        cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  rw [rationalIntervalFourier_integral]
  have he := (measurePreserving_smul (integralComplexMatrix (g : SL(2, O)))
    hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp cubicEisensteinResidue_continuous_representative
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae he (s := cuspPeriodStrip a b)] with w hw
  exact congrArg (fun z : ℂ => z * cuspWeightedFourierPhase ρ h w) hw

/-- Every opposite-cusp Fourier mode is the archimedean kernel times the actual Gauss residue. -/
theorem cubicResidualFunction_opposite_fourier (v : ℝ) (hv : 0 < v) (h : O) :
    (∫ z in periodDomain, cubicResidualFunction (rationalComplex ModularGroup.S • upperPoint z v hv) *
      tracePhase (-cuspFrequency h * z)) =
      oppositeCuspResidue h * ((v : ℂ) ^ (2 / 3 : ℂ) * sourceFourierKernel (4 / 3) (cuspFrequency h * v)) := by
  let f : HyperbolicSpace → ℂ := fun w => cubicResidualFunction (rationalComplex ModularGroup.S • w)
  have hf : Continuous f := cubicResidualFunction_continuous.comp (continuous_hyperbolic_action _)
  let D : ℝ → ℂ := fun v => oppositeCuspResidue h *
    ((v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * sourceFourierKernel (4 / 3) (cuspFrequency h * v))
  have hD : ContinuousOn D (Set.Ioi 0) := by
    intro v hv
    exact (continuousAt_const.mul
      ((Complex.continuousAt_ofReal_cpow_const v _ (Or.inr hv.ne')).mul
        (((sourceFourierKernel_continuous_freq (4 / 3) (by norm_num)).comp
          (Complex.continuous_ofReal.const_mul (cuspFrequency h))).continuousAt))).continuousWithinAt
  have he := continuousCuspSlice_eq_of_interval_tests f hf h D hD (by
    intro a b ha ρ
    change (∫ w in cuspPeriodStrip a b,
      cubicResidualFunction (integralComplexMatrix (oppositeSource : SL(2, O)) • w) *
        cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume) = _
    rw [← rationalIntervalFourier_residual_integral a b ha ρ h oppositeSource,
      rationalIntervalFourier_opposite_residue, cuspIntervalWhittakerFactor, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => by dsimp only [D]; ring)) v hv
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hpow : (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * (v : ℂ) ^ 3 = (v : ℂ) ^ (2 / 3 : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hv0]
    congr 1
    norm_num
  dsimp only [continuousCuspSlice, f, D] at he
  simp_rw [cuspCoordinateLift_positive v _ hv] at he
  rw [div_eq_iff (pow_ne_zero 3 hv0)] at he
  rw [he]
  linear_combination oppositeCuspResidue h * sourceFourierKernel (4 / 3) (cuspFrequency h * v) * hpow

lemma oppositeResidual_whittaker_bessel (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    oppositeCuspResidue h * ((v : ℂ) ^ (2 / 3 : ℂ) * sourceFourierKernel (4 / 3) (cuspFrequency h * v)) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * oppositeResidualFourierCoefficient h * (v : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * (v : ℂ) ^ 3 = (v : ℂ) ^ (2 / 3 : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hv0]
    congr 1
    norm_num
  calc
    _ = oppositeCuspResidue h * (((v : ℂ) ^ (-(4 / 3 : ℂ) - 1) *
        sourceFourierKernel (4 / 3) (cuspFrequency h * v)) * (v : ℂ) ^ 3) := by rw [← hp]; ring
    _ = _ := by
      rw [sourceFourierKernel_residual_height h hh v hv, oppositeResidualFourierCoefficient]
      field_simp [hv0, cusp_volume_ne_zero]

theorem cubicResidualFunction_opposite_fourier_bessel (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    (∫ z in periodDomain, cubicResidualFunction (rationalComplex ModularGroup.S • upperPoint z v hv) *
      tracePhase (-cuspFrequency h * z)) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * oppositeResidualFourierCoefficient h * (v : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  rw [cubicResidualFunction_opposite_fourier, oppositeResidual_whittaker_bessel v hv h hh]

/-- The explicit source coefficient is the Fourier coefficient of the actual projected residual vector. -/
theorem cubicSourceResidualFunction_fourier_bessel (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    (∫ z in periodDomain, cubicSourceResidualFunction (upperPoint z v hv) * tracePhase (-cuspFrequency h * z)) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * rationalSourceResidualFourierCoefficient h * (v : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  simp_rw [cubicSourceResidualFunction_four_cusps]
  rw [fourCuspAverage_fourier _ cubicResidualFunction_continuous cubicResidualFunction_automorphy,
    cubicResidualFunction_fourier, cubicResidualFunction_opposite_fourier_bessel v hv h hh,
    cubicResidualFullModeAmplitude, if_neg hh, rationalSourceResidualFourierCoefficient]
  ring

/-- The two independent ramified symbol classes force both a sign and a cube exponent. -/
lemma ramified_constant_support (u : Oˣ) (n : ℕ)
    (hA : arithmeticResidueSum 0 ((u : O) * lambda ^ (n + 2)) ≠ 0) :
    (u = 1 ∨ u = -1) ∧ 3 ∣ n + 2 := by
  have he := constant_coefficient_ramified_equation _ (ramifiedElement_ne_zero u (n + 2))
    (ramifiedElement_level u (n + 2) (by omega)) hA u (n + 2) 1 one_ne_zero
    (by simp only [one_pow, mul_one])
  have hu := unit_eq_sign_of_symbol_class u (by
    simpa only [cubicExp_zero, one_pow, mul_one] using he 0 1)
  have hpow : omega ^ (n + 2) = 1 := by
    rcases hu with hu | hu
    · simpa only [hu, symbol_one_numerator _ (primaryCoord_primary 1 0), one_mul,
        cubicExp, Int.reduceMod, Int.toNat_one, pow_one] using he 1 0
    · simpa only [hu, symbol_neg_one _ (primaryCoord_primary 1 0), one_mul,
        cubicExp, Int.reduceMod, Int.toNat_one, pow_one] using he 1 0
  exact ⟨hu.imp (fun h => Units.ext h) (fun h => Units.ext h),
    (omega_primitive.pow_eq_one_iff_dvd (n + 2)).mp hpow⟩

lemma arithmeticResidueSum_zero_ramified (u : Oˣ) (n : ℕ) :
    arithmeticResidueSum 0 ((u : O) * lambda ^ (n + 2)) =
      if u = 1 ∨ u = -1 then if 3 ∣ n + 2 then ((3 ^ (n + 2) : ℕ) : ℂ) else 0 else 0 := by
  by_cases hu : u = 1 ∨ u = -1
  · rw [if_pos hu]
    by_cases hn : 3 ∣ n + 2
    · rw [if_pos hn]
      obtain ⟨j, hj⟩ := hn
      have hjpos : 0 < j := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
      let I : GoodIdeal := ⟨1, by rw [primaryIdealGenerator_one]; exact one_ne_zero⟩
      have hcol (b : Bool) : cubeColumn b k I = cubeSign b * lambda ^ (n + 2) := by
        rw [cubeColumn_expanded]
        simp only [I, primaryIdealGenerator_one, mul_one, cubeSign_cube]
        rw [← hj]
        exact mul_comm _ _
      have hval (b : Bool) := (congrArg (arithmeticResidueSum 0) (hcol b)).symm.trans
        (cubeColumn_arithmetic_sum b k I)
      have htot : idealTotient (1 : Ideal O) = 1 := by
        have hz (x : O ⧸ (1 : Ideal O)) : x = 0 := by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)
        letI : Subsingleton (O ⧸ (1 : Ideal O)) := ⟨fun x y => (hz x).trans (hz y).symm⟩
        simp [idealTotient]
      simp only [I, map_one, one_pow, mul_one, htot] at hval
      rcases hu with rfl | rfl
      · simpa only [cubeSign, Units.val_one, one_mul, hj] using hval false
      · simpa only [cubeSign, Units.val_neg, Units.val_one, hj] using hval true
    · rw [if_neg hn]
      exact not_ne_iff.mp (fun hA => hn (ramified_constant_support u n hA).2)
  · rw [if_neg hu]
    exact not_ne_iff.mp (fun hA => hu (ramified_constant_support u n hA).1)

/-- The constant mode separates into a ramified scalar and the unramified Gauss series. -/
lemma arithmeticDirichletSeries_zero_separate (s : ℂ) (hs : 2 < s.re) :
    arithmeticDirichletSeries s 0 =
      (∑' u : Oˣ, ∑' n : ℕ, ((3 ^ (n + 2) : ℕ) : ℂ) ^ (-s) *
        arithmeticResidueSum 0 ((u : O) * lambda ^ (n + 2))) * unramifiedCubicGaussSeries s 0 := by
  rw [arithmeticDirichletSeries_ramified_reindex s hs 0, ← tsum_mul_right]
  apply tsum_congr
  intro u
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  rw [unramifiedCubicGaussSeries, ← tsum_mul_left]
  apply tsum_congr
  intro I
  simpa only [mul_zero, zero_mul] using arithmeticDirichletTerm_ramified_gauss s 0 u n I

/-- Positive ramified cube exponents, with the level-three shift removed. -/
def ramifiedCubeExponent : ℕ ≃ {n : ℕ // 3 ∣ n + 2} :=
  Equiv.ofBijective (fun k => ⟨3 * k + 1, ⟨k + 1, by omega⟩⟩) ⟨by
    intro a b he
    have he' := congrArg Subtype.val he
    dsimp only at he'
    omega, by
    rintro ⟨n, k, hk⟩
    refine ⟨k - 1, Subtype.ext ?_⟩
    dsimp only
    omega⟩

lemma zero_ramified_geometric (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, ((3 ^ (n + 2) : ℕ) : ℂ) ^ (-s) *
      (if 3 ∣ n + 2 then ((3 ^ (n + 2) : ℕ) : ℂ) else 0)) =
      ((3 : ℂ) ^ (3 * s - 3) - 1)⁻¹ := by
  let F : ℕ → ℂ := fun n => ((3 ^ (n + 2) : ℕ) : ℂ) ^ (-s) *
    (if 3 ∣ n + 2 then ((3 ^ (n + 2) : ℕ) : ℂ) else 0)
  have hsup : Function.support F ⊆ {n : ℕ | 3 ∣ n + 2} := by
    intro n hn
    by_contra h
    change ¬ 3 ∣ n + 2 at h
    exact hn (by simp only [F, if_neg h, mul_zero])
  change (∑' n, F n) = _
  rw [← tsum_subtype_eq_of_support_subset hsup]
  change (∑' n : {n : ℕ // 3 ∣ n + 2}, F n.val) = _
  rw [← ramifiedCubeExponent.tsum_eq]
  have he (k : ℕ) : F (ramifiedCubeExponent k).val = ramifiedRatio s ^ (k + 1) := by
    change ((3 ^ (3 * k + 1 + 2) : ℕ) : ℂ) ^ (-s) *
      (if 3 ∣ 3 * k + 1 + 2 then ((3 ^ (3 * k + 1 + 2) : ℕ) : ℂ) else 0) = _
    rw [if_pos (show 3 ∣ 3 * k + 1 + 2 from ⟨k + 1, by omega⟩),
      show 3 * k + 1 + 2 = 3 * (k + 1) by omega]
    simpa using cube_norm_weight_algebra s k 1 (by decide)
  simp_rw [he]
  exact ramified_geometric_sum s hs

lemma zero_ramified_factor (s : ℂ) (hs : 1 < s.re) :
    (∑' u : Oˣ, ∑' n : ℕ, ((3 ^ (n + 2) : ℕ) : ℂ) ^ (-s) *
      arithmeticResidueSum 0 ((u : O) * lambda ^ (n + 2))) =
      2 * ((3 : ℂ) ^ (3 * s - 3) - 1)⁻¹ := by
  have hne : (1 : Oˣ) ≠ -1 := by
    intro he
    have hv := congrArg Units.val he
    norm_num at hv
  rw [tsum_eq_sum (s := {1, -1}) (fun u hu => by
    have hn : ¬ (u = 1 ∨ u = -1) := by simpa only [Finset.mem_insert,
      Finset.mem_singleton] using hu
    simp only [arithmeticResidueSum_zero_ramified, if_neg hn, mul_zero, tsum_zero])]
  simp only [Finset.sum_insert, Finset.mem_singleton, hne, not_false_eq_true, Finset.sum_singleton,
    arithmeticResidueSum_zero_ramified, true_or, or_true, ite_true]
  rw [zero_ramified_geometric s hs]
  ring

theorem arithmeticDirichletSeries_zero_unramified (s : ℂ) (hs : 2 < s.re) :
    arithmeticDirichletSeries s 0 =
      (2 * ((3 : ℂ) ^ (3 * s - 3) - 1)⁻¹) * unramifiedCubicGaussSeries s 0 := by
  rw [arithmeticDirichletSeries_zero_separate s hs, zero_ramified_factor s (by linarith)]

lemma ramifiedDenominator_analytic (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (3 : ℂ) ^ (3 * z - 3) - 1) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall fun z =>
    (((differentiableAt_id.const_mul 3).sub_const 3).const_cpow
      (Or.inl (by norm_num : (3 : ℂ) ≠ 0))).sub_const 1

lemma ramifiedDenominator_ne_zero (s : ℂ) (hs : 1 < s.re) :
    (3 : ℂ) ^ (3 * s - 3) - 1 ≠ 0 := by
  intro hz
  have hn := norm_ramifiedRatio_lt_one s hs
  have hi : ramifiedRatio s = ((3 : ℂ) ^ (3 * s - 3))⁻¹ := by
    rw [ramifiedRatio, ← Complex.cpow_neg]
    congr 1
    ring
  rw [hi, sub_eq_zero.mp hz, inv_one, norm_one] at hn
  exact lt_irrefl 1 hn

lemma cuspWhittakerHeightFactor_zero (s : ℂ) (hs : 1 < s.re) :
    cuspWhittakerHeightFactor s 0 = (Real.pi : ℂ) / (s - 1) *
      cuspIntervalMellin 5 6 (BoundedContinuousFunction.const ℝ 1) (-s - 1) := by
  simp only [cuspWhittakerHeightFactor, cuspFrequency, map_zero, zero_div, zero_mul,
    sourceFourierKernel_zero s hs, integral_mul_const, cuspIntervalMellin,
    BoundedContinuousFunction.const_apply, one_mul]
  exact mul_comm _ _

lemma cuspIntervalOutgoingFamily_unit_initial (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    cuspIntervalOutgoingFamily 5 6 (by norm_num) (BoundedContinuousFunction.const ℝ 1) s =
      arithmeticDirichletSeries s 0 * cuspWhittakerHeightFactor s 0 := by
  rw [cuspIntervalOutgoingFamily,
    kernelCuspIntervalFourierFamily_zero_initial 5 6 (by norm_num) _ s hs hi,
    cuspWhittakerHeightFactor_zero s (by linarith), scatteringCoefficient]
  field_simp [cusp_volume_ne_zero]
  ring

/-- The opposite cusp has the same constant residue as the original cusp. -/
theorem oppositeCuspResidue_zero : oppositeCuspResidue 0 =
    ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * constantArithmeticResidue := by
  let η := BoundedContinuousFunction.const ℝ (1 : ℂ)
  have he := cuspScalarResidue_cross
    (cuspIntervalOutgoingFamily 5 6 (by norm_num) η)
    (rationalCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num))
    (fun _ => 2) (fun s => (3 : ℂ) ^ (3 * s - 3) - 1)
    (kernelCuspIntervalFourier 5 6 (by norm_num) η 0 cubicEisensteinResidue)
    (rationalCuspFourier 0 oppositeSource cubicEisensteinResidue)
    (fun s hs => cuspIntervalOutgoingFamily_analyticAt 5 6 (by norm_num) η s hs.1 hs.2)
    (fun s hs => rationalCuspFamily_analyticAt_nonreal 0 oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
    (fun _ _ => analyticAt_const) (fun s _ => ramifiedDenominator_analytic s)
    continuousAt_const (ramifiedDenominator_analytic (4 / 3)).continuousAt
    (cuspIntervalOutgoingFamily_residue_limit 5 6 (by norm_num) η)
    (rationalCuspFamily_residue_limit 0 oppositeSource 2 3 (by norm_num) (by norm_num)) (by
      intro s hs hi
      rw [cuspIntervalOutgoingFamily_unit_initial s hs hi,
        rationalCuspFamily_opposite_all_initial 0 s hs hi, mul_zero,
        arithmeticDirichletSeries_zero_unramified s (by linarith)]
      have hd := ramifiedDenominator_ne_zero s (by linarith)
      rw [show 3 * s - 3 = 3 * (s - 1) by ring] at hd ⊢
      field_simp [hd])
  norm_num at he
  rw [oppositeCuspResidue, ← he, kernelCuspIntervalFourier_zero_residue]
  apply (div_eq_iff (cuspWhittakerHeightFactor_center_ne_zero 0)).mpr
  rw [cuspWhittakerHeightFactor_zero (4 / 3) (by norm_num)]
  dsimp only [η]
  ring

theorem cubicSourceResidualFunction_fourier_zero (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, cubicSourceResidualFunction (upperPoint z v hv)) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * (3 * (Real.pi : ℂ)) * constantArithmeticResidue *
        (v : ℂ) ^ (2 / 3 : ℂ) := by
  have he := fourCuspAverage_fourier cubicResidualFunction cubicResidualFunction_continuous
    cubicResidualFunction_automorphy v hv 0
  simp_rw [← cubicSourceResidualFunction_four_cusps] at he
  rw [cubicResidualFunction_fourier, cubicResidualFullModeAmplitude, if_pos rfl,
    cubicResidualFunction_opposite_fourier, oppositeCuspResidue_zero] at he
  simp only [rationalCuspPhaseSum, cuspFrequency, map_zero, zero_div, zero_mul, neg_zero,
    AddChar.map_zero_eq_one, mul_one, sourceFourierKernel_zero (4 / 3) (by norm_num)] at he
  convert he using 1
  ring

theorem cubicSourceResidualFunction_ne_zero : cubicSourceResidualFunction ≠ 0 := by
  intro hz
  have he := cubicSourceResidualFunction_fourier_zero 1 (by norm_num)
  simp only [hz, Pi.zero_apply, integral_zero, Complex.ofReal_one, Complex.one_cpow, mul_one] at he
  exact (mul_ne_zero (mul_ne_zero cusp_volume_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      constantArithmeticResidue_ne_zero) he.symm

theorem kernelRationalSourceProjection_cubicEisensteinResidue_ne_zero :
    kernelRationalSourceProjection cubicEisensteinResidue ≠ 0 := by
  intro hz
  have he := cubicSourceResidualFunction_represents_projection
  rw [hz] at he
  have hae : (fun _ : HyperbolicSpace => (0 : ℂ)) =ᵐ[hyperbolicVolume] cubicSourceResidualFunction := by
    have hzero : (0 : KernelQuotientL2) =ᵐ[integralQuotientVolume globalKubotaKernel]
        (fun _ => (0 : ℂ)) := Lp.coeFn_zero ℂ 2 (integralQuotientVolume globalKubotaKernel)
    have hp := kernelProjection_quasiMeasurePreserving.ae_eq_comp hzero
    filter_upwards [hp, he] with w hw hr
    exact hw.symm.trans hr
  exact cubicSourceResidualFunction_ne_zero
    (Measure.eq_of_ae_eq hae continuous_const cubicSourceResidualFunction_continuous).symm

lemma kernelRationalAction_mul (g h : rationalExtension) (q : KernelQuotient) :
    kernelRationalAction (g * h) q = kernelRationalAction g (kernelRationalAction h q) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (integralComplexMatrix ((g : SL(2, O)) * h) • w) =
      integralOrbitProjection globalKubotaKernel (integralComplexMatrix (g : SL(2, O)) •
        (integralComplexMatrix (h : SL(2, O)) • w))
    rw [map_mul, mul_smul]

lemma kernelRationalAction_one (q : KernelQuotient) : kernelRationalAction 1 q = q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (integralComplexMatrix (1 : SL(2, O)) • w) = _
    rw [map_one, one_smul]
    rfl

def kernelRationalHomeomorph (g : rationalExtension) : KernelQuotient ≃ₜ KernelQuotient where
  toFun := kernelRationalAction g
  invFun := kernelRationalAction g⁻¹
  left_inv q := by rw [← kernelRationalAction_mul, inv_mul_cancel, kernelRationalAction_one]
  right_inv q := by rw [← kernelRationalAction_mul, mul_inv_cancel, kernelRationalAction_one]
  continuous_toFun := kernelRationalAction_continuous g
  continuous_invFun := kernelRationalAction_continuous g⁻¹

lemma kernelRationalPullback_comp (g h : rationalExtension) (F : KernelQuotientL2) :
    kernelRationalPullback g (kernelRationalPullback h F) = kernelRationalPullback (h * g) F := by
  apply Lp.ext
  have he := (kernelRationalAction_measurePreserving g).quasiMeasurePreserving.ae_eq_comp
    (kernelRationalPullback_ae h F)
  filter_upwards [kernelRationalPullback_ae g (kernelRationalPullback h F), he,
    kernelRationalPullback_ae (h * g) F] with q hleft hmiddle hright
  dsimp only [Function.comp_def] at hmiddle
  rw [hleft, hmiddle, hright, kernelRationalAction_mul]

lemma kernelRationalPullback_one (F : KernelQuotientL2) : kernelRationalPullback 1 F = F := by
  apply Lp.ext
  simpa only [kernelRationalAction_one] using kernelRationalPullback_ae 1 F

open scoped Manifold ContDiff

/-- The linear fractional action is smooth in the upper half-space atlas. -/
lemma hyperbolicAction_contMDiff (g : SL(2, ℂ)) :
    ContMDiff 𝓘(ℝ, SpatialCoordinates) 𝓘(ℝ, SpatialCoordinates) ∞
      (fun w : HyperbolicSpace => g • w) := by
  intro w
  rw [contMDiffAt_iff]
  refine ⟨(continuous_hyperbolic_action g).continuousAt, ?_⟩
  have hp : hyperbolicSpatialCoordinates w ∈ hyperbolicSpatialChart.target :=
    hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have he : (fun p : SpatialCoordinates => hyperbolicSpatialCoordinates
      (g • hyperbolicSpatialChart.symm p)) =ᶠ[𝓝 (hyperbolicSpatialCoordinates w)] mobiusSpatial g := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hpt
    rw [mobiusSpatial_coordinates_global]
    exact congrArg (mobiusSpatial g) (hyperbolicSpatialChart.right_inv hpt)
  have hd := ((mobiusSpatial_contDiffAt g _ (hyperbolicSpatialCoordinates_positive w)).congr_of_eventuallyEq
    he).contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.preimage_id_eq,
    Set.range_id, hyperbolicSpatial_chartAt, hyperbolicSpatialChart_apply, Function.comp_def, id_eq] using hd

/-- Smoothness descends through the covering charts of the cubic quotient. -/
lemma kernel_contMDiff_of_lift (f : KernelQuotient → ℂ)
    (hf : ContMDiff 𝓘(ℝ, SpatialCoordinates) 𝓘(ℝ, ℂ) ∞
      (fun w : HyperbolicSpace => f (integralOrbitProjection globalKubotaKernel w))) :
    ContMDiff 𝓘(ℝ, SpatialCoordinates) 𝓘(ℝ, ℂ) ∞ f := by
  intro q
  have hq : q ∈ (kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q ∈ hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hs : ContMDiffOn 𝓘(ℝ, SpatialCoordinates) 𝓘(ℝ, SpatialCoordinates) ∞
      hyperbolicSpatialChart.symm hyperbolicSpatialChart.target := by
    simpa only [hyperbolicSpatial_chartAt] using
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, SpatialCoordinates)) (n := ∞) (x := q.out))
  have hd := (hf (hyperbolicSpatialChart.symm (kernelQuotientChart q q))).comp _
    (hs.contMDiffAt (hyperbolicSpatialChart.open_target.mem_nhds hp))
  have he : (fun p => f ((kernelQuotientChart q).symm p)) =
      (fun p => f (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p))) := by
    funext p
    rw [kernelQuotientChart_symm]
  have hdc : ContDiffAt ℝ ∞ (fun p => f ((kernelQuotientChart q).symm p))
      (kernelQuotientChart q q) := by
    rw [he]
    exact hd.contDiffAt
  have hc : ContinuousAt f q := by
    have hc := hdc.continuousAt.comp ((kernelQuotientChart q).continuousOn.continuousAt
      ((kernelQuotientChart q).open_source.mem_nhds hq))
    apply hc.congr
    filter_upwards [(kernelQuotientChart q).open_source.mem_nhds hq] with r hr
    exact congrArg f ((kernelQuotientChart q).left_inv hr)
  rw [contMDiffAt_iff]
  refine ⟨hc, ?_⟩
  have hh := hdc.contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id,
    kernelSpatial_chartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, Function.comp_def, id_eq] using hh

lemma kernelRational_comp_contMDiff (g : rationalExtension) (f : KernelQuotient → ℂ)
    (hf : ContMDiff 𝓘(ℝ, SpatialCoordinates) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ, SpatialCoordinates) 𝓘(ℝ, ℂ) ∞ (fun q => f (kernelRationalAction g q)) := by
  apply kernel_contMDiff_of_lift
  exact (hf.comp kernelProjection_contMDiff).comp (hyperbolicAction_contMDiff (integralComplexMatrix (g : SL(2, O))))

def kernelRationalTest (g : rationalExtension) (f : kernelSmoothTests) : kernelSmoothTests :=
  ⟨fun q => f.1 (kernelRationalAction g q), kernelRational_comp_contMDiff g f.1 f.2.1,
    f.2.2.comp_homeomorph (kernelRationalHomeomorph g)⟩

def kernelRationalTestLinear (g : rationalExtension) : kernelSmoothTests →ₗ[ℂ] kernelSmoothTests where
  toFun := kernelRationalTest g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma kernelRationalTest_field (g : rationalExtension) (f : kernelSmoothTests) :
    kernelTestField (kernelRationalTest g f) = kernelTestField f ∘ euclideanAction (integralComplexMatrix (g : SL(2, O))) := by
  funext p
  change f.1 (integralOrbitProjection globalKubotaKernel
      (integralComplexMatrix (g : SL(2, O)) • euclideanToHyperbolic p)) =
    f.1 (integralOrbitProjection globalKubotaKernel
      (euclideanToHyperbolic (euclideanAction (integralComplexMatrix (g : SL(2, O))) p)))
  rw [euclideanAction, euclideanToHyperbolic_coordinates]

lemma kernelRationalTest_energyDensity (g : rationalExtension) (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (kernelRationalTest g f) w =
      kernelTestEnergyDensity f (integralComplexMatrix (g : SL(2, O)) • w) := by
  let A := integralComplexMatrix (g : SL(2, O))
  have he : hyperbolicEuclideanCoordinates (A • w) = euclideanAction A (hyperbolicEuclideanCoordinates w) := by
    rw [euclideanAction, euclideanToHyperbolic_coordinates]
  have hr := hyperbolic_cotangent_energy_comp A (fun p : EuclideanSpatial => (kernelTestField f p).re)
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
    ((kernelTestField_re_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp))
  have hi := hyperbolic_cotangent_energy_comp A (fun p : EuclideanSpatial => (kernelTestField f p).im)
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
    ((kernelTestField_im_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp))
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  rw [kernelRationalTest_field, he]
  exact congrArg₂ (fun a b : ℝ => a + b) hr hi

lemma kernelRationalTest_quotientDensity (g : rationalExtension) (f : kernelSmoothTests) (q : KernelQuotient) :
    kernelQuotientEnergyDensity (kernelRationalTest g f) q =
      kernelQuotientEnergyDensity f (kernelRationalAction g q) := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelRationalTest_energyDensity g f w

lemma kernelRationalTest_energy (g : rationalExtension) (f : kernelSmoothTests) :
    kernelDirichletEnergy (kernelRationalTest g f) = kernelDirichletEnergy f := by
  unfold kernelDirichletEnergy
  simp_rw [kernelRationalTest_quotientDensity]
  exact (kernelRationalAction_measurePreserving g).integral_comp
    (kernelRationalHomeomorph g).measurableEmbedding _

lemma kernelRationalTest_mass (g : rationalExtension) (f : kernelSmoothTests) :
    kernelSmoothTestsToL2 (kernelRationalTest g f) = kernelRationalPullback g (kernelSmoothTestsToL2 f) := by
  apply Lp.ext
  have he := (kernelRationalAction_measurePreserving g).quasiMeasurePreserving.ae_eq_comp
    (kernelSmoothTests_memLp f).coeFn_toLp
  filter_upwards [(kernelSmoothTests_memLp (kernelRationalTest g f)).coeFn_toLp,
    kernelRationalPullback_ae g (kernelSmoothTestsToL2 f), he] with q hnew hpull hbase
  exact hnew.trans (hpull.trans hbase).symm

lemma kernelRationalTest_graph_norm (g : rationalExtension) (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore (kernelRationalTest g f)‖ = ‖kernelEnergyGraphCore f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [kernelEnergyGraphCore_norm_sq, kernelEnergyGraphCore_norm_sq,
    kernelRationalTest_energy, kernelRationalTest_mass, LinearIsometry.norm_map]

def kernelRationalTestEquiv (g : rationalExtension) : kernelSmoothTests ≃ₗ[ℂ] kernelSmoothTests where
  __ := kernelRationalTestLinear g
  invFun := kernelRationalTest g⁻¹
  left_inv f := by
    apply Subtype.ext
    funext q
    change f.1 (kernelRationalAction g (kernelRationalAction g⁻¹ q)) = f.1 q
    rw [← kernelRationalAction_mul, mul_inv_cancel, kernelRationalAction_one]
  right_inv f := by
    apply Subtype.ext
    funext q
    change f.1 (kernelRationalAction g⁻¹ (kernelRationalAction g q)) = f.1 q
    rw [← kernelRationalAction_mul, inv_mul_cancel, kernelRationalAction_one]

/-- Rational pullback extends isometrically from smooth tests to the completed energy graph. -/
def kernelRationalEnergyPullback (g : rationalExtension) : KernelEnergyGraph ≃ₗᵢ[ℂ] KernelEnergyGraph :=
  (kernelRationalTestEquiv g).extendOfIsometry kernelEnergyGraphCore kernelEnergyGraphCore
    kernelEnergyGraphCore_dense kernelEnergyGraphCore_dense (kernelRationalTest_graph_norm g)

lemma kernelRationalEnergyPullback_core (g : rationalExtension) (f : kernelSmoothTests) :
    kernelRationalEnergyPullback g (kernelEnergyGraphCore f) = kernelEnergyGraphCore (kernelRationalTest g f) :=
  LinearEquiv.extendOfIsometry_eq (kernelRationalTestEquiv g) kernelEnergyGraphCore kernelEnergyGraphCore
    kernelEnergyGraphCore_dense kernelEnergyGraphCore_dense (kernelRationalTest_graph_norm g) f

lemma kernelRationalEnergyPullback_mass (g : rationalExtension) (u : KernelEnergyGraph) :
    kernelEnergyMass (kernelRationalEnergyPullback g u) = kernelRationalPullback g (kernelEnergyMass u) := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (kernelEnergyMass.continuous.comp (kernelRationalEnergyPullback g).continuous)
    ((kernelRationalPullback g).continuous.comp kernelEnergyMass.continuous) ?_) u
  funext f
  change kernelEnergyMass (kernelRationalEnergyPullback g (kernelEnergyGraphCore f)) =
    kernelRationalPullback g (kernelEnergyMass (kernelEnergyGraphCore f))
  rw [kernelRationalEnergyPullback_core, kernelEnergyMass_core, kernelEnergyMass_core, kernelRationalTest_mass]

theorem kernelRational_variationalSolution (g : rationalExtension) (F : KernelQuotientL2) :
    kernelRationalEnergyPullback g (kernelVariationalSolution F) =
      kernelVariationalSolution (kernelRationalPullback g F) := by
  apply kernelVariationalSolution_unique
  intro v
  obtain ⟨w, rfl⟩ := (kernelRationalEnergyPullback g).surjective v
  rw [← kernelEnergyGraph_inner, LinearIsometryEquiv.inner_map_map,
    kernelRationalEnergyPullback_mass, LinearIsometry.inner_map_map, kernelEnergyGraph_inner]
  exact kernelVariationalSolution_equation F w

theorem kernelRational_variationalResolvent (g : rationalExtension) (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelRationalPullback g F) =
      kernelRationalPullback g (kernelVariationalResolvent F) := by
  change kernelEnergyMass (kernelVariationalSolution (kernelRationalPullback g F)) =
    kernelRationalPullback g (kernelEnergyMass (kernelVariationalSolution F))
  rw [← kernelRational_variationalSolution, kernelRationalEnergyPullback_mass]

theorem kernelRational_operatorGraph (g : rationalExtension) (F G : KernelQuotientL2)
    (hFG : (F, G) ∈ kernelEnergyLaplacian.graph) :
    (kernelRationalPullback g F, kernelRationalPullback g G) ∈ kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph, mem_kernelLaplacianGraph] at hFG ⊢
  rw [← map_add, kernelRational_variationalResolvent, hFG]

theorem kernelRational_eigenvector (g : rationalExtension) (F : KernelQuotientL2) (z : ℂ)
    (hF : (F, z • F) ∈ kernelEnergyLaplacian.graph) :
    (kernelRationalPullback g F, z • kernelRationalPullback g F) ∈ kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelRational_operatorGraph g F (z • F) hF

theorem kernelRationalSourceProjection_variationalResolvent (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelRationalSourceProjection F) =
      kernelRationalSourceProjection (kernelVariationalResolvent F) := by
  simp only [kernelRationalSourceProjection_apply, map_smul, map_sum, kernelRational_variationalResolvent]

theorem kernelRationalSourceProjection_operatorGraph (F G : KernelQuotientL2)
    (hFG : (F, G) ∈ kernelEnergyLaplacian.graph) :
    (kernelRationalSourceProjection F, kernelRationalSourceProjection G) ∈ kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph, mem_kernelLaplacianGraph] at hFG ⊢
  rw [← map_add, kernelRationalSourceProjection_variationalResolvent, hFG]

/-- The nonzero projected residual vector retains the subcritical eigenvalue `8/9`. -/
theorem kernelRationalSourceProjection_cubicEisensteinResidue_eigenvector :
    (kernelRationalSourceProjection cubicEisensteinResidue,
      (8 / 9 : ℂ) • kernelRationalSourceProjection cubicEisensteinResidue) ∈ kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelRationalSourceProjection_operatorGraph
    cubicEisensteinResidue ((8 / 9 : ℂ) • cubicEisensteinResidue) cubicEisensteinResidue_eigenvector

lemma hilbertProjectionSandwich_symmetric {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : E →L[ℂ] G) (K : Submodule ℂ E) [K.HasOrthogonalProjection] (x y : G) :
    inner ℂ x (A (K.starProjection (A.adjoint y))) =
      inner ℂ (A (K.starProjection (A.adjoint x))) y := by
  rw [← A.adjoint_inner_left, ← A.adjoint_inner_right]
  exact (K.inner_starProjection_left_eq_right _ _).symm

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
