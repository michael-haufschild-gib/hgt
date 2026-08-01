import GaloisForLFunctions.RHTower.EntireExponentialMomentPolynomialDensity
import GaloisForLFunctions.HTGeometry.CarriedConclusion

/-!
# Compact-seed rigidity for the critical half-weight co-Poisson obstruction

This file closes the compact multiplicative-seed branch of Route G.  A finite signed density
carried on a positive compact interval cannot annihilate every even moment or every odd moment
unless it vanishes almost everywhere.

The proof stays at `L¹` strength.  It splits the density into mutually singular positive measures,
pushes both through the globally injective signed-square map `x ↦ x |x|`, and invokes compact
moment determinacy.  Positivity of the carrying interval makes signed-square equal ordinary square
on both measures.  This avoids an `L²` assumption and proves the exact compact-seed no-go needed by
the critical half-weight analysis.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology

namespace RHTower

noncomputable section

/-- Globally injective replacement for `x ↦ x²`; it agrees with square on the positive half-line. -/
def signedSquare (x : ℝ) : ℝ := x * |x|

lemma signedSquare_strictMono : StrictMono signedSquare := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · have hy : 0 ≤ y := le_trans hx hxy.le
    simp [signedSquare, abs_of_nonneg hx, abs_of_nonneg hy]
    nlinarith
  · have hx' : x < 0 := lt_of_not_ge hx
    by_cases hy : 0 ≤ y
    · simp [signedSquare, abs_of_neg hx', abs_of_nonneg hy]
      nlinarith
    · have hy' : y < 0 := lt_of_not_ge hy
      simp [signedSquare, abs_of_neg hx', abs_of_neg hy']
      nlinarith

lemma signedSquare_measurableEmbedding : MeasurableEmbedding signedSquare :=
  { injective := signedSquare_strictMono.injective
    measurable := signedSquare_strictMono.monotone.measurable
    measurableSet_image' := fun _ hs =>
      hs.image_of_monotoneOn (signedSquare_strictMono.monotone.monotoneOn _) }

lemma integrable_pow_of_compl_Icc_eq_zero {mu : Measure ℝ} [IsFiniteMeasure mu]
    {a b : ℝ} (hcarry : mu (Set.Icc a b)ᶜ = 0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) mu := by
  apply Integrable.of_bound (by fun_prop) ((max |a| |b|) ^ n)
  have hmem : ∀ᵐ x ∂mu, x ∈ Set.Icc a b := by
    rw [ae_iff]
    change mu (Set.Icc a b)ᶜ = 0
    exact hcarry
  filter_upwards [hmem] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  gcongr
  exact abs_le_max_abs_abs hx.1 hx.2

lemma integrable_pow_mul_of_compl_Icc_eq_zero {mu : Measure ℝ}
    {a b : ℝ} (hcarry : mu (Set.Icc a b)ᶜ = 0) {g : ℝ → ℝ}
    (hg : Integrable g mu) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * g x) mu := by
  apply hg.bdd_mul (c := (max |a| |b|) ^ n) (by fun_prop)
  have hmem : ∀ᵐ x ∂mu, x ∈ Set.Icc a b := by
    rw [ae_iff]
    change mu (Set.Icc a b)ᶜ = 0
    exact hcarry
  filter_upwards [hmem] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  gcongr
  exact abs_le_max_abs_abs hx.1 hx.2

lemma positiveDensityMeasure_compl_Icc_eq_zero {mu : Measure ℝ} {g : ℝ → ℝ}
    {a b : ℝ} (hcarry : mu (Set.Icc a b)ᶜ = 0) :
    positiveDensityMeasure mu g (Set.Icc a b)ᶜ = 0 :=
  withDensity_absolutelyContinuous mu _ hcarry

lemma negativeDensityMeasure_compl_Icc_eq_zero {mu : Measure ℝ} {g : ℝ → ℝ}
    {a b : ℝ} (hcarry : mu (Set.Icc a b)ᶜ = 0) :
    negativeDensityMeasure mu g (Set.Icc a b)ᶜ = 0 :=
  withDensity_absolutelyContinuous mu _ hcarry

lemma map_signedSquare_compl_Icc_eq_zero {eta : Measure ℝ} {a b : ℝ}
    (hcarry : eta (Set.Icc a b)ᶜ = 0) :
    Measure.map signedSquare eta
        (Set.Icc (-((max |a| |b|) ^ 2 + 1)) ((max |a| |b|) ^ 2 + 1))ᶜ = 0 := by
  rw [Measure.map_apply signedSquare_strictMono.monotone.measurable measurableSet_Icc.compl]
  apply measure_mono_null _ hcarry
  intro x hx
  by_contra hnot
  have hxin : x ∈ Set.Icc a b := by simpa using hnot
  have hxabs : |x| ≤ max |a| |b| := abs_le_max_abs_abs hxin.1 hxin.2
  have hsabs : |signedSquare x| ≤ (max |a| |b|) ^ 2 := by
    simp only [signedSquare, abs_mul, abs_abs, pow_two]
    exact mul_self_le_mul_self (abs_nonneg x) hxabs
  have himage : signedSquare x ∈
      Set.Icc (-((max |a| |b|) ^ 2 + 1)) ((max |a| |b|) ^ 2 + 1) := by
    rw [Set.mem_Icc]
    constructor <;> nlinarith [abs_nonneg (signedSquare x), neg_abs_le (signedSquare x),
      le_abs_self (signedSquare x)]
  exact hx himage

/-- An `L¹` density carried in a positive compact interval is determined by its even moments. -/
theorem ae_eq_zero_of_even_moments_of_positive_compact_support
    {mu : Measure ℝ} [IsFiniteMeasure mu] {a b : ℝ} (ha : 0 < a)
    (hcarry : mu (Set.Icc a b)ᶜ = 0) {g : ℝ → ℝ}
    (hgmeas : Measurable g) (hg : Integrable g mu)
    (hmom : ∀ n : ℕ, ∫ x, x ^ (2 * n) * g x ∂mu = 0) :
    g =ᵐ[mu] 0 := by
  let mup := positiveDensityMeasure mu g
  let mun := negativeDensityMeasure mu g
  letI : IsFiniteMeasure mup := positiveDensityMeasure_finite hg
  letI : IsFiniteMeasure mun := negativeDensityMeasure_finite hg
  have hmupCarry : mup (Set.Icc a b)ᶜ = 0 := by
    simpa only [mup] using
      (positiveDensityMeasure_compl_Icc_eq_zero (g := g) hcarry)
  have hmunCarry : mun (Set.Icc a b)ᶜ = 0 := by
    simpa only [mun] using
      (negativeDensityMeasure_compl_Icc_eq_zero (g := g) hcarry)
  have hmeasureMoment (n : ℕ) :
      ∫ x, x ^ (2 * n) ∂mup = ∫ x, x ^ (2 * n) ∂mun := by
    have hposInt := integrable_pow_mul_of_compl_Icc_eq_zero hcarry hg.pos_part (2 * n)
    have hnegInt := integrable_pow_mul_of_compl_Icc_eq_zero hcarry hg.neg_part (2 * n)
    have hsplit : (fun x : ℝ => x ^ (2 * n) * g x) =
        fun x => x ^ (2 * n) * max (g x) 0 - x ^ (2 * n) * max (-g x) 0 := by
      funext x
      rw [← mul_sub]
      congr 1
      exact (max_zero_sub_max_neg_zero_eq_self (g x)).symm
    have heq : ∫ x, x ^ (2 * n) * max (g x) 0 ∂mu =
        ∫ x, x ^ (2 * n) * max (-g x) 0 ∂mu := by
      have hz := hmom n
      rw [hsplit, integral_sub hposInt hnegInt] at hz
      exact sub_eq_zero.mp hz
    change ∫ x, x ^ (2 * n) ∂positiveDensityMeasure mu g =
      ∫ x, x ^ (2 * n) ∂negativeDensityMeasure mu g
    unfold positiveDensityMeasure negativeDensityMeasure
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hgmeas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hgmeas.neg.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal']
    simpa [smul_eq_mul, mul_comm] using heq
  have hmupSigned (n : ℕ) :
      ∫ x, signedSquare x ^ n ∂mup = ∫ x, x ^ (2 * n) ∂mup := by
    apply integral_congr_ae
    have hmem : ∀ᵐ x ∂mup, x ∈ Set.Icc a b := by
      rw [ae_iff]
      change mup (Set.Icc a b)ᶜ = 0
      exact hmupCarry
    filter_upwards [hmem] with x hx
    have hx0 : 0 ≤ x := le_trans ha.le hx.1
    simp only [signedSquare, abs_of_nonneg hx0]
    ring
  have hmunSigned (n : ℕ) :
      ∫ x, signedSquare x ^ n ∂mun = ∫ x, x ^ (2 * n) ∂mun := by
    apply integral_congr_ae
    have hmem : ∀ᵐ x ∂mun, x ∈ Set.Icc a b := by
      rw [ae_iff]
      change mun (Set.Icc a b)ᶜ = 0
      exact hmunCarry
    filter_upwards [hmem] with x hx
    have hx0 : 0 ≤ x := le_trans ha.le hx.1
    simp only [signedSquare, abs_of_nonneg hx0]
    ring
  let R : ℝ := (max |a| |b|) ^ 2 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let mp := Measure.map signedSquare mup
  let mn := Measure.map signedSquare mun
  letI : IsFiniteMeasure mp := by dsimp [mp]; infer_instance
  letI : IsFiniteMeasure mn := by dsimp [mn]; infer_instance
  have hmpCarry : mp (Set.Icc (-R) R)ᶜ = 0 := by
    simpa only [mp, R] using map_signedSquare_compl_Icc_eq_zero hmupCarry
  have hmnCarry : mn (Set.Icc (-R) R)ᶜ = 0 := by
    simpa only [mn, R] using map_signedSquare_compl_Icc_eq_zero hmunCarry
  have hmpInt (n : ℕ) : Integrable (fun x : ℝ => x ^ n) mp :=
    integrable_pow_of_compl_Icc_eq_zero hmpCarry n
  have hmnInt (n : ℕ) : Integrable (fun x : ℝ => x ^ n) mn :=
    integrable_pow_of_compl_Icc_eq_zero hmnCarry n
  have hmapMoment (n : ℕ) : ∫ x, x ^ n ∂mp = ∫ x, x ^ n ∂mn := by
    dsimp only [mp, mn]
    rw [signedSquare_measurableEmbedding.integral_map,
      signedSquare_measurableEmbedding.integral_map]
    exact (hmupSigned n).trans ((hmeasureMoment n).trans (hmunSigned n).symm)
  have hmapEq : mp = mn := by
    apply HTGeometry.measure_eq_of_moments_eq_of_one_carried
      (s := fun n => ∫ x, x ^ n ∂mp) (c := 0) (r := R) hR
    · simpa using hmpCarry
    · intro n; rfl
    · exact hmpInt
    · intro n; exact hmapMoment n
    · exact hmnInt
  have heq : mup = mun := by
    apply signedSquare_measurableEmbedding.map_injective
    simpa only [mp, mn] using hmapEq
  have hsing : mup ⟂ₘ mun := by
    simpa only [mup, mun, positiveDensityMeasure, negativeDensityMeasure] using!
      withDensity_ofReal_mutuallySingular hgmeas
  have hself : mup ⟂ₘ mup := by simpa [heq] using hsing
  have hmup : mup = 0 := (Measure.MutuallySingular.self_iff mup).mp hself
  have hmun : mun = 0 := by rw [← heq, hmup]
  have hpzero : (fun x => ENNReal.ofReal (g x)) =ᵐ[mu] (fun _ => 0) :=
    (withDensity_eq_zero_iff hgmeas.ennreal_ofReal.aemeasurable).mp (by
      simpa only [mup, positiveDensityMeasure] using hmup)
  have hnzero : (fun x => ENNReal.ofReal (-g x)) =ᵐ[mu] (fun _ => 0) :=
    (withDensity_eq_zero_iff hgmeas.neg.ennreal_ofReal.aemeasurable).mp (by
      simpa only [mun, negativeDensityMeasure] using hmun)
  filter_upwards [hpzero, hnzero] with x hpx hnx
  have hle : g x ≤ 0 := by simpa using hpx
  have hge : 0 ≤ g x := by simpa using hnx
  exact le_antisymm hle hge

/-- No nonzero `L¹` seed on a positive compact interval can have every odd moment vanish. -/
theorem ae_eq_zero_of_odd_moments_of_positive_compact_support
    {mu : Measure ℝ} [IsFiniteMeasure mu] {a b : ℝ} (ha : 0 < a)
    (hcarry : mu (Set.Icc a b)ᶜ = 0) {g : ℝ → ℝ}
    (hgmeas : Measurable g) (hg : Integrable g mu)
    (hmom : ∀ n : ℕ, ∫ x, x ^ (2 * n + 1) * g x ∂mu = 0) :
    g =ᵐ[mu] 0 := by
  have hxgInt : Integrable (fun x : ℝ => x * g x) mu := by
    simpa using integrable_pow_mul_of_compl_Icc_eq_zero hcarry hg 1
  have hxgZero : (fun x : ℝ => x * g x) =ᵐ[mu] 0 := by
    apply ae_eq_zero_of_even_moments_of_positive_compact_support ha hcarry
      (measurable_id.mul hgmeas) hxgInt
    intro n
    simpa [id_eq, pow_succ', Nat.mul_comm, mul_assoc, mul_comm, mul_left_comm] using hmom n
  have hmem : ∀ᵐ x ∂mu, x ∈ Set.Icc a b := by
    rw [ae_iff]
    change mu (Set.Icc a b)ᶜ = 0
    exact hcarry
  filter_upwards [hxgZero, hmem] with x hxg hx
  have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
  exact (mul_eq_zero.mp hxg).resolve_left hxne

end
end RHTower
