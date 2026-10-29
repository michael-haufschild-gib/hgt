import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerPositivity
import GaloisForLFunctions.HeckeKreinToeplitz.EveryReceiverAtEveryWidthIsBoundedByTheIndex
import GaloisForLFunctions.ArithmeticIndexDescent.TheSectionComplementCarriesAllNegativeSquares
import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheWeightOfOneZero

/-!
# Zero-Side Stratum of Fixed-Ratio Atomic Weil Positivity

This module establishes the zero-side relationships governing atomic families of fixed overlap ratio
`c > 0`:

1. **Unconditional trans-Metzler positivity on `(0, cZero]`**: for `cZero = 1 + 10⁻¹⁸ > 1` and
   `transMetzlerProfile = plateau (1 / 1000)`, eventual positive definiteness of
   `completeWeilMatrix transMetzlerProfile c N` holds unconditionally for all `c ∈ (0, cZero]`,
   requiring no hypothesis on the zeros of `ζ`.
2. **All-ratio positivity under `RiemannHypothesis`** (`weilQuad_atomicTest_nonneg_of_riemannHypothesis`):
   under `RiemannHypothesis`, `0 ≤ weilQuad (atomicTest N x (atomDilate φ (c / N)))` holds for every
   `c > 0`, every `N ≥ 1`, and every `C²` profile `φ` supported in `[0, 1]`.
3. **Uniform negative-index bound under finite off-line support**
   (`hermNegIndex_atomicShiftWeilGram_le_of_finiteOffLine`): if `(rightZeros zetaZeroConfig).Finite`
   holds, the Hermitian negative index of the atomic Weil Gram matrix at width `c / N` and horizon `N`
   is bounded by `(rightZeros zetaZeroConfig).ncard` uniformly across all `c > 0` and all `N ≥ 1`.
4. **Linear-in-`c` single-zero weight lower bound** (`re_Wsummand_atomicTest_const_one_ge`): a real
   zero `ρ` with `Re ρ ≥ 1/2` carries relative weight at least
   `m_ρ e^{-(Re ρ - 1/2) c / N} ((∫ φ)² / ∫ φ²) c` on the uniform vector `x ≡ 1`, matching the linear
   overlap-ratio growth in `norm_Wsummand_atomicTest_dilate_le`.
5. **Tempered finite-off-line countermodel at every overlap ratio**
   (`isolatedPairConfig_atomic_negative_every_ratio`): the configuration
   `Z = isolatedPairConfig (Real.log_pos one_lt_two) hδ hδ' 0` is tempered, has a single right-half
   zero `rightZeros Z = {offLinePoint δ 0}`, and obeys `norm_Wsummand_atomicTest_dilate_le` on every
   zero when `δ < 1/2`, yet the two-atom test `x₁ = 1, x₂ = -1` annihilates its entire on-line zero
   lattice `(1/2) + (2πik / log 2)` and makes `Re Z.W(f_x, f_x) < 0` at every `c > 0` and every
   `N ≥ 2`. Consequently, eventual atomic positivity at fixed `c` cannot be deduced from
   `TemperedConfig`, finite off-line support, and the single-zero bound alone without `ζ`'s
   growing `log T / (2π)` zero density.
-/

noncomputable section

open MeasureTheory Finset Filter Topology Complex Matrix
open scoped Real ComplexConjugate ENNReal

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics
open ArithmeticCastelnuovoSeveri (cx realTests weilGram rightZeros)
open ArithmeticIndexDescent (complexWeilMixed complexWeilMixed_eq_weilGram
  hermQuad_complexWeilMixed_ofReal realWeilForm realTestSynthesis)
open HTGeometry (hermNegIndex hermQuad negIndex)
open HeckeKreinToeplitz (zetaKernel negIndex_zetaKernel hermNegIndex_weilGram_le_negIndex_zetaKernel)
open RenormalizedArithmeticPotentialTheory (completeWeilMatrix finAtomicTest)
open SpacingScaleHarmonicAnalysis (dirichletPoly paperFT_atomicTest Wsummand_atomicTest
  norm_Wsummand_atomicTest_dilate_le gammaOf_im)
open SquareRootThreshold (offLinePoint gammaOf_offLinePoint isolatedPairConfig
  temperedConfig_isolatedPairConfig)
open RHTower (verticalLatticePoint gammaOf_verticalLatticePoint TemperedConfig)
open Zeta23

/-! ### 1. Unconditional regime and zero-side upper implications for `ζ` -/

/-- Eventual positive definiteness and atomic Weil nonnegativity hold unconditionally across the
Metzler threshold on the entire interval `(0, cZero]` (`cZero = 1 + 10⁻¹⁸ > 1`). -/
theorem unconditional_transMetzler_positivity_interval :
    1 < cZero ∧ ∀ c ∈ Set.Ioc (0 : ℝ) cZero,
      ∀ᶠ N : ℕ in atTop,
        (completeWeilMatrix transMetzlerProfile c N).PosDef ∧
        ∀ x : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N x (atomDilate transMetzlerProfile (c / N))) := by
  refine ⟨one_lt_cZero, fun c hc => ?_⟩
  filter_upwards [eventually_completeWeilMatrix_posDef_of_mem_Ioc hc, eventually_ge_atTop 1]
    with N hpos hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc.1 hN0
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun _ hu => transMetzlerProfile_eq_zero hu) hw0
  have hM : 0 < ∫ u, atomDilate transMetzlerProfile (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]
    exact mul_pos hw0 integral_transMetzlerProfile_sq_pos
  exact ⟨hpos, weilQuad_atomicTest_nonneg_of_posDef hg hgsupp hw0.le hM hpos⟩

/-- Under `RiemannHypothesis`, the complete Weil quadratic form is nonnegative on every atomic test
at every overlap ratio `c > 0` and every horizon `N ≥ 1`. -/
theorem weilQuad_atomicTest_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    0 ≤ weilQuad (atomicTest N x (atomDilate φ (c / N))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < c / N := div_pos hc hN0
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw0
  exact RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH _
    (contDiff_atomicTest hg N x) (hasCompactSupport_atomicTest hgsupp N x)

/-! ### 2. Uniform negative-index bound under finite off-line support -/

/-- The complex Hermitian Weil Gram matrix of the atomic shift family
`u ↦ atomDilate φ w (u - log(i + 1))` on `Fin N`. -/
def atomicShiftWeilGram (φ : ℝ → ℝ) (w : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (fun i : Fin N => ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1))
      (cx (atomDilate φ w)))

theorem atomDilate_mem_realTests {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ} (hw : 0 < w) :
    atomDilate φ w ∈ realTests := by
  obtain ⟨hg, _, hgc⟩ := atomDilate_facts hφ hsupp hw
  exact ⟨hg, hgc⟩

/-- The Hermitian quadratic form of `atomicShiftWeilGram φ w N` on real vectors equals the complete
Weil quadratic form `weilQuad` on the synthesized atomic test. -/
theorem hermQuad_atomicShiftWeilGram_eq_weilQuad {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ} (hw : 0 < w) (N : ℕ) (y : Fin N → ℝ) :
    hermQuad (atomicShiftWeilGram φ w N) (fun i => (y i : ℂ)) =
      weilQuad (finAtomicTest (atomDilate φ w) N y) := by
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw
  let f : Fin N → realTests := fun i =>
    ⟨atom (atomDilate φ w) (i.1 + 1), contDiff_atom hg (i.1 + 1),
      hasCompactSupport_atom hgsupp (i.1 + 1)⟩
  have hgram : complexWeilMixed f f = atomicShiftWeilGram φ w N := by
    rw [complexWeilMixed_eq_weilGram]
    unfold atomicShiftWeilGram
    congr 1
    funext i u
    simp only [f, atom, cx, ArithmeticCastelnuovoSeveri.translate, Nat.cast_add, Nat.cast_one]
  have hsynth : (realTestSynthesis f y).1 = finAtomicTest (atomDilate φ w) N y := by
    funext u
    change (∑ i : Fin N, y i • atom (atomDilate φ w) (i.1 + 1)) u =
      finAtomicTest (atomDilate φ w) N y u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, finAtomicTest]
  rw [← hgram, hermQuad_complexWeilMixed_ofReal]
  change ArithmeticCastelnuovoSeveri.weilPair (realTestSynthesis f y).1 (realTestSynthesis f y).1 = _
  rw [hsynth, ArithmeticCastelnuovoSeveri.weilPair_self]

/-- Under finite off-line zero support `(rightZeros zetaZeroConfig).Finite`, the negative index of
`atomicShiftWeilGram φ (c / N) N` is bounded by `(rightZeros zetaZeroConfig).ncard` uniformly across
every overlap ratio `c > 0`, every horizon `N ≥ 1`, and every admissible profile `φ`. -/
theorem hermNegIndex_atomicShiftWeilGram_le_of_finiteOffLine
    (hfin : (rightZeros zetaZeroConfig).Finite)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    hermNegIndex (atomicShiftWeilGram φ (c / N) N) ≤ (rightZeros zetaZeroConfig).ncard := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hmem := atomDilate_mem_realTests hφ hsupp hw
  have hle : (hermNegIndex (atomicShiftWeilGram φ (c / N) N) : ℕ∞) ≤
      ((rightZeros zetaZeroConfig).ncard : ℕ∞) := by
    calc (hermNegIndex (atomicShiftWeilGram φ (c / N) N) : ℕ∞)
        ≤ negIndex zetaKernel :=
          hermNegIndex_weilGram_le_negIndex_zetaKernel hmem
            (fun i : Fin N => Real.log ((i : ℝ) + 1))
      _ = (rightZeros zetaZeroConfig).encard := negIndex_zetaKernel
      _ = ((rightZeros zetaZeroConfig).ncard : ℕ∞) := hfin.encard_eq_coe
  exact_mod_cast hle

/-! ### 3. Linear-in-`c` lower bound for a single real zero summand -/

/-- Cauchy–Schwarz lower bound for opposite real power sums:
`N² ≤ (∑_{n=1}^N n^σ)(∑_{n=1}^N n^{-σ})`. -/
theorem sq_nat_le_sum_rpow_mul_sum_rpow_neg (σ : ℝ) (N : ℕ) :
    (N : ℝ) ^ 2 ≤
      (∑ n ∈ Icc 1 N, (n : ℝ) ^ σ) * (∑ n ∈ Icc 1 N, (n : ℝ) ^ (-σ)) := by
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 N)
    (fun n => (n : ℝ) ^ (σ / 2)) (fun n => (n : ℝ) ^ (-(σ / 2)))
  have hprod : ∀ n ∈ Icc 1 N, (n : ℝ) ^ (σ / 2) * (n : ℝ) ^ (-(σ / 2)) = 1 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero]
  have hsq1 : ∀ n ∈ Icc 1 N, ((n : ℝ) ^ (σ / 2)) ^ 2 = (n : ℝ) ^ σ := by
    intro n _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1; push_cast; ring
  have hsq2 : ∀ n ∈ Icc 1 N, ((n : ℝ) ^ (-(σ / 2))) ^ 2 = (n : ℝ) ^ (-σ) := by
    intro n _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1; push_cast; ring
  rw [sum_congr rfl hprod, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one,
    sum_congr rfl hsq1, sum_congr rfl hsq2] at hcs
  exact hcs

private theorem paperFT_cx_neg_I_mul_real (g : ℝ → ℝ) (α : ℝ) :
    paperFT (cx g) (-Complex.I * (α : ℂ)) = ((∫ u, g u * Real.exp (α * u) : ℝ) : ℂ) := by
  unfold paperFT
  have heq : (fun u : ℝ => cx g u * Complex.exp (Complex.I * (-Complex.I * (α : ℂ)) * (u : ℂ))) =
      fun u : ℝ => ((g u * Real.exp (α * u) : ℝ) : ℂ) := by
    funext u
    have hI : Complex.I * (-Complex.I * (α : ℂ)) * (u : ℂ) = ((α * u : ℝ) : ℂ) := by
      have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      linear_combination -(α : ℂ) * (u : ℂ) * hII
    rw [hI, cx, Complex.ofReal_exp, Complex.ofReal_mul]
  rw [heq, integral_complex_ofReal]

/-- On the uniform coefficient vector `x ≡ 1`, any real zero `ρ` with `Re ρ ≥ 1/2` and `Im ρ = 0`
contributes at least `m_ρ e^{-(Re ρ - 1/2) c / N} ((∫ φ)² / ∫ φ²) c` times the diagonal atomic
energy, showing that the linear factor `c` in `norm_Wsummand_atomicTest_dilate_le` is sharp in the
overlap ratio. -/
theorem re_Wsummand_atomicTest_const_one_ge (Z : ZeroConfig)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hnonneg : ∀ u, 0 ≤ φ u) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re) (him : ρ.im = 0) :
    (Z.mult ρ : ℝ) * Real.exp (-((ρ.re - 1 / 2) * (c / N))) *
        ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * c *
        ((∑ _n ∈ Icc 1 N, (1 : ℝ) ^ 2) * ∫ u, atomDilate φ (c / N) u ^ 2) ≤
      (Z.Wsummand (cx (atomicTest N (fun _ => 1) (atomDilate φ (c / N))))
        (cx (atomicTest N (fun _ => 1) (atomDilate φ (c / N)))) ρ).re := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set w := c / N
  have hw : 0 < w := div_pos hc hN0
  set σ := ρ.re - 1 / 2
  have hσ : 0 ≤ σ := sub_nonneg.mpr hre
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw
  have hg_nonneg : ∀ u, 0 ≤ atomDilate φ w u := fun u => hnonneg (u / w)
  have hγ : gammaOf ρ = -Complex.I * (σ : ℂ) := by
    rw [gammaOf, div_eq_iff Complex.I_ne_zero]
    apply Complex.ext
    · simp only [σ, Complex.sub_re, Complex.one_re, Complex.div_ofNat, Complex.mul_re,
        Complex.neg_re, Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
        Complex.neg_im, Complex.mul_im]
      ring
    · simp only [σ, him, Complex.sub_im, Complex.one_im, Complex.div_ofNat, Complex.mul_im,
        Complex.neg_re, Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
        Complex.neg_im, Complex.mul_re]
      ring
  have hγc : conj (gammaOf ρ) = -Complex.I * ((-σ : ℝ) : ℂ) := by
    rw [hγ, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  have hFT1 := paperFT_cx_neg_I_mul_real (atomDilate φ w) σ
  have hFT2 := paperFT_cx_neg_I_mul_real (atomDilate φ w) (-σ)
  have hD1 : dirichletPoly N (fun _ => 1) (gammaOf ρ) =
      ((∑ n ∈ Icc 1 N, (n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [SpacingScaleHarmonicAnalysis.dirichletPoly_gammaOf]
    have hρeq : ρ - 1 / 2 = (σ : ℂ) := by
      apply Complex.ext
      · simp [σ]
      · simp [him]
    rw [hρeq, Complex.ofReal_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [Complex.ofReal_one, one_mul, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      mul_comm, ← Real.rpow_def_of_pos hn0]
  have hD2 : dirichletPoly N (fun _ => 1) (conj (gammaOf ρ)) =
      ((∑ n ∈ Icc 1 N, (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    unfold dirichletPoly
    rw [hγc, Complex.ofReal_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hI : Complex.I * (-Complex.I * ((-σ : ℝ) : ℂ)) * (Real.log n : ℂ) =
        ((Real.log n * (-σ) : ℝ) : ℂ) := by
      have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      linear_combination (σ : ℂ) * (Real.log n : ℂ) * hII
    rw [Complex.ofReal_one, one_mul, hI, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hn0]
  rw [Wsummand_atomicTest Z hg.continuous hgc, hD1, hD2, hγ, hFT1,
    show conj (-Complex.I * (σ : ℂ)) = -Complex.I * ((-σ : ℝ) : ℂ) by
      rw [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring,
    hFT2]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hg_int : Integrable (atomDilate φ w) := hg.continuous.integrable_of_hasCompactSupport hgc
  have hge1 : w * ∫ u, φ u ≤ ∫ u, atomDilate φ w u * Real.exp (σ * u) := by
    have h1 : ∫ u, atomDilate φ w u = w * ∫ u, φ u := by
      simpa only [atomDilate, smul_eq_mul, abs_of_pos hw] using
        MeasureTheory.Measure.integral_comp_div φ w
    rw [← h1]
    refine integral_mono hg_int
      ((hg.continuous.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        hgc.mul_right) fun u => ?_
    by_cases hu : u ∈ Set.Icc 0 w
    · exact le_mul_of_one_le_right (hg_nonneg u)
        (Real.one_le_exp (mul_nonneg hσ hu.1))
    · simp [hgsupp u hu]
  have hge2 : Real.exp (-(σ * w)) * (w * ∫ u, φ u) ≤
      ∫ u, atomDilate φ w u * Real.exp (-σ * u) := by
    have h1 : ∫ u, atomDilate φ w u = w * ∫ u, φ u := by
      simpa only [atomDilate, smul_eq_mul, abs_of_pos hw] using
        MeasureTheory.Measure.integral_comp_div φ w
    rw [← h1, ← integral_const_mul]
    refine integral_mono (hg_int.const_mul _)
      ((hg.continuous.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        hgc.mul_right) fun u => ?_
    by_cases hu : u ∈ Set.Icc 0 w
    · rw [mul_comm (Real.exp _)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hg_nonneg u)
      nlinarith only [hσ, hu.2]
    · simp [hgsupp u hu]
  have hφ_int_nonneg : 0 ≤ ∫ u, φ u := integral_nonneg hnonneg
  have hA_prod : Real.exp (-(σ * w)) * (w * ∫ u, φ u) ^ 2 ≤
      (∫ u, atomDilate φ w u * Real.exp (σ * u)) *
        (∫ u, atomDilate φ w u * Real.exp (-σ * u)) := by
    calc Real.exp (-(σ * w)) * (w * ∫ u, φ u) ^ 2
        = (w * ∫ u, φ u) * (Real.exp (-(σ * w)) * (w * ∫ u, φ u)) := by ring
      _ ≤ (∫ u, atomDilate φ w u * Real.exp (σ * u)) *
            (∫ u, atomDilate φ w u * Real.exp (-σ * u)) :=
          mul_le_mul hge1 hge2 (by positivity) (le_trans (by positivity) hge1)
  have hD_prod := sq_nat_le_sum_rpow_mul_sum_rpow_neg σ N
  have hdiag : (∑ _n ∈ Icc 1 N, (1 : ℝ) ^ 2) * ∫ u, atomDilate φ w u ^ 2 =
      c * ∫ u, φ u ^ 2 := by
    rw [one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one,
      integral_atomDilate_sq hw]
    dsimp only [w]
    field_simp [hN0.ne']
  rw [hdiag]
  have hident : (Z.mult ρ : ℝ) * Real.exp (-((ρ.re - 1 / 2) * w)) *
      ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * c * (c * ∫ u, φ u ^ 2) =
      (Z.mult ρ : ℝ) * (Real.exp (-(σ * w)) * (w * ∫ u, φ u) ^ 2) * (N : ℝ) ^ 2 := by
    dsimp only [σ, w]
    field_simp [hN0.ne', hM.ne']
  rw [hident]
  have hS_pos : 0 ≤ (∑ n ∈ Icc 1 N, (n : ℝ) ^ σ) * (∑ n ∈ Icc 1 N, (n : ℝ) ^ (-σ)) :=
    (sq_nonneg (N : ℝ)).trans hD_prod
  have hAB_pos : 0 ≤ (∫ u, atomDilate φ w u * Real.exp (σ * u)) *
      (∫ u, atomDilate φ w u * Real.exp (-σ * u)) :=
    (by positivity : 0 ≤ Real.exp (-(σ * w)) * (w * ∫ u, φ u) ^ 2).trans hA_prod
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hA_prod (Nat.cast_nonneg _))
    hD_prod (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hAB_pos)

/-! ### 4. The `isolatedPairConfig` countermodel at every overlap ratio -/

/-- Two-atom difference weights `x₁ = 1`, `x₂ = -1`, `x_n = 0` for `n ≥ 3`. -/
def twoAtomWitness (n : ℕ) : ℝ :=
  if n = 1 then 1 else if n = 2 then -1 else 0

theorem dirichletPoly_twoAtomWitness {N : ℕ} (hN : 2 ≤ N) (z : ℂ) :
    dirichletPoly N twoAtomWitness z = 1 - Complex.exp (Complex.I * z * (Real.log 2 : ℂ)) := by
  unfold dirichletPoly
  have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 N := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl <;> exact mem_Icc.mpr ⟨by omega, by omega⟩
  rw [← sum_subset hsub]
  · rw [sum_pair (by decide)]
    simp [twoAtomWitness]
  · intro n _ hn
    simp only [mem_insert, mem_singleton, not_or] at hn
    simp [twoAtomWitness, hn.1, hn.2]

/-- The two-atom witness `x₁ = 1, x₂ = -1` annihilates every point of the vertical on-line lattice
`{1/2 + 2πik / log 2 : k ∈ ℤ}`. -/
theorem dirichletPoly_twoAtomWitness_verticalLatticePoint {N : ℕ} (hN : 2 ≤ N) (k : ℤ) :
    dirichletPoly N twoAtomWitness (gammaOf (verticalLatticePoint (Real.log 2) 0 k)) = 0 := by
  rw [dirichletPoly_twoAtomWitness hN, gammaOf_verticalLatticePoint]
  have hlog2 : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos one_lt_two).ne'
  have hexp_arg : Complex.I * ((((k : ℝ) * (2 * Real.pi / Real.log 2) : ℝ) : ℂ) -
      Complex.I * (0 : ℝ)) * (Real.log 2 : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp [hlog2]
  rw [hexp_arg, Complex.exp_int_mul_two_pi_mul_I, sub_self]

/-- Right-half zero set of `isolatedPairConfig`: exactly the single off-line point
`offLinePoint δ γ₀`. -/
theorem rightZeros_isolatedPairConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) :
    rightZeros (isolatedPairConfig hL hδ hδ' γ₀) = {offLinePoint δ γ₀} := by
  ext ρ
  simp only [rightZeros, isolatedPairConfig, Set.mem_setOf_eq, Set.mem_union,
    Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨((⟨k, rfl⟩ | rfl) | rfl), hre⟩
    · simp only [verticalLatticePoint] at hre
      linarith
    · rfl
    · simp only [offLinePoint] at hre
      linarith
  · rintro rfl
    refine ⟨Or.inl (Or.inr rfl), ?_⟩
    simp only [offLinePoint]
    linarith

private theorem integral_mul_exp_pos_of_sq_pos {g : ℝ → ℝ} {w : ℝ}
    (hg : Continuous g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hgc : HasCompactSupport g) (hnonneg : ∀ u, 0 ≤ g u) (hM : 0 < ∫ u, g u ^ 2)
    (α : ℝ) :
    0 < ∫ u, g u * Real.exp (α * u) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hgc
  set B₁ := max B 1
  have hB₁_pos : 0 < B₁ := lt_of_lt_of_le one_pos (le_max_right B 1)
  set C := B₁ * Real.exp (|α| * w)
  have hC_pos : 0 < C := by positivity
  have hle : ∀ u, g u ^ 2 ≤ C * (g u * Real.exp (α * u)) := by
    intro u
    by_cases hu : u ∈ Set.Icc 0 w
    · have hgu_le : g u ≤ B₁ := (hB u).trans (le_max_left B 1)
      have hexp_ge : 1 ≤ Real.exp (|α| * w) * Real.exp (α * u) := by
        rw [← Real.exp_add]
        refine Real.one_le_exp ?_
        have h1 : -(α * u) ≤ |α * u| := neg_le_abs _
        have h2 : |α * u| ≤ |α| * w := by
          rw [abs_mul, abs_of_nonneg hu.1]
          exact mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)
        linarith
      calc g u ^ 2 = g u * g u := sq (g u)
        _ ≤ B₁ * g u := mul_le_mul_of_nonneg_right hgu_le (hnonneg u)
        _ ≤ B₁ * g u * (Real.exp (|α| * w) * Real.exp (α * u)) :=
            le_mul_of_one_le_right (mul_nonneg hB₁_pos.le (hnonneg u)) hexp_ge
        _ = C * (g u * Real.exp (α * u)) := by dsimp only [C]; ring
    · simp [hgsupp u hu]
  have hint_sq : Integrable (fun u => g u ^ 2) :=
    (hg.pow 2).integrable_of_hasCompactSupport (by simpa only [sq] using hgc.mul_right)
  have hint_exp : Integrable (fun u => g u * Real.exp (α * u)) :=
    (hg.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hgc.mul_right
  have hint_le : ∫ u, g u ^ 2 ≤ C * ∫ u, g u * Real.exp (α * u) := by
    rw [← integral_const_mul]
    exact integral_mono hint_sq (hint_exp.const_mul C) hle
  have hpos_prod : 0 < C * ∫ u, g u * Real.exp (α * u) := lt_of_lt_of_le hM hint_le
  exact (mul_pos_iff_of_pos_left hC_pos).mp hpos_prod

/-- **Obstruction to purely zero-side fixed-ratio proofs**: on
`Z = isolatedPairConfig (Real.log_pos one_lt_two) hδ hδ' 0` (`0 < δ ≤ 1/2`), `Z` is tempered and
has a single right-half zero (`rightZeros Z = {offLinePoint δ 0}`), yet for every nonnegative `C²`
profile `φ` supported in `[0, 1]` with `∫ φ² > 0`, every overlap ratio `c > 0`, and every horizon
`N ≥ 2`, the two-atom test `twoAtomWitness` satisfies `Re Z.W(f_x, f_x) < 0`. -/
theorem isolatedPairConfig_atomic_negative_every_ratio {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hnonneg : ∀ u, 0 ≤ φ u) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 2 ≤ N) :
    let hL := Real.log_pos one_lt_two
    let Z := isolatedPairConfig hL hδ hδ' 0
    let f := cx (atomicTest N twoAtomWitness (atomDilate φ (c / N)))
    TemperedConfig Z ∧
      rightZeros Z = {offLinePoint δ 0} ∧
      (Z.W f f).re < 0 := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  let Z := isolatedPairConfig hL hδ hδ' 0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set w := c / N
  have hw : 0 < w := div_pos hc hN0
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw
  set g := atomDilate φ w
  set f := cx (atomicTest N twoAtomWitness g)
  refine ⟨temperedConfig_isolatedPairConfig hL hδ hδ' 0,
    rightZeros_isolatedPairConfig hL hδ hδ' 0, ?_⟩
  -- 1. Every lattice zero summand vanishes identically
  have hlat_zero : ∀ ρ : Set.range (verticalLatticePoint (Real.log 2) 0), Z.Wsummand f f ρ = 0 := by
    rintro ⟨_, k, rfl⟩
    rw [Wsummand_atomicTest Z hg.continuous hgc N twoAtomWitness,
      dirichletPoly_twoAtomWitness_verticalLatticePoint hN k, zero_mul, mul_zero]
  have h₁ : HasSum (fun ρ : Set.range (verticalLatticePoint (Real.log 2) 0) => Z.Wsummand f f ρ) 0 := by
    convert hasSum_zero using 1
    funext ρ
    exact hlat_zero ρ
  -- 2. Evaluate the two simple off-line points `offLinePoint (±δ) 0`
  have hmultdef : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else 1 := fun _ => rfl
  have hm_pos : Z.mult (offLinePoint δ 0) = 1 := by
    rw [hmultdef, if_neg]; simp only [offLinePoint]; linarith
  have hm_neg : Z.mult (offLinePoint (-δ) 0) = 1 := by
    rw [hmultdef, if_neg]; simp only [offLinePoint]; linarith
  have hγ_pos : gammaOf (offLinePoint δ 0) = -Complex.I * (δ : ℂ) := by
    rw [gammaOf_offLinePoint]; simp
  have hγ_neg : gammaOf (offLinePoint (-δ) 0) = -Complex.I * ((-δ : ℝ) : ℂ) := by
    rw [gammaOf_offLinePoint]; push_cast; ring
  have hconj_pos : conj (gammaOf (offLinePoint δ 0)) = -Complex.I * ((-δ : ℝ) : ℂ) := by
    rw [hγ_pos, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
  have hconj_neg : conj (gammaOf (offLinePoint (-δ) 0)) = -Complex.I * (δ : ℂ) := by
    rw [hγ_neg, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
  have hFT_pos := paperFT_cx_neg_I_mul_real g δ
  have hFT_neg := paperFT_cx_neg_I_mul_real g (-δ)
  have hD_pos : dirichletPoly N twoAtomWitness (-Complex.I * (δ : ℂ)) =
      ((1 - Real.exp (δ * Real.log 2) : ℝ) : ℂ) := by
    rw [dirichletPoly_twoAtomWitness hN]
    have hI : Complex.I * (-Complex.I * (δ : ℂ)) * (Real.log 2 : ℂ) =
        ((δ * Real.log 2 : ℝ) : ℂ) := by
      have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      linear_combination -(δ : ℂ) * (Real.log 2 : ℂ) * hII
    rw [hI, ← Complex.ofReal_exp, Complex.ofReal_sub, Complex.ofReal_one]
  have hD_neg : dirichletPoly N twoAtomWitness (-Complex.I * ((-δ : ℝ) : ℂ)) =
      ((1 - Real.exp (-δ * Real.log 2) : ℝ) : ℂ) := by
    rw [dirichletPoly_twoAtomWitness hN]
    have hI : Complex.I * (-Complex.I * ((-δ : ℝ) : ℂ)) * (Real.log 2 : ℂ) =
        ((-δ * Real.log 2 : ℝ) : ℂ) := by
      have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      linear_combination (δ : ℂ) * (Real.log 2 : ℂ) * hII
    rw [hI, ← Complex.ofReal_exp, Complex.ofReal_sub, Complex.ofReal_one]
  set v : ℝ := (∫ u, g u * Real.exp (δ * u)) * (∫ u, g u * Real.exp (-δ * u)) *
    ((1 - Real.exp (δ * Real.log 2)) * (1 - Real.exp (-δ * Real.log 2)))
  have hvp : Z.Wsummand f f (offLinePoint δ 0) = (v : ℂ) := by
    rw [Wsummand_atomicTest Z hg.continuous hgc N twoAtomWitness,
      hm_pos, hconj_pos, hγ_pos, hFT_pos, hFT_neg, hD_pos, hD_neg]
    simp only [Nat.cast_one, one_mul, Complex.conj_ofReal, ← Complex.ofReal_mul]
    rfl
  have hvq : Z.Wsummand f f (offLinePoint (-δ) 0) = (v : ℂ) := by
    rw [Wsummand_atomicTest Z hg.continuous hgc N twoAtomWitness,
      hm_neg, hconj_neg, hγ_neg, hFT_pos, hFT_neg, hD_pos, hD_neg]
    simp only [Nat.cast_one, one_mul, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    ring
  have hp := hasSum_singleton (offLinePoint δ 0) (Z.Wsummand f f)
  rw [hvp] at hp
  have hq := hasSum_singleton (offLinePoint (-δ) 0) (Z.Wsummand f f)
  rw [hvq] at hq
  have hd₁ : Disjoint (Set.range (verticalLatticePoint (Real.log 2) 0)) {offLinePoint δ 0} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨_, hk⟩
    have := congrArg Complex.re hk
    simp only [verticalLatticePoint, offLinePoint] at this
    linarith
  have hd₂ : Disjoint (Set.range (verticalLatticePoint (Real.log 2) 0) ∪ {offLinePoint δ 0})
      {offLinePoint (-δ) 0} := by
    rw [Set.disjoint_singleton_right]
    rintro (⟨_, hk⟩ | hk)
    · have := congrArg Complex.re hk
      simp only [verticalLatticePoint, offLinePoint] at this
      linarith
    · rw [Set.mem_singleton_iff] at hk
      have := congrArg Complex.re hk
      simp only [offLinePoint] at this
      linarith
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) hd₂
    (HasSum.add_disjoint (f := Z.Wsummand f f) hd₁ h₁ hp) hq
  have hW : Z.W f f = ((2 * v : ℝ) : ℂ) := by
    rw [ZeroConfig.W, hall.tsum_eq, zero_add, ← Complex.ofReal_add]
    congr 1; ring
  rw [hW, Complex.ofReal_re]
  -- 3. Strict negativity of `2 * v`
  have hg_M : 0 < ∫ u, g u ^ 2 := by
    rw [integral_atomDilate_sq hw]; exact mul_pos hw hM
  have hg_nonneg : ∀ u, 0 ≤ g u := fun u => hnonneg (u / w)
  have hA_pos : 0 < ∫ u, g u * Real.exp (δ * u) :=
    integral_mul_exp_pos_of_sq_pos hg.continuous hgsupp hgc hg_nonneg hg_M δ
  have hB_pos : 0 < ∫ u, g u * Real.exp (-δ * u) :=
    integral_mul_exp_pos_of_sq_pos hg.continuous hgsupp hgc hg_nonneg hg_M (-δ)
  have hD_lt : (1 - Real.exp (δ * Real.log 2)) * (1 - Real.exp (-δ * Real.log 2)) < 0 := by
    have h1 : 1 < Real.exp (δ * Real.log 2) :=
      Real.one_lt_exp_iff.mpr (mul_pos hδ hL)
    have h2 : Real.exp (-δ * Real.log 2) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith only [hδ, hL])
    exact mul_neg_of_neg_of_pos (by linarith only [h1]) (by linarith only [h2])
  have hv_lt : v < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hA_pos hB_pos) hD_lt
  linarith only [hv_lt]

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.unconditional_transMetzler_positivity_interval
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.weilQuad_atomicTest_nonneg_of_riemannHypothesis
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.hermQuad_atomicShiftWeilGram_eq_weilQuad
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.hermNegIndex_atomicShiftWeilGram_le_of_finiteOffLine
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.re_Wsummand_atomicTest_const_one_ge
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.isolatedPairConfig_atomic_negative_every_ratio
