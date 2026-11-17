import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.FiniteLayerKreinStructureAndRigidity
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalStatesFormAnOrthogonalLadder
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheOffLineZerosBoundTheCriticalRatioFromBelow
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZeroDensityFilteredWeilPositivityAndCoercivity

/-!
# The trace inequality of the critical ladder

Let `Φ_0, …, Φ_k` be a critical ladder: confined null vectors at ratios `R_0 ≤ … ≤ R_k`, orthogonal
for `W₈(F, G) = ∫ F G e^{-8u}`. Under a finite layer each rung satisfies the zero Parseval identity
`Σ_on |LΦ_j(z)|² + Σ_off LΦ_j(z) LΦ_j(-z) = -a(R_j) W₈(Φ_j)`, so
`a(R_j) W₈(Φ_j) ≤ Σ_off |LΦ_j(z)| |LΦ_j(-z)|`
(`IsConfinedNullVector.criticalAliasCoefficient_mul_le_offLine`).

* **Bessel against the zero exponentials** (`sum_norm_sq_laplace_div_le`). The profiles
  `Φ_j e^{-4u}/√W₈(Φ_j)` are orthonormal in `L²(du)`, and `LΦ_j(z)/√W₈(Φ_j)` is their coefficient
  against `e^{(z+4)u}` on `u < 0`, of squared norm `1/(2 Re z + 8)`; hence
  `Σ_j |LΦ_j(z)|²/W₈(Φ_j) ≤ 1/(2 Re z + 8)`.
* **The trace inequality** (`IsCriticalLadder.sum_criticalAliasCoefficient_le`). Cauchy–Schwarz over
  the rungs at each off-line pair `(z, -z)` gives
  `Σ_j a(R_j) ≤ Σ_{off-line ρ} m_ρ/√((8 + 2x_ρ)(8 - 2x_ρ))`, `x_ρ = Re ρ - ½`: the bound
  `criticalAliasCoefficient_le_offLineWeight` of the critical ratio holds for the whole ladder.
* **Corollaries.** `(j + 1)·a(R_j)` is at most the off-line weight `S`
  (`IsCriticalLadder.succ_mul_criticalAliasCoefficient_le`), so the ratios grow at least linearly,
  `R_j ≥ (j + 1)·a(1)/S` (`IsCriticalLadder.succ_mul_div_le_ratio`); and
  `√63·Σ_j a(R_j) ≤ N_off`, the number of off-line zeros with multiplicity
  (`IsCriticalLadder.sqrt_sixtyThree_mul_sum_le`).
-/

open MeasureTheory Set Filter Topology Zeta23

noncomputable section

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Bessel's inequality against the zero exponentials -/

/-- **Bessel** for real orthonormal `L²` functions against a complex `L²` function. -/
theorem sum_norm_sq_integral_le {ι : Type*} [Fintype ι] [DecidableEq ι] {ψ : ι → ℝ → ℝ}
    (hψ : ∀ j, MemLp (ψ j) 2) (horth : ∀ i j, ∫ u, ψ i u * ψ j u = if i = j then 1 else 0)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    ∑ j, ‖∫ u, (ψ j u : ℂ) * f u‖ ^ 2 ≤ ∫ u, ‖f u‖ ^ 2 := by
  have hψc : ∀ j, MemLp (fun u => (ψ j u : ℂ)) 2 := fun j => (hψ j).ofReal
  let v : ι → Lp ℂ 2 (volume : Measure ℝ) := fun j => (hψc j).toLp _
  have hinner : ∀ (g h : ℝ → ℂ) (hg : MemLp g 2) (hh : MemLp h 2),
      inner ℂ (hg.toLp g) (hh.toLp h) = ∫ u, (starRingEnd ℂ) (g u) * h u := by
    intro g h hg hh
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with u h1 h2
    rw [h1, h2, RCLike.inner_apply, mul_comm]
  have hon : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner]
    simp_rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [integral_complex_ofReal, horth i j]
    split_ifs <;> simp
  have hb := hon.sum_inner_products_le (x := hf.toLp f) (s := Finset.univ)
  have hn : ‖hf.toLp f‖ ^ 2 = ∫ u, ‖f u‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) (hf.toLp f), hinner]
    have : (fun u => (starRingEnd ℂ) (f u) * f u) = fun u => ((‖f u‖ ^ 2 : ℝ) : ℂ) := by
      funext u; rw [RCLike.conj_mul]; push_cast; rfl
    rw [this, integral_complex_ofReal]
    simp
  rw [hn] at hb
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) hb
  rw [hinner]
  simp_rw [Complex.conj_ofReal]


/-- The zero exponential `u ↦ e^{(z+4)u}` on the negative half-line. -/
def zeroExponential (z : ℂ) (u : ℝ) : ℂ :=
  (Iio (0 : ℝ)).indicator (fun v => Complex.exp ((z + 4) * v)) u

theorem norm_sq_zeroExponential (z : ℂ) (u : ℝ) :
    ‖zeroExponential z u‖ ^ 2 = (Iio (0 : ℝ)).indicator (fun v => Real.exp ((2 * z.re + 8) * v)) u := by
  by_cases hu : u < 0
  · rw [zeroExponential, indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu),
      indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu), Complex.norm_exp, sq, ← Real.exp_add]
    congr 1
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    norm_num
    ring
  · rw [zeroExponential, indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu),
      indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu), norm_zero]
    norm_num

theorem measurable_zeroExponential (z : ℂ) : Measurable (zeroExponential z) :=
  (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)).indicator
    measurableSet_Iio

theorem integral_norm_sq_zeroExponential {z : ℂ} (hz : -4 < z.re) :
    Integrable (fun u => ‖zeroExponential z u‖ ^ 2) ∧
      ∫ u, ‖zeroExponential z u‖ ^ 2 = 1 / (2 * z.re + 8) := by
  have ha : 0 < 2 * z.re + 8 := by linarith
  simp_rw [norm_sq_zeroExponential]
  refine ⟨((integrableOn_exp_mul_Iic ha 0).mono_set Iio_subset_Iic_self).integrable_indicator
    measurableSet_Iio, ?_⟩
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_Iic ha 0, mul_zero, Real.exp_zero]

theorem memLp_zeroExponential {z : ℂ} (hz : -4 < z.re) : MemLp (zeroExponential z) 2 :=
  (memLp_two_iff_integrable_sq_norm (measurable_zeroExponential z).aestronglyMeasurable).mpr
    (integral_norm_sq_zeroExponential hz).1

/-- **Bessel against the zero exponentials.** Real half-line profiles, orthogonal for
`W₈(F, G) = ∫ F G e^{-8u}` with `W₈(Φ_j, Φ_j) > 0`, satisfy
`Σ_j |∫ e^{zu} Φ_j|² / W₈(Φ_j, Φ_j) ≤ 1/(2 Re z + 8)` for `Re z > -4`. -/
theorem sum_norm_sq_laplace_div_le {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : ι → ℝ → ℝ}
    (hm : ∀ j, Measurable (Φ j)) (hsupp : ∀ j u, 0 ≤ u → Φ j u = 0)
    (hexp : ∀ j, Integrable fun u => Φ j u ^ 2 * Real.exp (-(8 * u)))
    (hpos : ∀ j, 0 < ∫ u, Φ j u * Φ j u * Real.exp (-(8 * u)))
    (horth : ∀ i j, i ≠ j → ∫ u, Φ i u * Φ j u * Real.exp (-(8 * u)) = 0)
    {z : ℂ} (hz : -4 < z.re) :
    ∑ j, ‖∫ u : ℝ, Complex.exp (z * u) * (Φ j u : ℂ)‖ ^ 2 /
        (∫ u, Φ j u * Φ j u * Real.exp (-(8 * u))) ≤ 1 / (2 * z.re + 8) := by
  set w : ι → ℝ := fun j => ∫ u, Φ j u * Φ j u * Real.exp (-(8 * u)) with hw
  have he : ∀ u : ℝ, Real.exp (-(4 * u)) * Real.exp (-(4 * u)) = Real.exp (-(8 * u)) := fun u => by
    rw [← Real.exp_add]; congr 1; ring
  -- the `W₈`-normalised rungs in `L²(du)`
  set ψ : ι → ℝ → ℝ := fun j u => Φ j u * Real.exp (-(4 * u)) / Real.sqrt (w j) with hψ
  have hψmeas : ∀ j, Measurable (ψ j) := fun j => by
    have := hm j
    simp only [hψ]
    fun_prop
  have hψm : ∀ j, MemLp (ψ j) 2 := fun j => by
    refine (memLp_two_iff_integrable_sq (hψmeas j).aestronglyMeasurable).mpr ?_
    refine ((hexp j).div_const (w j)).congr (Eventually.of_forall fun u => ?_)
    simp only [hψ]
    rw [div_pow, mul_pow, Real.sq_sqrt (hpos j).le, sq (Real.exp _), he]
  have hψo : ∀ i j, ∫ u, ψ i u * ψ j u = if i = j then 1 else 0 := by
    intro i j
    have e : (fun u => ψ i u * ψ j u) = fun u =>
        Φ i u * Φ j u * Real.exp (-(8 * u)) / (Real.sqrt (w i) * Real.sqrt (w j)) := by
      funext u; simp only [hψ]; rw [← he u]; field_simp
    rw [e, integral_div]
    split_ifs with h
    · subst h
      rw [Real.mul_self_sqrt (hpos i).le]
      exact div_self (hpos i).ne'
    · rw [horth i j h, zero_div]
  have hcouple : ∀ j (u : ℝ), (ψ j u : ℂ) * zeroExponential z u =
      Complex.exp (z * u) * (Φ j u : ℂ) / (Real.sqrt (w j) : ℂ) := by
    intro j u
    by_cases hu : u < 0
    · rw [zeroExponential, indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu)]
      simp only [hψ]
      push_cast
      rw [show Complex.exp (z * u) = Complex.exp (-(4 * (u : ℂ))) * Complex.exp ((z + 4) * u) by
        rw [← Complex.exp_add]; congr 1; ring]
      ring
    · simp [hψ, hsupp j u (not_lt.mp hu)]
  have hb := sum_norm_sq_integral_le hψm hψo (memLp_zeroExponential hz)
  rw [(integral_norm_sq_zeroExponential hz).2] at hb
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) hb
  have hsq : ‖((Real.sqrt (w j) : ℝ) : ℂ)‖ ^ 2 = w j := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hpos j).le]
  simp_rw [hcouple, integral_div, norm_div, div_pow, hsq]
  rfl

/-- **Cauchy–Schwarz over the rungs at an off-line pair.** -/
theorem sum_mul_div_le_of_bessel {ι : Type*} (s : Finset ι) {a b w : ι → ℝ} (hw : ∀ j, 0 < w j)
    (ha0 : ∀ j, 0 ≤ a j) (hb0 : ∀ j, 0 ≤ b j) {x : ℝ} (hx : |x| < 4)
    (ha : ∑ j ∈ s, a j ^ 2 / w j ≤ 1 / (2 * x + 8))
    (hb : ∑ j ∈ s, b j ^ 2 / w j ≤ 1 / (2 * -x + 8)) :
    ∑ j ∈ s, a j * b j / w j ≤ 1 / Real.sqrt ((8 + 2 * x) * (8 - 2 * x)) := by
  have hx' := abs_lt.mp hx
  have hA : 0 < 2 * x + 8 := by linarith
  have hB : 0 < 2 * -x + 8 := by linarith
  have e : ∀ j, a j * b j / w j = Real.sqrt (a j ^ 2 / w j) * Real.sqrt (b j ^ 2 / w j) := by
    intro j
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (ha0 j),
      Real.sqrt_sq (hb0 j), div_mul_div_comm, Real.mul_self_sqrt (hw j).le]
  calc ∑ j ∈ s, a j * b j / w j
      = ∑ j ∈ s, Real.sqrt (a j ^ 2 / w j) * Real.sqrt (b j ^ 2 / w j) :=
        Finset.sum_congr rfl fun j _ => e j
    _ ≤ Real.sqrt (∑ j ∈ s, a j ^ 2 / w j) * Real.sqrt (∑ j ∈ s, b j ^ 2 / w j) :=
        Real.sum_sqrt_mul_sqrt_le s (fun j => div_nonneg (sq_nonneg _) (hw j).le)
          (fun j => div_nonneg (sq_nonneg _) (hw j).le)
    _ ≤ Real.sqrt (1 / (2 * x + 8)) * Real.sqrt (1 / (2 * -x + 8)) :=
        mul_le_mul (Real.sqrt_le_sqrt ha) (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = 1 / Real.sqrt ((8 + 2 * x) * (8 - 2 * x)) := by
        rw [← Real.sqrt_mul (div_nonneg zero_le_one hA.le), one_div_mul_one_div, one_div,
          Real.sqrt_inv, one_div]
        congr 2
        ring

/-! ### The trace inequality -/

/-- Under a finite layer the off-line copies form a finite set. -/
theorem finite_onLineCopies_compl (hfin : BacklundConverse.FiniteOffLine) :
    (onLineCopiesᶜ : Set XiZeroCopy).Finite := by
  refine (show {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite from hfin).subset
    fun q hq => ?_
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint, Complex.mul_im]
  change (xiSpectralPoint q).im ≠ 0
  rw [him]
  intro h
  apply hq
  change (centredZero q).re = 0
  rw [centredZero, Complex.sub_re]
  norm_num
  linarith

/-- **One rung.** Under a finite layer a confined null vector satisfies
`a(R) W₈(Φ) ≤ Σ_off |LΦ(z)| |LΦ(-z)|`: the on-line part of its zero Parseval identity is
nonnegative. -/
theorem IsConfinedNullVector.criticalAliasCoefficient_mul_le_offLine {R : ℝ} (hR : 0 < R)
    {Φ : ℝ → ℝ} (hΦ : IsConfinedNullVector R Φ) (hfin : BacklundConverse.FiniteOffLine) :
    criticalAliasCoefficient R * criticalHalfLineExponentialPair Φ Φ ≤
      ∑' q : ↑(onLineCopiesᶜ : Set XiZeroCopy),
        ‖negativeHalfLineLaplace (cx Φ) (centredZero q)‖ *
          ‖negativeHalfLineLaplace (cx Φ) (-centredZero q)‖ := by
  haveI : Finite ↑(onLineCopiesᶜ : Set XiZeroCopy) := (finite_onLineCopies_compl hfin).to_subtype
  obtain ⟨-, hP⟩ := nullVector_zeroParseval_of_finiteOffLine hR hΦ hfin
  have hre := congrArg Complex.re hP
  rw [Complex.add_re, Complex.ofReal_re, Complex.ofReal_re, Complex.re_tsum Summable.of_finite]
    at hre
  have hon : 0 ≤ ∑' q : onLineCopies, zeroValueMass Φ q :=
    tsum_nonneg fun q => by unfold zeroValueMass; positivity
  have hle : ∑' q : ↑(onLineCopiesᶜ : Set XiZeroCopy),
      -(negativeHalfLineLaplace (cx Φ) (centredZero q) *
        negativeHalfLineLaplace (cx Φ) (-centredZero q)).re ≤
      ∑' q : ↑(onLineCopiesᶜ : Set XiZeroCopy),
        ‖negativeHalfLineLaplace (cx Φ) (centredZero q)‖ *
          ‖negativeHalfLineLaplace (cx Φ) (-centredZero q)‖ :=
    Summable.tsum_le_tsum (fun q => (neg_le_abs _).trans
      ((Complex.abs_re_le_norm _).trans (norm_mul _ _).le)) Summable.of_finite Summable.of_finite
  rw [tsum_neg] at hle
  rw [criticalHalfLineExponentialPair_self]
  unfold stateZeroNormLimit at hre
  linarith

/-- The weight `1/√((8 + 2x)(8 - 2x))` of a copy, `x = Re z`. -/
def offCopyWeight (q : XiZeroCopy) : ℝ :=
  1 / Real.sqrt ((8 + 2 * (centredZero q).re) * (8 - 2 * (centredZero q).re))

/-- **The trace inequality over copies.** Under a finite layer,
`Σ_j a(R_j) ≤ Σ_{off-line copies} 1/√((8 + 2x)(8 - 2x))`. -/
theorem IsCriticalLadder.sum_criticalAliasCoefficient_le_offCopyWeight {k : ℕ}
    {R : Fin (k + 1) → ℝ} {Φ : Fin (k + 1) → ℝ → ℝ} (hL : IsCriticalLadder k R Φ)
    (hfin : BacklundConverse.FiniteOffLine) :
    ∑ j, criticalAliasCoefficient (R j) ≤
      ∑' q : ↑(onLineCopiesᶜ : Set XiZeroCopy), offCopyWeight q := by
  haveI : Finite ↑(onLineCopiesᶜ : Set XiZeroCopy) := (finite_onLineCopies_compl hfin).to_subtype
  have hd : ∀ j, CriticalHalfLineEnergyDomain (Φ j) := fun j => (hL.null j).1
  have hw : ∀ j, 0 < criticalHalfLineExponentialPair (Φ j) (Φ j) := fun j =>
    exponentialPair_self_pos (hd j) (by rw [hL.unit j]; norm_num)
  set w : Fin (k + 1) → ℝ := fun j => criticalHalfLineExponentialPair (Φ j) (Φ j) with hwdef
  set A : Fin (k + 1) → ↑(onLineCopiesᶜ : Set XiZeroCopy) → ℝ := fun j q =>
    ‖negativeHalfLineLaplace (cx (Φ j)) (centredZero q)‖ *
      ‖negativeHalfLineLaplace (cx (Φ j)) (-centredZero q)‖ / w j with hA
  -- one rung at a time
  have h1 : ∀ j, criticalAliasCoefficient (R j) ≤ ∑' q, A j q := by
    intro j
    simp only [hA]
    rw [tsum_div_const, le_div_iff₀ (hw j)]
    exact (hL.null j).criticalAliasCoefficient_mul_le_offLine (hL.pos j) hfin
  -- Bessel at every point right of `Re z = -4`
  have hbessel : ∀ z : ℂ, -4 < z.re →
      ∑ j, ‖negativeHalfLineLaplace (cx (Φ j)) z‖ ^ 2 / w j ≤ 1 / (2 * z.re + 8) :=
    fun z hz => sum_norm_sq_laplace_div_le (fun j => (hd j).meas) (fun j => (hd j).support)
      (fun j => (hd j).exponential) hw (fun i j hij => hL.orth i j hij) hz
  -- Cauchy–Schwarz over the rungs at each off-line pair `(z, -z)`
  have h2 : ∀ q, ∑ j, A j q ≤ offCopyWeight q := by
    intro q
    have hx := abs_lt.mp (abs_re_centredZero_lt q)
    have hb1 := hbessel (centredZero q) (by linarith [hx.1])
    have hb2 := hbessel (-centredZero q) (by rw [Complex.neg_re]; linarith [hx.2])
    rw [Complex.neg_re] at hb2
    exact sum_mul_div_le_of_bessel Finset.univ hw (fun j => norm_nonneg _)
      (fun j => norm_nonneg _) (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) hb1 hb2
  calc ∑ j, criticalAliasCoefficient (R j) ≤ ∑ j, ∑' q, A j q :=
        Finset.sum_le_sum fun j _ => h1 j
    _ = ∑' q, ∑ j, A j q := (hasSum_sum fun j _ => (Summable.of_finite).hasSum).tsum_eq.symm
    _ ≤ ∑' q : ↑(onLineCopiesᶜ : Set XiZeroCopy), offCopyWeight q :=
        Summable.tsum_le_tsum h2 Summable.of_finite Summable.of_finite

/-- The copy weights sum to the off-line weight of the zeros counted with multiplicity. -/
theorem tsum_offCopyWeight_eq_tsum_offLineWeight (hfin : BacklundConverse.FiniteOffLine) :
    ∑' q : ↑(onLineCopiesᶜ : Set XiZeroCopy), offCopyWeight q = ∑' τ, offLineWeight τ := by
  let g : ℂ → ℝ := fun ρ => if (ρ - 1 / 2).re = 0 then 0 else
    1 / Real.sqrt ((8 + 2 * (ρ - 1 / 2).re) * (8 - 2 * (ρ - 1 / 2).re))
  have hind : (onLineCopiesᶜ : Set XiZeroCopy).indicator offCopyWeight =
      fun q : XiZeroCopy => g (q.1 : ℂ) := by
    funext q
    by_cases hq : ((q.1 : ℂ) - 1 / 2).re = 0
    · rw [indicator_of_notMem (show q ∉ (onLineCopiesᶜ : Set XiZeroCopy) from fun h => h hq)]
      simp only [g, if_pos hq]
    · rw [indicator_of_mem (show q ∈ (onLineCopiesᶜ : Set XiZeroCopy) from hq)]
      simp only [g, if_neg hq]
      rfl
  have hsumm : Summable fun q : XiZeroCopy => g (q.1 : ℂ) := by
    refine summable_of_hasFiniteSupport ((finite_onLineCopies_compl hfin).subset
      fun q hq hon => hq ?_)
    simp only [g, if_pos (show ((q.1 : ℂ) - 1 / 2).re = 0 from hon)]
  rw [tsum_subtype, hind, tsum_xiZeroCopy_eq_zetaCarrier hsumm]
  refine tsum_congr fun τ => ?_
  simp only [g, offLineWeight]
  split_ifs <;> ring

/-- **The trace inequality of the ladder.** Under a finite layer, for a critical ladder with ratios
`R_0 ≤ … ≤ R_k`: `Σ_j a(R_j) ≤ Σ_{off-line ρ} m_ρ/√((8 + 2x_ρ)(8 - 2x_ρ))`. -/
theorem IsCriticalLadder.sum_criticalAliasCoefficient_le {k : ℕ}
    {R : Fin (k + 1) → ℝ} {Φ : Fin (k + 1) → ℝ → ℝ} (hL : IsCriticalLadder k R Φ)
    (hfin : BacklundConverse.FiniteOffLine) :
    ∑ j, criticalAliasCoefficient (R j) ≤ ∑' τ, offLineWeight τ :=
  (hL.sum_criticalAliasCoefficient_le_offCopyWeight hfin).trans_eq
    (tsum_offCopyWeight_eq_tsum_offLineWeight hfin)

/-- **The ratios cannot cluster.** `(j + 1)·a(R_j)` is at most the off-line weight. -/
theorem IsCriticalLadder.succ_mul_criticalAliasCoefficient_le {k : ℕ}
    {R : Fin (k + 1) → ℝ} {Φ : Fin (k + 1) → ℝ → ℝ} (hL : IsCriticalLadder k R Φ)
    (hfin : BacklundConverse.FiniteOffLine) (j : Fin (k + 1)) :
    ((j : ℕ) + 1 : ℝ) * criticalAliasCoefficient (R j) ≤ ∑' τ, offLineWeight τ := by
  refine le_trans ?_ (hL.sum_criticalAliasCoefficient_le hfin)
  have hanti : ∀ i, i ≤ j → criticalAliasCoefficient (R j) ≤ criticalAliasCoefficient (R i) := by
    intro i hij
    rw [criticalAliasCoefficient_eq_div (R j), criticalAliasCoefficient_eq_div (R i)]
    exact div_le_div_of_nonneg_left (criticalAliasCoefficient_positive one_pos).le (hL.pos i)
      (hL.mono hij)
  calc ((j : ℕ) + 1 : ℝ) * criticalAliasCoefficient (R j)
      = ∑ _i ∈ Finset.Iic j, criticalAliasCoefficient (R j) := by
        rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∑ i ∈ Finset.Iic j, criticalAliasCoefficient (R i) :=
        Finset.sum_le_sum fun i hi => hanti i (Finset.mem_Iic.mp hi)
    _ ≤ ∑ i, criticalAliasCoefficient (R i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => (criticalAliasCoefficient_positive (hL.pos i)).le)

/-- **The ratios grow at least linearly:** `R_j ≥ (j + 1)·a(1)/S`, `S` the off-line weight. -/
theorem IsCriticalLadder.succ_mul_div_le_ratio {k : ℕ}
    {R : Fin (k + 1) → ℝ} {Φ : Fin (k + 1) → ℝ → ℝ} (hL : IsCriticalLadder k R Φ)
    (hfin : BacklundConverse.FiniteOffLine) (j : Fin (k + 1)) :
    ((j : ℕ) + 1 : ℝ) * criticalAliasCoefficient 1 / ∑' τ, offLineWeight τ ≤ R j := by
  have h := hL.succ_mul_criticalAliasCoefficient_le hfin j
  have hS : 0 < ∑' τ, offLineWeight τ :=
    lt_of_lt_of_le (mul_pos (by positivity) (criticalAliasCoefficient_positive (hL.pos j))) h
  rw [criticalAliasCoefficient_eq_div (R j), mul_div_assoc', div_le_iff₀ (hL.pos j)] at h
  rw [div_le_iff₀ hS]
  linarith

/-- **Counting form.** `√63·Σ_j a(R_j) ≤ N_off`, the number of off-line zeros with multiplicity. -/
theorem IsCriticalLadder.sqrt_sixtyThree_mul_sum_le {k : ℕ}
    {R : Fin (k + 1) → ℝ} {Φ : Fin (k + 1) → ℝ → ℝ} (hL : IsCriticalLadder k R Φ)
    (hfin : BacklundConverse.FiniteOffLine) :
    Real.sqrt 63 * ∑ j, criticalAliasCoefficient (R j) ≤
      Nat.card ↑(onLineCopiesᶜ : Set XiZeroCopy) := by
  haveI : Finite ↑(onLineCopiesᶜ : Set XiZeroCopy) := (finite_onLineCopies_compl hfin).to_subtype
  letI := Fintype.ofFinite ↑(onLineCopiesᶜ : Set XiZeroCopy)
  have hw : ∀ q : XiZeroCopy, offCopyWeight q ≤ 1 / Real.sqrt 63 := by
    intro q
    have hx := abs_lt.mp (abs_re_centredZero_lt q)
    unfold offCopyWeight
    exact one_div_le_one_div_of_le (by positivity) (Real.sqrt_le_sqrt (by nlinarith))
  have h := hL.sum_criticalAliasCoefficient_le_offCopyWeight hfin
  rw [tsum_fintype] at h
  have h2 : ∑ q : ↑(onLineCopiesᶜ : Set XiZeroCopy), offCopyWeight q ≤
      ∑ _q : ↑(onLineCopiesᶜ : Set XiZeroCopy), 1 / Real.sqrt 63 :=
    Finset.sum_le_sum fun q _ => hw q
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card] at h2
  have h63 : 0 < Real.sqrt 63 := by positivity
  calc Real.sqrt 63 * ∑ j, criticalAliasCoefficient (R j)
      ≤ Real.sqrt 63 * ((Nat.card ↑(onLineCopiesᶜ : Set XiZeroCopy) : ℝ) * (1 / Real.sqrt 63)) :=
        mul_le_mul_of_nonneg_left (h.trans h2) h63.le
    _ = Nat.card ↑(onLineCopiesᶜ : Set XiZeroCopy) := by
        field_simp

#print axioms IsCriticalLadder.sum_criticalAliasCoefficient_le
#print axioms IsCriticalLadder.succ_mul_div_le_ratio
#print axioms IsCriticalLadder.sqrt_sixtyThree_mul_sum_le

end GaloisForLFunctions.ExclusionOfTheCriticalState
