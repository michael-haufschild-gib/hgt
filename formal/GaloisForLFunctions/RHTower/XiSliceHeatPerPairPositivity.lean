import GaloisForLFunctions.RHTower.XiSliceHeatTransferNoSlack
import GaloisForLFunctions.RHTower.XiSliceCoeffNearDoublePositivity
import GaloisForLFunctions.RHTower.XiSliceFiniteOrderReduction
import GaloisForLFunctions.RHTower.XiResolventMassBudget
import GaloisForLFunctions.HTGeometry.PolynomialHeatFactorBounds

/-!
# Per-pair heat positivity of the slice

Write `S_0(t, x) = Ξ(t − ix) Ξ(t + ix) = Ξ(t)² ∏_z (1 + x²/(z − t)²)` (`Ξ(t) ≠ 0`).  A critical
zero gives the factor `1 + x²/d²`.  An off-line pair `z, z̄` with `z − t = d + ie` gives the even
quartic `1 + 2(d² − e²)/|z−t|⁴ · x² + x⁴/|z−t|⁴`.  Under the heat `e^{s∂_x²}` this quartic becomes
coefficient-positive iff `e² ≤ d² + 6s`.  The heat-positive cone is closed under products
(`HTGeometry.coeffNonneg_forwardPolyHeat_mul`).  So every symmetric truncation of the product is
coefficient-positive after the heat `s = λ/2` once every zero satisfies

  `(Im z)² ≤ (Re z − t)² + 3λ`   (**heated cone**).

**Theorem** (`xiSliceHeatTransfer_nonneg_of_heatedCone`).  Under the heated cone condition at a
height `t` with `Ξ(t) ≠ 0`, the heated slice coefficients are nonnegative:
`T_n(λ, 0, t) = Σ_k (λ/2)^k/k! · (n+2k)!/n! · c_{n+2k}(t) ≥ 0` for every `n`.

**Shifted form** (`xiSliceHeatTransfer_nonneg_of_heatedHyperbola`).  The heat commutes with Taylor
shifts, and the shifted heated pair factor is coefficient-positive at `r ≥ 0` iff
`(Im z)² ≤ (Re z − t)² + r² + 6s`.  So under the **heated hyperbola** condition
`(Im z)² ≤ (Re z − t)² + r² + 3λ` the heated slice is absolutely monotone from `r`:
`T_n(λ, r, t) ≥ 0`.  The limit uses the re-centring `T_n(λ, r, t) = Σ_j C(n+j, n) r^j T_{n+j}(λ, 0, t)`
(`hasSum_xiSliceHeatTransfer_center`).  At `λ = 0` this is the hyperbola criterion; heat `λ` is worth
`3λ` of abscissa².

The truncated coefficients converge, and a uniform factorial bound `|[y^m] R_S| ≤ C ρ^m/m!`
with `8sρ < 1` dominates the heated series (`HTGeometry.heatWeight_mul_pow_div_factorial_le`).
Finitely many zero copies near `t` are absorbed into the constant `C`.  The remaining copies
have small total atom mass `Σ 1/|z − t|²`, which makes the rate `ρ` small.

**Corollaries.**
* If every zero satisfies `(Im z)² ≤ 3λ`, then `λ` is WD-admissible
  (`mem_wdHeatAdmissible_of_im_sq_le`).  The heat flow of `Ξ` only gives the factor `2λ`.
* `λ_WD ≤ 1/12` (`wdHeatThreshold_le_twelfth`), since `(Im z)² < 1/4` for every zero.  The
  de Bruijn transfer gives `1/8`.
* Trade-off curve `x₀² + 3λ = ¼` (`xiSliceHeatTransfer_nonneg_perPair`): for every `λ ≥ 0` the heated
  slice is absolutely monotone from `√max(¼ − 3λ, 0)` at every height.  The de Bruijn transfer gives
  the curve `x₀² + 2λ = ¼`.

At `λ = 0` the heated cone is the visibility cone `|Im z| ≤ |Re z − t|`, so the criterion
degenerates to the cone criterion and carries no information about zeros near height `t`.
-/

open Complex Filter Topology Metric Polynomial MeasureTheory
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-! ## Coefficient convergence along the symmetric truncations -/

theorem tendsto_sliceTruncPoly_coeff {t : ℝ} (ht : XiC t ≠ 0) (j : ℕ) :
    Tendsto (fun S => (((sliceTruncPoly t S).coeff j : ℝ) : ℂ)) atTop
      (𝓝 (xiSliceCoeff t (2 * j) / xiHorizontalPair t 0)) := by
  have hconv := tendstoLocallyUniformlyOn_prod_sliceFactorTerm ht 1
  have hd : ∀ᶠ S in atTop, DifferentiableOn ℂ
      (fun σ => ∏ q ∈ S, (1 + sliceFactorTerm t q σ)) (ball 0 1) :=
    Eventually.of_forall fun S =>
      (Differentiable.fun_finsetProd fun q _ => by unfold sliceFactorTerm; fun_prop).differentiableOn
  have hD2 := ((GaloisForLFunctions.tendstoLocallyUniformlyOn_iteratedDeriv isOpen_ball hconv hd
    (2 * j)).1.tendsto_at (mem_ball_self one_pos)).comp tendsto_sliceTrunc
  have hlimval : (((2 * j).factorial : ℂ))⁻¹ *
      iteratedDeriv (2 * j) (fun σ => xiHorizontalPair t σ / xiHorizontalPair t 0) 0 =
        (-1) ^ j * (xiSliceCoeff t (2 * j) / xiHorizontalPair t 0) := by
    have e : (fun σ => xiHorizontalPair t σ / xiHorizontalPair t 0) =
        fun σ => (xiHorizontalPair t 0)⁻¹ * xiHorizontalPair t σ :=
      funext fun σ => by rw [div_eq_inv_mul]
    rw [e, iteratedDeriv_const_mul_field, mul_left_comm,
      factorial_inv_mul_iteratedDeriv_xiHorizontalPair, pow_mul, I_sq]
    ring
  have h3 := (hD2.const_mul ((((2 * j).factorial : ℂ))⁻¹)).const_mul ((-1 : ℂ) ^ j)
  rw [hlimval, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul] at h3
  refine h3.congr fun S => ?_
  simp only [Function.comp_apply]
  have e : (fun σ => ∏ q ∈ sliceTrunc S, (1 + sliceFactorTerm t q σ)) =
      fun σ => ((sliceTruncPoly t S).map (algebraMap ℝ ℂ)).eval (-σ ^ 2) :=
    funext (prod_sliceTrunc_eq_eval ht S)
  rw [e, factorial_inv_mul_iteratedDeriv_eval_neg_sq, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_mul]

/-! ## Heated factors -/

/-- The upper factor `(1 + a y)² − 4β y = 1 + (2a − 4β) y + a² y²`. -/
theorem slicePairFactor_eq (a β : ℝ) :
    ((1 + C a * X) ^ 2 - C (4 * β) * X : ℝ[X]) = 1 + C (2 * a - 4 * β) * X + C (a ^ 2) * X ^ 2 := by
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  ring

theorem sliceLinFactor_eq (a : ℝ) : (1 + C a * X : ℝ[X]) = 1 + C a * X + C 0 * X ^ 2 := by
  simp

/-- A critical factor `1 + a x²` with `a ≥ 0` is coefficient-positive under every forward heat. -/
theorem coeffNonneg_forwardPolyHeat_sliceLin {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) :
    CoeffNonneg (forwardPolyHeat s (expand ℝ 2 (1 + C a * X))) := by
  rw [sliceLinFactor_eq]
  exact coeffNonneg_forwardPolyHeat_expand_quadratic le_rfl (by linarith) (by positivity)

/-- **The per-pair heat law.**  The pair factor of an off-line zero `z` is coefficient-positive
under the heat `s ≥ 0` when `(Im z)² ≤ (Re z − t)² + 6s`. -/
theorem coeffNonneg_forwardPolyHeat_slicePair {t s : ℝ} (hs : 0 ≤ s) {q : XiZeroCopy}
    (hq : xiSpectralPoint q ≠ t)
    (hcone : (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + 6 * s) :
    CoeffNonneg (forwardPolyHeat s
      (expand ℝ 2 ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X))) := by
  have hc : xiSpectralPoint q - t ≠ 0 := sub_ne_zero.mpr hq
  have hn : 0 < ‖xiSpectralPoint q - t‖ := norm_pos_iff.mpr hc
  have hN : ‖xiSpectralPoint q - t‖ ^ 2 =
      ((xiSpectralPoint q).re - t) ^ 2 + (xiSpectralPoint q).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have ha : sliceAtom t q = 1 / ‖xiSpectralPoint q - t‖ ^ 2 := rfl
  have hβ : sliceDefect t q = (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 := rfl
  have ha0 : 0 ≤ sliceAtom t q := by rw [ha]; positivity
  have hβa : sliceDefect t q ≤ sliceAtom t q := by
    rw [ha, hβ, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (xiSpectralPoint q).im ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 := by
      rw [hN]; nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]
    nlinarith [sq_nonneg ‖xiSpectralPoint q - t‖]
  rw [slicePairFactor_eq]
  refine coeffNonneg_forwardPolyHeat_expand_quadratic (by positivity) ?_ ?_
  · have e : 2 * sliceAtom t q - 4 * sliceDefect t q + 12 * s * sliceAtom t q ^ 2 =
        2 * (‖xiSpectralPoint q - t‖ ^ 2 - 2 * (xiSpectralPoint q).im ^ 2 + 6 * s) /
          ‖xiSpectralPoint q - t‖ ^ 4 := by
      rw [ha, hβ]; field_simp; ring
    rw [e]
    refine div_nonneg ?_ (by positivity)
    rw [hN]
    linarith
  · nlinarith [mul_le_mul_of_nonneg_left hβa hs, sq_nonneg (1 - 2 * s * sliceAtom t q),
      sq_nonneg (s * sliceAtom t q)]

/-- **Heated truncations.**  Under the heated cone condition every symmetric truncation
`R_S(x²)` is coefficient-positive after the heat `s`. -/
theorem coeffNonneg_forwardPolyHeat_sliceTruncPoly {t s : ℝ} (ht : XiC t ≠ 0) (hs : 0 ≤ s)
    (hcone : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + 6 * s)
    (S : Finset XiZeroCopy) :
    CoeffNonneg (forwardPolyHeat s (expand ℝ 2 (sliceTruncPoly t S))) := by
  unfold sliceTruncPoly
  rw [map_mul, map_prod, map_prod]
  refine coeffNonneg_forwardPolyHeat_mul hs
    (coeffNonneg_forwardPolyHeat_prod hs _ fun q _ => ?_)
    (coeffNonneg_forwardPolyHeat_prod hs _ fun q _ => ?_)
  · exact coeffNonneg_forwardPolyHeat_sliceLin hs (by unfold sliceAtom; positivity)
  · exact coeffNonneg_forwardPolyHeat_slicePair hs (xiSpectralPoint_ne_ofReal ht q) (hcone q)

/-! ## A uniform factorial bound on the truncations -/

/-- The per-copy constant `K_q(ρ) = 1 + 2a/ρ + 2a²/ρ²`, `a = 1/|z − t|²`. -/
def sliceAtomConst (t ρ : ℝ) (q : XiZeroCopy) : ℝ :=
  1 + 2 * sliceAtom t q / ρ + 2 * sliceAtom t q ^ 2 / ρ ^ 2

theorem one_le_sliceAtomConst {t ρ : ℝ} (hρ : 0 < ρ) (q : XiZeroCopy) :
    1 ≤ sliceAtomConst t ρ q := by
  have : 0 ≤ sliceAtom t q := by unfold sliceAtom; positivity
  unfold sliceAtomConst
  have h1 : 0 ≤ 2 * sliceAtom t q / ρ := by positivity
  have h2 : 0 ≤ 2 * sliceAtom t q ^ 2 / ρ ^ 2 := by positivity
  linarith

/-- A slice factor `1 + b y + c y²` with `|b| ≤ 2a`, `|c| ≤ a²` has the bounds `(1, 2a)` and
`(K_q(ρ), ρ)`. -/
theorem factorialCoeffBound_sliceFactor {t : ℝ} (q : XiZeroCopy) {b c : ℝ}
    (hb : |b| ≤ 2 * sliceAtom t q) (hc : |c| ≤ sliceAtom t q ^ 2) {ρ : ℝ} (hρ : 0 < ρ) :
    FactorialCoeffBound 1 (2 * sliceAtom t q) (1 + C b * X + C c * X ^ 2) ∧
      FactorialCoeffBound (sliceAtomConst t ρ q) ρ (1 + C b * X + C c * X ^ 2) := by
  have ha : 0 ≤ sliceAtom t q := by unfold sliceAtom; positivity
  refine ⟨factorialCoeffBound_quadratic le_rfl (by positivity) (by linarith) (by nlinarith),
    factorialCoeffBound_quadratic (one_le_sliceAtomConst hρ q) hρ.le ?_ ?_⟩
  · unfold sliceAtomConst
    have e : (1 + 2 * sliceAtom t q / ρ + 2 * sliceAtom t q ^ 2 / ρ ^ 2) * ρ =
        ρ + 2 * sliceAtom t q + 2 * sliceAtom t q ^ 2 / ρ := by field_simp
    rw [e]
    have : 0 ≤ 2 * sliceAtom t q ^ 2 / ρ := by positivity
    linarith
  · unfold sliceAtomConst
    have e : (1 + 2 * sliceAtom t q / ρ + 2 * sliceAtom t q ^ 2 / ρ ^ 2) * ρ ^ 2 / 2 =
        ρ ^ 2 / 2 + sliceAtom t q * ρ + sliceAtom t q ^ 2 := by field_simp
    rw [e]
    have : 0 ≤ sliceAtom t q * ρ := by positivity
    nlinarith

theorem sliceDefect_le_sliceAtom {t : ℝ} (ht : XiC t ≠ 0) (q : XiZeroCopy) :
    sliceDefect t q ≤ sliceAtom t q := by
  have hn : 0 < ‖xiSpectralPoint q - t‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q))
  have him : |(xiSpectralPoint q).im| ≤ ‖xiSpectralPoint q - t‖ := by
    have := Complex.abs_im_le_norm (xiSpectralPoint q - t)
    simpa using this
  have h2 : (xiSpectralPoint q).im ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
  unfold sliceDefect sliceAtom
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ‖xiSpectralPoint q - t‖]

/-- **Uniform factorial bound.**  If the copies outside `K` have atom mass `< η` on every finite
set, then every truncation `R_S` has the bound `(∏_{q ∈ K} K_q(ρ₀), |K| ρ₀ + 2η)`. -/
theorem factorialCoeffBound_sliceTruncPoly {t : ℝ} (ht : XiC t ≠ 0) {ρ₀ η : ℝ} (hρ₀ : 0 < ρ₀)
    (K : Finset XiZeroCopy)
    (hK : ∀ F : Finset XiZeroCopy, Disjoint F K → ∑ q ∈ F, sliceAtom t q < η)
    (S : Finset XiZeroCopy) :
    FactorialCoeffBound (∏ q ∈ K, sliceAtomConst t ρ₀ q) (K.card * ρ₀ + 2 * η)
      (sliceTruncPoly t S) := by
  classical
  have ha0 : ∀ q, 0 ≤ sliceAtom t q := fun q => by unfold sliceAtom; positivity
  set c : XiZeroCopy → ℝ := fun q => if q ∈ K then sliceAtomConst t ρ₀ q else 1 with hc
  set r : XiZeroCopy → ℝ := fun q => if q ∈ K then ρ₀ else 2 * sliceAtom t q with hr
  have hfac : ∀ q {b c' : ℝ}, |b| ≤ 2 * sliceAtom t q → |c'| ≤ sliceAtom t q ^ 2 →
      FactorialCoeffBound (c q) (r q) (1 + C b * X + C c' * X ^ 2) := by
    intro q b c' hb hc'
    obtain ⟨h1, h2⟩ := factorialCoeffBound_sliceFactor q hb hc' hρ₀
    by_cases hq : q ∈ K
    · simpa [hc, hr, hq] using h2
    · simpa [hc, hr, hq] using h1
  have hlin : FactorialCoeffBound (∏ q ∈ sliceTruncCrit S, c q) (∑ q ∈ sliceTruncCrit S, r q)
      (∏ q ∈ sliceTruncCrit S, (1 + C (sliceAtom t q) * X)) := by
    refine FactorialCoeffBound.prod _ fun q _ => ?_
    rw [sliceLinFactor_eq]
    exact hfac q (by rw [abs_of_nonneg (ha0 q)]; linarith [ha0 q]) (by simp; positivity)
  have hpair : FactorialCoeffBound (∏ q ∈ sliceTruncUp S, c q) (∑ q ∈ sliceTruncUp S, r q)
      (∏ q ∈ sliceTruncUp S,
        ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X)) := by
    refine FactorialCoeffBound.prod _ fun q _ => ?_
    rw [slicePairFactor_eq]
    have hd0 : 0 ≤ sliceDefect t q := by unfold sliceDefect; positivity
    have hda := sliceDefect_le_sliceAtom ht q
    refine hfac q ?_ (by rw [abs_of_nonneg (by positivity)])
    rw [abs_le]
    constructor <;> linarith
  have hdisj : Disjoint (sliceTruncCrit S) (sliceTruncUp S) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have := (mem_sliceTruncCrit.mp h1).2
    have := (mem_sliceTruncUp.mp h2).2
    unfold XiCopyCritical at *; unfold XiCopyUpper at *
    linarith
  set U := sliceTruncCrit S ∪ sliceTruncUp S with hU
  have hprod := hlin.mul hpair
  rw [← Finset.prod_union hdisj, ← Finset.sum_union hdisj, ← hU] at hprod
  unfold sliceTruncPoly
  refine hprod.mono ?_ (Finset.sum_nonneg fun q _ => ?_) ?_
  · -- the constant
    have e : ∏ q ∈ U, c q = ∏ q ∈ U with q ∈ K, sliceAtomConst t ρ₀ q := by
      rw [hc, Finset.prod_ite, Finset.prod_const_one, mul_one]
    rw [e]
    have hsub : (U.filter fun q => q ∈ K) ⊆ K := fun q hq => (Finset.mem_filter.mp hq).2
    rw [← Finset.prod_sdiff hsub]
    refine le_mul_of_one_le_left (Finset.prod_nonneg fun q _ =>
      (zero_le_one.trans (one_le_sliceAtomConst hρ₀ q))) ?_
    exact Finset.one_le_prod fun q _ => one_le_sliceAtomConst hρ₀ q
  · simp only [hr]
    split_ifs
    · exact hρ₀.le
    · exact mul_nonneg zero_le_two (ha0 q)
  · -- the rate
    have e : ∑ q ∈ U, r q = ∑ q ∈ U with q ∈ K, ρ₀ + ∑ q ∈ U with q ∉ K, 2 * sliceAtom t q := by
      rw [hr, Finset.sum_ite]
    rw [e, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    have hcard : ((U.filter fun q => q ∈ K).card : ℝ) ≤ K.card := by
      exact_mod_cast Finset.card_le_card fun q hq => (Finset.mem_filter.mp hq).2
    have htail : ∑ q ∈ U with q ∉ K, sliceAtom t q < η := hK _ (by
      rw [Finset.disjoint_left]
      intro q hq hqK
      exact (Finset.mem_filter.mp hq).2 hqK)
    nlinarith

/-! ## Convergence of the heated truncations -/

theorem xiHorizontalPair_zero_ne {t : ℝ} (ht : XiC t ≠ 0) : xiHorizontalPair t 0 ≠ 0 := by
  have hreal : (XiC (t : ℂ)).im = 0 := by
    have h := XiC_conj (t : ℂ)
    rw [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hre0 : (XiC (t : ℂ)).re ≠ 0 := by
    intro h0
    exact ht (Complex.ext (by simp [h0]) (by simp [hreal]))
  rw [xiHorizontalPair_zero_eq_ofReal, Ne, Complex.ofReal_eq_zero]
  exact pow_ne_zero 2 hre0

/-- **A uniform factorial bound** on all symmetric truncations, with a rate `ρ` such that
`8sρ ≤ 1/2`.  The finitely many copies with large atoms go into the constant. -/
theorem exists_sliceTruncPoly_factorialCoeffBound {t s : ℝ} (ht : XiC t ≠ 0) (hs : 0 ≤ s) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ 8 * s * ρ ≤ 1 / 2 ∧
      ∀ S : Finset XiZeroCopy, FactorialCoeffBound C ρ (sliceTruncPoly t S) := by
  set ρ : ℝ := 1 / (16 * s + 1) with hρ
  have hρpos : 0 < ρ := by positivity
  have h8 : 8 * s * ρ ≤ 1 / 2 := by
    rw [hρ, mul_one_div, div_le_iff₀ (by positivity)]; linarith
  obtain ⟨K, hK⟩ := (summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)).vanishing
    (Iio_mem_nhds (show (0 : ℝ) < ρ / 4 by positivity))
  have hK' : ∀ F : Finset XiZeroCopy, Disjoint F K → ∑ q ∈ F, sliceAtom t q < ρ / 4 :=
    fun F hF => hK F hF
  set ρ₀ : ℝ := ρ / (2 * (K.card + 1)) with hρ₀
  have hρ₀pos : 0 < ρ₀ := by positivity
  have hrate : (K.card : ℝ) * ρ₀ + 2 * (ρ / 4) ≤ ρ := by
    have : (K.card : ℝ) * ρ₀ ≤ ρ / 2 := by
      rw [hρ₀, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  exact ⟨∏ q ∈ K, sliceAtomConst t ρ₀ q, ρ, Finset.prod_nonneg fun q _ =>
    zero_le_one.trans (one_le_sliceAtomConst hρ₀pos q), hρpos, h8, fun S =>
    (factorialCoeffBound_sliceTruncPoly ht hρ₀pos K hK' S).mono le_rfl (by positivity) hrate⟩

/-- The odd heated slice coefficients vanish. -/
theorem xiSliceHeatTransfer_odd_eq_zero {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (l : ℕ) :
    xiSliceHeatTransfer lam 0 t (2 * l + 1) = 0 := by
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam 0 t (2 * l + 1)
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  have h0 : (fun k : ℕ => (((lam / 2) ^ k / k.factorial *
      ((2 * l + 1 + 2 * k).factorial / (2 * l + 1).factorial) : ℝ) : ℂ) *
        xiSliceCoeff t (2 * l + 1 + 2 * k)) = fun _ => 0 := by
    funext k
    rw [show 2 * l + 1 + 2 * k = 2 * (l + k) + 1 by ring, xiSliceCoeff_odd_eq_zero, mul_zero]
  rw [h0] at hT
  exact hT.unique hasSum_zero

/-- **The heated truncations converge.**
`[x^{2l}] e^{(λ/2)D²} R_S(x²) → T_{2l}(λ, 0, t)/Ξ(t)²` along the symmetric truncations. -/
theorem tendsto_coeff_forwardPolyHeat_sliceTruncPoly {lam t : ℝ} (hlam : 0 ≤ lam)
    (ht : XiC t ≠ 0) (l : ℕ) :
    Tendsto (fun S => (((forwardPolyHeat (lam / 2)
        (expand ℝ 2 (sliceTruncPoly t S))).coeff (2 * l) : ℝ) : ℂ)) atTop
      (𝓝 (xiSliceHeatTransfer lam 0 t (2 * l) / xiHorizontalPair t 0)) := by
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam 0 t (2 * l)
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  set s := lam / 2 with hs_def
  have hs : 0 ≤ s := by positivity
  set w : ℕ → ℝ := fun k =>
    s ^ k / k.factorial * ((2 * l + 2 * k).factorial / (2 * l).factorial) with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by positivity
  obtain ⟨CB, ρ, hCB0, hρpos, h8, hB⟩ := exists_sliceTruncPoly_factorialCoeffBound ht hs
  set f : Finset XiZeroCopy → ℕ → ℂ := fun S k =>
    ((w k * (sliceTruncPoly t S).coeff (l + k) : ℝ) : ℂ) with hf
  set g : ℕ → ℂ := fun k =>
    (w k : ℂ) * xiSliceCoeff t (2 * l + 2 * k) / xiHorizontalPair t 0 with hg
  set G : ℝ := l.factorial * (8 * ρ) ^ l / (2 * l).factorial with hG
  have hG0 : 0 ≤ G := by positivity
  have hbound : ∀ S k, ‖f S k‖ ≤ CB * G * (1 / 2) ^ k := by
    intro S k
    simp only [hf, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 k)]
    calc w k * |(sliceTruncPoly t S).coeff (l + k)|
        ≤ w k * (CB * ρ ^ (l + k) / (l + k).factorial) :=
          mul_le_mul_of_nonneg_left (hB S (l + k)) (hw0 k)
      _ = CB * (w k * (ρ ^ (l + k) / (l + k).factorial)) := by ring
      _ ≤ CB * (G * (8 * s * ρ) ^ k) :=
          mul_le_mul_of_nonneg_left (heatWeight_mul_pow_div_factorial_le hs hρpos.le l k) hCB0
      _ ≤ CB * G * (1 / 2) ^ k := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h8 k)
            (mul_nonneg hCB0 hG0)
  have hsumb : Summable fun k : ℕ => CB * G * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hpt : ∀ k, Tendsto (fun S => f S k) atTop (𝓝 (g k)) := by
    intro k
    have h := (tendsto_sliceTruncPoly_coeff ht (l + k)).const_mul (w k : ℂ)
    rw [show 2 * (l + k) = 2 * l + 2 * k by ring] at h
    have e : g k = (w k : ℂ) * (xiSliceCoeff t (2 * l + 2 * k) / xiHorizontalPair t 0) := by
      simp only [hg]; ring
    rw [e]
    refine h.congr fun S => ?_
    simp only [hf]
    push_cast
    ring
  have hlim := tendsto_tsum_of_dominated_convergence hsumb hpt
    (Eventually.of_forall fun S k => hbound S k)
  have hfS : ∀ S, ∑' k, f S k =
      (((forwardPolyHeat s (expand ℝ 2 (sliceTruncPoly t S))).coeff (2 * l) : ℝ) : ℂ) := by
    intro S
    set N := (sliceTruncPoly t S).natDegree + 1 with hN
    rw [tsum_eq_sum (s := Finset.range N) fun k hk => by
      simp only [hf]
      rw [Finset.mem_range, not_lt] at hk
      rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, Complex.ofReal_zero],
      coeff_forwardPolyHeat_expand_two s (sliceTruncPoly t S) l (N := N) (by omega),
      Complex.ofReal_sum]
  have hgsum : ∑' k, g k = xiSliceHeatTransfer lam 0 t (2 * l) / xiHorizontalPair t 0 := by
    rw [← hT.tsum_eq]
    simp only [hg]
    rw [tsum_div_const]
  rw [hgsum] at hlim
  exact hlim.congr hfS

/-- **The heated cone criterion.**  Let `Ξ(t) ≠ 0` and `λ ≥ 0`.  If every zero `z` of `Ξ` satisfies
`(Im z)² ≤ (Re z − t)² + 3λ`, then `T_n(λ, 0, t) ≥ 0` for every `n`. -/
theorem xiSliceHeatTransfer_nonneg_of_heatedCone {lam t : ℝ} (hlam : 0 ≤ lam) (ht : XiC t ≠ 0)
    (hcone : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + 3 * lam) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam 0 t n := by
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hs : 0 ≤ lam / 2 := by positivity
    have hcone' : ∀ q : XiZeroCopy,
        (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + 6 * (lam / 2) :=
      fun q => by have := hcone q; linarith
    have hq : 0 ≤ xiSliceHeatTransfer lam 0 t (2 * l) / xiHorizontalPair t 0 :=
      ge_of_tendsto (tendsto_coeff_forwardPolyHeat_sliceTruncPoly hlam ht l)
        (Eventually.of_forall fun S => Complex.zero_le_real.mpr
          (coeffNonneg_forwardPolyHeat_sliceTruncPoly ht hs hcone' S (2 * l)))
    rw [← mul_div_cancel₀ (xiSliceHeatTransfer lam 0 t (2 * l)) (xiHorizontalPair_zero_ne ht)]
    refine mul_nonneg ?_ hq
    rw [xiHorizontalPair_zero_eq_ofReal]
    exact Complex.zero_le_real.mpr (sq_nonneg _)
  · rw [xiSliceHeatTransfer_odd_eq_zero hlam]

/-! ## The heated hyperbola criterion -/

/-- **Re-centring the transfer.**
`T_n(λ, r, t) = Σ_j C(n+j, n) r^j T_{n+j}(λ, 0, t)`. -/
theorem hasSum_xiSliceHeatTransfer_center {lam : ℝ} (hlam : 0 ≤ lam) (r t : ℝ) (n : ℕ) :
    HasSum (fun j : ℕ => ((((n + j).choose n : ℝ) * r ^ j : ℝ) : ℂ) *
      xiSliceHeatTransfer lam 0 t (n + j)) (xiSliceHeatTransfer lam r t n) := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set F : ℕ → ℝ × ℝ → ℂ := fun j p =>
    ((Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
      ((r * (p.1 - p.2)) ^ j / j.factorial) * ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) *
      cexp (I * t * (p.1 + p.2)) with hF
  set D : ℝ × ℝ → ℝ := fun p =>
    Φ p.1 * Real.exp (lam * p.1 ^ 2) * Real.exp ((|r| + 1) * |p.1|) *
      (Φ p.2 * Real.exp (lam * p.2 ^ 2) * Real.exp ((|r| + 1) * |p.2|)) with hD
  have hDi : Integrable D :=
    integrable_prod_majorant (riemannKernel_superExp.mul_exp_sq hlam) (|r| + 1)
  have hnormF : ∀ j p, ‖F j p‖ = Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
      (|r * (p.1 - p.2)| ^ j / j.factorial) * (|p.1 - p.2| ^ n / n.factorial) := by
    intro j p
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add,
      mul_one, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (hΦ0 _),
      abs_of_pos (Real.exp_pos _)]
  have hexpsq : ∀ p : ℝ × ℝ, Real.exp (lam * (p.1 - p.2) ^ 2 / 2) ≤
      Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2) := by
    intro p
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p.1 + p.2)])
  have hbound : ∀ N : ℕ, ∀ p : ℝ × ℝ, ∑ j ∈ Finset.range N, ‖F j p‖ ≤ D p := by
    intro N p
    simp only [hnormF]
    have hq : 0 ≤ |r * (p.1 - p.2)| := abs_nonneg _
    have e : ∑ j ∈ Finset.range N, Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
        (|r * (p.1 - p.2)| ^ j / j.factorial) * (|p.1 - p.2| ^ n / n.factorial) =
        Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * (|p.1 - p.2| ^ n / n.factorial) *
          ∑ j ∈ Finset.range N, |r * (p.1 - p.2)| ^ j / j.factorial := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    have h1 := Real.sum_le_exp_of_nonneg hq N
    have h2 := Real.pow_div_factorial_le_exp _ (abs_nonneg (p.1 - p.2)) n
    have h3 : Real.exp |p.1 - p.2| * Real.exp |r * (p.1 - p.2)| ≤
        Real.exp ((|r| + 1) * |p.1|) * Real.exp ((|r| + 1) * |p.2|) := by
      rw [← Real.exp_add, abs_mul,
        show |p.1 - p.2| + |r| * |p.1 - p.2| = (|r| + 1) * |p.1 - p.2| by ring]
      exact exp_mul_abs_sub_le (by positivity) p.1 p.2
    have hΦΦ : 0 ≤ Φ p.1 * Φ p.2 := mul_nonneg (hΦ0 _) (hΦ0 _)
    calc Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * (|p.1 - p.2| ^ n / n.factorial) *
          ∑ j ∈ Finset.range N, |r * (p.1 - p.2)| ^ j / j.factorial
        ≤ Φ p.1 * Φ p.2 * (Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2)) *
            (Real.exp |p.1 - p.2| * Real.exp |r * (p.1 - p.2)|) := by
          rw [mul_assoc (Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2))]
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hexpsq p) hΦΦ)
            (mul_le_mul h2 h1 (Finset.sum_nonneg fun j _ => by positivity) (by positivity))
            (by positivity) (by positivity)
      _ ≤ Φ p.1 * Φ p.2 * (Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2)) *
            (Real.exp ((|r| + 1) * |p.1|) * Real.exp ((|r| + 1) * |p.2|)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = D p := by simp only [hD]; ring
  have hmeas : ∀ j, AEStronglyMeasurable (F j) := by
    intro j
    refine Continuous.aestronglyMeasurable ?_
    have := continuous_riemannKernelReal
    simp only [hF, hΦ]
    fun_prop
  have hint : ∀ j, Integrable (F j) := by
    intro j
    refine hDi.mono' (hmeas j) (Eventually.of_forall fun p => ?_)
    have := hbound (j + 1) p
    rw [Finset.sum_range_succ] at this
    have hnn : 0 ≤ ∑ i ∈ Finset.range j, ‖F i p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hsum : Summable (fun j => ∫ p, ‖F j p‖) := by
    refine summable_of_sum_range_le (c := ∫ p, D p)
      (fun j => integral_nonneg fun p => norm_nonneg _) fun N => ?_
    rw [← integral_finsetSum _ (fun j _ => (hint j).norm)]
    exact integral_mono (integrable_finsetSum _ fun j _ => (hint j).norm) hDi (hbound N)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ p : ℝ × ℝ, ∑' j, F j p =
      ((Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * Real.exp (r * (p.1 - p.2)) *
        ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2)) := by
    intro p
    have hexp := NormedSpace.expSeries_div_hasSum_exp (r * (p.1 - p.2))
    rw [← Real.exp_eq_exp_ℝ] at hexp
    have hR := (hexp.mul_left (Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2))).mul_right
      ((p.1 - p.2) ^ n / n.factorial)
    have hC := (Complex.hasSum_ofReal.mpr hR).mul_right (cexp (I * t * (p.1 + p.2)))
    refine (hC.congr_fun fun j => ?_).tsum_eq.trans ?_
    all_goals simp only [hF]
  simp_rw [htsum] at h
  refine h.congr_fun fun j => ?_
  simp only [hF, xiSliceHeatTransfer]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have hn : ((n.factorial : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hj : ((j.factorial : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hnj : (((n + j).factorial : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hch : ((n + j).choose n : ℝ) * n.factorial * j.factorial = (n + j).factorial := by
    have := Nat.add_choose_mul_factorial_mul_factorial n j
    rw [← Nat.choose_symm_add] at this
    exact_mod_cast this
  have hc0 : ((n + j).choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hreal : Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
      ((r * (p.1 - p.2)) ^ j / j.factorial) * ((p.1 - p.2) ^ n / n.factorial) =
      ((n + j).choose n : ℝ) * r ^ j *
        (Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * Real.exp (0 * (p.1 - p.2)) *
          ((p.1 - p.2) ^ (n + j) / (n + j).factorial)) := by
    rw [zero_mul, Real.exp_zero, mul_one, mul_pow, ← hch]
    field_simp
    ring
  beta_reduce
  rw [hreal]
  push_cast
  ring

/-- **Positivity of a shifted heated critical factor.** -/
theorem coeffNonneg_taylor_forwardPolyHeat_sliceLin {s a r : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hr : 0 ≤ r) : CoeffNonneg (taylor r (forwardPolyHeat s (expand ℝ 2 (1 + C a * X)))) := by
  rw [sliceLinFactor_eq]
  exact coeffNonneg_taylor_forwardPolyHeat_expand_quadratic hr le_rfl (by simpa using ha)
    (by simp only [mul_zero, add_zero, zero_mul]; positivity)

/-- **The shifted per-pair heat law.**  For `r ≥ 0`, the pair factor of an off-line zero `z` has
nonnegative Taylor coefficients at `r` after the heat `s ≥ 0` when
`(Im z)² ≤ (Re z − t)² + r² + 6s`. -/
theorem coeffNonneg_taylor_forwardPolyHeat_slicePair {t s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    {q : XiZeroCopy} (hq : xiSpectralPoint q ≠ t)
    (hcone : (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + r ^ 2 + 6 * s) :
    CoeffNonneg (taylor r (forwardPolyHeat s
      (expand ℝ 2 ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X)))) := by
  have hc : xiSpectralPoint q - t ≠ 0 := sub_ne_zero.mpr hq
  have hn : 0 < ‖xiSpectralPoint q - t‖ := norm_pos_iff.mpr hc
  have hN : ‖xiSpectralPoint q - t‖ ^ 2 =
      ((xiSpectralPoint q).re - t) ^ 2 + (xiSpectralPoint q).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have ha : sliceAtom t q = 1 / ‖xiSpectralPoint q - t‖ ^ 2 := rfl
  have hβ : sliceDefect t q = (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 := rfl
  have ha0 : 0 < sliceAtom t q := by rw [ha]; positivity
  have hβ0 : 0 ≤ sliceDefect t q := by rw [hβ]; positivity
  have hβa : sliceDefect t q ≤ sliceAtom t q := by
    rw [ha, hβ, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (xiSpectralPoint q).im ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 := by
      rw [hN]; nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]
    nlinarith [sq_nonneg ‖xiSpectralPoint q - t‖]
  have hB : 0 ≤ 2 * sliceAtom t q - 4 * sliceDefect t q + 12 * s * sliceAtom t q ^ 2 +
      2 * sliceAtom t q ^ 2 * r ^ 2 := by
    have e : 2 * sliceAtom t q - 4 * sliceDefect t q + 12 * s * sliceAtom t q ^ 2 +
        2 * sliceAtom t q ^ 2 * r ^ 2 =
        2 * (‖xiSpectralPoint q - t‖ ^ 2 - 2 * (xiSpectralPoint q).im ^ 2 + 6 * s + r ^ 2) /
          ‖xiSpectralPoint q - t‖ ^ 4 := by
      rw [ha, hβ]; field_simp; ring
    rw [e]
    refine div_nonneg ?_ (by positivity)
    rw [hN]
    linarith
  rw [slicePairFactor_eq]
  refine coeffNonneg_taylor_forwardPolyHeat_expand_quadratic hr (by positivity) hB ?_
  generalize sliceAtom t q = a at ha0 hβa hB ⊢
  generalize sliceDefect t q = β at hβ0 hβa hB ⊢
  have hb1 : -(2 * a) ≤ 2 * a - 4 * β := by linarith
  have hα0 : 0 ≤ 1 + 2 * s * (2 * a - 4 * β) + 12 * s ^ 2 * a ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hb1 hs, sq_nonneg (1 - 2 * s * a), sq_nonneg (s * a)]
  by_cases hB0 : 0 ≤ 2 * a - 4 * β + 12 * s * a ^ 2
  · have : 0 ≤ (2 * a - 4 * β + 12 * s * a ^ 2) * r ^ 2 := mul_nonneg hB0 (sq_nonneg r)
    have : 0 ≤ a ^ 2 * r ^ 4 := by positivity
    linarith
  · push Not at hB0
    have hD : 0 ≤ 4 * (1 + 2 * s * (2 * a - 4 * β) + 12 * s ^ 2 * a ^ 2) * a ^ 2 -
        (2 * a - 4 * β + 12 * s * a ^ 2) ^ 2 := by
      have e : 4 * (1 + 2 * s * (2 * a - 4 * β) + 12 * s ^ 2 * a ^ 2) * a ^ 2 -
          (2 * a - 4 * β + 12 * s * a ^ 2) ^ 2 =
          4 * a ^ 2 - (2 * a - 4 * β) ^ 2 + 16 * s * a ^ 2 * (-(2 * a - 4 * β)) -
            96 * s ^ 2 * a ^ 4 := by ring
      rw [e]
      have h1 : 16 * s * a ^ 2 * (12 * s * a ^ 2) ≤ 16 * s * a ^ 2 * (-(2 * a - 4 * β)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith [sq_nonneg (s * a ^ 2)]
    have key : 4 * a ^ 2 * ((1 + 2 * s * (2 * a - 4 * β) + 12 * s ^ 2 * a ^ 2) +
        (2 * a - 4 * β + 12 * s * a ^ 2) * r ^ 2 + a ^ 2 * r ^ 4) =
        (2 * a ^ 2 * r ^ 2 + (2 * a - 4 * β + 12 * s * a ^ 2)) ^ 2 +
          (4 * (1 + 2 * s * (2 * a - 4 * β) + 12 * s ^ 2 * a ^ 2) * a ^ 2 -
            (2 * a - 4 * β + 12 * s * a ^ 2) ^ 2) := by ring
    have h4 : 0 < 4 * a ^ 2 := by positivity
    exact (mul_nonneg_iff_of_pos_left h4).mp (by rw [key]; positivity)

/-- **Shifted heated truncations.**  Under the heated hyperbola condition every symmetric
truncation `R_S(x²)` has nonnegative Taylor coefficients at `r ≥ 0` after the heat `s`. -/
theorem coeffNonneg_taylor_forwardPolyHeat_sliceTruncPoly {t s r : ℝ} (ht : XiC t ≠ 0)
    (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hcone : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + r ^ 2 + 6 * s)
    (S : Finset XiZeroCopy) :
    CoeffNonneg (taylor r (forwardPolyHeat s (expand ℝ 2 (sliceTruncPoly t S)))) := by
  unfold sliceTruncPoly
  rw [map_mul, map_prod, map_prod]
  refine coeffNonneg_taylor_forwardPolyHeat_mul hs r
    (coeffNonneg_taylor_forwardPolyHeat_prod hs r _ fun q _ => ?_)
    (coeffNonneg_taylor_forwardPolyHeat_prod hs r _ fun q _ => ?_)
  · exact coeffNonneg_taylor_forwardPolyHeat_sliceLin hs (by unfold sliceAtom; positivity) hr
  · exact coeffNonneg_taylor_forwardPolyHeat_slicePair hs hr (xiSpectralPoint_ne_ofReal ht q)
      (hcone q)

/-- **The heated hyperbola criterion.**  Let `Ξ(t) ≠ 0`, `λ ≥ 0` and `r ≥ 0`.  If every zero `z`
of `Ξ` satisfies `(Im z)² ≤ (Re z − t)² + r² + 3λ`, then `T_n(λ, r, t) ≥ 0` for every `n`: the
heated slice `e^{(λ/2)∂_x²} S_0(t, ·)` is absolutely monotone from `r`. -/
theorem xiSliceHeatTransfer_nonneg_of_heatedHyperbola {lam r t : ℝ} (hlam : 0 ≤ lam)
    (hr : 0 ≤ r) (ht : XiC t ≠ 0)
    (hcone : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + r ^ 2 + 3 * lam)
    (n : ℕ) : 0 ≤ xiSliceHeatTransfer lam r t n := by
  set s := lam / 2 with hs_def
  have hs : 0 ≤ s := by positivity
  have hcone' : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + r ^ 2 + 6 * s :=
    fun q => by have := hcone q; rw [hs_def]; linarith
  obtain ⟨CB, ρ, hCB0, hρpos, h8, hB⟩ := exists_sliceTruncPoly_factorialCoeffBound ht hs
  set A : ℕ → Finset XiZeroCopy → ℝ := fun m S =>
    (forwardPolyHeat s (expand ℝ 2 (sliceTruncPoly t S))).coeff m with hA
  set L : ℕ → ℂ := fun m => xiSliceHeatTransfer lam 0 t m / xiHorizontalPair t 0 with hL
  have hconv : ∀ m, Tendsto (fun S => (A m S : ℂ)) atTop (𝓝 (L m)) := by
    intro m
    obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' m
    · exact tendsto_coeff_forwardPolyHeat_sliceTruncPoly hlam ht l
    · simp only [hA, hL, coeff_forwardPolyHeat_expand_two_odd, Complex.ofReal_zero,
        xiSliceHeatTransfer_odd_eq_zero hlam, zero_div]
      exact tendsto_const_nhds
  set M : ℝ := max 1 r with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  set q₀ : ℝ := 32 * ρ * M ^ 2 with hq₀
  have hq₀0 : 0 ≤ q₀ := by positivity
  set E : ℝ := 2 * CB * Real.exp (4 * q₀) with hE
  have hjb : ∀ j S, |((n + j).choose n : ℝ) * r ^ j * A (n + j) S| ≤ E * (1 / 2) ^ j := by
    intro j S
    obtain ⟨l, hl | hl⟩ := Nat.even_or_odd' (n + j)
    · have hAl : |A (n + j) S| ≤ 2 * CB * (l.factorial * (8 * ρ) ^ l / (2 * l).factorial) := by
        simp only [hA]; rw [hl]; exact abs_coeff_forwardPolyHeat_expand_two_le hs hρpos h8 (hB S) l
      have hch : ((n + j).choose n : ℝ) ≤ 4 ^ l := by
        have h := Nat.choose_le_two_pow (n + j) n
        rw [hl, pow_mul] at h
        have h' : (2 * l).choose n ≤ 4 ^ l := by simpa using h
        rw [hl]; exact_mod_cast h'
      have hrj : |r| ^ j ≤ M ^ (2 * l) := by
        calc |r| ^ j ≤ M ^ j := pow_le_pow_left₀ (abs_nonneg r)
              (by rw [abs_of_nonneg hr]; exact le_max_right _ _) j
          _ ≤ M ^ (2 * l) := pow_le_pow_right₀ hM1 (by omega)
      have hfac : (l.factorial : ℝ) / (2 * l).factorial ≤ 1 / l.factorial := by
        have h := Nat.choose_mul_factorial_mul_factorial (show l ≤ 2 * l by omega)
        rw [show 2 * l - l = l by omega] at h
        have h' : (l.factorial : ℝ) * l.factorial ≤ (2 * l).factorial := by
          rw [← h]; push_cast
          have : (1 : ℝ) ≤ (2 * l).choose l := by exact_mod_cast Nat.choose_pos (by omega)
          nlinarith [(by positivity : (0 : ℝ) ≤ l.factorial * l.factorial)]
        have hl0 : (0 : ℝ) < l.factorial := by exact_mod_cast Nat.factorial_pos l
        rw [div_le_div_iff₀ (by exact_mod_cast Nat.factorial_pos _) hl0]
        linarith
      have hexp : q₀ ^ l / l.factorial ≤ Real.exp (4 * q₀) * (1 / 4) ^ l := by
        have := Real.pow_div_factorial_le_exp (4 * q₀) (by positivity) l
        rw [mul_pow] at this
        have h4 : (0 : ℝ) < 4 ^ l := by positivity
        rw [one_div_pow, mul_one_div, le_div_iff₀ h4]
        calc q₀ ^ l / l.factorial * 4 ^ l = 4 ^ l * q₀ ^ l / l.factorial := by ring
          _ ≤ Real.exp (4 * q₀) := this
      have h12 : ((1 : ℝ) / 4) ^ l ≤ (1 / 2) ^ j := by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, ← pow_mul]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n + j).choose n)]
      calc ((n + j).choose n : ℝ) * |r| ^ j * |A (n + j) S|
          ≤ 4 ^ l * M ^ (2 * l) * (2 * CB * (l.factorial * (8 * ρ) ^ l / (2 * l).factorial)) :=
            mul_le_mul (mul_le_mul hch hrj (by positivity) (by positivity)) hAl (abs_nonneg _)
              (by positivity)
        _ = 2 * CB * (q₀ ^ l * (l.factorial / (2 * l).factorial)) := by
            have e32 : (4 : ℝ) ^ l * M ^ (2 * l) * (8 * ρ) ^ l = q₀ ^ l := by
              rw [hq₀, pow_mul, ← mul_pow, ← mul_pow]
              congr 1
              ring
            rw [← e32]
            ring
        _ ≤ 2 * CB * (q₀ ^ l * (1 / l.factorial)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac (by positivity))
              (by positivity)
        _ = 2 * CB * (q₀ ^ l / l.factorial) := by ring
        _ ≤ 2 * CB * (Real.exp (4 * q₀) * (1 / 4) ^ l) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = (2 * CB * Real.exp (4 * q₀)) * (1 / 4) ^ l := by ring
        _ ≤ (2 * CB * Real.exp (4 * q₀)) * (1 / 2) ^ j :=
            mul_le_mul_of_nonneg_left h12 (by positivity)
    · have h0 : A (n + j) S = 0 := by
        simp only [hA]; rw [hl]; exact coeff_forwardPolyHeat_expand_two_odd _ _ _
      rw [h0, mul_zero, abs_zero]
      positivity
  set f : Finset XiZeroCopy → ℕ → ℂ := fun S j =>
    ((((n + j).choose n : ℝ) * r ^ j * A (n + j) S : ℝ) : ℂ) with hf
  set g : ℕ → ℂ := fun j =>
    ((((n + j).choose n : ℝ) * r ^ j : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 t (n + j) /
      xiHorizontalPair t 0 with hg
  have hsumb : Summable fun j : ℕ => E * (1 / 2 : ℝ) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hpt : ∀ j, Tendsto (fun S => f S j) atTop (𝓝 (g j)) := by
    intro j
    have h := (hconv (n + j)).const_mul ((((n + j).choose n : ℝ) * r ^ j : ℝ) : ℂ)
    have e : g j = ((((n + j).choose n : ℝ) * r ^ j : ℝ) : ℂ) * L (n + j) := by
      simp only [hg, hL]; ring
    rw [e]
    refine h.congr fun S => ?_
    simp only [hf]
    push_cast
    ring
  have hlim := tendsto_tsum_of_dominated_convergence hsumb hpt
    (Eventually.of_forall fun S j => by
      simp only [hf, Complex.norm_real, Real.norm_eq_abs]; exact hjb j S)
  have hfS : ∀ S, ∑' j, f S j =
      (((taylor r (forwardPolyHeat s (expand ℝ 2 (sliceTruncPoly t S)))).coeff n : ℝ) : ℂ) := by
    intro S
    set P := forwardPolyHeat s (expand ℝ 2 (sliceTruncPoly t S)) with hP
    set N := P.natDegree + 1 with hN
    rw [tsum_eq_sum (s := Finset.range N) fun j hj => by
      simp only [hf, hA]
      rw [Finset.mem_range, not_lt] at hj
      rw [← hP, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, Complex.ofReal_zero],
      coeff_taylor_eq_sum r P n (N := N) (by omega), Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hf, hA, ← hP]
    push_cast
    ring
  have hgsum : ∑' j, g j = xiSliceHeatTransfer lam r t n / xiHorizontalPair t 0 := by
    rw [← (hasSum_xiSliceHeatTransfer_center hlam r t n).tsum_eq]
    simp only [hg]
    rw [tsum_div_const]
  rw [hgsum] at hlim
  have hq : 0 ≤ xiSliceHeatTransfer lam r t n / xiHorizontalPair t 0 :=
    ge_of_tendsto (hlim.congr hfS) (Eventually.of_forall fun S => Complex.zero_le_real.mpr
      (coeffNonneg_taylor_forwardPolyHeat_sliceTruncPoly ht hs hr hcone' S n))
  rw [← mul_div_cancel₀ (xiSliceHeatTransfer lam r t n) (xiHorizontalPair_zero_ne ht)]
  refine mul_nonneg ?_ hq
  rw [xiHorizontalPair_zero_eq_ofReal]
  exact Complex.zero_le_real.mpr (sq_nonneg _)

/-! ## Uniform strips and the threshold `1/12` -/

/-- The heated slice transfer is continuous in the height. -/
theorem continuous_xiSliceHeatTransfer {lam : ℝ} (hlam : 0 ≤ lam) (x₀ : ℝ) (n : ℕ) :
    Continuous fun t => xiSliceHeatTransfer lam x₀ t n := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set F : ℝ × ℝ → ℝ := fun p => Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
    Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) with hF
  set D : ℝ × ℝ → ℝ := fun p =>
    Φ p.1 * Real.exp (lam * p.1 ^ 2) * Real.exp ((|x₀| + 1) * |p.1|) *
      (Φ p.2 * Real.exp (lam * p.2 ^ 2) * Real.exp ((|x₀| + 1) * |p.2|)) with hD
  have hDi : Integrable D :=
    integrable_prod_majorant (riemannKernel_superExp.mul_exp_sq hlam) (|x₀| + 1)
  have hFD : ∀ p, |F p| ≤ D p := by
    intro p
    have hexpsq : Real.exp (lam * (p.1 - p.2) ^ 2 / 2) ≤
        Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p.1 + p.2)])
    have h2 := abs_sub_pow_div_mul_exp_le x₀ p.1 p.2 n
    have habs : |F p| = Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
        (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) := by
      simp only [hF, abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (hΦ0 _),
        abs_of_pos (Real.exp_pos _)]
      ring
    rw [habs]
    calc Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
          (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2)))
        ≤ Φ p.1 * Φ p.2 * (Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2)) *
            (Real.exp ((|x₀| + 1) * |p.1|) * Real.exp ((|x₀| + 1) * |p.2|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexpsq (mul_nonneg (hΦ0 _) (hΦ0 _))) h2
            (by positivity) (by have := hΦ0 p.1; have := hΦ0 p.2; positivity)
      _ = D p := by simp only [hD]; ring
  have hcont : Continuous F := by
    have := continuous_riemannKernelReal
    simp only [hF, hΦ]
    fun_prop
  unfold xiSliceHeatTransfer
  refine continuous_of_dominated (bound := fun p => |F p|)
    (fun t => (by fun_prop : Continuous fun p : ℝ × ℝ =>
      ((F p : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2))).aestronglyMeasurable)
    (fun t => Eventually.of_forall fun p => ?_)
    (hDi.mono' hcont.abs.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs, abs_abs]; exact hFD p))
    (Eventually.of_forall fun p => by fun_prop)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add, mul_one]

/-- Near every real height, `Ξ` vanishes at no other real height. -/
theorem eventually_XiC_ofReal_ne_zero (t : ℝ) : ∀ᶠ t' : ℝ in 𝓝[≠] t, XiC (t' : ℂ) ≠ 0 := by
  rcases (XiC_analytic (t : ℂ) (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with
    h | h
  · have hzero := XiC_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ (t : ℂ)) h
    have hX : XiC = riemannHeat 0 := by
      funext z; rw [riemannHeat_zero, XiC, mul_comm I z]
    exact absurd (hzero (Set.mem_univ (0 : ℂ))) (hX ▸ riemannHeat_zero_ne le_rfl)
  · have hmap : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] t) (𝓝[≠] (t : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_ofReal.tendsto t).mono_left
        nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
      exact fun h' => hx (Complex.ofReal_injective h')
    exact hmap.eventually h

/-- **Uniform heated strips.**  If every zero of `Ξ` satisfies `(Im z)² ≤ 3λ`, then
`T_n(λ, 0, t) ≥ 0` at every height and order. -/
theorem xiSliceHeatTransfer_nonneg_of_im_sq_le {lam : ℝ} (hlam : 0 ≤ lam)
    (him : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 ≤ 3 * lam) (t : ℝ) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam 0 t n := by
  have hgood : ∀ t' : ℝ, XiC (t' : ℂ) ≠ 0 → 0 ≤ xiSliceHeatTransfer lam 0 t' n := fun t' ht' =>
    xiSliceHeatTransfer_nonneg_of_heatedCone hlam ht' (fun q => by
      nlinarith [him q, sq_nonneg ((xiSpectralPoint q).re - t')]) n
  by_cases ht : XiC (t : ℂ) ≠ 0
  · exact hgood t ht
  · have hc := ((continuous_xiSliceHeatTransfer hlam 0 n).tendsto t).mono_left
      (nhdsWithin_le_nhds (s := {t}ᶜ))
    exact ge_of_tendsto hc ((eventually_XiC_ofReal_ne_zero t).mono fun t' h => hgood t' h)

/-- **Uniform heated strips, shifted.**  If every zero of `Ξ` satisfies `(Im z)² ≤ r² + 3λ`
(`r ≥ 0`), then `T_n(λ, r, t) ≥ 0` at every height and order. -/
theorem xiSliceHeatTransfer_nonneg_of_im_sq_le_shift {lam r : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r)
    (him : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 ≤ r ^ 2 + 3 * lam) (t : ℝ) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam r t n := by
  have hgood : ∀ t' : ℝ, XiC (t' : ℂ) ≠ 0 → 0 ≤ xiSliceHeatTransfer lam r t' n := fun t' ht' =>
    xiSliceHeatTransfer_nonneg_of_heatedHyperbola hlam hr ht' (fun q => by
      nlinarith [him q, sq_nonneg ((xiSpectralPoint q).re - t')]) n
  by_cases ht : XiC (t : ℂ) ≠ 0
  · exact hgood t ht
  · have hc := ((continuous_xiSliceHeatTransfer hlam r n).tendsto t).mono_left
      (nhdsWithin_le_nhds (s := {t}ᶜ))
    exact ge_of_tendsto hc ((eventually_XiC_ofReal_ne_zero t).mono fun t' h => hgood t' h)

/-- **The per-pair heat–abscissa trade-off.**  For every `λ ≥ 0` and every height `t`, the heated
slice `e^{(λ/2)∂_x²} S_0(t, ·)` is absolutely monotone from `x₀ = √max(¼ − 3λ, 0)`.  The de Bruijn
transfer (`xiSliceHeatTransfer_nonneg_debruijn`) gives `x₀ = √max(¼ − 2λ, 0)`. -/
theorem xiSliceHeatTransfer_nonneg_perPair {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam (Real.sqrt (max (1 / 4 - 3 * lam) 0)) t n := by
  have hr2 : Real.sqrt (max (1 / 4 - 3 * lam) 0) ^ 2 = max (1 / 4 - 3 * lam) 0 :=
    Real.sq_sqrt (le_max_right _ _)
  refine xiSliceHeatTransfer_nonneg_of_im_sq_le_shift hlam (Real.sqrt_nonneg _) (fun q => ?_) t n
  have := xiSpectralPoint_im_sq_lt_quarter q
  rw [hr2]
  have hm := le_max_left (1 / 4 - 3 * lam) 0
  simp only [pow_two] at this ⊢
  linarith

theorem mem_wdHeatAdmissible_of_im_sq_le {lam : ℝ} (hlam : 0 ≤ lam)
    (him : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 ≤ 3 * lam) :
    lam ∈ wdHeatAdmissible :=
  fun t n => xiSliceHeatTransfer_nonneg_of_im_sq_le hlam him t n

/-- **Heated slice positivity at `λ = 1/12`.** -/
theorem xiSliceHeatTransfer_nonneg_twelfth {lam : ℝ} (hlam : 1 / 12 ≤ lam) (t : ℝ) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam 0 t n :=
  xiSliceHeatTransfer_nonneg_of_im_sq_le (by linarith) (fun q => by
    have := xiSpectralPoint_im_sq_lt_quarter q
    simp only [pow_two] at this ⊢
    linarith) t n

/-- **`λ_WD ≤ 1/12`.** -/
theorem wdHeatThreshold_le_twelfth : wdHeatThreshold ≤ 1 / 12 :=
  csInf_le wdHeatAdmissible_bddBelow fun t n => xiSliceHeatTransfer_nonneg_twelfth le_rfl t n

end

end RHTower.DeBruijn
