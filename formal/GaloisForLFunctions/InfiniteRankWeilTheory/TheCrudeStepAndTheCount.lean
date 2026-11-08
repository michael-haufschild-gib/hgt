import GaloisForLFunctions.InfiniteRankWeilTheory.TheTowersOfZeta
import GaloisForLFunctions.InfiniteRankWeilTheory.TheCriticalWeight
import GaloisForLFunctions.HeckeKreinToeplitz.Index.WeightedGrams
import GaloisForLFunctions.HTGeometry.HermitianConeStrictConvexity
import GaloisForLFunctions.RHTower.WeilLagFunctionGrowth
import GaloisForLFunctions.RHTower.WeilLagFunctionExponentialExceptionCriterion
import GaloisForLFunctions.RHTower.WeilLagFunctionOneSided

/-!
# The crude step and the count

The open input of infinite-rank Weil theory is the crude step. This file fixes its strength in three
readings, and shows that the count at the critical weight is the crude step in positive form.

**The count of a tower.** The lag along the tower of `ζ` at base `ℓ` is a Toeplitz kernel
`k_ℓ(ν) = Φ(νℓ)` on `ℤ` (`lagKernel`). It is the critical-weight count of the tower.

* `toeplitzPositive_lagKernel_of_riemannHypothesis`: under RH every tower is Toeplitz positive: the
  zeros are a critical layer with positive weights `1/|ρ|²`.
* `norm_weilLagFunction_le_of_toeplitzPositive`: a Toeplitz positive tower has bounded lag,
  `|Φ(νℓ)| ≤ Φ(0)` at every level: **positivity of the count is a crude bound**.
* `toeplitzPositive_lagKernel_iff_damped`: the damped counts at every weight `δ > 0` are positive iff
  the count at `δ = 0` is (damping is lossless).
* `asymptoticAbscissaLaw_of_toeplitzPositive_lagKernel` and
  `riemannHypothesis_iff_zerosApproachLine_and_toeplitzPositive_lagKernel`: a positive count of one
  tower gives AAL; with ZAL it is RH.

**The level set decides the strength.**

* Continuous levels (all towers at once): a bound `|Φ(L)| ≤ M e^{aL}` for all `L ≥ 0`, `0 ≤ a < ½`, is
  equivalent to the zero-free half-plane `Re ρ ≤ ½ + a` (`lag_bound_iff_halfPlane`). There is no rank
  barrier here: the continuous lag sees every zero, and a bound at `a < ½` is a zero-free region.
* One tower, a thick set of levels: the bound at every exponent `a > 0` gives AAL, at `a = 0` with ZAL
  it is RH (`TheTowersOfZeta`). The thick set is sharp (`TheRankBarrier`).
* So the crude step sits between AAL and RH: `RH ⇒` (positive count of one tower) `⇒` (bounded lag
  along one tower) `⇒` (thick-set lag bound) `⇒ AAL`, and each of the middle statements is RH
  together with ZAL.

**The finite stratum.** Finitely many off-line zeros imply ZAL (`zerosApproachLine_of_finiteOffLine`),
so B13 — finitely many off-line zeros imply none — is equivalent to the statement that in the finite
stratum one tower has a positive count (`b13_iff_toeplitzPositive`), or a bounded lag on a thick set of
levels (`b13_iff_thick_lag_bounded`).
-/

open Complex Finset Matrix
open scoped ComplexOrder
open RHTower (XiZeroCopy weilLagFunction)

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The lag kernel of the tower of `ζ` at base `ℓ`: `ν ↦ Φ(νℓ)`. -/
def lagKernel (ℓ : ℝ) (ν : ℤ) : ℂ := weilLagFunction (ν * ℓ)

/-- `Φ(νℓ) = Σ_q (1/(q(1−q))) z_qᵛ` at every integer level. -/
theorem weilLagFunction_intMul_eq (ℓ : ℝ) (ν : ℤ) :
    weilLagFunction (ν * ℓ) = ∑' q, lagWeight q * frobTower ℓ zetaConfig q ^ ν := by
  unfold weilLagFunction
  refine tsum_congr fun q => ?_
  rw [frobTower, ← Complex.exp_int_mul, lagWeight, zetaConfig]
  push_cast
  ring_nf

theorem lagKernel_neg (ℓ : ℝ) (ν : ℤ) : lagKernel ℓ (-ν) = starRingEnd ℂ (lagKernel ℓ ν) := by
  unfold lagKernel
  rw [RHTower.weilLagFunction_eq_ofReal, RHTower.weilLagFunction_eq_ofReal, Complex.conj_ofReal]
  push_cast
  rw [neg_mul, ← RHTower.weilLagFunction_eq_ofReal, RHTower.weilLagFunction_neg,
    RHTower.weilLagFunction_eq_ofReal]

theorem frobTower_zpow_sub {u : ℂ} (hu : ‖u‖ = 1) (i j : ℕ) :
    u ^ ((i : ℤ) - j) = u ^ i * (starRingEnd ℂ u) ^ j := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  rw [← Complex.inv_eq_conj hu, inv_pow, zpow_sub₀ hu0, zpow_natCast, zpow_natCast,
    div_eq_mul_inv]

/-- **Under RH every tower of `ζ` is Toeplitz positive.** -/
theorem toeplitzPositive_lagKernel_of_riemannHypothesis (hRH : RiemannHypothesis) (ℓ : ℝ) :
    ToeplitzPositive (lagKernel ℓ) := by
  intro n
  have hre : ∀ q : XiZeroCopy, (zetaConfig q).re = 1 / 2 := fun q =>
    RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  have hunit : ∀ q, ‖frobTower ℓ zetaConfig q‖ = 1 := fun q => by
    rw [norm_frobTower, hre, sub_self, mul_zero, Real.exp_zero]
  have hwreal : ∀ q, lagWeight q = ((lagWeight q).re : ℂ) := fun q => by
    have him : (lagWeight q).im = 0 := by
      have hw : ((zetaConfig q) * (1 - zetaConfig q)).im = 0 := by
        simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
          Complex.one_im, hre]
        ring
      rw [lagWeight, one_div, Complex.inv_im]
      change -((q.1 : ℂ) * (1 - (q.1 : ℂ))).im / _ = 0
      rw [show ((q.1 : ℂ) * (1 - (q.1 : ℂ))).im = 0 from hw, neg_zero, zero_div]
    exact Complex.ext rfl (by rw [Complex.ofReal_im, him])
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [conjTranspose_apply, toeplitz]
    rw [show ((j : ℤ) - i) = -((i : ℤ) - j) by ring, lagKernel_neg, RCLike.star_def,
      Complex.conj_conj]
  · set u : XiZeroCopy → ℂ := frobTower ℓ zetaConfig with hu
    set v : XiZeroCopy → ℂ := fun q => ∑ j : Fin n, x j * starRingEnd ℂ (u q) ^ (j : ℕ) with hv
    set g : Fin n → Fin n → XiZeroCopy → ℂ := fun i j q =>
      starRingEnd ℂ (x i) * (lagWeight q * u q ^ ((i : ℤ) - (j : ℕ)) * x j) with hg
    have hsumm : ∀ i j, Summable (g i j) := fun i j => by
      have hw : Summable fun q => lagWeight q * u q ^ ((i : ℤ) - (j : ℕ)) :=
        Summable.of_norm_bounded summable_norm_lagWeight fun q => by
          rw [norm_mul, norm_zpow, hunit, _root_.one_zpow, mul_one]
      simpa [hg, mul_assoc, mul_comm, mul_left_comm] using
        (hw.mul_left (starRingEnd ℂ (x i) * x j))
    have hentry : ∀ i j, starRingEnd ℂ (x i) * (toeplitz (lagKernel ℓ) n i j * x j) =
        ∑' q, g i j q := fun i j => by
      simp only [toeplitz, lagKernel, hg]
      rw [weilLagFunction_intMul_eq, ← tsum_mul_right, ← tsum_mul_left]
    have hq : ∀ q, ∑ i : Fin n, ∑ j : Fin n, g i j q =
        ((((lagWeight q).re * Complex.normSq (v q)) : ℝ) : ℂ) := fun q => by
      have hcv : starRingEnd ℂ (v q) = ∑ i : Fin n, starRingEnd ℂ (x i) * u q ^ (i : ℕ) := by
        simp only [hv, map_sum, map_mul, map_pow, Complex.conj_conj]
      calc ∑ i : Fin n, ∑ j : Fin n, g i j q
          = lagWeight q * ((∑ i : Fin n, starRingEnd ℂ (x i) * u q ^ (i : ℕ)) * v q) := by
            rw [hv, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [hg, frobTower_zpow_sub (hunit q)]
            ring
        _ = lagWeight q * (starRingEnd ℂ (v q) * v q) := by rw [hcv]
        _ = _ := by
            rw [← Complex.normSq_eq_conj_mul_self]
            conv_lhs => rw [hwreal q]
            push_cast
            ring
    have hform : star x ⬝ᵥ (toeplitz (lagKernel ℓ) n) *ᵥ x =
        ∑' q, ((((lagWeight q).re * Complex.normSq (v q)) : ℝ) : ℂ) := by
      calc star x ⬝ᵥ (toeplitz (lagKernel ℓ) n) *ᵥ x
          = ∑ i : Fin n, ∑ j : Fin n, ∑' q, g i j q := by
            simp only [dotProduct, mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hentry i j
        _ = ∑' q, ∑ i : Fin n, ∑ j : Fin n, g i j q := by
            rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hsumm i j]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Summable.tsum_finsetSum fun j _ => hsumm i j]
        _ = _ := tsum_congr hq
    rw [hform, ← Complex.ofReal_tsum]
    exact Complex.zero_le_real.2 (tsum_nonneg fun q =>
      mul_nonneg (re_lagWeight_pos q).le (Complex.normSq_nonneg _))

/-- **A positive count is a crude bound.** If the tower at base `ℓ` is Toeplitz positive, then
`|Φ(νℓ)| ≤ Φ(0)` at every level. -/
theorem norm_weilLagFunction_le_of_toeplitzPositive {ℓ : ℝ} (h : ToeplitzPositive (lagKernel ℓ))
    (ν : ℕ) : ‖weilLagFunction (ν * ℓ)‖ ≤ (weilLagFunction 0).re := by
  have hA := h (ν + 1)
  have hdiag : ∀ i : Fin (ν + 1), toeplitz (lagKernel ℓ) (ν + 1) i i =
      (((weilLagFunction 0).re : ℝ) : ℂ) := fun i => by
    simp only [toeplitz, lagKernel, sub_self, Int.cast_zero, zero_mul]
    exact RHTower.weilLagFunction_eq_ofReal 0
  have hδ : 0 ≤ (weilLagFunction 0).re := by
    have := HTGeometry.posSemidef_diag_nonneg hA 0
    rw [hdiag 0] at this
    exact Complex.zero_le_real.1 this
  have := HeckeKreinToeplitz.norm_entry_le_constant_posSemidef_diagonal hA hδ hdiag
    ⟨ν, Nat.lt_succ_self ν⟩ ⟨0, Nat.succ_pos ν⟩
  simpa [toeplitz, lagKernel] using this

/-- **Damping is lossless for the towers of `ζ`.** -/
theorem toeplitzPositive_lagKernel_iff_damped (ℓ : ℝ) :
    ToeplitzPositive (lagKernel ℓ) ↔
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ToeplitzPositive fun ν => dampWeight ρ ν * lagKernel ℓ ν :=
  ⟨fun h _ h0 h1 => toeplitzPositive_damp h h0.le h1.le,
    toeplitzPositive_of_damped (lagKernel_neg ℓ)⟩

/-- **A positive count of one tower gives AAL.** -/
theorem asymptoticAbscissaLaw_of_toeplitzPositive_lagKernel {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : ToeplitzPositive (lagKernel ℓ)) : RHTower.AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_thick_lag_bound hℓ fun a ha =>
    ⟨Set.univ, thick_univ, (weilLagFunction 0).re, fun ν _ => ?_⟩
  have hb := norm_weilLagFunction_le_of_toeplitzPositive h ν
  have h0 : 0 ≤ (weilLagFunction 0).re := (norm_nonneg _).trans hb
  exact hb.trans (le_mul_of_one_le_right h0 (Real.one_le_exp (by positivity)))

/-- **RH is ZAL plus a positive count of one tower.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_toeplitzPositive_lagKernel :
    RiemannHypothesis ↔ RHTower.BacklundConverse.ZerosApproachLine ∧
      ∃ ℓ : ℝ, 0 < ℓ ∧ ToeplitzPositive (lagKernel ℓ) := by
  constructor
  · intro hRH
    exact ⟨(RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.1 hRH).1,
      1, one_pos, toeplitzPositive_lagKernel_of_riemannHypothesis hRH 1⟩
  · rintro ⟨hZ, ℓ, hℓ, h⟩
    exact RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.2
      ⟨hZ, asymptoticAbscissaLaw_of_toeplitzPositive_lagKernel hℓ h⟩

/-! ### Continuous levels: the crude count is a zero-free region -/

/-- **On continuous levels there is no rank barrier.** For `0 ≤ a < ½`, the lag is `O(e^{aL})` on
`L ≥ 0` iff every zero has `Re ρ ≤ ½ + a`. -/
theorem lag_bound_iff_halfPlane {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    (∃ M : ℝ, ∀ L : ℝ, 0 ≤ L → ‖weilLagFunction L‖ ≤ M * Real.exp (a * L)) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + a := by
  constructor
  · rintro ⟨M, hM⟩ q
    refine RHTower.re_le_half_add_of_weilLagFunctionReal_le_exp ha0 ha (M := M) (fun L hL => ?_) q
    have := hM L hL
    rw [RHTower.weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  · intro hq
    refine ⟨RHTower.lagWeightTotal, fun L hL => ?_⟩
    rw [RHTower.weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact RHTower.abs_weilLagFunctionReal_le_of_strip hq hL

/-! ### The finite stratum -/

/-- Finitely many off-line zeros. -/
def FiniteOffLine : Prop := {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite

theorem zerosApproachLine_of_finiteOffLine (h : FiniteOffLine) :
    RHTower.BacklundConverse.ZerosApproachLine := by
  intro δ hδ
  refine h.subset fun q hq => ?_
  have him : (RHTower.xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [RHTower.xiSpectralPoint, Complex.mul_im]
  have : δ < (RHTower.xiSpectralPoint q).im := hq
  rw [him] at this
  show (q.1 : ℂ).re ≠ 1 / 2
  intro heq
  linarith

/-- **B13 in tower form (count).** Finitely many off-line zeros force none iff, in the finite
stratum, one tower of `ζ` has a positive count. -/
theorem b13_iff_toeplitzPositive :
    (FiniteOffLine → RiemannHypothesis) ↔
      (FiniteOffLine → ∃ ℓ : ℝ, 0 < ℓ ∧ ToeplitzPositive (lagKernel ℓ)) := by
  constructor
  · intro h hF
    exact ⟨1, one_pos, toeplitzPositive_lagKernel_of_riemannHypothesis (h hF) 1⟩
  · intro h hF
    exact riemannHypothesis_iff_zerosApproachLine_and_toeplitzPositive_lagKernel.2
      ⟨zerosApproachLine_of_finiteOffLine hF, h hF⟩

/-- **B13 in tower form (crude bound).** Finitely many off-line zeros force none iff, in the finite
stratum, one tower of `ζ` has a bounded lag on a thick set of levels. -/
theorem b13_iff_thick_lag_bounded :
    (FiniteOffLine → RiemannHypothesis) ↔
      (FiniteOffLine → ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ,
        ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤ C) := by
  constructor
  · intro h hF
    exact (riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded.1 (h hF)).2
  · intro h hF
    exact riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded.2
      ⟨zerosApproachLine_of_finiteOffLine hF, h hF⟩

end GaloisForLFunctions.InfiniteRankWeilTheory
