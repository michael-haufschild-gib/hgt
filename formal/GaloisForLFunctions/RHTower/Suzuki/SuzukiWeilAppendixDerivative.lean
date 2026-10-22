import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilDigammaOffPoles
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilFrakP
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCheckpointEventDynamics
import GaloisForLFunctions.HTGeometry.RealDirichletSeries

/-!
# Suzuki, appendix Theorem 7.1, equation (7.2)

Masatoshi Suzuki, *On the Hilbert space derived from the Weil distribution* (arXiv:2301.00421v3),
appendix, second half of the unnumbered theorem of section 7:

`lim (y -> infinity) [ y * P_t(-i y) - psi(1/4 + y/2)/2 + (log pi)/2 ]  =  - g_xi'(t)`

for every `t > 0` that is not a prime-power atom `log n`.  Both sides are unconditional.

Three things have to be built.

* **The derivative of `g_xi`.**  Off the atoms the prime staircase `screwPrimeSum` is affine on a
  window, with slope the checkpoint mass, so `screwFn` is differentiable there with the explicit
  derivative `-2 e^{t/2} + 2 e^{-t/2} + mass - c1/2 + screwLerchTail_1 t`.

* **The five-block decomposition of the energy.**  Substituting the reflection formula for
  `zeta'/zeta` and the (off-poles) Gauss bridge for `psi(1/4 - y/2)` makes every singular term
  cancel: what is left is a polar block, an exponentially damped block, the finite prime block, a
  constant block, and one Lerch series.

* **The Lerch series limit.**  Its `n`-th term is
  `(e^{-yt} - e^{-y_n t}) * 2y / (y_n (y_n - y))` with `y_n = 2n + 1/2`, whose apparent pole at
  `y = y_n` is cancelled by the vanishing of the numerator there.  A `y`-uniform summable dominant
  exists in the three regimes `y_n <= y/2`, `y/2 < y_n < 2y`, `y_n >= 2y`, so dominated convergence
  applies and the limit is `-2 * screwLerchTail_1 t`.

The limit is taken along `suzukiVerticalFilter = atTop` meet the principal filter of
`{y | for all m, 1/4 <= |y - (2m + 1/2)|}`: at `y = 2m + 1/2` the *printed* formula (1.6) is Lean
junk, because the trivial zero of `zeta(1/2 - y)` and the poles of `psi(1/4 - y/2)` and of the Lerch
block all sit there, even though the total is regular.  The filter is not trivial:
`suzukiVerticalFilter_neBot` exhibits `y_k = 2k + 3/2` as a cofinal sequence inside it.

A defect of the printed proof, recorded here: it states
`(d/dt)(e^{-t/2} Phi(e^{-2t}, 2, 1/4)) = -2 e^{-t/2} Phi(e^{-2t}, 2, 1/4)`, where the correct
identity has `1` in the second Lerch slot.  With the printed version the theorem is false; with the
corrected version it is exactly right.  The printed statement also writes `B_t` for `P_t`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## The derivative of Suzuki's screw function off the prime-power atoms -/

theorem exp_ne_natCast_of_atomFree {t : ℝ} (hatom : ∀ n : ℕ, t ≠ Real.log n)
    (n : ℕ) : Real.exp t ≠ (n : ℝ) := by
  intro h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply hatom n
    rw [← h, Real.log_exp]

theorem log_floor_lt_of_atomFree {t : ℝ} (ht : 0 < t) (hatom : ∀ n : ℕ, t ≠ Real.log n) :
    Real.log (⌊Real.exp t⌋₊ : ℝ) < t ∧ t < Real.log ((⌊Real.exp t⌋₊ + 1 : ℕ) : ℝ) := by
  have hepos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hfl : (⌊Real.exp t⌋₊ : ℝ) ≤ Real.exp t := Nat.floor_le hepos.le
  have hne : Real.exp t ≠ (⌊Real.exp t⌋₊ : ℝ) := fun h => exp_ne_natCast_of_atomFree hatom _ h
  have hlt : (⌊Real.exp t⌋₊ : ℝ) < Real.exp t := lt_of_le_of_ne hfl (Ne.symm hne)
  have hgt : Real.exp t < ((⌊Real.exp t⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  have hone : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht.le
  have hfl1 : 1 ≤ ⌊Real.exp t⌋₊ := Nat.le_floor (by exact_mod_cast hone)
  have hflpos : (0 : ℝ) < (⌊Real.exp t⌋₊ : ℝ) := by exact_mod_cast hfl1
  constructor
  · exact (Real.log_lt_iff_lt_exp hflpos).mpr hlt
  · exact (Real.lt_log_iff_exp_lt (by positivity)).mpr hgt

/-- **The derivative of Suzuki's screw function at an atom-free time.** -/
theorem hasDerivAt_screwFn_atomFree {t : ℝ} (ht : 0 < t) (hatom : ∀ n : ℕ, t ≠ Real.log n) :
    HasDerivAt (screwFn screwLinearCoeff screwLerchConst)
      (-2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2))
        + suzukiCheckpointMass ⌊Real.exp t⌋₊ - screwLinearCoeff / 2 + screwLerchTail₁ t) t := by
  obtain ⟨hlo, hhi⟩ := log_floor_lt_of_atomFree ht hatom
  set N : ℕ := ⌊Real.exp t⌋₊ with hN
  set δ : ℝ := min (min (t - Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ) - t)) (t / 2) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    refine lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hδt : δ ≤ t / 2 := min_le_right _ _
  have haff : ∀ r ∈ Set.Ioo (t - δ) (t + δ),
      screwPrimeSum r = suzukiCheckpointMass N * r - suzukiCheckpointMoment N := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have hd1 : δ ≤ t - Real.log (N : ℝ) := le_trans (min_le_left _ _) (min_le_left _ _)
    have hd2 : δ ≤ Real.log ((N + 1 : ℕ) : ℝ) - t := le_trans (min_le_left _ _) (min_le_right _ _)
    have hrmem : r ∈ Set.Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ)) := by
      constructor <;> [linarith; linarith]
    rcases le_or_gt 2 N with hN2 | hN2
    · exact screwPrimeSum_eq_checkpoint_affine hN2 hrmem
    · -- N ≤ 1, so r < log 2 and both sides vanish
      have hN1 : N ≤ 1 := by omega
      have hmass : suzukiCheckpointMass N = 0 := by
        rw [suzukiCheckpointMass, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      have hmoment : suzukiCheckpointMoment N = 0 := by
        rw [suzukiCheckpointMoment, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      have hrlt : r < Real.log 2 := by
        have : ((N + 1 : ℕ) : ℝ) ≤ 2 := by
          have : N + 1 ≤ 2 := by omega
          exact_mod_cast this
        have hlog : Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log 2 :=
          Real.log_le_log (by positivity) this
        linarith [hrmem.2]
      rw [screwPrimeSum_eq_zero_of_lt_log_two hrlt, hmass, hmoment]
      ring
  exact hasDerivAt_screwFn_of_affine screwLinearCoeff screwLerchConst
    (suzukiCheckpointMass N) (suzukiCheckpointMoment N) ht hδt haff
    ⟨by linarith, by linarith⟩

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## `ζ'/ζ → 0` on the positive real ray -/

theorem tsum_vonMangoldt_rpow_le_suzukiWeilAppendixDerivative {σ : ℝ} (hσ : 3 ≤ σ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ))
      ≤ (2 : ℝ) ^ (2 - σ) *
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ)) := by
  have hs1 := GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow (σ := σ) (by linarith)
  have hs2 := GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow (σ := 2) (by norm_num)
  rw [← hs2.tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) hs1 (hs2.mul_left _)
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsplit : (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-(2 : ℝ)) * (n : ℝ) ^ (2 - σ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    have hpow : (n : ℝ) ^ (2 - σ) ≤ (2 : ℝ) ^ (2 - σ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) h2n (by linarith)
    rw [hsplit]
    have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hp2 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg hnpos.le _
    calc ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-(2 : ℝ)) * (n : ℝ) ^ (2 - σ))
        = (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))) * (n : ℝ) ^ (2 - σ) := by ring
      _ ≤ (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))) * (2 : ℝ) ^ (2 - σ) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (2 : ℝ) ^ (2 - σ) * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))) := by
          ring

theorem tendsto_tsum_vonMangoldt_rpow_atTop :
    Tendsto (fun σ : ℝ => ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ))
      atTop (𝓝 0) := by
  set S : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ)) with hS
  have hSnn : (0 : ℝ) ≤ S := by
    rw [hS]
    refine tsum_nonneg fun n => ?_
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)
  have hmaj : Tendsto (fun σ : ℝ => (2 : ℝ) ^ (2 - σ) * S) atTop (𝓝 0) := by
    have h1 : Tendsto (fun σ : ℝ => (2 : ℝ) ^ (2 - σ)) atTop (𝓝 0) := by
      have hrw : ∀ σ : ℝ, (2 : ℝ) ^ (2 - σ) = Real.exp (Real.log 2 * (2 - σ)) := fun σ =>
        Real.rpow_def_of_pos (by norm_num) _
      have hcomp : Tendsto (fun σ : ℝ => Real.log 2 * (2 - σ)) atTop atBot := by
        have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have h2 : Tendsto (fun σ : ℝ => 2 - σ) atTop atBot :=
          tendsto_atBot_add_const_left _ 2 tendsto_neg_atTop_atBot
        exact Filter.Tendsto.const_mul_atBot hlog h2
      have hexp : Tendsto (fun σ : ℝ => Real.exp (Real.log 2 * (2 - σ))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hcomp
      exact hexp.congr fun σ => (hrw σ).symm
    simpa using h1.mul_const S
  refine squeeze_zero' (Eventually.of_forall fun σ => ?_) ?_ hmaj
  · refine tsum_nonneg fun n => ?_
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with σ hσ
    exact tsum_vonMangoldt_rpow_le_suzukiWeilAppendixDerivative hσ

theorem tendsto_logDeriv_riemannZeta_ofReal_atTop :
    Tendsto (fun σ : ℝ => logDeriv riemannZeta ((σ : ℝ) : ℂ)) atTop (𝓝 0) := by
  have hval : ∀ σ : ℝ, 1 < σ → logDeriv riemannZeta ((σ : ℝ) : ℂ)
      = -(((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ)) : ℂ) := by
    intro σ hσ
    rw [GaloisForLFunctions.HTGeometry.ofReal_tsum_vonMangoldt_eq hσ, logDeriv_apply]
    ring
  have hlim : Tendsto (fun σ : ℝ =>
      -(((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ)) : ℂ))
      atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_tsum_vonMangoldt_rpow_atTop
    simpa using this.neg
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
  exact (hval σ hσ).symm

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## The combined archimedean Lerch block along the vertical ray -/

/-- The `n`-th term of the combined block
`e^{-yt}·(Φ(1,1,¼-y/2) - Φ(1,1,¼)) - e^{-t/2}(Φ(e^{-2t},1,¼-y/2) - Φ(e^{-2t},1,¼))`. -/
def suzukiVerticalLerchTerm (t y : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-(y * t)) - Real.exp (-(lerchExp n * t))) *
    (2 * y / (lerchExp n * (lerchExp n - y)))

/-- The pole-avoiding approach filter of Suzuki's appendix limit. -/
def suzukiVerticalFilter : Filter ℝ :=
  atTop ⊓ 𝓟 {y : ℝ | ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m|}

theorem lerchExp_pos' (n : ℕ) : (0 : ℝ) < lerchExp n := by
  rw [lerchExp]
  positivity

theorem tendsto_suzukiVerticalLerchTerm {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Tendsto (fun y : ℝ => suzukiVerticalLerchTerm t y n) atTop
      (𝓝 (2 * Real.exp (-(lerchExp n * t)) / lerchExp n)) := by
  have hlam : (0 : ℝ) < lerchExp n := lerchExp_pos' n
  have h1 : Tendsto (fun y : ℝ => Real.exp (-(y * t))) atTop (𝓝 0) := by
    have hc : Tendsto (fun y : ℝ => -(y * t)) atTop atBot := by
      have : Tendsto (fun y : ℝ => y * t) atTop atTop :=
        Filter.Tendsto.atTop_mul_const ht tendsto_id
      exact tendsto_neg_atTop_atBot.comp this
    exact Real.tendsto_exp_atBot.comp hc
  have h2 : Tendsto (fun y : ℝ => lerchExp n / y) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have h3 : Tendsto (fun y : ℝ => lerchExp n * (lerchExp n / y - 1)) atTop
      (𝓝 (lerchExp n * (0 - 1))) := ((h2.sub tendsto_const_nhds).const_mul _)
  have hne : lerchExp n * ((0 : ℝ) - 1) ≠ 0 := by
    simp
    exact ne_of_gt hlam
  have h4 : Tendsto (fun y : ℝ => 2 / (lerchExp n * (lerchExp n / y - 1))) atTop
      (𝓝 (2 / (lerchExp n * (0 - 1)))) := tendsto_const_nhds.div h3 hne
  have hcombine := (h1.sub (tendsto_const_nhds (x := Real.exp (-(lerchExp n * t))))).mul h4
  have hval : ((0 : ℝ) - Real.exp (-(lerchExp n * t))) * (2 / (lerchExp n * ((0 : ℝ) - 1)))
      = 2 * Real.exp (-(lerchExp n * t)) / lerchExp n := by
    field_simp
    ring
  rw [← hval]
  refine hcombine.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (lerchExp n)] with y hy0 hylam
  rw [suzukiVerticalLerchTerm]
  congr 1
  have hd1 : lerchExp n / y - 1 ≠ 0 := by
    have : lerchExp n / y < 1 := (div_lt_one hy0).mpr hylam
    linarith
  have hd2 : lerchExp n - y ≠ 0 := by linarith
  rw [div_eq_div_iff (mul_ne_zero (ne_of_gt hlam) hd1) (mul_ne_zero (ne_of_gt hlam) hd2)]
  field_simp

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-- A `y`-uniform summable dominant for the vertical Lerch terms. -/
def suzukiVerticalLerchBound (t : ℝ) (n : ℕ) : ℝ :=
  4 * Real.exp (-(lerchExp n * t)) / lerchExp n
    + 16 * Real.exp (-(lerchExp n * (t / 2)))
    + (4 / t) / (lerchExp n) ^ 2

theorem summable_suzukiVerticalLerchBound {t : ℝ} (ht : 0 < t) :
    Summable (suzukiVerticalLerchBound t) := by
  have h1 : Summable (fun n : ℕ => 4 * Real.exp (-(lerchExp n * t)) / lerchExp n) := by
    have h := (summable_screwLerchTerm₁ ht).neg
    refine (h.mul_left 4).congr fun n => ?_
    simp only [neg_neg]
    ring
  have h2 : Summable (fun n : ℕ => 16 * Real.exp (-(lerchExp n * (t / 2)))) :=
    (summable_exp_neg_lerchExp (by linarith)).mul_left 16
  have h3 : Summable (fun n : ℕ => (4 / t) / (lerchExp n) ^ 2) := by
    refine (summable_one_div_lerchExp_sq.mul_left (4 / t)).congr fun n => ?_
    ring
  exact (h1.add h2).add h3

theorem norm_suzukiVerticalLerchTerm_le {t : ℝ} (ht : 0 < t) {y : ℝ} (hy : 1 ≤ y)
    (hsep : ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m|) (n : ℕ) :
    |suzukiVerticalLerchTerm t y n| ≤ suzukiVerticalLerchBound t n := by
  set L : ℝ := lerchExp n with hL
  have hLpos : (0 : ℝ) < L := lerchExp_pos' n
  have hypos : (0 : ℝ) < y := by linarith
  set Ey : ℝ := Real.exp (-(y * t)) with hEy
  set EL : ℝ := Real.exp (-(L * t)) with hEL
  have hEypos : (0 : ℝ) < Ey := Real.exp_pos _
  have hELpos : (0 : ℝ) < EL := Real.exp_pos _
  have hb1 : (0 : ℝ) ≤ 4 * EL / L := by positivity
  have hb2 : (0 : ℝ) ≤ 16 * Real.exp (-(L * (t / 2))) := by positivity
  have hb3 : (0 : ℝ) ≤ (4 / t) / L ^ 2 := by positivity
  have habs : |suzukiVerticalLerchTerm t y n| = |Ey - EL| * (2 * y / (L * |L - y|)) := by
    rw [suzukiVerticalLerchTerm, ← hL, ← hEy, ← hEL, abs_mul]
    congr 1
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hLpos, abs_of_pos hypos]
    norm_num
  rw [habs, suzukiVerticalLerchBound, ← hL]
  rcases le_or_gt L (y / 2) with hcase | hcase
  · -- L ≤ y/2
    have hLy : L ≤ y := by linarith
    have hgap : y / 2 ≤ |L - y| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hdiff : |Ey - EL| ≤ EL := by
      have hle : Ey ≤ EL := Real.exp_le_exp.mpr (by nlinarith)
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hkey : |Ey - EL| * (2 * y / (L * |L - y|)) ≤ 4 * EL / L := by
      have hden : L * (y / 2) ≤ L * |L - y| := by nlinarith
      have hpos : (0 : ℝ) < L * (y / 2) := by positivity
      calc |Ey - EL| * (2 * y / (L * |L - y|))
          ≤ EL * (2 * y / (L * (y / 2))) := by
            refine mul_le_mul hdiff (div_le_div_of_nonneg_left (by positivity) hpos hden)
              (by positivity) hELpos.le
        _ = 4 * EL / L := by field_simp; ring
    linarith
  · rcases lt_or_ge L (2 * y) with hcase2 | hcase2
    · -- y/2 < L < 2y
      have hgap : (1 : ℝ) / 4 ≤ |L - y| := by
        rw [abs_sub_comm]
        exact hsep n
      have hmin : L / 2 ≤ min y L := by
        rw [le_min_iff]
        exact ⟨by linarith, by linarith⟩
      have hdiff : |Ey - EL| ≤ Real.exp (-(L * (t / 2))) := by
        have h1 : Ey ≤ Real.exp (-(L * (t / 2))) := by
          refine Real.exp_le_exp.mpr ?_
          have : L / 2 ≤ y := le_trans hmin (min_le_left _ _)
          nlinarith
        have h2 : EL ≤ Real.exp (-(L * (t / 2))) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith
        rw [abs_sub_le_iff]
        constructor <;> [linarith; linarith]
      have hratio : 2 * y / (L * |L - y|) ≤ 16 := by
        have hnum : 2 * y ≤ 4 * L := by linarith
        have hden : L * (1 / 4) ≤ L * |L - y| := by nlinarith
        have hpos : (0 : ℝ) < L * (1 / 4) := by positivity
        calc 2 * y / (L * |L - y|) ≤ 2 * y / (L * (1 / 4)) :=
              div_le_div_of_nonneg_left (by positivity) hpos hden
          _ ≤ 4 * L / (L * (1 / 4)) := by
              refine div_le_div_of_nonneg_right hnum (by positivity)
          _ = 16 := by field_simp; norm_num
      have hkey : |Ey - EL| * (2 * y / (L * |L - y|)) ≤ 16 * Real.exp (-(L * (t / 2))) := by
        calc |Ey - EL| * (2 * y / (L * |L - y|))
            ≤ Real.exp (-(L * (t / 2))) * 16 := by
              refine mul_le_mul hdiff hratio (by positivity) (Real.exp_pos _).le
          _ = 16 * Real.exp (-(L * (t / 2))) := by ring
      linarith
    · -- L ≥ 2y
      have hgap : L / 2 ≤ |L - y| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      have hdiff : |Ey - EL| ≤ Ey := by
        have hle : EL ≤ Ey := Real.exp_le_exp.mpr (by nlinarith)
        rw [abs_of_nonneg (by linarith)]
        linarith
      have hyE : y * Ey ≤ 1 / t := by
        have hexp : y * t + 1 ≤ Real.exp (y * t) := Real.add_one_le_exp _
        have hEinv : Ey = (Real.exp (y * t))⁻¹ := by
          rw [hEy, ← Real.exp_neg]
        rw [hEinv, mul_inv_le_iff₀ (Real.exp_pos _)]
        have hpos : (0 : ℝ) < Real.exp (y * t) := Real.exp_pos _
        have : y * t ≤ Real.exp (y * t) := by linarith
        rw [div_mul_eq_mul_div, le_div_iff₀ ht]
        nlinarith
      have hkey : |Ey - EL| * (2 * y / (L * |L - y|)) ≤ (4 / t) / L ^ 2 := by
        have hden : L * (L / 2) ≤ L * |L - y| := by nlinarith
        have hpos : (0 : ℝ) < L * (L / 2) := by positivity
        calc |Ey - EL| * (2 * y / (L * |L - y|))
            ≤ Ey * (2 * y / (L * (L / 2))) := by
              refine mul_le_mul hdiff (div_le_div_of_nonneg_left (by positivity) hpos hden)
                (by positivity) hEypos.le
          _ = 4 * (y * Ey) / L ^ 2 := by field_simp; ring
          _ ≤ 4 * (1 / t) / L ^ 2 := by
              refine div_le_div_of_nonneg_right ?_ (by positivity)
              nlinarith
          _ = (4 / t) / L ^ 2 := by ring
      linarith

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## The vertical Lerch series as a real object -/

theorem suzukiLerchDiffTerm_vertical {t y : ℝ}
    (hsep : ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m|) (n : ℕ) :
    suzukiLerchDiffTerm t ((1 : ℂ) / 4 - (y : ℂ) / 2) n
      = ((Real.exp (-(2 * n * t)) * (2 * y / (lerchExp n * (lerchExp n - y))) : ℝ) : ℂ) := by
  have hL : (0 : ℝ) < lerchExp n := lerchExp_pos' n
  have hne : lerchExp n - y ≠ 0 := by
    intro h
    have hs := hsep n
    rw [show y - lerchExp n = -(lerchExp n - y) by ring, h] at hs
    norm_num at hs
  have hhalf : (n : ℝ) + 1 / 4 - y / 2 = (lerchExp n - y) / 2 := by rw [lerchExp]; ring
  have hquart : (n : ℝ) + 1 / 4 = lerchExp n / 2 := by rw [lerchExp]; ring
  have ha : ((n : ℝ) + 1 / 4 - y / 2) ≠ 0 := by
    rw [hhalf]; exact div_ne_zero hne two_ne_zero
  have hb : ((n : ℝ) + 1 / 4) ≠ 0 := by positivity
  have hcast1 : ((n : ℂ) + ((1 : ℂ) / 4 - (y : ℂ) / 2)) = (((n : ℝ) + 1 / 4 - y / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have hcast2 : ((n : ℂ) + 1 / 4) = (((n : ℝ) + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [suzukiLerchDiffTerm, hcast1, hcast2, ← Complex.ofReal_inv, ← Complex.ofReal_inv,
    ← Complex.ofReal_sub, ← Complex.ofReal_mul]
  congr 1
  congr 1
  rw [hhalf, hquart]
  field_simp
  ring

theorem summable_suzukiVerticalLerchTerm {t : ℝ} (ht : 0 < t) {y : ℝ} (hy : 1 ≤ y)
    (hsep : ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m|) :
    Summable (fun n : ℕ => suzukiVerticalLerchTerm t y n) := by
  refine Summable.of_norm_bounded (summable_suzukiVerticalLerchBound ht) fun n => ?_
  rw [Real.norm_eq_abs]
  exact norm_suzukiVerticalLerchTerm_le ht hy hsep n

/-- **The combined archimedean Lerch block of Suzuki eq. (1.6) on the vertical ray.** -/
theorem suzukiVerticalLerch_eq {t : ℝ} (ht : 0 < t) {y : ℝ}
    (hsep : ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m|) :
    ((Real.exp (-(y * t)) : ℝ) : ℂ) * suzukiLerchDiff 0 ((1 : ℂ) / 4 - (y : ℂ) / 2)
        - ((Real.exp (-(t / 2)) : ℝ) : ℂ) * suzukiLerchDiff t ((1 : ℂ) / 4 - (y : ℂ) / 2)
      = ((∑' n : ℕ, suzukiVerticalLerchTerm t y n : ℝ) : ℂ) := by
  have hS0 : Summable (suzukiLerchDiffTerm 0 ((1 : ℂ) / 4 - (y : ℂ) / 2)) :=
    summable_suzukiLerchDiffTerm_all le_rfl _
  have hSt : Summable (suzukiLerchDiffTerm t ((1 : ℂ) / 4 - (y : ℂ) / 2)) :=
    summable_suzukiLerchDiffTerm_all ht.le _
  have hterm : ∀ n : ℕ,
      ((Real.exp (-(y * t)) : ℝ) : ℂ) * suzukiLerchDiffTerm 0 ((1 : ℂ) / 4 - (y : ℂ) / 2) n
          - ((Real.exp (-(t / 2)) : ℝ) : ℂ) * suzukiLerchDiffTerm t ((1 : ℂ) / 4 - (y : ℂ) / 2) n
        = ((suzukiVerticalLerchTerm t y n : ℝ) : ℂ) := by
    intro n
    rw [suzukiLerchDiffTerm_vertical hsep, suzukiLerchDiffTerm_vertical hsep,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    congr 1
    have hexp : Real.exp (-(t / 2)) * Real.exp (-(2 * (n : ℝ) * t))
        = Real.exp (-(lerchExp n * t)) := by
      rw [← Real.exp_add, lerchExp]
      congr 1
      ring
    rw [suzukiVerticalLerchTerm]
    have e0 : Real.exp (-(2 * (n : ℝ) * 0)) = 1 := by norm_num
    rw [e0]
    linear_combination (-(2 * y / (lerchExp n * (lerchExp n - y)))) * hexp
  calc ((Real.exp (-(y * t)) : ℝ) : ℂ) * suzukiLerchDiff 0 ((1 : ℂ) / 4 - (y : ℂ) / 2)
        - ((Real.exp (-(t / 2)) : ℝ) : ℂ) * suzukiLerchDiff t ((1 : ℂ) / 4 - (y : ℂ) / 2)
      = ∑' n : ℕ,
          (((Real.exp (-(y * t)) : ℝ) : ℂ) * suzukiLerchDiffTerm 0 ((1 : ℂ) / 4 - (y : ℂ) / 2) n
            - ((Real.exp (-(t / 2)) : ℝ) : ℂ)
              * suzukiLerchDiffTerm t ((1 : ℂ) / 4 - (y : ℂ) / 2) n) := by
        rw [(hS0.mul_left _).tsum_sub (hSt.mul_left _), tsum_mul_left, tsum_mul_left,
          suzukiLerchDiff, suzukiLerchDiff]
    _ = ∑' n : ℕ, ((suzukiVerticalLerchTerm t y n : ℝ) : ℂ) := tsum_congr hterm
    _ = ((∑' n : ℕ, suzukiVerticalLerchTerm t y n : ℝ) : ℂ) := (Complex.ofReal_tsum _).symm

/-! ## The pole-avoiding filter -/

theorem suzukiVerticalFilter_le_atTop : suzukiVerticalFilter ≤ atTop := inf_le_left

theorem suzukiVerticalFilter_sep : ∀ᶠ y : ℝ in suzukiVerticalFilter,
    ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m| := by
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨{y : ℝ | ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m|}, ?_, fun y hy => hy⟩
  exact Filter.mem_inf_of_right (Filter.mem_principal_self _)

/-- The approach filter of Suzuki's appendix limit is not the trivial filter: the sequence
`y_k = 2k + 3/2` is cofinal in it. -/
instance suzukiVerticalFilter_neBot : suzukiVerticalFilter.NeBot := by
  have hmap : Filter.map (fun k : ℕ => 2 * (k : ℝ) + 3 / 2) atTop ≤ suzukiVerticalFilter := by
    refine le_inf ?_ ?_
    · refine Filter.Tendsto.atTop_add ?_ tendsto_const_nhds
      exact Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    · rw [Filter.le_principal_iff, Filter.mem_map]
      refine Filter.univ_mem' fun k => ?_
      intro m
      have hval : 2 * (k : ℝ) + 3 / 2 - lerchExp m = 2 * ((k : ℝ) - (m : ℝ)) + 1 := by
        rw [lerchExp]; ring
      rw [hval]
      rcases le_or_gt (m : ℝ) (k : ℝ) with h | h
      · have : (1 : ℝ) ≤ 2 * ((k : ℝ) - (m : ℝ)) + 1 := by linarith
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have hint : (k : ℝ) + 1 ≤ (m : ℝ) := by
          have : k < m := by exact_mod_cast h
          exact_mod_cast Nat.succ_le_of_lt this
        have : 2 * ((k : ℝ) - (m : ℝ)) + 1 ≤ -1 := by linarith
        rw [abs_of_nonpos (by linarith)]
        linarith
  exact Filter.neBot_of_le hmap

/-! ## The limit of the vertical Lerch series -/

theorem tendsto_tsum_suzukiVerticalLerchTerm {t : ℝ} (ht : 0 < t) :
    Tendsto (fun y : ℝ => ∑' n : ℕ, suzukiVerticalLerchTerm t y n) suzukiVerticalFilter
      (𝓝 (-2 * screwLerchTail₁ t)) := by
  have hval : (∑' n : ℕ, 2 * Real.exp (-(lerchExp n * t)) / lerchExp n)
      = -2 * screwLerchTail₁ t := by
    rw [screwLerchTail₁, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    ring
  rw [← hval]
  refine tendsto_tsum_of_dominated_convergence (summable_suzukiVerticalLerchBound ht) ?_ ?_
  · intro n
    exact (tendsto_suzukiVerticalLerchTerm ht n).mono_left suzukiVerticalFilter_le_atTop
  · filter_upwards [suzukiVerticalFilter_sep,
      (eventually_ge_atTop (1 : ℝ)).filter_mono suzukiVerticalFilter_le_atTop] with y hsep hy n
    rw [Real.norm_eq_abs]
    exact norm_suzukiVerticalLerchTerm_le ht hy hsep n

/-! ## The linear screw coefficient is `psi(1/4) - log pi` -/

theorem digamma_quarter_sub_logPi :
    Complex.digamma (1 / 4) - ((Real.log Real.pi : ℝ) : ℂ) = ((screwLinearCoeff : ℝ) : ℂ) := by
  have hq : ∀ m : ℕ, ((1 : ℂ) / 2) / 2 ≠ -(m : ℂ) := by
    intro m h
    have hre : (((1 : ℂ) / 2) / 2).re = (-(m : ℂ)).re := by rw [h]
    simp at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hq' : ∀ m : ℕ, ((1 : ℂ) - 1 / 2) / 2 ≠ -(m : ℂ) := by
    intro m
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]
    exact hq m
  have hz : riemannZeta (1 / 2 : ℂ) ≠ 0 := riemannZeta_half_ne_zero
  have hz' : riemannZeta ((1 : ℂ) - 1 / 2) ≠ 0 := by
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]; exact hz
  have hrefl := logDeriv_riemannZeta_add_reflect_off_poles hq hq' hz hz'
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring, show ((1 : ℂ) / 2) / 2 = 1 / 4 by ring] at hrefl
  rw [logDeriv_riemannZeta_half] at hrefl
  push_cast at hrefl ⊢
  linear_combination hrefl

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## Suzuki eq. (1.6) on the vertical ray `z = -iy` -/

/-- **`y · 𝔓_t(-iy)` in real-exponential form.** -/
theorem suzukiFrakP_vertical_mul {t y : ℝ} (hy : 1 ≤ y) :
    (y : ℂ) * suzukiFrakP t (-(I * (y : ℂ)))
      = 4 * (y : ℂ) * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * (y : ℂ))
        + 4 * (y : ℂ) * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * (y : ℂ))
        + (((Real.exp (-(y * t)) : ℝ) : ℂ) - 1) * logDeriv riemannZeta (1 / 2 - (y : ℂ))
        + (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, (screwPrimeWeight n : ℂ)
            * (((Real.exp (-(y * (t - Real.log n))) : ℝ) : ℂ) - 1))
        - (Complex.digamma (1 / 4 - (y : ℂ) / 2) - Complex.digamma (1 / 4)) / 2
        - (Real.exp (-(t / 2)) : ℂ) * suzukiLerchDiff t (1 / 4 - (y : ℂ) / 2) / 2 := by
  have hY0 : ((y : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hp : (1 : ℂ) + 2 * (y : ℂ) ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) + 2 * (y : ℂ)).re = 0 := by rw [h]; simp
    simp at hre
    linarith
  have hm : (1 : ℂ) - 2 * (y : ℂ) ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) - 2 * (y : ℂ)).re = 0 := by rw [h]; simp
    simp at hre
    linarith
  have e3 : I * (-(I * (y : ℂ))) = (y : ℂ) := by linear_combination (-(y : ℂ)) * Complex.I_sq
  have e1 : (2 : ℂ) * I * (-(I * (y : ℂ))) = 2 * (y : ℂ) := by
    linear_combination (-2 * (y : ℂ)) * Complex.I_sq
  rw [suzukiFrakP, e3, e1]
  have hEt : Complex.exp (-((y : ℂ) * (t : ℂ))) = ((Real.exp (-(y * t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hEn : ∀ n : ℕ, Complex.exp (-((y : ℂ) * ((t : ℂ) - ((Real.log n : ℝ) : ℂ))))
      = ((Real.exp (-(y * (t - Real.log n))) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hEt]
  rw [Finset.sum_congr rfl (fun n _ => by rw [hEn n] :
    ∀ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
      (screwPrimeWeight n : ℂ) *
        ((Complex.exp (-((y : ℂ) * ((t : ℂ) - ((Real.log n : ℝ) : ℂ)))) - 1) / (y : ℂ))
      = (screwPrimeWeight n : ℂ)
        * ((((Real.exp (-(y * (t - Real.log n))) : ℝ) : ℂ) - 1) / (y : ℂ)))]
  have hsumeq : (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, (screwPrimeWeight n : ℂ)
        * ((((Real.exp (-(y * (t - Real.log n))) : ℝ) : ℂ) - 1) / (y : ℂ)))
      = (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, (screwPrimeWeight n : ℂ)
        * (((Real.exp (-(y * (t - Real.log n))) : ℝ) : ℂ) - 1)) / (y : ℂ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsumeq]
  field_simp

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-- The separation condition rules out the trivial zeros of `ζ(1/2-y)` and the poles of
`ψ(1/4-y/2)`, which sit at exactly the same points `y = 2m + 1/2`. -/
theorem lerchExp_ne_of_sep {y : ℝ} (hsep : ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m|) (m : ℕ) :
    y ≠ lerchExp m := by
  intro h
  have := hsep m
  rw [h, sub_self, abs_zero] at this
  linarith

/-- **Reflection of `ζ'/ζ` on the vertical ray.** -/
theorem logDeriv_riemannZeta_vertical_reflect {y : ℝ} (hy : 1 ≤ y)
    (hsep : ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m|) :
    logDeriv riemannZeta (1 / 2 - (y : ℂ)) + logDeriv riemannZeta (1 / 2 + (y : ℂ))
      = ((Real.log Real.pi : ℝ) : ℂ) - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2
        - Complex.digamma (1 / 4 - (y : ℂ) / 2) / 2 := by
  have hre : 1 < ((1 : ℂ) / 2 + (y : ℂ)).re := by
    simp [Complex.add_re]
    linarith
  have hodd : ∀ m : ℕ, ((1 : ℂ) / 2 + (y : ℂ)) ≠ 1 + 2 * (m : ℂ) := by
    intro m hc
    have hre2 : ((1 : ℂ) / 2 + (y : ℂ)).re = ((1 : ℂ) + 2 * (m : ℂ)).re := by rw [hc]
    simp [Complex.add_re] at hre2
    refine lerchExp_ne_of_sep hsep m ?_
    rw [lerchExp]
    linarith
  have hkey := logDeriv_riemannZeta_add_reflect_of_one_lt_re hre hodd
  rw [show (1 : ℂ) - (1 / 2 + (y : ℂ)) = 1 / 2 - (y : ℂ) by ring,
    show ((1 : ℂ) / 2 + (y : ℂ)) / 2 = 1 / 4 + (y : ℂ) / 2 by ring,
    show ((1 : ℂ) / 2 - (y : ℂ)) / 2 = 1 / 4 - (y : ℂ) / 2 by ring] at hkey
  linear_combination hkey

/-- **The Gauss bridge on the vertical ray**, where the argument `1/4 - y/2` is far to the left. -/
theorem digamma_vertical_lower {y : ℝ} (hsep : ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m|) :
    Complex.digamma (1 / 4 - (y : ℂ) / 2) - Complex.digamma (1 / 4)
      = -suzukiLerchDiff 0 (1 / 4 - (y : ℂ) / 2) := by
  refine digamma_sub_quarter_eq_offPoles fun m hc => ?_
  have hre : ((1 : ℂ) / 4 - (y : ℂ) / 2).re = (-(m : ℂ)).re := by rw [hc]
  simp [Complex.sub_re] at hre
  refine lerchExp_ne_of_sep hsep m ?_
  rw [lerchExp]
  linarith

/-- **The five-block decomposition of Suzuki's appendix energy on the vertical ray.** -/
theorem suzukiVerticalEnergy_eq {t : ℝ} (ht : 0 < t) {y : ℝ} (hy : 1 ≤ y)
    (hsep : ∀ m : ℕ, (1 : ℝ) / 4 ≤ |y - lerchExp m|) :
    (y : ℂ) * suzukiFrakP t (-(I * (y : ℂ)))
        - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2 + ((Real.log Real.pi : ℝ) : ℂ) / 2
      = (4 * (y : ℂ) * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * (y : ℂ))
          + 4 * (y : ℂ) * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * (y : ℂ)))
        + ((Real.exp (-(y * t)) : ℝ) : ℂ) * (((Real.log Real.pi : ℝ) : ℂ)
            - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2
            - logDeriv riemannZeta (1 / 2 + (y : ℂ)) - Complex.digamma (1 / 4) / 2)
        + (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, (screwPrimeWeight n : ℂ)
            * (((Real.exp (-(y * (t - Real.log n))) : ℝ) : ℂ) - 1))
        + (Complex.digamma (1 / 4) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2
            + logDeriv riemannZeta (1 / 2 + (y : ℂ)))
        + (1 / 2 : ℂ) * ((∑' n : ℕ, suzukiVerticalLerchTerm t y n : ℝ) : ℂ) := by
  rw [suzukiFrakP_vertical_mul hy]
  have hR := logDeriv_riemannZeta_vertical_reflect hy hsep
  have hG := digamma_vertical_lower hsep
  have hL := suzukiVerticalLerch_eq ht hsep
  linear_combination (((Real.exp (-(y * t)) : ℝ) : ℂ) - 1) * hR
    - (((Real.exp (-(y * t)) : ℝ) : ℂ) / 2) * hG + (1 / 2 : ℂ) * hL

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## Limits of the five blocks -/

/-- The polar block is a cast of a real rational function of `y`. -/
theorem suzukiVerticalPolar_cast (t y : ℝ) :
    4 * (y : ℂ) * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * (y : ℂ))
        + 4 * (y : ℂ) * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * (y : ℂ))
      = ((4 * y * (Real.exp (t / 2) - 1) / (1 + 2 * y)
          + 4 * y * (Real.exp (-(t / 2)) - 1) / (1 - 2 * y) : ℝ) : ℂ) := by
  push_cast
  ring

theorem tendsto_four_mul_div_add : Tendsto (fun y : ℝ => 4 * y / (1 + 2 * y)) atTop (𝓝 2) := by
  have hden : Tendsto (fun y : ℝ => 1 + 2 * y) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id)
  have hfrac : Tendsto (fun y : ℝ => (2 : ℝ) / (1 + 2 * y)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hden
  have hsub : Tendsto (fun y : ℝ => (2 : ℝ) - 2 / (1 + 2 * y)) atTop (𝓝 (2 - 0)) :=
    tendsto_const_nhds.sub hfrac
  rw [show (2 : ℝ) - 0 = 2 by ring] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have h : (1 : ℝ) + 2 * y ≠ 0 := by intro hc; linarith
  field_simp
  ring

theorem tendsto_four_mul_div_sub : Tendsto (fun y : ℝ => 4 * y / (1 - 2 * y)) atTop (𝓝 (-2)) := by
  have hden : Tendsto (fun y : ℝ => 2 * y - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1)
      (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id)
  have hfrac : Tendsto (fun y : ℝ => (2 : ℝ) / (2 * y - 1)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hden
  have hsub : Tendsto (fun y : ℝ => (-2 : ℝ) - 2 / (2 * y - 1)) atTop (𝓝 (-2 - 0)) :=
    tendsto_const_nhds.sub hfrac
  rw [show (-2 : ℝ) - 0 = -2 by ring] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  have h : (2 : ℝ) * y - 1 ≠ 0 := by intro hc; linarith
  have h2 : (1 : ℝ) - 2 * y ≠ 0 := by intro hc; linarith
  field_simp
  ring

theorem tendsto_suzukiVerticalPolar (t : ℝ) :
    Tendsto (fun y : ℝ => 4 * (y : ℂ) * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * (y : ℂ))
        + 4 * (y : ℂ) * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * (y : ℂ))) atTop
      (𝓝 ((2 * (Real.exp (t / 2) - 1) + (-2) * (Real.exp (-(t / 2)) - 1) : ℝ) : ℂ)) := by
  have hreal : Tendsto (fun y : ℝ => 4 * y * (Real.exp (t / 2) - 1) / (1 + 2 * y)
      + 4 * y * (Real.exp (-(t / 2)) - 1) / (1 - 2 * y)) atTop
      (𝓝 (2 * (Real.exp (t / 2) - 1) + (-2) * (Real.exp (-(t / 2)) - 1))) := by
    have h1 := tendsto_four_mul_div_add.mul_const (Real.exp (t / 2) - 1)
    have h2 := tendsto_four_mul_div_sub.mul_const (Real.exp (-(t / 2)) - 1)
    have := h1.add h2
    refine this.congr fun y => ?_
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  have := (Complex.continuous_ofReal.tendsto _).comp hreal
  refine this.congr fun y => ?_
  simp only [Function.comp_apply]
  exact (suzukiVerticalPolar_cast t y).symm

/-! ### The decaying block -/

theorem norm_digamma_shift_le {y : ℝ} (hy : 2 ≤ y) :
    ‖Complex.digamma (1 / 4 + (y : ℂ) / 2)‖
      ≤ ‖Complex.digamma (1 / 4)‖ + (2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) * y := by
  have hre : (1 : ℝ) ≤ ((1 : ℂ) / 4 + (y : ℂ) / 2).re := by
    simp [Complex.add_re]
    linarith
  have hrepos : (0 : ℝ) < ((1 : ℂ) / 4 + (y : ℂ) / 2).re := by linarith
  have hbridge := digamma_sub_quarter_eq hrepos
  have hfac := suzukiLerchDiff_eq (t := 0) hrepos
  have hker := norm_suzukiLerchKernel_le_of_one_le_re (t := 0) le_rfl hre
  have hcoef : ‖(1 : ℂ) / 4 - ((1 : ℂ) / 4 + (y : ℂ) / 2)‖ = y / 2 := by
    rw [show (1 : ℂ) / 4 - ((1 : ℂ) / 4 + (y : ℂ) / 2) = -((y : ℝ) / 2 : ℝ) by push_cast; ring]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hC : (0 : ℝ) ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 :=
    tsum_nonneg fun n => by positivity
  have hnormdiff : ‖suzukiLerchDiff 0 ((1 : ℂ) / 4 + (y : ℂ) / 2)‖
      ≤ (y / 2) * (4 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) := by
    rw [hfac, norm_mul, hcoef]
    exact mul_le_mul_of_nonneg_left hker (by linarith)
  have hsplit : Complex.digamma (1 / 4 + (y : ℂ) / 2)
      = Complex.digamma (1 / 4) - suzukiLerchDiff 0 ((1 : ℂ) / 4 + (y : ℂ) / 2) := by
    linear_combination hbridge
  rw [hsplit]
  calc ‖Complex.digamma (1 / 4) - suzukiLerchDiff 0 ((1 : ℂ) / 4 + (y : ℂ) / 2)‖
      ≤ ‖Complex.digamma (1 / 4)‖ + ‖suzukiLerchDiff 0 ((1 : ℂ) / 4 + (y : ℂ) / 2)‖ :=
        norm_sub_le _ _
    _ ≤ ‖Complex.digamma (1 / 4)‖ + (y / 2) * (4 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) := by
        linarith
    _ = ‖Complex.digamma (1 / 4)‖ + (2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) * y := by ring

private theorem tendsto_exp_neg_mul_linear {t : ℝ} (ht : 0 < t) (K₁ K₂ : ℝ) :
    Tendsto (fun y : ℝ => Real.exp (-(y * t)) * (K₁ + K₂ * y)) atTop (𝓝 0) := by
  have hmul : Tendsto (fun y : ℝ => y * t) atTop atTop :=
    Filter.Tendsto.atTop_mul_const ht tendsto_id
  have h1 : Tendsto (fun y : ℝ => Real.exp (-(y * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hmul)
  have h2 : Tendsto (fun y : ℝ => (y * t) ^ 1 * Real.exp (-(y * t))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hmul
  have h3 : Tendsto (fun y : ℝ => y * Real.exp (-(y * t))) atTop (𝓝 0) := by
    have hc : Tendsto (fun y : ℝ => (1 / t) * ((y * t) ^ 1 * Real.exp (-(y * t)))) atTop (𝓝 0) := by
      simpa using h2.const_mul (1 / t)
    refine hc.congr fun y => ?_
    field_simp
  have hsum : Tendsto (fun y : ℝ => K₁ * Real.exp (-(y * t))
      + K₂ * (y * Real.exp (-(y * t)))) atTop (𝓝 0) := by
    simpa using (h1.const_mul K₁).add (h3.const_mul K₂)
  refine hsum.congr fun y => ?_
  ring

theorem tendsto_logDeriv_riemannZeta_vertical :
    Tendsto (fun y : ℝ => logDeriv riemannZeta (1 / 2 + (y : ℂ))) atTop (𝓝 0) := by
  have hcomp : Tendsto (fun y : ℝ => 1 / 2 + y) atTop atTop :=
    tendsto_atTop_add_const_left _ (1 / 2) tendsto_id
  have hkey := tendsto_logDeriv_riemannZeta_ofReal_atTop.comp hcomp
  refine hkey.congr fun y => ?_
  simp only [Function.comp_apply]
  congr 1
  push_cast
  ring

theorem tendsto_suzukiVerticalDecay {t : ℝ} (ht : 0 < t) :
    Tendsto (fun y : ℝ => ((Real.exp (-(y * t)) : ℝ) : ℂ) * (((Real.log Real.pi : ℝ) : ℂ)
        - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2
        - logDeriv riemannZeta (1 / 2 + (y : ℂ)) - Complex.digamma (1 / 4) / 2))
      atTop (𝓝 0) := by
  set C : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 with hC
  set K₁ : ℝ := ‖((Real.log Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 / 4)‖ + 1 with hK₁
  refine squeeze_zero_norm' ?_ (tendsto_exp_neg_mul_linear ht K₁ C)
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    tendsto_logDeriv_riemannZeta_vertical (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with y hy hLp
  have hLpnorm : ‖logDeriv riemannZeta (1 / 2 + (y : ℂ))‖ ≤ 1 := by
    have := Metric.mem_ball.mp hLp
    rw [dist_zero_right] at this
    linarith
  have hPp := norm_digamma_shift_le hy
  have hEpos : (0 : ℝ) < Real.exp (-(y * t)) := Real.exp_pos _
  have hnorm : ‖((Real.log Real.pi : ℝ) : ℂ) - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2
      - logDeriv riemannZeta (1 / 2 + (y : ℂ)) - Complex.digamma (1 / 4) / 2‖
      ≤ K₁ + C * y := by
    have h1 : ‖((Real.log Real.pi : ℝ) : ℂ) - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2
        - logDeriv riemannZeta (1 / 2 + (y : ℂ)) - Complex.digamma (1 / 4) / 2‖
        ≤ ‖((Real.log Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2‖
          + ‖logDeriv riemannZeta (1 / 2 + (y : ℂ))‖ + ‖Complex.digamma (1 / 4) / 2‖ := by
      calc ‖((Real.log Real.pi : ℝ) : ℂ) - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2
            - logDeriv riemannZeta (1 / 2 + (y : ℂ)) - Complex.digamma (1 / 4) / 2‖
          ≤ ‖((Real.log Real.pi : ℝ) : ℂ) - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2
              - logDeriv riemannZeta (1 / 2 + (y : ℂ))‖ + ‖Complex.digamma (1 / 4) / 2‖ :=
            norm_sub_le _ _
        _ ≤ (‖((Real.log Real.pi : ℝ) : ℂ) - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2‖
              + ‖logDeriv riemannZeta (1 / 2 + (y : ℂ))‖) + ‖Complex.digamma (1 / 4) / 2‖ := by
            gcongr
            exact norm_sub_le _ _
        _ ≤ ((‖((Real.log Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2‖)
              + ‖logDeriv riemannZeta (1 / 2 + (y : ℂ))‖) + ‖Complex.digamma (1 / 4) / 2‖ := by
            gcongr
            exact norm_sub_le _ _
        _ = ‖((Real.log Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2‖
              + ‖logDeriv riemannZeta (1 / 2 + (y : ℂ))‖ + ‖Complex.digamma (1 / 4) / 2‖ := by
            ring
    have h2 : ‖Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2‖
        = ‖Complex.digamma (1 / 4 + (y : ℂ) / 2)‖ / 2 := by
      rw [norm_div]
      norm_num
    have h3 : ‖Complex.digamma (1 / 4) / 2‖ = ‖Complex.digamma (1 / 4)‖ / 2 := by
      rw [norm_div]
      norm_num
    rw [h2, h3] at h1
    rw [hK₁]
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hEpos]
  calc Real.exp (-(y * t))
        * ‖((Real.log Real.pi : ℝ) : ℂ) - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2
          - logDeriv riemannZeta (1 / 2 + (y : ℂ)) - Complex.digamma (1 / 4) / 2‖
      ≤ Real.exp (-(y * t)) * (K₁ + C * y) :=
        mul_le_mul_of_nonneg_left hnorm hEpos.le

/-! ### The prime block -/

theorem tendsto_suzukiVerticalPrime {t : ℝ} (ht : 0 < t) (hatom : ∀ n : ℕ, t ≠ Real.log n) :
    Tendsto (fun y : ℝ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, (screwPrimeWeight n : ℂ)
        * (((Real.exp (-(y * (t - Real.log n))) : ℝ) : ℂ) - 1))
      atTop (𝓝 (-((suzukiCheckpointMass ⌊Real.exp t⌋₊ : ℝ) : ℂ))) := by
  obtain ⟨hlo, _⟩ := log_floor_lt_of_atomFree ht hatom
  have hval : (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, (screwPrimeWeight n : ℂ) * ((0 : ℂ) - 1))
      = -((suzukiCheckpointMass ⌊Real.exp t⌋₊ : ℝ) : ℂ) := by
    rw [suzukiCheckpointMass, Complex.ofReal_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [← hval]
  refine tendsto_finsetSum _ fun n hn => ?_
  have hnN : n ≤ ⌊Real.exp t⌋₊ := (Finset.mem_Icc.mp hn).2
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hpos : 0 < t - Real.log n := by
    have hlog : Real.log (n : ℝ) ≤ Real.log ((⌊Real.exp t⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hnN)
    linarith
  have hr : Tendsto (fun y : ℝ => Real.exp (-(y * (t - Real.log n)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (Filter.Tendsto.atTop_mul_const hpos tendsto_id))
  have hE : Tendsto (fun y : ℝ => ((Real.exp (-(y * (t - Real.log n))) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have hcast := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    rw [Complex.ofReal_zero] at hcast
    exact hcast
  exact (hE.sub tendsto_const_nhds).const_mul (screwPrimeWeight n : ℂ)

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## Suzuki, appendix Theorem 7.1, equation (7.2) -/

/-- **Suzuki eq. (7.2), unconditional.**  For every `t > 0` off the prime-power atoms,

`lim_{y → ∞} [ y·𝔓_t(-iy) − ψ(1/4 + y/2)/2 + (log π)/2 ] = −g_ξ'(t)`,

the limit being taken along the pole-avoiding filter `suzukiVerticalFilter`, on which the printed
formula (1.6) is not Lean junk: at `y = 2m + 1/2` the individual blocks of (1.6) have poles (the
trivial zeros of `ζ(1/2−y)` and the poles of `ψ(1/4−y/2)` and of the Lerch block), even though the
total is regular there. -/
theorem tendsto_suzukiFrakP_vertical {t : ℝ} (ht : 0 < t) (hatom : ∀ n : ℕ, t ≠ Real.log n) :
    Tendsto (fun y : ℝ => (y : ℂ) * suzukiFrakP t (-(I * (y : ℂ)))
        - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2 + ((Real.log Real.pi : ℝ) : ℂ) / 2)
      suzukiVerticalFilter
      (𝓝 (-((deriv (screwFn screwLinearCoeff screwLerchConst) t : ℝ) : ℂ))) := by
  have hderiv : deriv (screwFn screwLinearCoeff screwLerchConst) t
      = -2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2))
        + suzukiCheckpointMass ⌊Real.exp t⌋₊ - screwLinearCoeff / 2 + screwLerchTail₁ t :=
    (hasDerivAt_screwFn_atomFree ht hatom).deriv
  have hL1 := (tendsto_suzukiVerticalPolar t).mono_left suzukiVerticalFilter_le_atTop
  have hL2 := (tendsto_suzukiVerticalDecay ht).mono_left suzukiVerticalFilter_le_atTop
  have hL3 := (tendsto_suzukiVerticalPrime ht hatom).mono_left suzukiVerticalFilter_le_atTop
  have hL4 : Tendsto (fun y : ℝ => Complex.digamma (1 / 4) / 2
      - ((Real.log Real.pi : ℝ) : ℂ) / 2 + logDeriv riemannZeta (1 / 2 + (y : ℂ)))
      suzukiVerticalFilter
      (𝓝 (Complex.digamma (1 / 4) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2 + 0)) :=
    (tendsto_const_nhds.add tendsto_logDeriv_riemannZeta_vertical).mono_left
      suzukiVerticalFilter_le_atTop
  have hL5 : Tendsto (fun y : ℝ => (1 / 2 : ℂ) * ((∑' n : ℕ, suzukiVerticalLerchTerm t y n : ℝ) : ℂ))
      suzukiVerticalFilter (𝓝 ((1 / 2 : ℂ) * ((-2 * screwLerchTail₁ t : ℝ) : ℂ))) := by
    refine Filter.Tendsto.const_mul _ ?_
    exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_tsum_suzukiVerticalLerchTerm ht)
  have hsum := ((((hL1.add hL2).add hL3).add hL4).add hL5)
  have hEq : (fun y : ℝ =>
      (4 * (y : ℂ) * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * (y : ℂ))
          + 4 * (y : ℂ) * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * (y : ℂ)))
        + ((Real.exp (-(y * t)) : ℝ) : ℂ) * (((Real.log Real.pi : ℝ) : ℂ)
            - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2
            - logDeriv riemannZeta (1 / 2 + (y : ℂ)) - Complex.digamma (1 / 4) / 2)
        + (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, (screwPrimeWeight n : ℂ)
            * (((Real.exp (-(y * (t - Real.log n))) : ℝ) : ℂ) - 1))
        + (Complex.digamma (1 / 4) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2
            + logDeriv riemannZeta (1 / 2 + (y : ℂ)))
        + (1 / 2 : ℂ) * ((∑' n : ℕ, suzukiVerticalLerchTerm t y n : ℝ) : ℂ))
      =ᶠ[suzukiVerticalFilter]
      (fun y : ℝ => (y : ℂ) * suzukiFrakP t (-(I * (y : ℂ)))
        - Complex.digamma (1 / 4 + (y : ℂ) / 2) / 2 + ((Real.log Real.pi : ℝ) : ℂ) / 2) := by
    filter_upwards [suzukiVerticalFilter_sep,
      (eventually_ge_atTop (1 : ℝ)).filter_mono suzukiVerticalFilter_le_atTop] with y hsep hy
    exact (suzukiVerticalEnergy_eq ht hy hsep).symm
  have hgoal := Filter.Tendsto.congr' hEq hsum
  have hval : ((((((2 * (Real.exp (t / 2) - 1) + (-2) * (Real.exp (-(t / 2)) - 1) : ℝ) : ℂ)
        + 0) + -((suzukiCheckpointMass ⌊Real.exp t⌋₊ : ℝ) : ℂ))
        + (Complex.digamma (1 / 4) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2 + 0))
        + (1 / 2 : ℂ) * ((-2 * screwLerchTail₁ t : ℝ) : ℂ))
      = -((deriv (screwFn screwLinearCoeff screwLerchConst) t : ℝ) : ℂ) := by
    rw [hderiv]
    push_cast
    linear_combination (1 / 2 : ℂ) * digamma_quarter_sub_logPi
  rw [← hval]
  exact hgoal

end
end RHTower

