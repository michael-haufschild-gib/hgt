import GaloisForLFunctions.RHTower.PrimeArchThetaThermalSusceptibility
import GaloisForLFunctions.HTGeometry.MonotoneLikelihoodRatio
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Likelihood-ratio order of the theta source atoms

This file records a source-specific `[BRIDGE]` from the exact Born--Witten equation to statistical
mechanics and reliability order.  On the open half-line, the logarithmic derivative of the `n`th
positive theta atom is `-2 * B_n`, where `B_n` is its Born--Witten superpotential.  The explicit
Morse formula makes `B_n` increasing in the atom index.  Consequently

`d/dx (thetaCuspSourceTerm x n / thetaCuspSourceTerm x 1)
  = -2 * (B_n x - B_1 x) *
      (thetaCuspSourceTerm x n / thetaCuspSourceTerm x 1)`.

The ratio is antitone for every `n >= 1` and strictly antitone for `n > 1`.  Summing the positive
higher atoms preserves this order: the complete higher-to-first density ratio is antitone.  The
division-free cross-product form is the two-point likelihood-ratio kernel needed to compare the
normalized first-atom and higher-tail expectations in the total-covariance decomposition.

The terminology is classical, not a novelty claim.  Karlin--McGregor total positivity and the
monotone-likelihood-ratio order supply the probability coordinate; the exact superpotential
difference and its theta-cusp application are proved here from the existing source formulas.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ### Index order of the exact Morse and Born--Witten coordinates -/

/-- The exponential Morse scale is monotone in the positive atom index. -/
theorem thetaCuspMorseScale_mono_nat
    {m n : ℕ} (hmn : m ≤ n) (x : ℝ) :
    thetaCuspMorseScale m x ≤ thetaCuspMorseScale n x := by
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hm0 : 0 ≤ (m : ℝ) * Real.exp x := by positivity
  have hmnExp : (m : ℝ) * Real.exp x ≤ (n : ℝ) * Real.exp x := by
    exact mul_le_mul_of_nonneg_right hmnR (Real.exp_pos x).le
  have hn0 : 0 ≤ (n : ℝ) * Real.exp x := hm0.trans hmnExp
  simp only [thetaCuspMorseScale]
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ hm0 hn0).2 hmnExp) Real.pi_pos.le

/-- Distinct positive atom indices give strictly ordered Morse scales. -/
theorem thetaCuspMorseScale_strictMono_nat
    {m n : ℕ} (hmn : m < n) (x : ℝ) :
    thetaCuspMorseScale m x < thetaCuspMorseScale n x := by
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hm0 : 0 ≤ (m : ℝ) * Real.exp x := by positivity
  have hprod : (m : ℝ) * Real.exp x < (n : ℝ) * Real.exp x :=
    mul_lt_mul_of_pos_right hmnR (Real.exp_pos x)
  have hsquare :
      ((m : ℝ) * Real.exp x) ^ 2 < ((n : ℝ) * Real.exp x) ^ 2 := by
    nlinarith
  simp only [thetaCuspMorseScale]
  exact mul_lt_mul_of_pos_left hsquare Real.pi_pos

/-- Exact positive-factor formula behind index monotonicity of the Born--Witten
superpotential. -/
theorem thetaCuspBornWittenSuperpotential_sub_eq_scaleDifference_mul
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenSuperpotential n x -
        thetaCuspBornWittenSuperpotential m x =
      (thetaCuspMorseScale n x - thetaCuspMorseScale m x) *
        (1 + (3 / 2 : ℝ) /
          (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x)) := by
  have hwn := thetaCuspBornWittenWeight_pos hn hx
  have hwm := thetaCuspBornWittenWeight_pos hm hx
  rw [thetaCuspBornWittenSuperpotential, thetaCuspBornWittenSuperpotential,
    thetaCuspMorseSuperpotential, thetaCuspMorseSuperpotential,
    thetaCuspBornWittenWeight_eq, thetaCuspBornWittenWeight_eq]
  field_simp [show thetaCuspMorseScale n x - 3 / 2 ≠ 0 by
      simpa only [← thetaCuspBornWittenWeight_eq] using hwn.ne',
    show thetaCuspMorseScale m x - 3 / 2 ≠ 0 by
      simpa only [← thetaCuspBornWittenWeight_eq] using hwm.ne']
  ring

/-- The Born--Witten superpotential is monotone in the positive atom index. -/
theorem thetaCuspBornWittenSuperpotential_mono_nat
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenSuperpotential m x ≤
      thetaCuspBornWittenSuperpotential n x := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hscale := thetaCuspMorseScale_mono_nat hmn x
  have hwn := thetaCuspBornWittenWeight_pos hn hx
  have hwm := thetaCuspBornWittenWeight_pos hm hx
  have hfactor : 0 ≤
      1 + (3 / 2 : ℝ) /
        (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x) := by
    positivity
  rw [← sub_nonneg]
  rw [thetaCuspBornWittenSuperpotential_sub_eq_scaleDifference_mul hm hn hx]
  exact mul_nonneg (sub_nonneg.mpr hscale) hfactor

/-- Distinct positive atom indices give strictly ordered Born--Witten superpotentials. -/
theorem thetaCuspBornWittenSuperpotential_strictMono_nat
    {m n : ℕ} (hm : 0 < m) (hmn : m < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenSuperpotential m x <
      thetaCuspBornWittenSuperpotential n x := by
  have hn : 0 < n := lt_trans hm hmn
  have hscale := thetaCuspMorseScale_strictMono_nat hmn x
  have hwn := thetaCuspBornWittenWeight_pos hn hx
  have hwm := thetaCuspBornWittenWeight_pos hm hx
  have hfactor : 0 <
      1 + (3 / 2 : ℝ) /
        (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x) := by
    positivity
  rw [← sub_pos]
  rw [thetaCuspBornWittenSuperpotential_sub_eq_scaleDifference_mul hm hn hx]
  exact mul_pos (sub_pos.mpr hscale) hfactor

/-! ### Source score and atom likelihood ratios -/

/-- Every positive atom is an exact translated copy of the first source profile, up to the
positive half-density factor.  This is the residual-life/aging coordinate behind the
likelihood-ratio order. -/
theorem thetaCuspSourceTerm_shift_one
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    thetaCuspSourceTerm (x + Real.log (n : ℝ)) 1 =
      Real.exp (Real.log (n : ℝ) / 2) * thetaCuspSourceTerm x n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold thetaCuspSourceTerm
  rw [show Real.exp (x + Real.log (n : ℝ)) =
      (n : ℝ) * Real.exp x by
    rw [Real.exp_add, Real.exp_log hnR]
    ring]
  rw [show Real.exp ((x + Real.log (n : ℝ)) / 2) =
      Real.exp (Real.log (n : ℝ) / 2) * Real.exp (x / 2) by
    rw [show (x + Real.log (n : ℝ)) / 2 =
        Real.log (n : ℝ) / 2 + x / 2 by ring, Real.exp_add]]
  simp only [Nat.cast_one, one_mul]
  ring

/-- The source density inherits twice the exact Born--Witten logarithmic score. -/
theorem hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => thetaCuspSourceTerm y n)
      (-2 * thetaCuspBornWittenSuperpotential n x *
        thetaCuspSourceTerm x n) x := by
  have heq :
      (fun y : ℝ => thetaCuspSourceTerm y n) =ᶠ[nhds x]
        fun y : ℝ => Real.pi * thetaCuspBornWittenAmplitude n y ^ 2 := by
    filter_upwards [show ∀ᶠ y : ℝ in nhds x, y ∈ Ioi 0 from Ioi_mem_nhds hx] with y hy
    exact thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq hn hy.le
  have hamp : HasDerivAt
      (fun y : ℝ => Real.pi * thetaCuspBornWittenAmplitude n y ^ 2)
      (Real.pi * (-2 * thetaCuspBornWittenSuperpotential n x *
        thetaCuspBornWittenAmplitude n x ^ 2)) x :=
    (hasDerivAt_thetaCuspBornWittenAmplitude_sq hn hx.le).const_mul Real.pi
  have hsource := hamp.congr_of_eventuallyEq heq
  convert hsource using 1
  rw [thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq hn hx.le]
  ring

/-- Density ratio of the `n`th theta atom against the first atom. -/
def thetaCuspAtomLikelihoodRatio (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspSourceTerm x n / thetaCuspSourceTerm x 1

theorem thetaCuspAtomLikelihoodRatio_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspAtomLikelihoodRatio n x := by
  exact div_pos
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hn)
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num))

/-- Exact score-difference equation for one atom likelihood ratio. -/
theorem hasDerivAt_thetaCuspAtomLikelihoodRatio
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspAtomLikelihoodRatio n)
      (-2 * (thetaCuspBornWittenSuperpotential n x -
          thetaCuspBornWittenSuperpotential 1 x) *
        thetaCuspAtomLikelihoodRatio n x) x := by
  have hnDeriv := hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore hn hx
  have hfirstDeriv := hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore
    (n := 1) (by norm_num) hx
  have hfirst := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hx (by norm_num)
  have hquot := hnDeriv.div hfirstDeriv hfirst.ne'
  convert hquot using 1
  simp only [thetaCuspAtomLikelihoodRatio]
  field_simp [hfirst.ne']
  ring

theorem deriv_thetaCuspAtomLikelihoodRatio
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    deriv (thetaCuspAtomLikelihoodRatio n) x =
      -2 * (thetaCuspBornWittenSuperpotential n x -
          thetaCuspBornWittenSuperpotential 1 x) *
        thetaCuspAtomLikelihoodRatio n x :=
  (hasDerivAt_thetaCuspAtomLikelihoodRatio hn hx).deriv

theorem deriv_thetaCuspAtomLikelihoodRatio_nonpos
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    deriv (thetaCuspAtomLikelihoodRatio n) x ≤ 0 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hB := thetaCuspBornWittenSuperpotential_mono_nat
    (m := 1) (n := n) (by norm_num) hn hx.le
  have hratio := (thetaCuspAtomLikelihoodRatio_pos hnpos hx).le
  rw [deriv_thetaCuspAtomLikelihoodRatio hnpos hx]
  have hprod : 0 ≤
      (thetaCuspBornWittenSuperpotential n x -
        thetaCuspBornWittenSuperpotential 1 x) *
          thetaCuspAtomLikelihoodRatio n x :=
    mul_nonneg (sub_nonneg.mpr hB) hratio
  nlinarith

theorem deriv_thetaCuspAtomLikelihoodRatio_neg
    {n : ℕ} (hn : 1 < n) {x : ℝ} (hx : 0 < x) :
    deriv (thetaCuspAtomLikelihoodRatio n) x < 0 := by
  have hB := thetaCuspBornWittenSuperpotential_strictMono_nat
    (m := 1) (n := n) (by norm_num) hn hx.le
  have hratio := thetaCuspAtomLikelihoodRatio_pos (lt_trans (by norm_num) hn) hx
  rw [deriv_thetaCuspAtomLikelihoodRatio (lt_trans (by norm_num) hn) hx]
  have hprod : 0 <
      (thetaCuspBornWittenSuperpotential n x -
        thetaCuspBornWittenSuperpotential 1 x) *
          thetaCuspAtomLikelihoodRatio n x :=
    mul_pos (sub_pos.mpr hB) hratio
  nlinarith

/-- Every positive atom has an antitone likelihood ratio against the first atom. -/
theorem thetaCuspAtomLikelihoodRatio_antitoneOn
    {n : ℕ} (hn : 1 ≤ n) :
    AntitoneOn (thetaCuspAtomLikelihoodRatio n) (Ioi 0) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_thetaCuspAtomLikelihoodRatio hnpos hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_thetaCuspAtomLikelihoodRatio hnpos hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact deriv_thetaCuspAtomLikelihoodRatio_nonpos hn hx

/-- Every atom strictly above the first has a strictly antitone likelihood ratio. -/
theorem thetaCuspAtomLikelihoodRatio_strictAntiOn
    {n : ℕ} (hn : 1 < n) :
    StrictAntiOn (thetaCuspAtomLikelihoodRatio n) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_thetaCuspAtomLikelihoodRatio
      (lt_trans (by norm_num) hn) hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact deriv_thetaCuspAtomLikelihoodRatio_neg hn hx

/-! ### The complete higher tail and its division-free ordering kernel -/

/-- Likelihood ratio of the complete higher-atom tail against the first atom. -/
def thetaCuspHigherToFirstAtomLikelihoodRatio (x : ℝ) : ℝ :=
  (thetaCuspFullSource x - thetaCuspSourceTerm x 1) /
    thetaCuspSourceTerm x 1

theorem summable_thetaCuspHigherAtomLikelihoodRatios (x : ℝ) :
    Summable (fun k : ℕ => thetaCuspAtomLikelihoodRatio (k + 2) x) := by
  have hs := summable_thetaCuspSourceTerm x
  have htail : Summable (fun k : ℕ => thetaCuspSourceTerm x (k + 2)) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  simpa only [thetaCuspAtomLikelihoodRatio] using
    htail.div_const (thetaCuspSourceTerm x 1)

/-- The higher-to-first ratio is the sum of the individual positive-atom ratios. -/
theorem thetaCuspHigherToFirstAtomLikelihoodRatio_eq_tsum (x : ℝ) :
    thetaCuspHigherToFirstAtomLikelihoodRatio x =
      ∑' k : ℕ, thetaCuspAtomLikelihoodRatio (k + 2) x := by
  have hs := summable_thetaCuspSourceTerm x
  have hhead :
      (∑ n ∈ Finset.range 2, thetaCuspSourceTerm x n) =
        thetaCuspSourceTerm x 1 := by
    calc
      (∑ n ∈ Finset.range 2, thetaCuspSourceTerm x n) =
          thetaCuspSourceTerm x 0 + thetaCuspSourceTerm x 1 := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      _ = thetaCuspSourceTerm x 1 := by
        simp [thetaCuspSourceTerm, thetaCuspSeed]
  have htail :
      thetaCuspFullSource x - thetaCuspSourceTerm x 1 =
        ∑' k : ℕ, thetaCuspSourceTerm x (k + 2) := by
    rw [thetaCuspFullSource, ← hs.sum_add_tsum_nat_add 2, hhead]
    ring
  rw [thetaCuspHigherToFirstAtomLikelihoodRatio, htail]
  simpa only [thetaCuspAtomLikelihoodRatio] using
    (tsum_div_const (f := fun k : ℕ => thetaCuspSourceTerm x (k + 2))
      (a := thetaCuspSourceTerm x 1)).symm

/-- Positive summation preserves the monotone-likelihood-ratio order for the complete higher
tail. -/
theorem thetaCuspHigherToFirstAtomLikelihoodRatio_antitoneOn :
    AntitoneOn thetaCuspHigherToFirstAtomLikelihoodRatio (Ioi 0) := by
  intro x hx y hy hxy
  rw [thetaCuspHigherToFirstAtomLikelihoodRatio_eq_tsum,
    thetaCuspHigherToFirstAtomLikelihoodRatio_eq_tsum]
  exact Summable.tsum_le_tsum
    (fun k => thetaCuspAtomLikelihoodRatio_antitoneOn
      (n := k + 2) (by omega) hx hy hxy)
    (summable_thetaCuspHigherAtomLikelihoodRatios y)
    (summable_thetaCuspHigherAtomLikelihoodRatios x)

/-- Division-free two-point likelihood-ratio order of the complete higher tail against the first
atom.  This is the kernel that can be integrated without dividing by either density. -/
theorem thetaCuspHigherFirst_crossProduct_order
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (thetaCuspFullSource y - thetaCuspSourceTerm y 1) *
        thetaCuspSourceTerm x 1 ≤
      (thetaCuspFullSource x - thetaCuspSourceTerm x 1) *
        thetaCuspSourceTerm y 1 := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hratio := thetaCuspHigherToFirstAtomLikelihoodRatio_antitoneOn hx hy hxy
  have hfirstX := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hx (by norm_num)
  have hfirstY := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hy (by norm_num)
  exact (div_le_div_iff₀ hfirstY hfirstX).mp hratio

/-- Every increasing observable has a nonnegative two-sample kernel against the higher/first
likelihood-ratio order.  Integrating this kernel is the remaining standard route to normalized
expectation order and hence to the sign of the between-atom covariance term. -/
theorem thetaCuspHigherFirst_monotoneObservableKernel_nonneg
    {g : ℝ → ℝ} (hg : MonotoneOn g (Ioi 0))
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ (g y - g x) *
      ((thetaCuspFullSource x - thetaCuspSourceTerm x 1) *
          thetaCuspSourceTerm y 1 -
        (thetaCuspFullSource y - thetaCuspSourceTerm y 1) *
          thetaCuspSourceTerm x 1) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  exact mul_nonneg
    (sub_nonneg.mpr (hg hx hy hxy))
    (sub_nonneg.mpr (thetaCuspHigherFirst_crossProduct_order hx hxy))

/-! ### Integrated application to the existing total-covariance decomposition -/

/-- Every even-power insertion against the positive higher-atom source is integrable. -/
theorem integrableOn_pow_mul_thetaCuspHigherSource (j : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * j) *
      (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) (Ioi 0) := by
  have hfull := integrableOn_thetaCuspRawMoment (2 * j)
  have hfirst := integrableOn_pow_mul_thetaCuspSourceTerm j 1
  have hsub := hfull.sub hfirst
  apply hsub.congr
  filter_upwards [] with x
  ring

/-- Integral representation of the higher-atom raw moment, separated from the first atom. -/
theorem thetaCuspHigherAtomRawEvenMoment_eq_integral_higherSource (j : ℕ) :
    thetaCuspHigherAtomRawEvenMoment j =
      2 * ∫ x : ℝ in Ioi 0,
        x ^ (2 * j) *
          (thetaCuspFullSource x - thetaCuspSourceTerm x 1) := by
  have hfull := integrableOn_thetaCuspRawMoment (2 * j)
  have hfirst := integrableOn_pow_mul_thetaCuspSourceTerm j 1
  rw [thetaCuspHigherAtomRawEvenMoment, thetaCuspRawEvenMoment,
    thetaCuspAtomRawEvenMoment, ← mul_sub, ← integral_sub hfull hfirst]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The likelihood-ratio kernel orders every power moment in every size-biased first/tail pair.
This is the division-free moment form consumed by normalized expectations. -/
theorem thetaCuspHigherFirst_rawEvenMoment_cross_le (k n : ℕ) :
    thetaCuspHigherAtomRawEvenMoment (k + n) *
        thetaCuspAtomRawEvenMoment k 1 ≤
      thetaCuspAtomRawEvenMoment (k + n) 1 *
        thetaCuspHigherAtomRawEvenMoment k := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x =>
    x ^ (2 * k) * thetaCuspSourceTerm x 1
  let h : ℝ → ℝ := fun x =>
    x ^ (2 * k) *
      (thetaCuspFullSource x - thetaCuspSourceTerm x 1)
  let g : ℝ → ℝ := fun x => x ^ (2 * n)
  have hf : Integrable f mu := by
    simpa only [f, mu] using integrableOn_pow_mul_thetaCuspSourceTerm k 1
  have hh : Integrable h mu := by
    simpa only [h, mu] using integrableOn_pow_mul_thetaCuspHigherSource k
  have hgf : Integrable (fun x => g x * f x) mu := by
    have hbase := integrableOn_pow_mul_thetaCuspSourceTerm (k + n) 1
    apply hbase.congr
    filter_upwards [] with x
    simp only [g, f, mu]
    rw [show 2 * (k + n) = 2 * n + 2 * k by omega, pow_add]
    ring
  have hgh : Integrable (fun x => g x * h x) mu := by
    have hbase := integrableOn_pow_mul_thetaCuspHigherSource (k + n)
    apply hbase.congr
    filter_upwards [] with x
    simp only [g, h, mu]
    rw [show 2 * (k + n) = 2 * n + 2 * k by omega, pow_add]
    ring
  have hgmono : MonotoneOn g (Ioi 0) := by
    intro x hx y hy hxy
    exact pow_le_pow_left₀ hx.le hxy (2 * n)
  have hmem : ∀ᶠ z : ℝ × ℝ ∂mu.prod mu,
      z ∈ (Ioi 0 ×ˢ Ioi 0) := by
    apply (ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ⟨hx, hy⟩
  have hkernel : ∀ᶠ z : ℝ × ℝ ∂mu.prod mu,
      0 ≤ (g z.2 - g z.1) *
        (h z.1 * f z.2 - h z.2 * f z.1) := by
    filter_upwards [hmem] with z hz
    rcases hz with ⟨hx, hy⟩
    have hbase : 0 ≤
        (g z.2 - g z.1) *
          ((thetaCuspFullSource z.1 - thetaCuspSourceTerm z.1 1) *
              thetaCuspSourceTerm z.2 1 -
            (thetaCuspFullSource z.2 - thetaCuspSourceTerm z.2 1) *
              thetaCuspSourceTerm z.1 1) := by
      rcases le_total z.1 z.2 with hxy | hyx
      · exact thetaCuspHigherFirst_monotoneObservableKernel_nonneg hgmono hx hxy
      · have hswap := thetaCuspHigherFirst_monotoneObservableKernel_nonneg
          hgmono hy hyx
        convert hswap using 1 <;> ring
    have hweight : 0 ≤ z.1 ^ (2 * k) * z.2 ^ (2 * k) := by positivity
    have hweighted := mul_nonneg hweight hbase
    simp only [g, h, f]
    convert hweighted using 1 <;> ring
  have hcross := HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel
    hf hh hgf hgh hkernel
  have hgf_eq :
      (∫ x, g x * f x ∂mu) =
        ∫ x : ℝ in Ioi 0,
          x ^ (2 * (k + n)) * thetaCuspSourceTerm x 1 := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g, f, mu]
    rw [show 2 * (k + n) = 2 * n + 2 * k by omega, pow_add]
    ring
  have hgh_eq :
      (∫ x, g x * h x ∂mu) =
        ∫ x : ℝ in Ioi 0,
          x ^ (2 * (k + n)) *
            (thetaCuspFullSource x - thetaCuspSourceTerm x 1) := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g, h, mu]
    rw [show 2 * (k + n) = 2 * n + 2 * k by omega, pow_add]
    ring
  rw [hgf_eq, hgh_eq] at hcross
  rw [thetaCuspHigherAtomRawEvenMoment_eq_integral_higherSource,
    thetaCuspHigherAtomRawEvenMoment_eq_integral_higherSource,
    thetaCuspAtomRawEvenMoment, thetaCuspAtomRawEvenMoment]
  change (2 * ∫ x : ℝ in Ioi 0,
      x ^ (2 * (k + n)) *
        (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) *
      (2 * ∫ x : ℝ in Ioi 0,
        x ^ (2 * k) * thetaCuspSourceTerm x 1) ≤
    (2 * ∫ x : ℝ in Ioi 0,
      x ^ (2 * (k + n)) * thetaCuspSourceTerm x 1) *
      (2 * ∫ x : ℝ in Ioi 0,
        x ^ (2 * k) *
          (thetaCuspFullSource x - thetaCuspSourceTerm x 1))
  dsimp only [f, h, mu] at hcross
  nlinarith

/-- Every power expectation in a size-biased higher-atom state is at most the corresponding
first-atom expectation.  This discharges the common-sign input in the total-covariance term. -/
theorem thetaCuspHigherAtomSizeBiasedPowerExpectation_le_first
    (k n : ℕ) :
    HTGeometry.momentNormalizedExpectation
        (thetaCuspHigherAtomSizeBiasedSequence k) (X ^ n) ≤
      HTGeometry.momentNormalizedExpectation
        (thetaCuspFirstAtomSizeBiasedSequence k) (X ^ n) := by
  rw [thetaCuspHigherAtomSizeBiasedSequence,
    thetaCuspFirstAtomSizeBiasedSequence,
    HTGeometry.momentNormalizedExpectation_X_pow_sizeBiased,
    HTGeometry.momentNormalizedExpectation_X_pow_sizeBiased]
  exact (div_le_div_iff₀
    (thetaCuspHigherAtomRawEvenMoment_pos k)
    (thetaCuspAtomRawEvenMoment_pos_of_nat_pos k (n := 1) (by norm_num))).2
      (thetaCuspHigherFirst_rawEvenMoment_cross_le k n)

/-- The between-atom factor in the existing total-covariance decomposition is nonnegative for
every size bias and every power observable. -/
theorem thetaCuspFirstHigher_betweenPowerFactor_nonneg (k n : ℕ) :
    0 ≤
      (HTGeometry.momentNormalizedExpectation
          (thetaCuspFirstAtomSizeBiasedSequence k) X -
        HTGeometry.momentNormalizedExpectation
          (thetaCuspHigherAtomSizeBiasedSequence k) X) *
      (HTGeometry.momentNormalizedExpectation
          (thetaCuspFirstAtomSizeBiasedSequence k) (X ^ n) -
        HTGeometry.momentNormalizedExpectation
          (thetaCuspHigherAtomSizeBiasedSequence k) (X ^ n)) := by
  apply mul_nonneg
  · exact sub_nonneg.mpr (by
      simpa using
        thetaCuspHigherAtomSizeBiasedPowerExpectation_le_first k 1)
  · exact sub_nonneg.mpr
      (thetaCuspHigherAtomSizeBiasedPowerExpectation_le_first k n)

/-- Direct strengthening of the existing theta law of total covariance: the full power response
dominates the sum of its two weighted within-component responses because the newly ordered
between-component term is nonnegative. -/
theorem thetaCuspSizeBiasPowerCovariance_within_le (k n : ℕ) :
    thetaCuspFirstAtomSizeBiasedSequence k 0 /
          (thetaCuspFirstAtomSizeBiasedSequence k 0 +
            thetaCuspHigherAtomSizeBiasedSequence k 0) *
          HTGeometry.momentNormalizedCovariance
            (thetaCuspFirstAtomSizeBiasedSequence k) X (X ^ n) +
        thetaCuspHigherAtomSizeBiasedSequence k 0 /
          (thetaCuspFirstAtomSizeBiasedSequence k 0 +
            thetaCuspHigherAtomSizeBiasedSequence k 0) *
          HTGeometry.momentNormalizedCovariance
            (thetaCuspHigherAtomSizeBiasedSequence k) X (X ^ n) ≤
      thetaCuspSizeBiasPowerCovariance k n := by
  have hcoeff : 0 ≤
      thetaCuspFirstAtomSizeBiasedSequence k 0 *
          thetaCuspHigherAtomSizeBiasedSequence k 0 /
        (thetaCuspFirstAtomSizeBiasedSequence k 0 +
          thetaCuspHigherAtomSizeBiasedSequence k 0) ^ 2 :=
    div_nonneg
      (mul_nonneg
        (thetaCuspFirstAtomSizeBiasedSequence_zero_pos k).le
        (thetaCuspHigherAtomSizeBiasedSequence_zero_pos k).le)
      (sq_nonneg _)
  have hbetween := mul_nonneg hcoeff
    (thetaCuspFirstHigher_betweenPowerFactor_nonneg k n)
  rw [thetaCuspSizeBiasPowerCovariance_eq_within_add_between]
  exact le_add_of_nonneg_right (by
    simpa only [mul_assoc] using hbetween)

end
end RHTower
