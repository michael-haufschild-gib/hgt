import GaloisForLFunctions.RHTower.WeilFiniteTypeContinuation
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIIEstimate
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIPieces
import GaloisForLFunctions.RHTower.Sieve.DivisorSumMeanSquareSmooth
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheZerosSeeEveryAtomicVectorThroughItsMobiusHorizons
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerIsPaidExactlyAtTheZerosOfZeta

/-!
# The short Vaughan cofactor at a zero of zeta

Summing the truncated divisor convolution along each divisor gives a zeta
partial sum at the real cutoff `W/d`. Its integral term depends on the
Möbius coefficients only through their harmonic sum. After removing this
term the multiplier at a zero differs from one by at most `C(s) V W^(-Re s)`.
-/

noncomputable section

open Complex Finset ArithmeticFunction Filter Topology
open RHTower.Sieve RHTower.WeilFiniteType
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (cpowPartialSum norm_cpowPartialSum_sub_le partialSumRate partialSumRate_nonneg ofReal_div_cpow)

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The integral of the constant density against the Mellin weight up to `W`. -/
private def cutoffIntegral (W : ℕ) (s : ℂ) : ℂ := (W : ℂ) ^ (1 - s) / (1 - s)

private theorem weighted_cell_error (a : ℝ) {W d : ℕ} (hd : 1 ≤ d) (hdW : d ≤ W)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖(a : ℂ) * (d : ℂ) ^ (-s) * cpowPartialSum s (W / d) -
        (a : ℂ) / d * cutoffIntegral W s -
        (a : ℂ) * (d : ℂ) ^ (-s) * riemannZeta s‖ ≤
      |a| * (partialSumRate s * (W : ℝ) ^ (-s.re)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (hd.trans hdW)
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfloor := (abs_le.mp (abs_natDiv_sub_div_le (N := W) hd)).1
  have he := norm_cpowPartialSum_sub_le hs hs1 ((Nat.one_le_div_iff hd).mpr hdW)
    (Nat.cast_div_le (m := W) (n := d) (α := ℝ)) (by linarith only [hfloor])
  have hmain : (d : ℂ) ^ (-s) * ((((W : ℝ) / d : ℝ) : ℂ) ^ (1 - s)) =
      (W : ℂ) ^ (1 - s) / d := by
    rw [ofReal_div_cpow hW0 hd0, Complex.ofReal_natCast, Complex.ofReal_natCast,
      mul_left_comm, ← Complex.cpow_add _ _ hdC, show -s + -(1 - s) = -1 by ring,
      Complex.cpow_neg_one, div_eq_mul_inv]
  have hfac : (a : ℂ) * (d : ℂ) ^ (-s) * cpowPartialSum s (W / d) -
      (a : ℂ) / d * cutoffIntegral W s - (a : ℂ) * (d : ℂ) ^ (-s) * riemannZeta s =
      (a : ℂ) * (d : ℂ) ^ (-s) *
        (cpowPartialSum s (W / d) - ((((W : ℝ) / d : ℝ) : ℂ) ^ (1 - s)) / (1 - s) -
          riemannZeta s) := by
    unfold cutoffIntegral
    linear_combination -(a : ℂ) / (1 - s) * hmain
  rw [hfac, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast_cpow_of_pos hd, Complex.neg_re]
  refine (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq ?_
  rw [Real.div_rpow hW0.le hd0.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hd0 (-s.re))]

/-- Quantitative multiplier formula for an arbitrary finite divisor weight.
The error depends on its total absolute mass. -/
theorem norm_dirPoly_zeta_convolution_sub_le (f : ArithmeticFunction ℝ) {W : ℕ}
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖dirPoly W ((zeta : ArithmeticFunction ℝ) * f) s -
        (∑ d ∈ Icc 1 W, (f d : ℂ) / d) * ((W : ℂ) ^ (1 - s) / (1 - s)) -
        dirPoly W f s * riemannZeta s‖ ≤
      (∑ d ∈ Icc 1 W, |f d|) * (partialSumRate s * (W : ℝ) ^ (-s.re)) := by
  have hexpand : dirPoly W ((zeta : ArithmeticFunction ℝ) * f) s =
      ∑ d ∈ Icc 1 W, (f d : ℂ) * (d : ℂ) ^ (-s) * cpowPartialSum s (W / d) := by
    unfold dirPoly
    simp_rw [ArithmeticFunction.coe_zeta_mul_apply, Complex.ofReal_sum]
    exact RenormalizedArithmeticPotentialTheory.sum_divisorSum_mul_cpow _ W s
  rw [hexpand, dirPoly, sum_mul, sum_mul, ← sum_sub_distrib, ← sum_sub_distrib, sum_mul]
  exact (norm_sum_le _ _).trans (sum_le_sum fun d hd =>
    weighted_cell_error _ (mem_Icc.mp hd).1 (mem_Icc.mp hd).2 hs hs1)

private theorem dirPoly_short_eq (V : ℕ) {W : ℕ} (hW : 1 ≤ W) (s : ℂ) :
    dirPoly W (typeIIShort V) s =
      1 - dirPoly W ((zeta : ArithmeticFunction ℝ) * truncAF moebius V) s := by
  unfold dirPoly
  have hsub (n : ℕ) : typeIIShort V n = (1 : ArithmeticFunction ℝ) n -
      ((zeta : ArithmeticFunction ℝ) * truncAF moebius V) n := rfl
  simp only [hsub, Complex.ofReal_sub, sub_mul, sum_sub_distrib]
  congr 1
  rw [sum_eq_single 1]
  · simp
  · intro n _ hn
    simp [ArithmeticFunction.one_apply, hn]
  · exact fun h => False.elim (h (mem_Icc.mpr ⟨le_rfl, hW⟩))

/-- The short cofactor Dirichlet polynomial with its finite cutoff pole removed. -/
def centredShortCofactor (V W : ℕ) (s : ℂ) : ℂ :=
  dirPoly W (typeIIShort V) s +
    (∑ d ∈ Icc 1 V, ((moebius : ArithmeticFunction ℝ) d : ℂ) / d) *
      ((W : ℂ) ^ (1 - s) / (1 - s))

/-- At every zero in the positive half-plane the centred short cofactor retains
unit amplitude, up to an explicit error uniform in both cutoffs. -/
theorem norm_centredShortCofactor_sub_one_le {V W : ℕ} (hW : 1 ≤ W) (hVW : V ≤ W)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ‖centredShortCofactor V W s - 1‖ ≤
      (V : ℝ) * (partialSumRate s * (W : ℝ) ^ (-s.re)) := by
  let μ := (moebius : ArithmeticFunction ℝ)
  have restrictSum {E : Type*} [AddCommMonoid E] (g : ℕ → ℝ → E) (hg : ∀ d, g d 0 = 0) :
      (∑ d ∈ Icc 1 W, g d (truncAF μ V d)) = ∑ d ∈ Icc 1 V, g d (μ d) := by
    rw [← sum_subset (Icc_subset_Icc_right hVW)
      (fun d hdW hdV => show g d (truncAF μ V d) = 0 by
        have hd : V < d := by
          have := (mem_Icc.mp hdW).1
          by_contra! h
          exact hdV (mem_Icc.mpr ⟨this, h⟩)
        rw [truncAF_apply_of_gt hd, hg])]
    apply sum_congr rfl
    intro d hd
    rw [truncAF_apply, if_pos (mem_Icc.mp hd).2]
  have he := norm_dirPoly_zeta_convolution_sub_le (W := W) (truncAF μ V) hs hs1
  rw [hz, mul_zero, sub_zero, restrictSum (fun d x => (x : ℂ) / d) (by simp),
    restrictSum (fun _ x => |x|) (by simp)] at he
  have hmass : (∑ d ∈ Icc 1 V, |μ d|) ≤ V := by
    calc
      _ ≤ ∑ _d ∈ Icc 1 V, (1 : ℝ) := sum_le_sum fun d hd => by
        simpa only [truncAF_apply, if_pos (mem_Icc.mp hd).2, μ] using abs_truncAF_moebius_le_one V d
      _ = V := by simp
  rw [centredShortCofactor, dirPoly_short_eq _ hW]
  rw [← norm_neg, show ∀ x y : ℂ, -(1 - x + y - 1) = x - y from fun x y => by ring]
  exact he.trans (mul_le_mul_of_nonneg_right hmass
    (mul_nonneg (partialSumRate_nonneg hs) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

/-- At two adjacent dyadic cutoffs, subtraction cancels the continuum term
exactly. This bound involves only the two raw Dirichlet polynomials. -/
theorem norm_dyadic_shortCofactor_sub_le {V W : ℕ} (hW : 1 ≤ W) (hVW : V ≤ W)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    let r := (2 : ℂ) ^ (1 - s)
    ‖dirPoly (2 * W) (typeIIShort V) s - r * dirPoly W (typeIIShort V) s - (1 - r)‖ ≤
      (1 + ‖r‖) * ((V : ℝ) * (partialSumRate s * (W : ℝ) ^ (-s.re))) := by
  intro r
  have hWd : W ≤ 2 * W := by omega
  have hpow : ((2 * W : ℕ) : ℂ) ^ (1 - s) = r * (W : ℂ) ^ (1 - s) := by
    simpa [r] using Complex.mul_cpow_ofReal_nonneg (by norm_num : 0 ≤ (2 : ℝ))
      (Nat.cast_nonneg W) (1 - s)
  have hid : dirPoly (2 * W) (typeIIShort V) s - r * dirPoly W (typeIIShort V) s - (1 - r) =
      (centredShortCofactor V (2 * W) s - 1) - r * (centredShortCofactor V W s - 1) := by
    unfold centredShortCofactor
    rw [hpow]
    ring
  have hsmall := norm_centredShortCofactor_sub_one_le hW hVW hs hs1 hz
  have hbig := norm_centredShortCofactor_sub_one_le (hW.trans hWd) (hVW.trans hWd) hs hs1 hz
  have hdec := Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hW : (0 : ℝ) < W)
    (by exact_mod_cast hWd : (W : ℝ) ≤ ((2 * W : ℕ) : ℝ)) (neg_nonpos.mpr hs.le)
  have hbig' := hbig.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hdec (partialSumRate_nonneg hs)) (Nat.cast_nonneg V))
  rw [hid]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, add_mul, one_mul]
  exact add_le_add hbig' (mul_le_mul_of_nonneg_left hsmall (norm_nonneg _))

end GaloisForLFunctions.ExceptionalLayerTheory
