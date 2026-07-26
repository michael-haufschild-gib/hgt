import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticPairCurrent
import GaloisForLFunctions.RHTower.PrimeLambertMobiusInversion

/-!
# Möbius constraint for the canonical theta-tail density

The logarithmic-translate expansion of the differentiated theta tail is a Dirichlet convolution.
On this particular Gaussian source the convolution has an absolutely convergent Möbius inverse at
the critical half-density weight.  This is a static signed constraint on the complete canonical
density, not a positivity assertion.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial ArithmeticFunction Nat
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Multiplying the integer label is the same as applying the corresponding critical logarithmic
shift to the remaining density atom. -/
theorem thetaCuspTailSecondDensityAtom_pnat_mul
    (n m : ℕ+) (x : ℝ) :
    thetaCuspTailSecondDensityAtom (n * m) x =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensityAtom m (x + Real.log n) := by
  have hn : 0 < (n : ℕ) := n.pos
  have hm : 0 < (m : ℕ) := m.pos
  change thetaCuspTailSecondDensityAtom ((n : ℕ) * (m : ℕ)) x = _
  rw [thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate
      (n := (n : ℕ) * (m : ℕ)) (Nat.mul_pos hn hm),
    thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate (n := (m : ℕ)) hm]
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg m),
    Real.log_mul (by exact_mod_cast n.ne_zero) (by exact_mod_cast m.ne_zero)]
  ring_nf

theorem summable_thetaCuspTailSecondDensityAtom_pnat (x : ℝ) :
    Summable (fun n : ℕ+ => thetaCuspTailSecondDensityAtom n x) := by
  have hnat : Summable
      (fun k : ℕ => thetaCuspTailSecondDensityAtom (k + 1) x) := by
    unfold thetaCuspTailSecondDensityAtom
    simpa only using (summable_thetaCuspTailDerivative 2 x).mul_left 4
  have h := (Equiv.pnatEquivNat.summable_iff).mpr hnat
  apply h.congr
  intro n
  simp only [Function.comp_apply, Equiv.pnatEquivNat_apply]
  rw [PNat.natPred_add_one]

private theorem summable_thetaCuspTailSecondDensityAtom_pnat_mul
    (n : ℕ+) (x : ℝ) :
    Summable (fun m : ℕ+ => thetaCuspTailSecondDensityAtom (n * m) x) := by
  apply ((summable_thetaCuspTailSecondDensityAtom_pnat
    (x + Real.log n)).mul_left ((n : ℝ) ^ (-(1 / 2 : ℝ)))).congr
  intro m
  exact (thetaCuspTailSecondDensityAtom_pnat_mul n m x).symm

/-- The atom row indexed by multiples of `n` sums to the correspondingly shifted full density. -/
theorem tsum_thetaCuspTailSecondDensityAtom_pnat_mul
    (n : ℕ+) (x : ℝ) :
    (∑' m : ℕ+, thetaCuspTailSecondDensityAtom (n * m) x) =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensity (x + Real.log n) := by
  rw [show (fun m : ℕ+ => thetaCuspTailSecondDensityAtom (n * m) x) =
      fun m : ℕ+ => (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensityAtom m (x + Real.log n) by
    funext m
    exact thetaCuspTailSecondDensityAtom_pnat_mul n m x]
  rw [tsum_mul_left]
  rw [thetaCuspTailSecondDensity_eq_tsum_atom]
  congr 1
  simpa only [Equiv.pnatEquivNat_apply, PNat.natPred_add_one] using
    (Equiv.tsum_eq Equiv.pnatEquivNat
      (fun k : ℕ => thetaCuspTailSecondDensityAtom (k + 1)
        (x + Real.log n)))

/-- Auxiliary sequence that turns ordinary Möbius inversion into the already formalized weighted
Lambert inversion. -/
def thetaCuspTailSecondDensityMobiusAux (x : ℝ) (n : ℕ+) : ℂ :=
  (thetaCuspTailSecondDensityAtom n x : ℂ) / (n : ℂ)

/-- On the positive logarithmic half-line the auxiliary atom sequence has a geometric majorant.
The actual decay is Gaussian; the weaker geometric form is exactly what the absolute Lambert
inversion theorem consumes. -/
theorem norm_thetaCuspTailSecondDensityMobiusAux_le_geometric
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ+) :
    ‖thetaCuspTailSecondDensityMobiusAux x n‖ ≤
      (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) *
        (Real.exp (-(Real.pi / 2))) ^ (n : ℕ) := by
  let P : ℝ[X] := thetaCuspTailDerivativePolynomial 2
  let C : ℝ := thetaCuspGaussianConstant P
  have hnR : (1 : ℝ) ≤ (n : ℕ) := by
    exact_mod_cast (show 0 < (n : ℕ) from n.pos)
  have hnPos : (0 : ℝ) < (n : ℕ) := lt_of_lt_of_le zero_lt_one hnR
  have hC : 0 ≤ C := thetaCuspGaussianConstant_nonneg P
  have hatom := exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos
    P hx n.pos
  have hgauss :
      Real.exp (-(Real.pi / 2) * ((n : ℝ) ^ 2)) ≤
        (Real.exp (-(Real.pi / 2))) ^ (n : ℕ) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hpi : 0 < Real.pi / 2 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) hnPos.le]
  have hatom' :
      |thetaCuspPolynomialAtom P n x| ≤
        C * Real.exp (-x) *
          Real.exp (-(Real.pi / 2) * ((n : ℝ) ^ 2)) := by
    calc
      |thetaCuspPolynomialAtom P n x| =
          Real.exp (-x) *
            (Real.exp x * |thetaCuspPolynomialAtom P n x|) := by
              rw [← mul_assoc, ← Real.exp_add]
              simp
      _ ≤ Real.exp (-x) *
          (C * Real.exp (-(Real.pi / 2) * ((n : ℝ) ^ 2))) := by
            exact mul_le_mul_of_nonneg_left hatom (Real.exp_pos _).le
      _ = C * Real.exp (-x) *
          Real.exp (-(Real.pi / 2) * ((n : ℝ) ^ 2)) := by ring
  rw [show ‖thetaCuspTailSecondDensityMobiusAux x n‖ =
      4 * |thetaCuspPolynomialAtom P n x| / (n : ℝ) by
    simp [thetaCuspTailSecondDensityMobiusAux,
      thetaCuspTailSecondDensityAtom, P, Real.norm_eq_abs]]
  calc
    4 * |thetaCuspPolynomialAtom P n x| / (n : ℝ) ≤
        4 * |thetaCuspPolynomialAtom P n x| := by
      exact div_le_self (mul_nonneg (by norm_num) (abs_nonneg _)) hnR
    _ ≤ 4 * (C * Real.exp (-x) *
        Real.exp (-(Real.pi / 2) * ((n : ℝ) ^ 2))) := by gcongr
    _ ≤ 4 * (C * Real.exp (-x) *
        (Real.exp (-(Real.pi / 2))) ^ (n : ℕ)) := by gcongr
    _ = (4 * C * Real.exp (-x)) *
        (Real.exp (-(Real.pi / 2))) ^ (n : ℕ) := by ring

theorem thetaCuspTailSecondDensityAtom_le_geometric
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ+) :
    thetaCuspTailSecondDensityAtom k x ≤
      (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) * (k : ℝ) *
        (Real.exp (-(Real.pi / 2))) ^ (k : ℕ) := by
  have h := norm_thetaCuspTailSecondDensityMobiusAux_le_geometric hx k
  have hatom : 0 ≤ thetaCuspTailSecondDensityAtom k x :=
    (thetaCuspTailSecondDensityAtom_pos k.pos hx).le
  rw [thetaCuspTailSecondDensityMobiusAux] at h
  simp only [norm_div, Complex.norm_real, Complex.norm_natCast,
    Real.norm_eq_abs, abs_of_nonneg hatom] at h
  calc
    thetaCuspTailSecondDensityAtom k x =
        (thetaCuspTailSecondDensityAtom k x / (k : ℝ)) * (k : ℝ) := by
          field_simp
    _ ≤ ((4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) * (Real.exp (-(Real.pi / 2))) ^ (k : ℕ)) *
        (k : ℝ) := by gcongr
    _ = _ := by ring

theorem summable_pnat_geometric_firstMoment :
    Summable (fun m : ℕ+ =>
      (m : ℝ) * (Real.exp (-(Real.pi / 2))) ^ ((m : ℕ) - 1)) := by
  have hpi : 0 < Real.pi / 2 := by positivity
  have h0 := summable_pow_mul_exp_neg_nat_mul 0 hpi
  have h1 := summable_pow_mul_exp_neg_nat_mul 1 hpi
  have hnat : Summable (fun n : ℕ =>
      (n + 1 : ℝ) * (Real.exp (-(Real.pi / 2))) ^ n) := by
    apply (h1.add h0).congr
    intro n
    simp only [pow_one, pow_zero, one_mul]
    rw [← Real.exp_nat_mul]
    ring_nf
  have h := (Equiv.pnatEquivNat.summable_iff).mpr hnat
  apply h.congr
  intro m
  simp only [Function.comp_apply, Equiv.pnatEquivNat_apply]
  have hm : m.natPred + 1 = (m : ℕ) := PNat.natPred_add_one m
  have hcast : (m.natPred : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hm
  have hsub : (m : ℕ) - 1 = m.natPred := by omega
  rw [hcast, hsub]

theorem thetaCuspTailSecondDensityAtom_mul_le_geometric
    {x : ℝ} (hx : 0 ≤ x) (n m : ℕ+) :
    thetaCuspTailSecondDensityAtom (n * m) x ≤
      (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) * (n : ℝ) *
        (Real.exp (-(Real.pi / 2))) ^ (n : ℕ) *
          ((m : ℝ) *
            (Real.exp (-(Real.pi / 2))) ^ ((m : ℕ) - 1)) := by
  let q : ℝ := Real.exp (-(Real.pi / 2))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos]
  have hexp : (n : ℕ) + ((m : ℕ) - 1) ≤ (n * m : ℕ) := by
    have hn1 : 1 ≤ (n : ℕ) := n.pos
    have hmpos : 0 < (m : ℕ) := m.pos
    have hm : (m : ℕ) = (m : ℕ) - 1 + 1 := by omega
    have hmul : 1 * ((m : ℕ) - 1) ≤ (n : ℕ) * ((m : ℕ) - 1) :=
      Nat.mul_le_mul_right ((m : ℕ) - 1) hn1
    calc
      (n : ℕ) + ((m : ℕ) - 1) ≤
          (n : ℕ) + (n : ℕ) * ((m : ℕ) - 1) := by omega
      _ = (n : ℕ) * ((m : ℕ) - 1) + (n : ℕ) := by omega
      _ = (n : ℕ) * (((m : ℕ) - 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = (n : ℕ) * (m : ℕ) := by rw [← hm]
  have hpow : q ^ (n * m : ℕ) ≤
      q ^ ((n : ℕ) + ((m : ℕ) - 1)) :=
    pow_le_pow_of_le_one hq0 hq1 hexp
  have hatom := thetaCuspTailSecondDensityAtom_le_geometric hx (n * m)
  dsimp [q] at hpow ⊢
  calc
    thetaCuspTailSecondDensityAtom (n * m) x ≤
        (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) * ((n * m : ℕ+) : ℝ) *
            Real.exp (-(Real.pi / 2)) ^ ((n * m : ℕ+) : ℕ) := hatom
    _ ≤ (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) * ((n * m : ℕ+) : ℝ) *
            Real.exp (-(Real.pi / 2)) ^ ((n : ℕ) + ((m : ℕ) - 1)) := by
      apply mul_le_mul_of_nonneg_left hpow
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (thetaCuspGaussianConstant_nonneg _))
          (Real.exp_pos _).le)
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [pow_add]
      push_cast
      ring

theorem criticalThetaCuspDensityTranslate_le_geometric
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ+) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensity (x + Real.log n) ≤
      (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) * (n : ℝ) *
        (Real.exp (-(Real.pi / 2))) ^ (n : ℕ) *
          ∑' m : ℕ+, (m : ℝ) *
            (Real.exp (-(Real.pi / 2))) ^ ((m : ℕ) - 1) := by
  rw [← tsum_thetaCuspTailSecondDensityAtom_pnat_mul]
  let C : ℝ := (4 * thetaCuspGaussianConstant
      (thetaCuspTailDerivativePolynomial 2) * Real.exp (-x)) *
        (n : ℝ) * (Real.exp (-(Real.pi / 2))) ^ (n : ℕ)
  rw [show C * ∑' m : ℕ+, (m : ℝ) *
      (Real.exp (-(Real.pi / 2))) ^ ((m : ℕ) - 1) =
        ∑' m : ℕ+, C * ((m : ℝ) *
          (Real.exp (-(Real.pi / 2))) ^ ((m : ℕ) - 1)) by
    rw [tsum_mul_left]]
  apply Summable.tsum_le_tsum
  · intro m
    exact thetaCuspTailSecondDensityAtom_mul_le_geometric hx n m
  · exact summable_thetaCuspTailSecondDensityAtom_pnat_mul n x
  · exact summable_pnat_geometric_firstMoment.mul_left C

theorem summable_thetaCuspTailSecondDensityMobiusPair
    {x : ℝ} (hx : 0 ≤ x) :
    Summable (weightedLambertMobiusPair
      (thetaCuspTailSecondDensityMobiusAux x)) := by
  apply weightedLambertMobiusPair_summable_of_geometric
    (thetaCuspTailSecondDensityMobiusAux x)
    (4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
      Real.exp (-x))
    (Real.exp (-(Real.pi / 2)))
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        (thetaCuspGaussianConstant_nonneg _))
      (Real.exp_pos _).le
  · exact (Real.exp_pos _).le
  · rw [Real.exp_lt_one_iff]
    have hpi : 0 < Real.pi / 2 := by positivity
    linarith
  · exact norm_thetaCuspTailSecondDensityMobiusAux_le_geometric hx

/-- The weighted Lambert row of the auxiliary sequence is the shifted full density divided by
its row index. -/
theorem weightedLambertTransform_thetaCuspTailSecondDensityMobiusAux
    (x : ℝ) (n : ℕ+) :
    weightedLambertTransform (thetaCuspTailSecondDensityMobiusAux x) n =
      (n : ℂ)⁻¹ *
        (((n : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaCuspTailSecondDensity (x + Real.log n) : ℝ) : ℂ) := by
  let a : ℕ+ → ℂ := fun m =>
    (thetaCuspTailSecondDensityAtom (n * m) x : ℂ)
  have haReal := summable_thetaCuspTailSecondDensityAtom_pnat_mul n x
  have ha : Summable a := by
    exact Complex.summable_ofReal.mpr haReal
  have hrowReal := tsum_thetaCuspTailSecondDensityAtom_pnat_mul n x
  have hrow : (∑' m, a m) =
      (((n : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensity (x + Real.log n) : ℝ) : ℂ) := by
    rw [show (∑' m, a m) =
        (((∑' m : ℕ+, thetaCuspTailSecondDensityAtom (n * m) x) : ℝ) : ℂ) by
      exact (Complex.ofRealCLM.map_tsum haReal).symm]
    rw [hrowReal]
  unfold weightedLambertTransform
  rw [show (fun m : ℕ+ => (m : ℂ) *
      thetaCuspTailSecondDensityMobiusAux x (n * m)) =
      fun m => (n : ℂ)⁻¹ * a m by
    funext m
    unfold thetaCuspTailSecondDensityMobiusAux
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
    push_cast
    field_simp
    rfl]
  rw [tsum_mul_left, hrow]

/-- **Absolute critical Möbius inversion of the canonical theta-tail density.**  On the positive
logarithmic half-line the first differentiated Gaussian atom is recovered from the complete
density by the signed critical translate series

`rho₁(x) = Σ μ(n) n^(-1/2) rho(x + log n)`.

Absolute convergence is supplied by the Gaussian source before the divisor regrouping; no
conditional reciprocal-zeta boundary value is used. -/
theorem thetaCuspTailSecondDensityAtom_one_eq_tsum_moebius_translate
    {x : ℝ} (hx : 0 ≤ x) :
    (thetaCuspTailSecondDensityAtom 1 x : ℂ) =
      ∑' n : ℕ+,
        (ArithmeticFunction.moebius n : ℂ) *
          (((n : ℝ) ^ (-(1 / 2 : ℝ)) *
            thetaCuspTailSecondDensity (x + Real.log n) : ℝ) : ℂ) := by
  let a : ℕ+ → ℂ := thetaCuspTailSecondDensityMobiusAux x
  have hsum : Summable (weightedLambertMobiusPair a) :=
    summable_thetaCuspTailSecondDensityMobiusPair hx
  have hinv := weightedLambertMobius_inversion a hsum
  calc
    (thetaCuspTailSecondDensityAtom 1 x : ℂ) = a 1 := by
      simp [a, thetaCuspTailSecondDensityMobiusAux]
    _ = ∑' n : ℕ+, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) *
        weightedLambertTransform a n := hinv.symm
    _ = ∑' n : ℕ+,
        (ArithmeticFunction.moebius n : ℂ) *
          (((n : ℝ) ^ (-(1 / 2 : ℝ)) *
            thetaCuspTailSecondDensity (x + Real.log n) : ℝ) : ℂ) := by
      apply tsum_congr
      intro n
      rw [weightedLambertTransform_thetaCuspTailSecondDensityMobiusAux]
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
      field_simp

/-- At the critical half-density weight, reflection of one logarithmic shift separates into the
two elementary boundary characters `n⁻¹` and `1`. -/
theorem exp_neg_half_log_mul_thetaCuspReflectionMode_sub_log
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    Real.exp (-(Real.log n) / 2) *
        thetaCuspReflectionMode (x - Real.log n) =
      (Real.exp (x / 2) / (n : ℝ) - Real.exp (-x / 2)) / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfirst :
      Real.exp (-(Real.log n) / 2) *
          Real.exp ((x - Real.log n) / 2) =
        Real.exp (x / 2) / (n : ℝ) := by
    rw [← Real.exp_add]
    rw [show -(Real.log n) / 2 + (x - Real.log n) / 2 =
        x / 2 - Real.log n by ring]
    rw [Real.exp_sub, Real.exp_log hnR]
  have hsecond :
      Real.exp (-(Real.log n) / 2) *
          Real.exp (-(x - Real.log n) / 2) =
        Real.exp (-x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold thetaCuspReflectionMode
  calc
    Real.exp (-(Real.log n) / 2) *
          ((Real.exp ((x - Real.log n) / 2) -
            Real.exp (-(x - Real.log n) / 2)) / 2) =
        (Real.exp (-(Real.log n) / 2) * Real.exp ((x - Real.log n) / 2) -
          Real.exp (-(Real.log n) / 2) * Real.exp (-(x - Real.log n) / 2)) / 2 := by
            ring
    _ = (Real.exp (x / 2) / (n : ℝ) - Real.exp (-x / 2)) / 2 := by
          rw [hfirst, hsecond]

/-- Finite critical Möbius translate of the complete density. -/
def thetaCuspTailSecondDensityFiniteMobiusTranslate
    (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    moebiusCoeff n * Real.exp (-(Real.log n) / 2) *
      thetaCuspTailSecondDensity (x + Real.log n)

/-- Finite left-shift channel paired with the same critical Möbius weights. -/
def thetaCuspTailSecondDensityFiniteMobiusLeftShift
    (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    moebiusCoeff n * Real.exp (-(Real.log n) / 2) *
      thetaCuspTailSecondDensity (x - Real.log n)

def finiteMoebiusSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, moebiusCoeff n

def finiteMoebiusHarmonicSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, moebiusCoeff n / (n : ℝ)

theorem abs_finiteMoebiusSum_le (N : ℕ) :
    |finiteMoebiusSum N| ≤ N := by
  unfold finiteMoebiusSum
  calc
    |∑ n ∈ Finset.Icc 1 N, moebiusCoeff n| ≤
        ∑ n ∈ Finset.Icc 1 N, |moebiusCoeff n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
      exact Finset.sum_le_sum fun n _hn => abs_moebiusCoeff_le_one n
    _ = N := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp

theorem abs_finiteMoebiusHarmonicSum_le (N : ℕ) :
    |finiteMoebiusHarmonicSum N| ≤ N := by
  unfold finiteMoebiusHarmonicSum
  calc
    |∑ n ∈ Finset.Icc 1 N, moebiusCoeff n / (n : ℝ)| ≤
        ∑ n ∈ Finset.Icc 1 N, |moebiusCoeff n / (n : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [abs_div]
      calc
        |moebiusCoeff n| / |(n : ℝ)| ≤ 1 / 1 := by
          gcongr
          · exact abs_moebiusCoeff_le_one n
          · simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)] using hn1
        _ = 1 := by norm_num
    _ = N := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp

/-- Exact reflection anomaly of the finite critical Möbius inverse.  The entire failure of right
shifts to commute with source reflection lies in the two completion characters, with coefficients
the ordinary and harmonic Mertens sums. -/
theorem thetaCuspTailSecondDensityFiniteMobiusTranslate_neg
    (N : ℕ) (x : ℝ) :
    thetaCuspTailSecondDensityFiniteMobiusTranslate N (-x) =
      thetaCuspTailSecondDensityFiniteMobiusLeftShift N x +
        (Real.exp (x / 2) / 2) * finiteMoebiusHarmonicSum N -
        (Real.exp (-x / 2) / 2) * finiteMoebiusSum N := by
  unfold thetaCuspTailSecondDensityFiniteMobiusTranslate
    thetaCuspTailSecondDensityFiniteMobiusLeftShift
    finiteMoebiusHarmonicSum finiteMoebiusSum
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hnmem
  have hn : 0 < n := by
    have := (Finset.mem_Icc.mp hnmem).1
    omega
  have hreflect := thetaCuspTailSecondDensity_neg (x - Real.log n)
  rw [show -x + Real.log n = -(x - Real.log n) by ring,
    hreflect]
  have hmode := exp_neg_half_log_mul_thetaCuspReflectionMode_sub_log hn x
  calc
    moebiusCoeff n * Real.exp (-(Real.log n) / 2) *
          (thetaCuspTailSecondDensity (x - Real.log n) +
            thetaCuspReflectionMode (x - Real.log n)) =
        moebiusCoeff n * Real.exp (-(Real.log n) / 2) *
            thetaCuspTailSecondDensity (x - Real.log n) +
          moebiusCoeff n *
            (Real.exp (-(Real.log n) / 2) *
              thetaCuspReflectionMode (x - Real.log n)) := by ring
    _ = moebiusCoeff n * Real.exp (-(Real.log n) / 2) *
            thetaCuspTailSecondDensity (x - Real.log n) +
          (Real.exp (x / 2) / 2) * (moebiusCoeff n / (n : ℝ)) -
          (Real.exp (-x / 2) / 2) * moebiusCoeff n := by
            rw [hmode]
            ring

/-- First correction coefficient which kills the two completion characters of a finite
Möbius packet.  The correction is placed at label `N+1`. -/
def finiteMoebiusBalanceFirst (N : ℕ) : ℝ :=
  (N + 1 : ℝ) * finiteMoebiusSum N -
    (N + 1 : ℝ) * (N + 2 : ℝ) * finiteMoebiusHarmonicSum N

/-- Second correction coefficient, placed at label `N+2`. -/
def finiteMoebiusBalanceSecond (N : ℕ) : ℝ :=
  (N + 1 : ℝ) * (N + 2 : ℝ) * finiteMoebiusHarmonicSum N -
    (N + 2 : ℝ) * finiteMoebiusSum N

/-- The completion-balancing coefficients grow at most polynomially.  This deliberately uses only
`|mu(n)| <= 1`; no cancellation estimate for either Mertens sum enters. -/
theorem abs_finiteMoebiusBalance_add_le (N : ℕ) :
    |finiteMoebiusBalanceFirst N| + |finiteMoebiusBalanceSecond N| ≤
      4 * (N + 2 : ℝ) ^ 3 := by
  have hM := abs_finiteMoebiusSum_le N
  have hH := abs_finiteMoebiusHarmonicSum_le N
  have hN1 : (0 : ℝ) ≤ N + 1 := by positivity
  have hN2 : (0 : ℝ) ≤ N + 2 := by positivity
  have hN_le : (N : ℝ) ≤ N + 2 := by norm_num
  have hN1_le : (N + 1 : ℝ) ≤ N + 2 := by norm_num
  have hM2 : |finiteMoebiusSum N| ≤ (N + 2 : ℝ) := hM.trans hN_le
  have hH2 : |finiteMoebiusHarmonicSum N| ≤ (N + 2 : ℝ) := hH.trans hN_le
  have hAM : (N + 1 : ℝ) * |finiteMoebiusSum N| ≤ (N + 2 : ℝ) ^ 3 := by
    calc
      (N + 1 : ℝ) * |finiteMoebiusSum N| ≤
          (N + 2 : ℝ) * (N + 2 : ℝ) := by gcongr
      _ ≤ (N + 2 : ℝ) ^ 3 := by nlinarith [mul_nonneg hN2 hN2]
  have hBM : (N + 2 : ℝ) * |finiteMoebiusSum N| ≤ (N + 2 : ℝ) ^ 3 := by
    calc
      (N + 2 : ℝ) * |finiteMoebiusSum N| ≤
          (N + 2 : ℝ) * (N + 2 : ℝ) := by gcongr
      _ ≤ (N + 2 : ℝ) ^ 3 := by nlinarith [mul_nonneg hN2 hN2]
  have hABH : (N + 1 : ℝ) * (N + 2 : ℝ) *
      |finiteMoebiusHarmonicSum N| ≤ (N + 2 : ℝ) ^ 3 := by
    calc
      (N + 1 : ℝ) * (N + 2 : ℝ) * |finiteMoebiusHarmonicSum N| ≤
          (N + 2 : ℝ) * (N + 2 : ℝ) * (N + 2 : ℝ) := by gcongr
      _ = (N + 2 : ℝ) ^ 3 := by ring
  unfold finiteMoebiusBalanceFirst finiteMoebiusBalanceSecond
  calc
    |(N + 1 : ℝ) * finiteMoebiusSum N -
          (N + 1 : ℝ) * (N + 2 : ℝ) * finiteMoebiusHarmonicSum N| +
        |(N + 1 : ℝ) * (N + 2 : ℝ) * finiteMoebiusHarmonicSum N -
          (N + 2 : ℝ) * finiteMoebiusSum N| ≤
        ((N + 1 : ℝ) * |finiteMoebiusSum N| +
          (N + 1 : ℝ) * (N + 2 : ℝ) * |finiteMoebiusHarmonicSum N|) +
        ((N + 1 : ℝ) * (N + 2 : ℝ) * |finiteMoebiusHarmonicSum N| +
          (N + 2 : ℝ) * |finiteMoebiusSum N|) := by
      gcongr
      · calc
          _ ≤ |(N + 1 : ℝ) * finiteMoebiusSum N| +
              |(N + 1 : ℝ) * (N + 2 : ℝ) * finiteMoebiusHarmonicSum N| :=
            abs_sub _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_mul,
            abs_of_nonneg hN1, abs_of_nonneg hN2]
      · calc
          _ ≤ |(N + 1 : ℝ) * (N + 2 : ℝ) * finiteMoebiusHarmonicSum N| +
              |(N + 2 : ℝ) * finiteMoebiusSum N| := abs_sub _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_mul,
            abs_of_nonneg hN1, abs_of_nonneg hN2]
    _ ≤ ((N + 2 : ℝ) ^ 3 + (N + 2 : ℝ) ^ 3) +
          ((N + 2 : ℝ) ^ 3 + (N + 2 : ℝ) ^ 3) := by
      linarith
    _ = 4 * (N + 2 : ℝ) ^ 3 := by ring

/-- Absolute majorant of the two remote translates used to completion-balance the finite Möbius
packet. -/
def thetaCuspTailSecondDensityBalancedMobiusCorrectionMajorant
    (N : ℕ) (x : ℝ) : ℝ :=
  |finiteMoebiusBalanceFirst N| *
      (N + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensity (x + Real.log (N + 1)) +
    |finiteMoebiusBalanceSecond N| *
      (N + 2 : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensity (x + Real.log (N + 2))

/-- The balancing correction is bounded by a fourth-degree polynomial times the canonical
Gaussian ratio.  This is the quantitative bridge from exact reflection balance to vanishing tail
cost; it uses no cancellation in either Mertens sum. -/
theorem thetaCuspTailSecondDensityBalancedMobiusCorrectionMajorant_le
    {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    thetaCuspTailSecondDensityBalancedMobiusCorrectionMajorant N x ≤
      4 * (N + 2 : ℝ) ^ 3 *
        ((4 * thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-x)) * (N + 2 : ℝ) *
            (Real.exp (-(Real.pi / 2))) ^ (N + 1) *
              ∑' m : ℕ+, (m : ℝ) *
                (Real.exp (-(Real.pi / 2))) ^ ((m : ℕ) - 1)) := by
  let a : ℕ+ := ⟨N + 1, by omega⟩
  let b : ℕ+ := ⟨N + 2, by omega⟩
  let A : ℝ := 4 * thetaCuspGaussianConstant
      (thetaCuspTailDerivativePolynomial 2) * Real.exp (-x)
  let q : ℝ := Real.exp (-(Real.pi / 2))
  let B : ℝ := ∑' m : ℕ+, (m : ℝ) * q ^ ((m : ℕ) - 1)
  let R1 : ℝ := (a : ℝ) ^ (-(1 / 2 : ℝ)) *
    thetaCuspTailSecondDensity (x + Real.log a)
  let R2 : ℝ := (b : ℝ) ^ (-(1 / 2 : ℝ)) *
    thetaCuspTailSecondDensity (x + Real.log b)
  let Rmax : ℝ := A * (b : ℝ) * q ^ (a : ℕ) * B
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos]
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (thetaCuspGaussianConstant_nonneg _))
      (Real.exp_pos _).le
  have hB : 0 ≤ B := by
    dsimp [B, q]
    exact tsum_nonneg fun m => mul_nonneg (by positivity) (by positivity)
  have hR1 : R1 ≤ Rmax := by
    have h := criticalThetaCuspDensityTranslate_le_geometric hx a
    change R1 ≤ A * (a : ℝ) * q ^ (a : ℕ) * B at h
    calc
      R1 ≤ A * (a : ℝ) * q ^ (a : ℕ) * B := h
      _ ≤ A * (b : ℝ) * q ^ (a : ℕ) * B := by
        gcongr
        dsimp [a, b]
        norm_num
      _ = Rmax := rfl
  have hR2 : R2 ≤ Rmax := by
    have h := criticalThetaCuspDensityTranslate_le_geometric hx b
    change R2 ≤ A * (b : ℝ) * q ^ (b : ℕ) * B at h
    have hpow : q ^ (b : ℕ) ≤ q ^ (a : ℕ) := by
      apply pow_le_pow_of_le_one hq0 hq1
      dsimp [a, b]
      omega
    calc
      R2 ≤ A * (b : ℝ) * q ^ (b : ℕ) * B := h
      _ ≤ A * (b : ℝ) * q ^ (a : ℕ) * B := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left hpow
          exact mul_nonneg hA (by positivity)
        · exact hB
      _ = Rmax := rfl
  have hRmax : 0 ≤ Rmax := by
    dsimp [Rmax]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hA (by positivity)) (pow_nonneg hq0 _)) hB
  have hcoeff := abs_finiteMoebiusBalance_add_le N
  unfold thetaCuspTailSecondDensityBalancedMobiusCorrectionMajorant
  rw [show |finiteMoebiusBalanceFirst N| *
        (N + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaCuspTailSecondDensity (x + Real.log (N + 1)) =
        |finiteMoebiusBalanceFirst N| * R1 by
      dsimp [R1, a]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring]
  rw [show |finiteMoebiusBalanceSecond N| *
        (N + 2 : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaCuspTailSecondDensity (x + Real.log (N + 2)) =
        |finiteMoebiusBalanceSecond N| * R2 by
      dsimp [R2, b]
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      ring]
  calc
    _ ≤ (|finiteMoebiusBalanceFirst N| +
        |finiteMoebiusBalanceSecond N|) * Rmax := by
      rw [add_mul]
      gcongr
    _ ≤ (4 * (N + 2 : ℝ) ^ 3) * Rmax := by gcongr
    _ = _ := by
      dsimp [Rmax, A, B, q, a, b]
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]

/-- The exact reflection-balancing correction vanishes at every nonnegative source coordinate.
The proof is purely Gaussian: polynomially growing correction coefficients are absorbed by the
geometric row bound. -/
theorem tendsto_thetaCuspTailSecondDensityBalancedMobiusCorrectionMajorant
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun N : ℕ =>
      thetaCuspTailSecondDensityBalancedMobiusCorrectionMajorant N x)
      atTop (nhds 0) := by
  let q : ℝ := Real.exp (-(Real.pi / 2))
  let A : ℝ := 4 * thetaCuspGaussianConstant
      (thetaCuspTailDerivativePolynomial 2) * Real.exp (-x)
  let B : ℝ := ∑' m : ℕ+, (m : ℝ) * q ^ ((m : ℕ) - 1)
  let K : ℝ := 4 * A * B
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hqne : q ≠ 0 := (Real.exp_pos _).ne'
  have hbase := tendsto_pow_const_mul_const_pow_of_lt_one 4 hq0 hq1
  have hshift : Tendsto (fun N : ℕ =>
      (N + 2 : ℝ) ^ 4 * q ^ (N + 2)) atTop (nhds 0) := by
    have h := (Filter.tendsto_add_atTop_iff_nat 2).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have hupper : Tendsto (fun N : ℕ =>
      4 * (N + 2 : ℝ) ^ 3 *
        (A * (N + 2 : ℝ) * q ^ (N + 1) * B)) atTop (nhds 0) := by
    have h := hshift.const_mul (K * q⁻¹)
    convert h using 1
    · funext N
      dsimp [K]
      rw [show q ^ (N + 2) = q ^ (N + 1) * q by
        rw [show N + 2 = N + 1 + 1 by omega, pow_succ]]
      field_simp [hqne]
    · simp
  apply squeeze_zero
  · intro N
    unfold thetaCuspTailSecondDensityBalancedMobiusCorrectionMajorant
    have hlog1 : 0 ≤ Real.log ((N : ℝ) + 1) := by
      apply Real.log_nonneg
      norm_num
    have hlog2 : 0 ≤ Real.log ((N : ℝ) + 2) := by
      apply Real.log_nonneg
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    have hrho1 : 0 ≤ thetaCuspTailSecondDensity (x + Real.log (N + 1)) := by
      unfold thetaCuspTailSecondDensity
      exact mul_nonneg (by norm_num)
        (thetaCuspTailDerivative_two_pos (add_nonneg hx hlog1)).le
    have hrho2 : 0 ≤ thetaCuspTailSecondDensity (x + Real.log (N + 2)) := by
      unfold thetaCuspTailSecondDensity
      exact mul_nonneg (by norm_num)
        (thetaCuspTailDerivative_two_pos (add_nonneg hx hlog2)).le
    positivity
  · intro N
    simpa [A, B, q] using
      thetaCuspTailSecondDensityBalancedMobiusCorrectionMajorant_le hx N
  · exact hupper

/-- The two correction coefficients cancel the ordinary Mertens coefficient exactly. -/
theorem finiteMoebiusBalance_sum (N : ℕ) :
    finiteMoebiusBalanceFirst N + finiteMoebiusBalanceSecond N =
      -finiteMoebiusSum N := by
  unfold finiteMoebiusBalanceFirst finiteMoebiusBalanceSecond
  ring

/-- The same two coefficients cancel the harmonic Mertens coefficient exactly. -/
theorem finiteMoebiusBalance_harmonic_sum (N : ℕ) :
    finiteMoebiusBalanceFirst N / (N + 1 : ℝ) +
        finiteMoebiusBalanceSecond N / (N + 2 : ℝ) =
      -finiteMoebiusHarmonicSum N := by
  have hN1 : (N + 1 : ℝ) ≠ 0 := by positivity
  have hN2 : (N + 2 : ℝ) ≠ 0 := by positivity
  unfold finiteMoebiusBalanceFirst finiteMoebiusBalanceSecond
  field_simp [hN1, hN2]
  ring

/-- Finite coefficient functional of the completion-balanced Möbius packet.  It records the
arithmetic packet independently of the theta density on which the packet later acts. -/
def finiteMoebiusBalancedCoefficientMoment
    (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 N, moebiusCoeff n * f n) +
    finiteMoebiusBalanceFirst N * f (N + 1) +
    finiteMoebiusBalanceSecond N * f (N + 2)

/-- The balanced packet annihilates the constant completion character.  Equivalently, its finite
Dirichlet symbol vanishes at exponent zero. -/
theorem finiteMoebiusBalancedCoefficientMoment_one (N : ℕ) :
    finiteMoebiusBalancedCoefficientMoment N (fun _ => 1) = 0 := by
  rw [finiteMoebiusBalancedCoefficientMoment]
  simp only [mul_one]
  rw [show (∑ n ∈ Finset.Icc 1 N, moebiusCoeff n) = finiteMoebiusSum N by
    rfl]
  linarith [finiteMoebiusBalance_sum N]

/-- The balanced packet also annihilates the reciprocal completion character.  Equivalently, its
finite Dirichlet symbol vanishes at exponent one. -/
theorem finiteMoebiusBalancedCoefficientMoment_inv (N : ℕ) :
    finiteMoebiusBalancedCoefficientMoment N (fun n => ((n : ℝ))⁻¹) = 0 := by
  rw [finiteMoebiusBalancedCoefficientMoment]
  rw [show (∑ n ∈ Finset.Icc 1 N, moebiusCoeff n * ((n : ℝ))⁻¹) =
      finiteMoebiusHarmonicSum N by
    unfold finiteMoebiusHarmonicSum
    apply Finset.sum_congr rfl
    intro n _hn
    rw [div_eq_mul_inv]]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [inv_eq_one_div, inv_eq_one_div]
  calc
    finiteMoebiusHarmonicSum N +
          finiteMoebiusBalanceFirst N * (1 / ((N : ℝ) + 1)) +
          finiteMoebiusBalanceSecond N * (1 / ((N : ℝ) + 2)) =
        finiteMoebiusHarmonicSum N +
          (finiteMoebiusBalanceFirst N / ((N : ℝ) + 1) +
            finiteMoebiusBalanceSecond N / ((N : ℝ) + 2)) := by ring
    _ = 0 := by rw [finiteMoebiusBalance_harmonic_sum]; ring

/-- Reflection of one critically weighted density translate with an arbitrary real coefficient. -/
theorem coeff_mul_exp_neg_half_log_mul_thetaCuspTailSecondDensity_neg_add_log
    {n : ℕ} (hn : 0 < n) (c x : ℝ) :
    c * Real.exp (-(Real.log n) / 2) *
        thetaCuspTailSecondDensity (-x + Real.log n) =
      c * Real.exp (-(Real.log n) / 2) *
          thetaCuspTailSecondDensity (x - Real.log n) +
        c * Real.exp (x / 2) / (2 * (n : ℝ)) -
        c * Real.exp (-x / 2) / 2 := by
  have hreflect := thetaCuspTailSecondDensity_neg (x - Real.log n)
  have hmode := exp_neg_half_log_mul_thetaCuspReflectionMode_sub_log hn x
  rw [show -x + Real.log n = -(x - Real.log n) by ring, hreflect]
  calc
    c * Real.exp (-(Real.log n) / 2) *
          (thetaCuspTailSecondDensity (x - Real.log n) +
            thetaCuspReflectionMode (x - Real.log n)) =
        c * Real.exp (-(Real.log n) / 2) *
            thetaCuspTailSecondDensity (x - Real.log n) +
          c * (Real.exp (-(Real.log n) / 2) *
            thetaCuspReflectionMode (x - Real.log n)) := by ring
    _ = _ := by
      rw [hmode]
      ring

/-- Finite Möbius packet with two tail corrections chosen to annihilate both completion
characters. -/
def thetaCuspTailSecondDensityBalancedMobiusTranslate
    (N : ℕ) (x : ℝ) : ℝ :=
  thetaCuspTailSecondDensityFiniteMobiusTranslate N x +
    finiteMoebiusBalanceFirst N *
      Real.exp (-(Real.log (N + 1)) / 2) *
        thetaCuspTailSecondDensity (x + Real.log (N + 1)) +
    finiteMoebiusBalanceSecond N *
      Real.exp (-(Real.log (N + 2)) / 2) *
        thetaCuspTailSecondDensity (x + Real.log (N + 2))

/-- Left-shift version of the completion-balanced finite Möbius packet. -/
def thetaCuspTailSecondDensityBalancedMobiusLeftShift
    (N : ℕ) (x : ℝ) : ℝ :=
  thetaCuspTailSecondDensityFiniteMobiusLeftShift N x +
    finiteMoebiusBalanceFirst N *
      Real.exp (-(Real.log (N + 1)) / 2) *
        thetaCuspTailSecondDensity (x - Real.log (N + 1)) +
    finiteMoebiusBalanceSecond N *
      Real.exp (-(Real.log (N + 2)) / 2) *
        thetaCuspTailSecondDensity (x - Real.log (N + 2))

/-- Exact completion-balanced reflection law.  Unlike the raw finite Möbius inverse, this packet
has no residual `exp(x/2)` or `exp(-x/2)` boundary character. -/
theorem thetaCuspTailSecondDensityBalancedMobiusTranslate_neg
    (N : ℕ) (x : ℝ) :
    thetaCuspTailSecondDensityBalancedMobiusTranslate N (-x) =
      thetaCuspTailSecondDensityBalancedMobiusLeftShift N x := by
  rw [thetaCuspTailSecondDensityBalancedMobiusTranslate,
    thetaCuspTailSecondDensityBalancedMobiusLeftShift,
    thetaCuspTailSecondDensityFiniteMobiusTranslate_neg]
  have hfirst :
      finiteMoebiusBalanceFirst N * Real.exp (-(Real.log ((N : ℝ) + 1)) / 2) *
          thetaCuspTailSecondDensity (-x + Real.log ((N : ℝ) + 1)) =
        finiteMoebiusBalanceFirst N * Real.exp (-(Real.log ((N : ℝ) + 1)) / 2) *
            thetaCuspTailSecondDensity (x - Real.log ((N : ℝ) + 1)) +
          finiteMoebiusBalanceFirst N * Real.exp (x / 2) /
              (2 * ((N : ℝ) + 1)) -
          finiteMoebiusBalanceFirst N * Real.exp (-x / 2) / 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (coeff_mul_exp_neg_half_log_mul_thetaCuspTailSecondDensity_neg_add_log
        (n := N + 1) (by omega) (finiteMoebiusBalanceFirst N) x)
  have hsecond :
      finiteMoebiusBalanceSecond N * Real.exp (-(Real.log ((N : ℝ) + 2)) / 2) *
          thetaCuspTailSecondDensity (-x + Real.log ((N : ℝ) + 2)) =
        finiteMoebiusBalanceSecond N * Real.exp (-(Real.log ((N : ℝ) + 2)) / 2) *
            thetaCuspTailSecondDensity (x - Real.log ((N : ℝ) + 2)) +
          finiteMoebiusBalanceSecond N * Real.exp (x / 2) /
              (2 * ((N : ℝ) + 2)) -
          finiteMoebiusBalanceSecond N * Real.exp (-x / 2) / 2 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (coeff_mul_exp_neg_half_log_mul_thetaCuspTailSecondDensity_neg_add_log
        (n := N + 2) (by omega) (finiteMoebiusBalanceSecond N) x)
  rw [hfirst, hsecond]
  have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hN2 : ((N : ℝ) + 2) ≠ 0 := by positivity
  unfold finiteMoebiusBalanceFirst finiteMoebiusBalanceSecond
  field_simp [hN1, hN2]
  ring

end

end RHTower
