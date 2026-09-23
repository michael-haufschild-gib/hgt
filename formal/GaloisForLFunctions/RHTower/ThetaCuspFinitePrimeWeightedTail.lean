import GaloisForLFunctions.HTGeometry.ExpRayL2
import GaloisForLFunctions.RHTower.ThetaCuspSchwartz

/-!
# Uniform exponentially weighted tails for finite-prime theta sources

Every logarithmic derivative of every finite-prime theta source decays faster than any prescribed
exponential on the positive half-line, with constants independent of the prime cutoff.  The proof
absorbs extra exponential weights into powers of the polynomial--Gaussian scaling variable and
then dominates every smooth-integer subseries by the all-integer Gaussian series.

The resulting explicit tail-integral bound is the analytic input needed by cofinal cusp screens.
-/

open Filter Topology Set Polynomial MeasureTheory

noncomputable section

namespace RHTower

/-- Polynomial absorbing `q` extra exponential weights under logarithmic scaling. -/
def thetaCuspWeightedPolynomial (P : ℝ[X]) (q : ℕ) : ℝ[X] :=
  X ^ q * P

theorem exp_natSucc_mul_abs_thetaCuspPolynomialAtom_le
    (P : ℝ[X]) (q : ℕ) {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
    Real.exp (((q + 1 : ℕ) : ℝ) * x) *
        abs (thetaCuspPolynomialAtom P n x) ≤
      thetaCuspGaussianConstant (thetaCuspWeightedPolynomial P q) *
        Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ q := one_le_pow₀ hnR
  have hnonneg : 0 ≤ Real.exp (((q + 1 : ℕ) : ℝ) * x) *
      |thetaCuspPolynomialAtom P n x| := by positivity
  have hrewrite :
      Real.exp x *
          |thetaCuspPolynomialAtom (thetaCuspWeightedPolynomial P q) n x| =
        (n : ℝ) ^ q *
          (Real.exp (((q + 1 : ℕ) : ℝ) * x) *
            |thetaCuspPolynomialAtom P n x|) := by
    unfold thetaCuspPolynomialAtom thetaCuspWeightedPolynomial
    simp only [eval_mul, eval_pow, eval_X, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) * Real.exp x)]
    rw [show ((n : ℝ) * Real.exp x) ^ q =
        (n : ℝ) ^ q * Real.exp ((q : ℝ) * x) by
      rw [mul_pow, ← Real.exp_nat_mul]]
    have hexp : Real.exp x * Real.exp ((q : ℝ) * x) =
        Real.exp (((q + 1 : ℕ) : ℝ) * x) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    calc
      Real.exp x *
          (Real.exp (x / 2) *
              ((n : ℝ) ^ q * Real.exp ((q : ℝ) * x) * |eval ((n : ℝ) * Real.exp x) P|) *
            Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ (2 : ℕ))) =
        (n : ℝ) ^ q *
          ((Real.exp x * Real.exp ((q : ℝ) * x)) *
            (Real.exp (x / 2) * |eval ((n : ℝ) * Real.exp x) P| *
              Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ (2 : ℕ)))) := by ring
      _ = (n : ℝ) ^ q *
          (Real.exp (((q + 1 : ℕ) : ℝ) * x) *
            (Real.exp (x / 2) * |eval ((n : ℝ) * Real.exp x) P| *
              Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ (2 : ℕ)))) := by rw [hexp]
  calc
    Real.exp (((q + 1 : ℕ) : ℝ) * x) *
        |thetaCuspPolynomialAtom P n x| ≤
      (n : ℝ) ^ q *
        (Real.exp (((q + 1 : ℕ) : ℝ) * x) *
          |thetaCuspPolynomialAtom P n x|) := by
      exact le_mul_of_one_le_left hnonneg hnPow
    _ = Real.exp x *
        |thetaCuspPolynomialAtom (thetaCuspWeightedPolynomial P q) n x| :=
      hrewrite.symm
    _ ≤ thetaCuspGaussianConstant (thetaCuspWeightedPolynomial P q) *
        Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ)) :=
      exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos _ hx hn

/-- Uniform constant for the `(q+1)`-exponentially weighted `m`-th derivative of every
finite-prime theta-cusp source. -/
def finitePrimeThetaCuspWeightedDerivativeConstant (m q : ℕ) : ℝ :=
  thetaCuspGaussianConstant
      (thetaCuspWeightedPolynomial (thetaCuspLogDerivativePolynomial m) q) *
    ∑' n : ℕ, Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ))

theorem finitePrimeThetaCuspWeightedDerivativeConstant_nonneg (m q : ℕ) :
    0 ≤ finitePrimeThetaCuspWeightedDerivativeConstant m q := by
  unfold finitePrimeThetaCuspWeightedDerivativeConstant
  exact mul_nonneg (thetaCuspGaussianConstant_nonneg _)
    (tsum_nonneg fun _ ↦ (Real.exp_pos _).le)

/-- Every finite-prime derivative has a positive-tail bound faster than any prescribed integer
exponential, with a constant independent of the prime cutoff. -/
theorem exp_natSucc_mul_abs_finitePrimeThetaCuspDerivative_le
    (m q N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (((q + 1 : ℕ) : ℝ) * x) *
        |finitePrimeThetaCuspDerivative m N x| ≤
      finitePrimeThetaCuspWeightedDerivativeConstant m q := by
  let S : Set ℕ := (N + 1).smoothNumbers
  let a : S → ℝ := fun n ↦
    thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial m) n x
  let g : ℕ → ℝ := fun n ↦
    Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ))
  let C : ℝ := thetaCuspGaussianConstant
    (thetaCuspWeightedPolynomial (thetaCuspLogDerivativePolynomial m) q)
  have ha : Summable a := by
    exact ((summable_iteratedDeriv_thetaCuspSourceTerm m x).subtype S).congr
      (fun n ↦ by
        dsimp [a]
        rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom])
  have hgauss : Summable g := by
    simpa [g] using summable_thetaCuspHalfGaussian
  have hgaussSub : Summable (fun n : S ↦ g n) := hgauss.subtype S
  have hweighted : Summable (fun n : S ↦
      Real.exp (((q + 1 : ℕ) : ℝ) * x) * |a n|) :=
    ha.norm.mul_left _
  have hmajor : Summable (fun n : S ↦ C * g n) := hgaussSub.mul_left C
  have hterm (n : S) :
      Real.exp (((q + 1 : ℕ) : ℝ) * x) * |a n| ≤ C * g n := by
    dsimp [a, C, g]
    exact exp_natSucc_mul_abs_thetaCuspPolynomialAtom_le _ q hx
      (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property))
  have hsub : ∑' n : S, g n ≤ ∑' n : ℕ, g n := by
    have hsplit := hgauss.tsum_subtype_add_tsum_subtype_compl S
    have hcomp : 0 ≤ ∑' n : ↑(Sᶜ), g n :=
      tsum_nonneg fun n ↦ (Real.exp_pos _).le
    linarith
  have hsource : finitePrimeThetaCuspDerivative m N x = ∑' n : S, a n := by
    unfold finitePrimeThetaCuspDerivative
    apply tsum_congr
    intro n
    dsimp [S, a]
    rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
  rw [hsource]
  calc
    Real.exp (((q + 1 : ℕ) : ℝ) * x) * |∑' n : S, a n| ≤
        Real.exp (((q + 1 : ℕ) : ℝ) * x) * ∑' n : S, |a n| := by
      gcongr
      exact norm_tsum_le_tsum_norm ha.norm
    _ = ∑' n : S,
        Real.exp (((q + 1 : ℕ) : ℝ) * x) * |a n| := by
      rw [tsum_mul_left]
    _ ≤ ∑' n : S, C * g n := hweighted.tsum_le_tsum hterm hmajor
    _ = C * ∑' n : S, g n := by rw [tsum_mul_left]
    _ ≤ C * ∑' n : ℕ, g n := by
      exact mul_le_mul_of_nonneg_left hsub (thetaCuspGaussianConstant_nonneg _)
    _ = finitePrimeThetaCuspWeightedDerivativeConstant m q := by
      rfl

/-- An arbitrary real exponential weight is absorbed by choosing a larger integer tail rate. -/
theorem exp_mul_abs_finitePrimeThetaCuspDerivative_le
    (m q N : ℕ) (A : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (A * x) * |finitePrimeThetaCuspDerivative m N x| ≤
      finitePrimeThetaCuspWeightedDerivativeConstant m q *
        Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * x) := by
  have hbase := exp_natSucc_mul_abs_finitePrimeThetaCuspDerivative_le m q N hx
  have hre : A * x = -(((q + 1 : ℕ) : ℝ) - A) * x +
      ((q + 1 : ℕ) : ℝ) * x := by ring
  rw [hre, Real.exp_add]
  calc
    Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * x) *
        Real.exp (((q + 1 : ℕ) : ℝ) * x) *
          |finitePrimeThetaCuspDerivative m N x| =
      Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * x) *
        (Real.exp (((q + 1 : ℕ) : ℝ) * x) *
          |finitePrimeThetaCuspDerivative m N x|) := by ring
    _ ≤ Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * x) *
        finitePrimeThetaCuspWeightedDerivativeConstant m q := by
      gcongr
    _ = finitePrimeThetaCuspWeightedDerivativeConstant m q *
        Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * x) := by ring

/-- Every exponentially weighted finite-prime derivative is integrable on the positive ray,
uniformly dominated by an `N`-independent exponential. -/
theorem integrableOn_exp_mul_abs_finitePrimeThetaCuspDerivative
    (m q N : ℕ) (A : ℝ) (hA : A < (q + 1 : ℕ)) :
    IntegrableOn (fun x : ℝ ↦
      Real.exp (A * x) * |finitePrimeThetaCuspDerivative m N x|) (Ioi 0) := by
  let c : ℝ := ((q + 1 : ℕ) : ℝ) - A
  let C : ℝ := finitePrimeThetaCuspWeightedDerivativeConstant m q
  have hc : 0 < c := by exact sub_pos.mpr hA
  have hC : 0 ≤ C := finitePrimeThetaCuspWeightedDerivativeConstant_nonneg m q
  have hdom : IntegrableOn (fun x : ℝ ↦ C * Real.exp (-(c * x))) (Ioi 0) :=
    (GaloisForLFunctions.HTGeometry.integrableOn_exp_neg_mul_Ioi hc 0).const_mul C
  apply Integrable.mono hdom
  · have hcont : Continuous (finitePrimeThetaCuspDerivative m N) :=
      continuous_iff_continuousAt.mpr fun x ↦
        (hasDerivAt_finitePrimeThetaCuspDerivative m N x).continuousAt
    have hprod : Continuous (fun x : ℝ ↦
        Real.exp (A * x) * |finitePrimeThetaCuspDerivative m N x|) :=
      (by fun_prop : Continuous fun x : ℝ ↦ Real.exp (A * x)).mul hcont.abs
    exact hprod.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ Real.exp (A * x) * |finitePrimeThetaCuspDerivative m N x|),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
    dsimp only [C, c]
    simpa only [neg_mul] using
      exp_mul_abs_finitePrimeThetaCuspDerivative_le m q N A hx.le

/-- Uniform explicit tail mass for every finite-prime derivative. -/
theorem integral_Ioi_exp_mul_abs_finitePrimeThetaCuspDerivative_le
    (m q N : ℕ) (A R : ℝ) (hA : A < (q + 1 : ℕ)) (hR : 0 ≤ R) :
    (∫ x : ℝ in Ioi R,
        Real.exp (A * x) * |finitePrimeThetaCuspDerivative m N x|) ≤
      finitePrimeThetaCuspWeightedDerivativeConstant m q *
        (Real.exp (-((((q + 1 : ℕ) : ℝ) - A) * R)) /
          (((q + 1 : ℕ) : ℝ) - A)) := by
  let c : ℝ := ((q + 1 : ℕ) : ℝ) - A
  let C : ℝ := finitePrimeThetaCuspWeightedDerivativeConstant m q
  have hc : 0 < c := sub_pos.mpr hA
  have hf0 := integrableOn_exp_mul_abs_finitePrimeThetaCuspDerivative m q N A hA
  have hf : IntegrableOn (fun x : ℝ ↦
      Real.exp (A * x) * |finitePrimeThetaCuspDerivative m N x|) (Ioi R) :=
    hf0.mono_set (fun x hx ↦ hR.trans_lt hx)
  have hg : IntegrableOn (fun x : ℝ ↦ C * Real.exp (-(c * x))) (Ioi R) :=
    (GaloisForLFunctions.HTGeometry.integrableOn_exp_neg_mul_Ioi hc R).const_mul C
  calc
    (∫ x : ℝ in Ioi R,
        Real.exp (A * x) * |finitePrimeThetaCuspDerivative m N x|) ≤
      ∫ x : ℝ in Ioi R, C * Real.exp (-(c * x)) := by
        apply setIntegral_mono_on hf hg measurableSet_Ioi
        intro x hx
        dsimp only [C, c]
        simpa only [neg_mul] using
          exp_mul_abs_finitePrimeThetaCuspDerivative_le m q N A
            (hR.trans_lt hx).le
    _ = C * (Real.exp (-(c * R)) / c) := by
      rw [integral_const_mul,
        GaloisForLFunctions.HTGeometry.integral_exp_neg_mul_Ioi hc R]
    _ = finitePrimeThetaCuspWeightedDerivativeConstant m q *
        (Real.exp (-((((q + 1 : ℕ) : ℝ) - A) * R)) /
          (((q + 1 : ℕ) : ℝ) - A)) := by rfl

end RHTower
