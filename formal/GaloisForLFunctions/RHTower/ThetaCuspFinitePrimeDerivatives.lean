import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeSource
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Polynomial.Basic

/-!
# Smooth compact-local convergence of finite-prime theta-cusp sources

Every logarithmic derivative of a theta-cusp summand is an explicit polynomial times the same
Gaussian.  This gives a summable envelope on each compact logarithmic interval, justifies
termwise differentiation of both the all-integer and smooth-integer sums, and upgrades the
order-zero convergence theorem to convergence in every derivative order.
-/

open Filter Topology Set Polynomial

noncomputable section

namespace RHTower

/-- Polynomial part of the normalized theta-cusp seed. -/
def thetaCuspSeedPolynomial : ℝ[X] :=
  C (4 * Real.pi ^ 2) * X ^ 4 - C (6 * Real.pi) * X ^ 2

theorem thetaCuspSeed_eq_polynomial (t : ℝ) :
    thetaCuspSeed t =
      eval t thetaCuspSeedPolynomial * Real.exp (-Real.pi * t ^ 2) := by
  simp [thetaCuspSeed, thetaCuspSeedPolynomial]
  ring

/-- Polynomial recursion induced by logarithmic differentiation after the `e^(x/2)` weight. -/
def thetaCuspLogDerivativeStep (P : ℝ[X]) : ℝ[X] :=
  C (1 / 2) * P + X * derivative P - C (2 * Real.pi) * X ^ 2 * P

/-- Polynomial part of the `m`-th logarithmic derivative. -/
def thetaCuspLogDerivativePolynomial : ℕ → ℝ[X]
  | 0 => thetaCuspSeedPolynomial
  | m + 1 => thetaCuspLogDerivativeStep (thetaCuspLogDerivativePolynomial m)

/-- A polynomial-Gaussian atom at the logarithmically scaled integer `n`. -/
def thetaCuspPolynomialAtom (P : ℝ[X]) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) * eval ((n : ℝ) * Real.exp x) P *
    Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2)

theorem hasDerivAt_thetaCuspPolynomialAtom (P : ℝ[X]) (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspPolynomialAtom P n)
      (thetaCuspPolynomialAtom (thetaCuspLogDerivativeStep P) n x) x := by
  let y : ℝ := (n : ℝ) * Real.exp x
  have hy : HasDerivAt (fun z : ℝ => (n : ℝ) * Real.exp z) y x := by
    simpa [y] using (Real.hasDerivAt_exp x).const_mul (n : ℝ)
  have hhalf : HasDerivAt (fun z : ℝ => Real.exp (z / 2))
      ((1 / 2 : ℝ) * Real.exp (x / 2)) x := by
    have hinner : HasDerivAt (fun z : ℝ => z / 2) (1 / 2 : ℝ) x := by
      have hraw := (hasDerivAt_id x).div_const 2
      have hfun : (fun z : ℝ => z / 2) = fun z => id z / 2 := by
        funext z
        rfl
      rw [hfun]
      exact hraw
    have hraw := (Real.hasDerivAt_exp (x / 2)).comp x hinner
    have hfun :
        (fun z : ℝ => Real.exp (z / 2)) = Real.exp ∘ fun z : ℝ => z / 2 := by
      funext z
      rfl
    rw [hfun]
    exact hraw.congr_deriv (mul_comm _ _)
  have hpoly : HasDerivAt (fun z : ℝ => eval ((n : ℝ) * Real.exp z) P)
      (eval y (derivative P) * y) x := by
    have hraw := (P.hasDerivAt y).comp x hy
    have hfun :
        (fun z : ℝ => eval ((n : ℝ) * Real.exp z) P) =
          (fun u : ℝ => eval u P) ∘ fun z : ℝ => (n : ℝ) * Real.exp z := by
      funext z
      rfl
    rw [hfun]
    exact hraw
  have hsq : HasDerivAt (fun z : ℝ => ((n : ℝ) * Real.exp z) ^ 2)
      (2 * y ^ 2) x := by
    have hraw := hy.pow 2
    have hfun :
        (fun z : ℝ => ((n : ℝ) * Real.exp z) ^ 2) =
          (fun z : ℝ => (n : ℝ) * Real.exp z) ^ 2 := by
      funext z
      rfl
    have hcoef :
        (2 : ℝ) * ((n : ℝ) * Real.exp x) ^ (2 - 1) * y = 2 * y ^ 2 := by
      norm_num
      dsimp [y]
      ring
    rw [hfun]
    exact hraw.congr_deriv hcoef
  have hgauss : HasDerivAt
      (fun z : ℝ => Real.exp (-Real.pi * ((n : ℝ) * Real.exp z) ^ 2))
      ((-2 * Real.pi * y ^ 2) * Real.exp (-Real.pi * y ^ 2)) x := by
    have hinnerRaw := (hasDerivAt_const x (-Real.pi)).mul hsq
    have hinnerFun :
        (fun z : ℝ => -Real.pi * ((n : ℝ) * Real.exp z) ^ 2) =
          (fun _ : ℝ => -Real.pi) *
            fun z : ℝ => ((n : ℝ) * Real.exp z) ^ 2 := by
      funext z
      rfl
    have hinner : HasDerivAt
        (fun z : ℝ => -Real.pi * ((n : ℝ) * Real.exp z) ^ 2)
        (-2 * Real.pi * y ^ 2) x := by
      rw [hinnerFun]
      exact hinnerRaw.congr_deriv (by ring)
    have hraw := (Real.hasDerivAt_exp (-Real.pi * y ^ 2)).comp x hinner
    have hfun :
        (fun z : ℝ => Real.exp (-Real.pi * ((n : ℝ) * Real.exp z) ^ 2)) =
          Real.exp ∘ fun z : ℝ => -Real.pi * ((n : ℝ) * Real.exp z) ^ 2 := by
      funext z
      rfl
    rw [hfun]
    exact hraw.congr_deriv (by ring)
  have hraw := (hhalf.mul hpoly).mul hgauss
  have hfun :
      thetaCuspPolynomialAtom P n =
        ((fun z : ℝ => Real.exp (z / 2)) *
          fun z : ℝ => eval ((n : ℝ) * Real.exp z) P) *
            fun z : ℝ => Real.exp (-Real.pi * ((n : ℝ) * Real.exp z) ^ 2) := by
    funext z
    rfl
  rw [hfun]
  apply hraw.congr_deriv
  unfold thetaCuspPolynomialAtom thetaCuspLogDerivativeStep
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow]
  dsimp [y]
  ring

theorem thetaCuspSourceTerm_eq_polynomialAtom (n : ℕ) :
    (fun x => thetaCuspSourceTerm x n) =
      thetaCuspPolynomialAtom thetaCuspSeedPolynomial n := by
  funext x
  rw [thetaCuspSourceTerm, thetaCuspSeed_eq_polynomial]
  unfold thetaCuspPolynomialAtom
  ring

/-- Exact closed form for every logarithmic derivative of a source summand. -/
theorem iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom (m n : ℕ) :
    iteratedDeriv m (fun x => thetaCuspSourceTerm x n) =
      thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial m) n := by
  induction m with
  | zero =>
      simpa [iteratedDeriv_zero, thetaCuspLogDerivativePolynomial] using
        thetaCuspSourceTerm_eq_polynomialAtom n
  | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      change deriv (thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial m) n) =
        thetaCuspPolynomialAtom
          (thetaCuspLogDerivativeStep (thetaCuspLogDerivativePolynomial m)) n
      funext x
      exact (hasDerivAt_thetaCuspPolynomialAtom
        (thetaCuspLogDerivativePolynomial m) n x).deriv

/-- A summable envelope for a polynomial-Gaussian atom on `[-R,R]`. -/
def thetaCuspPolynomialMajorant (P : ℝ[X]) (R : ℝ) (n : ℕ) : ℝ :=
  Real.exp (R / 2) *
    (∑ k ∈ P.support, |P.coeff k| * ((n : ℝ) * Real.exp R) ^ k) *
    Real.exp (-(Real.pi * Real.exp (-2 * R)) * n)

theorem abs_eval_le_coefficient_sum (P : ℝ[X]) {y : ℝ} (hy : 0 ≤ y) :
    |eval y P| ≤ ∑ k ∈ P.support, |P.coeff k| * y ^ k := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  calc
    |∑ x ∈ P.support, P.coeff x * y ^ x| ≤
        ∑ x ∈ P.support, |P.coeff x * y ^ x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ P.support, |P.coeff x| * y ^ x := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [abs_mul, abs_pow, abs_of_nonneg hy]

theorem summable_thetaCuspPolynomialMajorant (P : ℝ[X]) (R : ℝ) :
    Summable (thetaCuspPolynomialMajorant P R) := by
  have hsigma : 0 < Real.pi * Real.exp (-2 * R) :=
    mul_pos Real.pi_pos (Real.exp_pos _)
  unfold thetaCuspPolynomialMajorant
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply summable_sum
  intro k _hk
  refine ((summable_pow_mul_exp_neg k hsigma).mul_left
    (Real.exp (R / 2) * |P.coeff k| * Real.exp R ^ k)).congr (fun n => ?_)
  ring_nf

theorem thetaCuspPolynomialMajorant_nonneg (P : ℝ[X]) (R : ℝ) (n : ℕ) :
    0 ≤ thetaCuspPolynomialMajorant P R n := by
  unfold thetaCuspPolynomialMajorant
  positivity

theorem abs_thetaCuspPolynomialAtom_le_majorant
    (P : ℝ[X]) {R x : ℝ} (hx : x ∈ Icc (-R) R) (n : ℕ) :
    |thetaCuspPolynomialAtom P n x| ≤ thetaCuspPolynomialMajorant P R n := by
  have hexpUpper : Real.exp x ≤ Real.exp R := Real.exp_le_exp.mpr hx.2
  have hexpHalf : Real.exp (x / 2) ≤ Real.exp (R / 2) :=
    Real.exp_le_exp.mpr (by linarith [hx.2])
  have hexpLower : Real.exp (-R) ≤ Real.exp x := Real.exp_le_exp.mpr hx.1
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
        have h1 : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast n.succ_pos
        nlinarith
  have hexpSq : Real.exp (-2 * R) ≤ Real.exp x ^ 2 := by
    rw [show Real.exp (-2 * R) = Real.exp (-R) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    exact (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).2 hexpLower
  have hscale : (n : ℝ) * Real.exp (-2 * R) ≤
      (n : ℝ) ^ 2 * Real.exp x ^ 2 := by
    calc
      (n : ℝ) * Real.exp (-2 * R) ≤ (n : ℝ) ^ 2 * Real.exp (-2 * R) := by gcongr
      _ ≤ (n : ℝ) ^ 2 * Real.exp x ^ 2 := by gcongr
  have hdecay : Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2) ≤
      Real.exp (-(Real.pi * Real.exp (-2 * R)) * n) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hscale Real.pi_pos.le
    nlinarith
  have hy : 0 ≤ (n : ℝ) * Real.exp x := by positivity
  have hcoeff :
      (∑ k ∈ P.support, |P.coeff k| * ((n : ℝ) * Real.exp x) ^ k) ≤
        ∑ k ∈ P.support, |P.coeff k| * ((n : ℝ) * Real.exp R) ^ k := by
    apply Finset.sum_le_sum
    intro k _hk
    gcongr
  rw [thetaCuspPolynomialAtom, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _)]
  have heval := abs_eval_le_coefficient_sum P hy
  let A : ℝ := Real.exp (R / 2) *
    (∑ k ∈ P.support, |P.coeff k| * ((n : ℝ) * Real.exp R) ^ k)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    Real.exp (x / 2) * |eval ((n : ℝ) * Real.exp x) P| *
        Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2) ≤
      Real.exp (R / 2) *
        (∑ k ∈ P.support, |P.coeff k| * ((n : ℝ) * Real.exp R) ^ k) *
        Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2) := by
      gcongr
      exact heval.trans hcoeff
    _ = A * Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2) := by rfl
    _ ≤ A * Real.exp (-(Real.pi * Real.exp (-2 * R)) * n) :=
      mul_le_mul_of_nonneg_left hdecay hA
    _ = thetaCuspPolynomialMajorant P R n := by rfl

theorem thetaCuspLogDerivativePolynomial_coeff_zero (m : ℕ) :
    (thetaCuspLogDerivativePolynomial m).coeff 0 = 0 := by
  induction m with
  | zero => simp [thetaCuspLogDerivativePolynomial, thetaCuspSeedPolynomial]
  | succ m ih =>
      simp [thetaCuspLogDerivativePolynomial, thetaCuspLogDerivativeStep, ih]

theorem thetaCuspPolynomialMajorant_derivative_zero (m : ℕ) (R : ℝ) :
    thetaCuspPolynomialMajorant (thetaCuspLogDerivativePolynomial m) R 0 = 0 := by
  unfold thetaCuspPolynomialMajorant
  have hsum : ∑ k ∈ (thetaCuspLogDerivativePolynomial m).support,
      |(thetaCuspLogDerivativePolynomial m).coeff k| * (0 : ℝ) ^ k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk0 : k ≠ 0 := by
      intro h
      subst k
      exact (Polynomial.mem_support_iff.mp hk)
        (thetaCuspLogDerivativePolynomial_coeff_zero m)
    rw [zero_pow hk0, mul_zero]
  simpa using hsum

/-- The `m`-th derivative series of the all-integer source. -/
def thetaCuspFullDerivative (m : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, iteratedDeriv m (fun y => thetaCuspSourceTerm y n) x

/-- The `m`-th derivative series of the finite-prime source. -/
def finitePrimeThetaCuspDerivative (m N : ℕ) (x : ℝ) : ℝ :=
  ∑' n : (N + 1).smoothNumbers,
    iteratedDeriv m (fun y => thetaCuspSourceTerm y n) x

theorem summable_iteratedDeriv_thetaCuspSourceTerm (m : ℕ) (x : ℝ) :
    Summable (fun n : ℕ => iteratedDeriv m (fun y => thetaCuspSourceTerm y n) x) := by
  let R := |x|
  have hx : x ∈ Icc (-R) R := by dsimp [R]; exact ⟨neg_abs_le x, le_abs_self x⟩
  have hM := summable_thetaCuspPolynomialMajorant (thetaCuspLogDerivativePolynomial m) R
  refine Summable.of_norm_bounded hM fun n => ?_
  rw [Real.norm_eq_abs, iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
  exact abs_thetaCuspPolynomialAtom_le_majorant _ hx n

theorem hasDerivAt_iteratedDeriv_thetaCuspSourceTerm (m n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv m (fun y => thetaCuspSourceTerm y n))
      (iteratedDeriv (m + 1) (fun y => thetaCuspSourceTerm y n) x) x := by
  rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom,
    iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
  exact hasDerivAt_thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial m) n x

theorem hasDerivAt_thetaCuspFullDerivative (m : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspFullDerivative m) (thetaCuspFullDerivative (m + 1) x) x := by
  let R : ℝ := |x| + 1
  have hx : x ∈ Ioo (-R) R := by dsimp [R]; constructor <;> linarith [neg_abs_le x, le_abs_self x]
  let u : ℕ → ℝ := thetaCuspPolynomialMajorant (thetaCuspLogDerivativePolynomial (m + 1)) R
  have hu : Summable u := summable_thetaCuspPolynomialMajorant _ _
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    ordConnected_Ioo.isPreconnected
    (fun n y _hy => hasDerivAt_iteratedDeriv_thetaCuspSourceTerm m n y)
    (fun n y hy => by
      rw [Real.norm_eq_abs, iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
      exact abs_thetaCuspPolynomialAtom_le_majorant _ (Ioo_subset_Icc_self hy) n)
    hx (summable_iteratedDeriv_thetaCuspSourceTerm m x) hx
  have hfun :
      thetaCuspFullDerivative m =
        fun z => ∑' n : ℕ, iteratedDeriv m (fun y => thetaCuspSourceTerm y n) z := by
    funext z
    rfl
  have hderiv :
      thetaCuspFullDerivative (m + 1) x =
        ∑' n : ℕ, iteratedDeriv (m + 1) (fun y => thetaCuspSourceTerm y n) x := rfl
  rw [hfun, hderiv]
  exact key

theorem hasDerivAt_finitePrimeThetaCuspDerivative (m N : ℕ) (x : ℝ) :
    HasDerivAt (finitePrimeThetaCuspDerivative m N)
      (finitePrimeThetaCuspDerivative (m + 1) N x) x := by
  let R : ℝ := |x| + 1
  have hx : x ∈ Ioo (-R) R := by dsimp [R]; constructor <;> linarith [neg_abs_le x, le_abs_self x]
  let u : (N + 1).smoothNumbers → ℝ := fun n =>
    thetaCuspPolynomialMajorant (thetaCuspLogDerivativePolynomial (m + 1)) R n
  have hu : Summable u :=
    (summable_thetaCuspPolynomialMajorant (thetaCuspLogDerivativePolynomial (m + 1)) R).subtype _
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    ordConnected_Ioo.isPreconnected
    (fun n y _hy => hasDerivAt_iteratedDeriv_thetaCuspSourceTerm m n y)
    (fun n y hy => by
      rw [Real.norm_eq_abs, iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
      exact abs_thetaCuspPolynomialAtom_le_majorant _ (Ioo_subset_Icc_self hy) n)
    hx ((summable_iteratedDeriv_thetaCuspSourceTerm m x).subtype _) hx
  have hfun :
      finitePrimeThetaCuspDerivative m N =
        fun z => ∑' n : (N + 1).smoothNumbers,
          iteratedDeriv m (fun y => thetaCuspSourceTerm y n) z := by
    funext z
    rfl
  have hderiv :
      finitePrimeThetaCuspDerivative (m + 1) N x =
        ∑' n : (N + 1).smoothNumbers,
          iteratedDeriv (m + 1) (fun y => thetaCuspSourceTerm y n) x := rfl
  rw [hfun, hderiv]
  exact key

/-- The derivative series is the actual iterated derivative of the all-integer theta-cusp source. -/
theorem iteratedDeriv_thetaCuspFullSource (m : ℕ) :
    iteratedDeriv m thetaCuspFullSource = thetaCuspFullDerivative m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_thetaCuspFullDerivative m x).deriv

/-- The derivative series is the actual iterated derivative of every finite-prime source. -/
theorem iteratedDeriv_finitePrimeThetaCuspSource (m N : ℕ) :
    iteratedDeriv m (finitePrimeThetaCuspSource N) = finitePrimeThetaCuspDerivative m N := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_finitePrimeThetaCuspDerivative m N x).deriv

/-- Every logarithmic derivative of the finite-prime source converges uniformly on `[-R,R]`. -/
theorem finitePrimeThetaCuspDerivative_tendstoUniformlyOn_Icc (m : ℕ) (R : ℝ) :
    TendstoUniformlyOn (finitePrimeThetaCuspDerivative m) (thetaCuspFullDerivative m) atTop
      (Icc (-R) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let M := thetaCuspPolynomialMajorant (thetaCuspLogDerivativePolynomial m) R
  obtain ⟨N0, hN0⟩ := EulerProduct.norm_tsum_smoothNumbers_sub_tsum_lt
    (summable_thetaCuspPolynomialMajorant (thetaCuspLogDerivativePolynomial m) R)
    (thetaCuspPolynomialMajorant_derivative_zero m R) hepsilon
  filter_upwards [eventually_ge_atTop N0] with N hN x hx
  let S : Set ℕ := (N + 1).smoothNumbers
  let f : ℕ → ℝ := fun n => iteratedDeriv m (fun y => thetaCuspSourceTerm y n) x
  have hf : Summable f := summable_iteratedDeriv_thetaCuspSourceTerm m x
  have hfSplit := hf.tsum_subtype_add_tsum_subtype_compl S
  have hdiff : thetaCuspFullDerivative m x - finitePrimeThetaCuspDerivative m N x =
      ∑' n : ↥(Sᶜ), f n := by
    rw [thetaCuspFullDerivative, finitePrimeThetaCuspDerivative]
    change (∑' n : ℕ, f n) - (∑' n : S, f n) = _
    rw [← hfSplit]
    ring
  have hnorm : |∑' n : ↥(Sᶜ), f n| ≤ ∑' n : ↥(Sᶜ), M n := by
    calc
      |∑' n : ↥(Sᶜ), f n| ≤ ∑' n : ↥(Sᶜ), |f n| :=
        norm_tsum_le_tsum_norm (hf.norm.subtype _)
      _ ≤ ∑' n : ↥(Sᶜ), M n :=
        (hf.norm.subtype _).tsum_le_tsum
          (fun n => by
            change |iteratedDeriv m (fun y => thetaCuspSourceTerm y n) x| ≤ M n
            rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
            exact abs_thetaCuspPolynomialAtom_le_majorant _ hx n)
          ((summable_thetaCuspPolynomialMajorant
            (thetaCuspLogDerivativePolynomial m) R).subtype _)
  have hM : Summable M := summable_thetaCuspPolynomialMajorant _ _
  have hMSplit := hM.tsum_subtype_add_tsum_subtype_compl S
  have hMdiff : (∑' n : ℕ, M n) - (∑' n : S, M n) = ∑' n : ↥(Sᶜ), M n := by
    rw [← hMSplit]
    ring
  have htailNonneg : 0 ≤ ∑' n : ↥(Sᶜ), M n :=
    tsum_nonneg fun n => thetaCuspPolynomialMajorant_nonneg _ _ n
  have htail : (∑' n : ↥(Sᶜ), M n) < epsilon := by
    have hNtail := hN0 (N + 1) (by omega)
    change |(∑' n : ℕ, M n) - (∑' n : S, M n)| < epsilon at hNtail
    rw [hMdiff, abs_of_nonneg htailNonneg] at hNtail
    exact hNtail
  rw [Real.dist_eq, hdiff]
  exact hnorm.trans_lt htail

/-- Smooth compact-local convergence of the actual finite-prime theta-cusp sources. -/
theorem iteratedDeriv_finitePrimeThetaCuspSource_tendstoUniformlyOn_Icc
    (m : ℕ) (R : ℝ) :
    TendstoUniformlyOn (fun N => iteratedDeriv m (finitePrimeThetaCuspSource N))
      (iteratedDeriv m thetaCuspFullSource) atTop (Icc (-R) R) := by
  simpa only [iteratedDeriv_finitePrimeThetaCuspSource,
    iteratedDeriv_thetaCuspFullSource] using
    finitePrimeThetaCuspDerivative_tendstoUniformlyOn_Icc m R

end RHTower
