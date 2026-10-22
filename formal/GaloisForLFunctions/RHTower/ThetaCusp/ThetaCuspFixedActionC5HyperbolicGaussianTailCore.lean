import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5JacobianCompensation
import GaloisForLFunctions.HTGeometry.HyperbolicBounds
import GaloisForLFunctions.RHTower.LegStripSteepness

open Set

namespace RHTower

noncomputable section

def c5HyperbolicShiftedSinhTerm (x : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => 5 * x ^ (2 : ℕ) *
      (x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ))

def c5HyperbolicCertificateSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  18 * ((3 * x) ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) -
    (119 / 2 : ℝ) * ((2 * x) ^ (2 * n + 1) /
      (Nat.factorial (2 * n + 1) : ℝ)) +
    65 * (x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) +
    c5HyperbolicShiftedSinhTerm x n -
    41 * x * ((2 * x) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) +
    129 * x * (x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) +
    (if n = 0 then -88 * x else 0)

def c5HyperbolicCertificate (x : ℝ) : ℝ :=
  Real.sinh x *
      (72 * Real.cosh x ^ (2 : ℕ) - 119 * Real.cosh x + 47 + 5 * x ^ (2 : ℕ)) -
    x * (82 * Real.cosh x ^ (2 : ℕ) - 129 * Real.cosh x + 47)

private theorem hasSum_c5HyperbolicShiftedSinhTerm (x : ℝ) :
    HasSum (c5HyperbolicShiftedSinhTerm x) (5 * x ^ (2 : ℕ) * Real.sinh x) := by
  have htail : HasSum (fun n => c5HyperbolicShiftedSinhTerm x (n + 1))
      (5 * x ^ (2 : ℕ) * Real.sinh x) := by
    have h := HasSum.const_smul (5 * x ^ (2 : ℕ)) (Real.hasSum_sinh x)
    convert h using 1 <;> simp [c5HyperbolicShiftedSinhTerm, smul_eq_mul]
  have hfull := (hasSum_nat_add_iff (f := c5HyperbolicShiftedSinhTerm x) 1).1 htail
  simpa only [Finset.sum_range_one, c5HyperbolicShiftedSinhTerm, add_zero] using hfull

private theorem hasSum_c5HyperbolicCertificateSeriesTerm (x : ℝ) :
    HasSum (c5HyperbolicCertificateSeriesTerm x) (c5HyperbolicCertificate x) := by
  have h3 := HasSum.const_smul (18 : ℝ) (Real.hasSum_sinh (3 * x))
  have h2 := HasSum.const_smul (-119 / 2 : ℝ) (Real.hasSum_sinh (2 * x))
  have h1 := HasSum.const_smul (65 : ℝ) (Real.hasSum_sinh x)
  have hs := hasSum_c5HyperbolicShiftedSinhTerm x
  have hc2 := HasSum.const_smul (-41 * x) (Real.hasSum_cosh (2 * x))
  have hc1 := HasSum.const_smul (129 * x) (Real.hasSum_cosh x)
  have hlin := hasSum_ite_eq (0 : ℕ) (-88 * x)
  have h := (((((h3.add h2).add h1).add hs).add hc2).add hc1).add hlin
  have hraw : HasSum (c5HyperbolicCertificateSeriesTerm x)
      (18 * Real.sinh (3 * x) - 119 / 2 * Real.sinh (2 * x) +
          65 * Real.sinh x + 5 * x ^ (2 : ℕ) * Real.sinh x -
        41 * x * Real.cosh (2 * x) + 129 * x * Real.cosh x + -88 * x) := by
    convert h using 1
    · funext n
      unfold c5HyperbolicCertificateSeriesTerm
      ring
    · ring
  have hvalue : c5HyperbolicCertificate x =
      18 * Real.sinh (3 * x) - 119 / 2 * Real.sinh (2 * x) +
          65 * Real.sinh x + 5 * x ^ (2 : ℕ) * Real.sinh x -
        41 * x * Real.cosh (2 * x) + 129 * x * Real.cosh x + -88 * x := by
    unfold c5HyperbolicCertificate
    rw [Real.sinh_three_mul, Real.sinh_two_mul, Real.cosh_two_mul]
    rw [Real.cosh_sq]
    ring
  rw [hvalue]
  exact hraw

private theorem c5Hyperbolic_exponential_core_pos {n : ℕ} (hn : 3 ≤ n) :
    (160 + 82 * (n : ℝ)) * (4 : ℝ) ^ n < 54 * (9 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ, pow_succ]
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hcoeff : 4 * (160 + 82 * ((n : ℝ) + 1)) <
          9 * (160 + 82 * (n : ℝ)) := by nlinarith
      have hpow : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
      calc
        (160 + 82 * ((n + 1 : ℕ) : ℝ)) * 4 ^ (n + 1) =
            (4 * (160 + 82 * ((n : ℝ) + 1))) * 4 ^ n := by
              norm_num
              ring
        _ < (9 * (160 + 82 * (n : ℝ))) * 4 ^ n :=
          mul_lt_mul_of_pos_right hcoeff hpow
        _ < 9 * (54 * 9 ^ n) := by nlinarith
        _ = 54 * 9 ^ (n + 1) := by ring

private theorem c5HyperbolicCertificateSeriesTerm_nonneg
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ c5HyperbolicCertificateSeriesTerm x n := by
  rcases lt_trichotomy n 3 with hn | hn | hn
  · interval_cases n <;>
      simp [c5HyperbolicCertificateSeriesTerm, c5HyperbolicShiftedSinhTerm] <;>
      ring_nf <;> rfl
  · subst n
    simp [c5HyperbolicCertificateSeriesTerm, c5HyperbolicShiftedSinhTerm]
    ring_nf
    positivity
  · have hcore := c5Hyperbolic_exponential_core_pos (show 3 ≤ n by omega)
    have hcoeff : 0 <
        54 * (9 : ℝ) ^ n - (160 + 82 * (n : ℝ)) * (4 : ℝ) ^ n +
          (20 * (n : ℝ) ^ (2 : ℕ) + 268 * (n : ℝ) + 194) := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [sq_nonneg (n : ℝ)]
    have hfac : 0 < (Nat.factorial (2 * n + 1) : ℝ) := by positivity
    have hpow : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx _
    have hformula :
        c5HyperbolicCertificateSeriesTerm x n =
          (54 * (9 : ℝ) ^ n - (160 + 82 * (n : ℝ)) * (4 : ℝ) ^ n +
              (20 * (n : ℝ) ^ (2 : ℕ) + 268 * (n : ℝ) + 194)) *
            x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ) := by
      cases n with
      | zero => omega
      | succ k =>
          simp only [c5HyperbolicCertificateSeriesTerm,
            c5HyperbolicShiftedSinhTerm]
          have hodd : 2 * (Nat.succ k) + 1 = (2 * k + 1) + 2 := by omega
          have heven : 2 * (Nat.succ k) = (2 * k + 1) + 1 := by omega
          have hfacOdd : (Nat.factorial (2 * (Nat.succ k) + 1) : ℝ) =
              ((2 * k + 3 : ℕ) : ℝ) * ((2 * k + 2 : ℕ) : ℝ) *
                (Nat.factorial (2 * k + 1) : ℝ) := by
            rw [hodd, show 2 * k + 1 + 2 = Nat.succ (Nat.succ (2 * k + 1)) by omega,
              Nat.factorial_succ, Nat.factorial_succ]
            push_cast
            ring
          have hfacEven : (Nat.factorial (2 * (Nat.succ k)) : ℝ) =
              ((2 * k + 2 : ℕ) : ℝ) * (Nat.factorial (2 * k + 1) : ℝ) := by
            rw [heven, show 2 * k + 1 + 1 = Nat.succ (2 * k + 1) by omega,
              Nat.factorial_succ]
            push_cast
            ring
          have hxpow : x ^ (2 * (Nat.succ k) + 1) =
              x ^ (2 : ℕ) * x ^ (2 * k + 1) := by rw [hodd, pow_add]; ring
          have hxpow' : x ^ (2 * (k + 1) + 1) =
              x ^ (2 : ℕ) * x ^ (2 * k + 1) := by
            simpa only [Nat.succ_eq_add_one] using hxpow
          have hxeven : x ^ (2 * (k + 1)) = x ^ (2 : ℕ) * x ^ (2 * k) := by
            rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
          have htwoOdd : (2 : ℝ) ^ (2 * (k + 1) + 1) =
              2 * 4 ^ (k + 1) := by
            rw [pow_add, pow_mul]
            norm_num
            ring
          have hthreeOdd : (3 : ℝ) ^ (2 * (k + 1) + 1) =
              3 * 9 ^ (k + 1) := by
            rw [pow_add, pow_mul]
            norm_num
            ring
          have htwoEven : (2 : ℝ) ^ (2 * (k + 1)) = 4 ^ (k + 1) := by
            rw [pow_mul]
            norm_num
          rw [hfacOdd, hfacEven]
          simp only [mul_pow]
          rw [hxpow, hxeven]
          rw [htwoOdd, hthreeOdd, htwoEven]
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
            Nat.cast_ofNat]
          push_cast
          field_simp [show (Nat.factorial (2 * k + 1) : ℝ) ≠ 0 by positivity]
          ring
    rw [hformula]
    exact div_nonneg (mul_nonneg hcoeff.le hpow) hfac.le

theorem c5HyperbolicCertificate_pos {x : ℝ} (hx : 0 < x) :
    0 < c5HyperbolicCertificate x := by
  let f := c5HyperbolicCertificateSeriesTerm x
  let g : ℕ → ℝ := fun n => if n = 3 then f n else 0
  have hf := hasSum_c5HyperbolicCertificateSeriesTerm x
  have hg : HasSum g (f 3) := by
    have h := hasSum_ite_eq (3 : ℕ) (f 3)
    convert h using 1
    funext n
    by_cases hn : n = 3
    · subst n
      simp [g]
    · simp [g, hn]
  have hle : ∀ n, g n ≤ f n := by
    intro n
    by_cases hn : n = 3
    · simp [g, hn]
    · simp only [g, hn, if_false]
      exact c5HyperbolicCertificateSeriesTerm_nonneg hx.le n
  have hsum := Summable.tsum_le_tsum hle hg.summable hf.summable
  rw [hg.tsum_eq, hf.tsum_eq] at hsum
  have hterm : 0 < f 3 := by
    dsimp [f]
    simp [c5HyperbolicCertificateSeriesTerm, c5HyperbolicShiftedSinhTerm]
    ring_nf
    positivity
  exact lt_of_lt_of_le hterm hsum

private def c5BoseLowerAuxOne (q : ℝ) : ℝ :=
  1 - (1 - q) * Real.exp q

private theorem c5BoseLowerAuxOne_pos {q : ℝ} (hq : 0 < q) :
    0 < c5BoseLowerAuxOne q := by
  have hmono : StrictMonoOn c5BoseLowerAuxOne (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · unfold c5BoseLowerAuxOne
      exact Continuous.continuousOn (by fun_prop)
    · intro x hx
      rw [interior_Ici] at hx
      have hderiv : HasDerivAt c5BoseLowerAuxOne (x * Real.exp x) x := by
        have hraw := (hasDerivAt_const x 1).sub
            (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul
              (Real.hasDerivAt_exp x))
        have hcongr : c5BoseLowerAuxOne =ᶠ[nhds x]
            ((fun y : ℝ => 1) - ((fun y : ℝ => 1) - id) * Real.exp) := by
          filter_upwards [] with y
          unfold c5BoseLowerAuxOne
          rfl
        have hderiv := hraw.congr_of_eventuallyEq hcongr
        change HasDerivAt c5BoseLowerAuxOne
          (0 - ((0 - 1) * Real.exp x + (1 - x) * Real.exp x)) x at hderiv
        have hvalue :
            0 - ((0 - 1) * Real.exp x + (1 - x) * Real.exp x) =
              x * Real.exp x := by
          ring
        rw [hvalue] at hderiv
        exact hderiv
      rw [hderiv.deriv]
      exact mul_pos hx (Real.exp_pos x)
  have h := hmono self_mem_Ici (mem_Ici.mpr hq.le) hq
  simpa [c5BoseLowerAuxOne] using h

private def c5BoseLowerAuxTwo (q : ℝ) : ℝ :=
  q - (1 - q / 2) * (Real.exp q - 1)

private theorem c5BoseLowerAuxTwo_pos {q : ℝ} (hq : 0 < q) :
    0 < c5BoseLowerAuxTwo q := by
  have hmono : StrictMonoOn c5BoseLowerAuxTwo (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · unfold c5BoseLowerAuxTwo
      exact Continuous.continuousOn (by fun_prop)
    · intro x hx
      rw [interior_Ici] at hx
      have hderiv : HasDerivAt c5BoseLowerAuxTwo
          (c5BoseLowerAuxOne x / 2) x := by
        have hleft := hasDerivAt_id x
        have hfactor := (hasDerivAt_const x 1).sub
          ((hasDerivAt_id x).const_mul (1 / 2 : ℝ))
        have hexp := (Real.hasDerivAt_exp x).sub_const 1
        have hraw := hleft.sub (hfactor.mul hexp)
        have hcongr : c5BoseLowerAuxTwo =ᶠ[nhds x]
            id - ((fun y : ℝ => 1) - fun y => (1 / 2 : ℝ) * id y) *
              (fun y => Real.exp y - 1) := by
          filter_upwards [] with y
          unfold c5BoseLowerAuxTwo
          dsimp
          ring
        have hderiv := hraw.congr_of_eventuallyEq hcongr
        change HasDerivAt c5BoseLowerAuxTwo
          (1 - ((0 - (1 / 2 : ℝ) * 1) * (Real.exp x - 1) +
            (1 - (1 / 2 : ℝ) * x) * Real.exp x)) x at hderiv
        have hvalue :
            1 - ((0 - (1 / 2 : ℝ) * 1) * (Real.exp x - 1) +
              (1 - (1 / 2 : ℝ) * x) * Real.exp x) =
                c5BoseLowerAuxOne x / 2 := by
          unfold c5BoseLowerAuxOne
          ring
        rw [hvalue] at hderiv
        exact hderiv
      rw [hderiv.deriv]
      exact div_pos (c5BoseLowerAuxOne_pos hx) (by norm_num)
  have h := hmono self_mem_Ici (mem_Ici.mpr hq.le) hq
  simpa [c5BoseLowerAuxTwo] using h

/-- Sharp global lower tangent for the Bose action radius. -/
theorem eight_add_six_mul_lt_ten_mul_add_eight_mul_div_exp_sub_one
    {q : ℝ} (hq : 0 < q) :
    8 + 6 * q < 10 * q + 8 * q / (Real.exp q - 1) := by
  have hr : 0 < Real.exp q - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hq
  have haux := c5BoseLowerAuxTwo_pos hq
  have hratio : 1 - q / 2 < q / (Real.exp q - 1) := by
    rw [lt_div_iff₀ hr]
    dsimp only [c5BoseLowerAuxTwo] at haux
    linarith
  calc
    8 + 6 * q = 10 * q + 8 * (1 - q / 2) := by ring
    _ < 10 * q + 8 * (q / (Real.exp q - 1)) := by nlinarith
    _ = 10 * q + 8 * q / (Real.exp q - 1) := by ring

/-- Pure hyperbolic Gaussian reflected action. -/
def c5HyperbolicGaussianAction (A t : ℝ) : ℝ :=
  2 * A * (Real.cosh (2 * t) - 1)

/-- First displacement jet of the pure hyperbolic Gaussian action. -/
def c5HyperbolicGaussianJetOne (A t : ℝ) : ℝ :=
  4 * A * Real.sinh (2 * t)

/-- Second displacement jet of the pure hyperbolic Gaussian action. -/
def c5HyperbolicGaussianJetTwo (A t : ℝ) : ℝ :=
  8 * A * Real.cosh (2 * t)

/-- Third displacement jet of the pure hyperbolic Gaussian action. -/
def c5HyperbolicGaussianJetThree (A t : ℝ) : ℝ :=
  16 * A * Real.sinh (2 * t)

/-- Fixed-action centre numerator for hyperbolic Gaussian velocity. -/
def c5HyperbolicGaussianVelocityCenterNumerator (A t : ℝ) : ℝ :=
  let q := c5HyperbolicGaussianAction A t
  let a := c5HyperbolicGaussianJetOne A t
  let b := c5HyperbolicGaussianJetTwo A t
  let s := 2 * q
  let m := 2 * a
  a * (t * m) - (a + t * b) * s

/-- Fixed-action centre numerator for hyperbolic Gaussian velocity--slope current. -/
def c5HyperbolicGaussianVelocitySlopeCenterNumerator (A t : ℝ) : ℝ :=
  let q := c5HyperbolicGaussianAction A t
  let a := c5HyperbolicGaussianJetOne A t
  let b := c5HyperbolicGaussianJetTwo A t
  let c := c5HyperbolicGaussianJetThree A t
  let s := 2 * q
  let m := 2 * a
  let n := 2 * b
  a * (t * m + t ^ (2 : ℕ) * n) - (a + 3 * t * b + t ^ (2 : ℕ) * c) * s

/-- Exact direct-C5 compensation numerator for the pure hyperbolic Gaussian scale flow. -/
def c5HyperbolicGaussianCompensationMargin (A t : ℝ) : ℝ :=
  let q := c5HyperbolicGaussianAction A t
  let v := t * c5HyperbolicGaussianJetOne A t
  5 * c5HyperbolicGaussianVelocitySlopeCenterNumerator A t -
    (14 + 10 * v + 8 * v / (Real.exp q - 1)) *
      c5HyperbolicGaussianVelocityCenterNumerator A t

private theorem c5HyperbolicGaussianVelocityCenterNumerator_eq
    (A t : ℝ) :
    c5HyperbolicGaussianVelocityCenterNumerator A t =
      -16 * A ^ (2 : ℕ) * (Real.cosh (2 * t) - 1) *
        (Real.sinh (2 * t) - 2 * t) := by
  unfold c5HyperbolicGaussianVelocityCenterNumerator
    c5HyperbolicGaussianAction c5HyperbolicGaussianJetOne
    c5HyperbolicGaussianJetTwo
  dsimp
  ring_nf
  rw [Real.sinh_sq]
  ring

private theorem c5HyperbolicGaussianVelocitySlopeCenterNumerator_eq
    (A t : ℝ) :
    c5HyperbolicGaussianVelocitySlopeCenterNumerator A t =
      -16 * A ^ (2 : ℕ) *
        ((Real.cosh (2 * t) - 1) * Real.sinh (2 * t) +
          2 * t * (Real.cosh (2 * t) - 1) *
            (2 * (Real.cosh (2 * t) - 1) + 1) -
          4 * t ^ (2 : ℕ) * Real.sinh (2 * t)) := by
  unfold c5HyperbolicGaussianVelocitySlopeCenterNumerator
    c5HyperbolicGaussianAction c5HyperbolicGaussianJetOne
    c5HyperbolicGaussianJetTwo c5HyperbolicGaussianJetThree
  dsimp
  ring_nf
  rw [Real.sinh_sq]
  ring

private theorem two_mul_cosh_sub_two_le_two_mul_self_mul_sinh
    {t : ℝ} :
    2 * (Real.cosh (2 * t) - 1) ≤ 2 * t * Real.sinh (2 * t) := by
  simpa only [mul_sub, mul_one, mul_assoc] using
    HTGeometry.two_cosh_sub_two_le_self_mul_sinh (2 * t)

/-- **Pure first-atom tail core.** The hyperbolic Gaussian action has strictly positive direct-C5
fixed-action compensation for every physical scale `A > 3` and displacement `t > 0`. -/
theorem c5HyperbolicGaussianCompensationMargin_pos
    {A t : ℝ} (hA : 3 < A) (ht : 0 < t) :
    0 < c5HyperbolicGaussianCompensationMargin A t := by
  let z := Real.cosh (2 * t) - 1
  let S := Real.sinh (2 * t)
  let q := 2 * A * z
  let v := 4 * A * t * S
  let r := Real.exp q - 1
  let h := 2 * t * S / z
  let D := S - 2 * t
  let K := z * S + 2 * t * z * (2 * z + 1) - 4 * t ^ (2 : ℕ) * S
  let W := 14 + 10 * v + 8 * v / r
  have hz : 0 < z := by
    dsimp only [z]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
  have hS : 0 < S := by
    dsimp only [S]
    exact Real.sinh_pos_iff.mpr (by linarith)
  have hD : 0 < D := by
    dsimp only [D, S]
    exact sub_pos.mpr (self_lt_sinh (by linarith : 0 < 2 * t))
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hr : 0 < r := by
    dsimp only [r]
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hq
  have hqz : 6 * z < q := by
    dsimp only [q]
    nlinarith
  have hhz : z ≤ t * S := by
    have hraw := two_mul_cosh_sub_two_le_two_mul_self_mul_sinh (t := t)
    dsimp only [z, S]
    linarith
  have hh : 2 ≤ h := by
    dsimp only [h]
    rw [le_div_iff₀ hz]
    nlinarith
  have hvqh : v = q * h := by
    dsimp only [v, q, h]
    field_simp [hz.ne']
    ring
  have hBose := eight_add_six_mul_lt_ten_mul_add_eight_mul_div_exp_sub_one hq
  have hbase : 0 < 8 + 6 * q := by positivity
  have hhBose : h * (8 + 6 * q) < h * (10 * q + 8 * q / r) :=
    mul_lt_mul_of_pos_left hBose (lt_of_lt_of_le (by norm_num) hh)
  have hW : 30 + 72 * z < W := by
    have hlow : 2 * (8 + 6 * q) ≤ h * (8 + 6 * q) :=
      mul_le_mul_of_nonneg_right hh hbase.le
    dsimp only [W]
    rw [hvqh]
    dsimp only [r] at hhBose ⊢
    calc
      30 + 72 * z < 14 + 2 * (8 + 6 * q) := by nlinarith
      _ ≤ 14 + h * (8 + 6 * q) := by linarith
      _ < 14 + h * (10 * q + 8 * q / (Real.exp q - 1)) := by linarith
      _ = 14 + 10 * (q * h) + 8 * (q * h) / (Real.exp q - 1) := by
        field_simp [hr.ne']
        ring
  have hcert : 0 < (30 + 72 * z) * z * D - 5 * K := by
    have hp := c5HyperbolicCertificate_pos (show 0 < 2 * t by linarith)
    dsimp only [c5HyperbolicCertificate, z, S, D, K] at hp ⊢
    convert hp using 1
    ring
  have hweighted :
      (30 + 72 * z) * z * D - 5 * K < W * z * D - 5 * K := by
    have hzd : 0 < z * D := mul_pos hz hD
    nlinarith [mul_lt_mul_of_pos_right hW hzd]
  have hfactor :
      c5HyperbolicGaussianCompensationMargin A t =
        16 * A ^ (2 : ℕ) * (W * z * D - 5 * K) := by
    unfold c5HyperbolicGaussianCompensationMargin
    rw [c5HyperbolicGaussianVelocityCenterNumerator_eq,
      c5HyperbolicGaussianVelocitySlopeCenterNumerator_eq]
    unfold c5HyperbolicGaussianAction c5HyperbolicGaussianJetOne
    dsimp only [z, S, q, v, r, D, K, W]
    ring
  rw [hfactor]
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
    (lt_trans hcert hweighted)

end

end RHTower
