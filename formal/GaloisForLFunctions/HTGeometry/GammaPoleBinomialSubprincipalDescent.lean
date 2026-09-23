import GaloisForLFunctions.HTGeometry.GammaPolePrincipalRemainderFreeness

/-!
# Binomial subprincipal descent for simple-pole jet packets

The principal coefficients of the simple-pole jets form a divided-power sequence.  Thus the
binomial quadratic packet `J₀ J_{j+k} - choose (j+k) j J_j J_k` loses its entire top pole grade.
When `j,k > 0`, exactly one contribution survives at the next grade: the principal coefficient of
`J_{j+k}` times the finite part of `J₀`.  For Gamma, relative finite-part freeness detects this
survivor on arbitrarily remote pole branches and yields an exact native pole-order law.
-/

open Complex Filter Topology Finset

namespace GaloisForLFunctions

noncomputable section

/-- Principal coefficient of the `j`th covariant jet of `U/x`. -/
def simplePoleJetPrincipalCoefficient (U : ℂ → ℂ) (j : ℕ) : ℂ :=
  U 0 * ((-1 : ℂ) ^ j * (j.factorial : ℂ))

/-- Canonical analytic remainder after the principal monomial of the `j`th jet of `U/x`. -/
def simplePoleJetRegularRemainder (U : ℂ → ℂ) (j : ℕ) (x : ℂ) : ℂ :=
  iteratedDeriv j (dslope U 0) x

theorem analyticAt_simplePoleJetRegularRemainder
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j : ℕ) :
    AnalyticAt ℂ (simplePoleJetRegularRemainder U j) 0 := by
  exact analyticAt_iteratedDeriv_of_analyticAt
    (analyticAt_dslope_zero_of_analyticAt hU) j

theorem simplePoleJetRegularRemainder_zero_zero
    (U : ℂ → ℂ) :
    simplePoleJetRegularRemainder U 0 0 = iteratedDeriv 1 U 0 := by
  simp [simplePoleJetRegularRemainder, dslope]

theorem simplePoleJetPrincipalCoefficient_ne_zero
    {U : ℂ → ℂ} (hU0 : U 0 ≠ 0) (j : ℕ) :
    simplePoleJetPrincipalCoefficient U j ≠ 0 := by
  exact mul_ne_zero hU0 (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by
    exact_mod_cast Nat.factorial_ne_zero j))

/-- The principal simple-pole coefficients obey the exact divided-power binomial law. -/
theorem simplePoleJetPrincipalCoefficient_binomial
    (U : ℂ → ℂ) (j k : ℕ) :
    simplePoleJetPrincipalCoefficient U 0 *
        simplePoleJetPrincipalCoefficient U (j + k) =
      (Nat.choose (j + k) j : ℂ) *
        simplePoleJetPrincipalCoefficient U j *
          simplePoleJetPrincipalCoefficient U k := by
  have hj : j ≤ j + k := Nat.le_add_right j k
  have hfacNat := Nat.choose_mul_factorial_mul_factorial hj
  have hfac :
      (Nat.choose (j + k) j : ℂ) * (j.factorial : ℂ) * (k.factorial : ℂ) =
        ((j + k).factorial : ℂ) := by
    simpa using congrArg (fun n : ℕ => (n : ℂ)) hfacNat
  simp only [simplePoleJetPrincipalCoefficient, pow_zero, Nat.factorial_zero]
  rw [pow_add]
  rw [← hfac]
  ring

/-- Quadratic jet packet whose top simple-pole grade cancels binomially. -/
def simplePoleBinomialJetDefect (U : ℂ → ℂ) (j k : ℕ) (x : ℂ) : ℂ :=
  simplePoleCovariantJetValue U 0 x *
      simplePoleCovariantJetValue U (j + k) x -
    (Nat.choose (j + k) j : ℂ) *
      simplePoleCovariantJetValue U j x *
        simplePoleCovariantJetValue U k x

theorem meromorphicAt_simplePoleBinomialJetDefect
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j k : ℕ) :
    MeromorphicAt (simplePoleBinomialJetDefect U j k) 0 := by
  exact (meromorphicAt_simplePoleCovariantJetValue hU 0).mul
      (meromorphicAt_simplePoleCovariantJetValue hU (j + k)) |>.sub
    ((analyticAt_const.meromorphicAt.mul
      (meromorphicAt_simplePoleCovariantJetValue hU j)).mul
        (meromorphicAt_simplePoleCovariantJetValue hU k))

/-- An analytic germ times a positive power vanishes on approach to the center. -/
theorem tendsto_pow_mul_analyticAt_zero
    {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0) {p : ℕ} (hp : 0 < p) :
    Tendsto (fun x : ℂ => x ^ p * R x) (𝓝[≠] 0) (𝓝 0) := by
  have h := (continuousAt_id.pow p).mul hR.continuousAt
  change ContinuousAt (fun x : ℂ => x ^ p * R x) 0 at h
  have h' : Tendsto (fun x : ℂ => x ^ p * R x) (𝓝[≠] 0)
      (𝓝 (0 ^ p * R 0)) :=
    h.mono_left nhdsWithin_le_nhds
  simpa [zero_pow hp.ne'] using h'

/-- **Universal one-grade binomial descent.**  After top-grade cancellation, the normalized
quadratic packet converges to the principal coefficient of `J_{j+k}` times the finite part of
`J₀`.  The positivity assumptions exclude the other two possible subprincipal contributions. -/
theorem tendsto_pow_add_one_mul_simplePoleBinomialJetDefect
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0)
    (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    Tendsto
      (fun x : ℂ => x ^ (j + k + 1) * simplePoleBinomialJetDefect U j k x)
      (𝓝[≠] 0)
      (𝓝 (simplePoleJetPrincipalCoefficient U (j + k) *
        simplePoleJetRegularRemainder U 0 0)) := by
  let C : ℕ → ℂ := simplePoleJetPrincipalCoefficient U
  let R : ℕ → ℂ → ℂ := simplePoleJetRegularRemainder U
  have hdecomp (q : ℕ) :
      simplePoleCovariantJetValue U q =ᶠ[𝓝[≠] 0]
        (fun x => C q * x⁻¹ ^ (q + 1) + R q x) := by
    filter_upwards [simplePoleCovariantJetValue_sub_principal_eventuallyEq hU q]
      with x hx
    change simplePoleCovariantJetValue U q x - C q * x⁻¹ ^ (q + 1) = R q x at hx
    calc
      simplePoleCovariantJetValue U q x =
          (simplePoleCovariantJetValue U q x - C q * x⁻¹ ^ (q + 1)) +
            C q * x⁻¹ ^ (q + 1) := by ring
      _ = R q x + C q * x⁻¹ ^ (q + 1) := by rw [hx]
      _ = C q * x⁻¹ ^ (q + 1) + R q x := by ring
  have hev :
      (fun x : ℂ => x ^ (j + k + 1) * simplePoleBinomialJetDefect U j k x) =ᶠ[𝓝[≠] 0]
      (fun x =>
        C 0 * x ^ (j + k) * R (j + k) x +
          C (j + k) * R 0 x +
          x ^ (j + k + 1) * (R 0 x * R (j + k) x) -
        (Nat.choose (j + k) j : ℂ) *
          (C j * x ^ k * R k x +
            C k * x ^ j * R j x +
            x ^ (j + k + 1) * (R j x * R k x))) := by
    filter_upwards [hdecomp 0, hdecomp (j + k), hdecomp j, hdecomp k,
      self_mem_nhdsWithin] with x h0 hs hjx hkx hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [simplePoleBinomialJetDefect]
    rw [h0, hs, hjx, hkx]
    have hpow (a b : ℕ) (hab : b ≤ a) :
        x ^ a * x⁻¹ ^ b = x ^ (a - b) := by
      rw [inv_pow, ← pow_sub₀ x hx0 hab]
    have hcancel : x ^ (j + k + 1) * x⁻¹ ^ (j + k + 1) = 1 := by
      rw [hpow (j + k + 1) (j + k + 1) le_rfl]
      simp
    have htop0 :
        x ^ (j + k + 1) *
            ((C 0 * x⁻¹ ^ (0 + 1)) * (C (j + k) * x⁻¹ ^ (j + k + 1))) =
          C 0 * C (j + k) * x⁻¹ := by
      have hinv0 : x⁻¹ ^ (0 + 1) * x⁻¹ ^ (j + k + 1) =
          x⁻¹ ^ (j + k + 1) * x⁻¹ := by
        rw [show 0 + 1 = 1 by omega, pow_one]
        ring
      calc
        _ = C 0 * C (j + k) *
            (x ^ (j + k + 1) *
              (x⁻¹ ^ (0 + 1) * x⁻¹ ^ (j + k + 1))) := by ring
        _ = C 0 * C (j + k) *
            ((x ^ (j + k + 1) * x⁻¹ ^ (j + k + 1)) * x⁻¹) := by
              rw [hinv0]
              ring
        _ = C 0 * C (j + k) * x⁻¹ := by rw [hcancel]; ring
    have htopjk :
        x ^ (j + k + 1) *
            ((C j * x⁻¹ ^ (j + 1)) * (C k * x⁻¹ ^ (k + 1))) =
          C j * C k * x⁻¹ := by
      have hinv : x⁻¹ ^ (j + 1) * x⁻¹ ^ (k + 1) =
          x⁻¹ ^ (j + k + 1) * x⁻¹ := by
        rw [← pow_add, show j + 1 + (k + 1) = (j + k + 1) + 1 by omega,
          pow_succ]
      calc
        _ = C j * C k *
            (x ^ (j + k + 1) *
              (x⁻¹ ^ (j + 1) * x⁻¹ ^ (k + 1))) := by ring
        _ = C j * C k *
            ((x ^ (j + k + 1) * x⁻¹ ^ (j + k + 1)) * x⁻¹) := by
              rw [hinv]
              ring
        _ = C j * C k * x⁻¹ := by rw [hcancel]; ring
    have h0s :
        x ^ (j + k + 1) * ((C 0 * x⁻¹ ^ (0 + 1)) * R (j + k) x) =
          C 0 * x ^ (j + k) * R (j + k) x := by
      rw [show 0 + 1 = 1 by omega]
      have hpow1 : x ^ (j + k + 1) * x⁻¹ ^ (1 : ℕ) = x ^ (j + k) := by
        simpa only [Nat.add_sub_cancel_right] using
          hpow (j + k + 1) 1 (by omega)
      calc
        _ = C 0 * (x ^ (j + k + 1) * x⁻¹ ^ (1 : ℕ)) * R (j + k) x := by ring
        _ = _ := by rw [hpow1]
    have hs0 :
        x ^ (j + k + 1) * (R 0 x * (C (j + k) * x⁻¹ ^ (j + k + 1))) =
          C (j + k) * R 0 x := by
      calc
        _ = C (j + k) * R 0 x *
            (x ^ (j + k + 1) * x⁻¹ ^ (j + k + 1)) := by ring
        _ = _ := by rw [hcancel]; ring
    have hjk :
        x ^ (j + k + 1) * ((C j * x⁻¹ ^ (j + 1)) * R k x) =
          C j * x ^ k * R k x := by
      have hpowj : x ^ (j + k + 1) * x⁻¹ ^ (j + 1) = x ^ k := by
        rw [hpow (j + k + 1) (j + 1) (by omega)]
        congr 1
        omega
      calc
        _ = C j * (x ^ (j + k + 1) * x⁻¹ ^ (j + 1)) * R k x := by ring
        _ = _ := by rw [hpowj]
    have hkj :
        x ^ (j + k + 1) * (R j x * (C k * x⁻¹ ^ (k + 1))) =
          C k * x ^ j * R j x := by
      have hpowk : x ^ (j + k + 1) * x⁻¹ ^ (k + 1) = x ^ j := by
        rw [hpow (j + k + 1) (k + 1) (by omega)]
        congr 1
        omega
      calc
        _ = C k * (x ^ (j + k + 1) * x⁻¹ ^ (k + 1)) * R j x := by ring
        _ = _ := by rw [hpowk]
    have hC := simplePoleJetPrincipalCoefficient_binomial U j k
    change C 0 * C (j + k) =
      (Nat.choose (j + k) j : ℂ) * C j * C k at hC
    linear_combination htop0 + h0s + hs0 -
      (Nat.choose (j + k) j : ℂ) * htopjk -
      (Nat.choose (j + k) j : ℂ) * hjk -
      (Nat.choose (j + k) j : ℂ) * hkj + x⁻¹ * hC
  have hR (q : ℕ) : AnalyticAt ℂ (R q) 0 :=
    analyticAt_simplePoleJetRegularRemainder hU q
  have h0sBase : Tendsto
      (fun x : ℂ => x ^ (j + k) * R (j + k) x)
      (𝓝[≠] 0) (𝓝 0) :=
    tendsto_pow_mul_analyticAt_zero (hR (j + k)) (by omega)
  have h0s : Tendsto
      (fun x : ℂ => C 0 * x ^ (j + k) * R (j + k) x)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using tendsto_const_nhds.mul h0sBase
  have hs0 : Tendsto (fun x : ℂ => C (j + k) * R 0 x)
      (𝓝[≠] 0) (𝓝 (C (j + k) * R 0 0)) :=
    tendsto_const_nhds.mul ((hR 0).continuousAt.mono_left inf_le_left)
  have hrr0 : Tendsto
      (fun x : ℂ => x ^ (j + k + 1) * (R 0 x * R (j + k) x))
      (𝓝[≠] 0) (𝓝 0) :=
    tendsto_pow_mul_analyticAt_zero ((hR 0).mul (hR (j + k)))
      (p := j + k + 1) (by omega)
  have hjr : Tendsto (fun x : ℂ => x ^ k * R k x) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_pow_mul_analyticAt_zero (hR k) (p := k) hk
  have hkr : Tendsto (fun x : ℂ => x ^ j * R j x) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_pow_mul_analyticAt_zero (hR j) (p := j) hj
  have hrrjk : Tendsto
      (fun x : ℂ => x ^ (j + k + 1) * (R j x * R k x))
      (𝓝[≠] 0) (𝓝 0) :=
    tendsto_pow_mul_analyticAt_zero ((hR j).mul (hR k))
      (p := j + k + 1) (by omega)
  have hjrC : Tendsto (fun x : ℂ => C j * x ^ k * R k x)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using tendsto_const_nhds.mul hjr
  have hkrC : Tendsto (fun x : ℂ => C k * x ^ j * R j x)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using tendsto_const_nhds.mul hkr
  have hleft : Tendsto
      (fun x : ℂ =>
        C 0 * x ^ (j + k) * R (j + k) x + C (j + k) * R 0 x +
          x ^ (j + k + 1) * (R 0 x * R (j + k) x))
      (𝓝[≠] 0) (𝓝 (C (j + k) * R 0 0)) := by
    simpa only [zero_add, add_zero] using (h0s.add hs0).add hrr0
  have hrightInside : Tendsto
      (fun x : ℂ => C j * x ^ k * R k x + C k * x ^ j * R j x +
        x ^ (j + k + 1) * (R j x * R k x))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [zero_add, add_zero] using (hjrC.add hkrC).add hrrjk
  have hright : Tendsto
      (fun x : ℂ => (Nat.choose (j + k) j : ℂ) *
        (C j * x ^ k * R k x + C k * x ^ j * R j x +
          x ^ (j + k + 1) * (R j x * R k x)))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hrightInside
  have hlim := hleft.sub hright
  simpa [C, R] using hlim.congr' (hev.mono fun _ hx => hx.symm)

/-- If the simple-pole numerator and its first derivative are nonzero, the binomial packet has
exactly one less pole grade than its two top monomials. -/
theorem meromorphicOrderAt_simplePoleBinomialJetDefect
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0)
    (hU0 : U 0 ≠ 0) (hU1 : iteratedDeriv 1 U 0 ≠ 0)
    (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    meromorphicOrderAt (simplePoleBinomialJetDefect U j k) 0 =
      ((-((j + k + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  refine meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul (j + k + 1)
    (meromorphicAt_simplePoleBinomialJetDefect hU j k)
    (c := simplePoleJetPrincipalCoefficient U (j + k) *
      simplePoleJetRegularRemainder U 0 0) ?_ ?_
  · exact mul_ne_zero (simplePoleJetPrincipalCoefficient_ne_zero hU0 (j + k))
      (by simpa [simplePoleJetRegularRemainder_zero_zero U] using hU1)
  · simpa only [sub_zero] using
      tendsto_pow_add_one_mul_simplePoleBinomialJetDefect hU j k hj hk

/-- Principal coefficient of a normalized Gamma covariant jet. -/
def gammaPoleJetPrincipalCoefficient (branch j : ℕ) : ℂ :=
  -(reciprocalGammaFactorialScale branch)⁻¹ ^ j *
    ((-1 : ℂ) ^ j * (j.factorial : ℂ))

theorem gammaPoleJetPrincipalCoefficient_ne_zero (branch j : ℕ) :
    gammaPoleJetPrincipalCoefficient branch j ≠ 0 := by
  exact mul_ne_zero
    (neg_ne_zero.mpr (pow_ne_zero _
      (inv_ne_zero (reciprocalGammaFactorialScale_ne_zero branch))))
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by
      exact_mod_cast Nat.factorial_ne_zero j))

theorem gammaPoleJetPrincipalCoefficient_binomial (branch j k : ℕ) :
    gammaPoleJetPrincipalCoefficient branch 0 *
        gammaPoleJetPrincipalCoefficient branch (j + k) =
      (Nat.choose (j + k) j : ℂ) *
        gammaPoleJetPrincipalCoefficient branch j *
          gammaPoleJetPrincipalCoefficient branch k := by
  have hj : j ≤ j + k := Nat.le_add_right j k
  have hfacNat := Nat.choose_mul_factorial_mul_factorial hj
  have hfac :
      (Nat.choose (j + k) j : ℂ) * (j.factorial : ℂ) * (k.factorial : ℂ) =
        ((j + k).factorial : ℂ) := by
    simpa using congrArg (fun n : ℕ => (n : ℂ)) hfacNat
  simp only [gammaPoleJetPrincipalCoefficient, pow_zero, neg_mul, one_mul]
  rw [pow_add, pow_add]
  rw [← hfac]
  ring

/-- Gamma specialization of the binomial quadratic jet packet. -/
def gammaPoleBinomialJetDefect (branch j k : ℕ) (x : ℂ) : ℂ :=
  gammaPoleCovariantJetValue branch 0 x *
      gammaPoleCovariantJetValue branch (j + k) x -
    (Nat.choose (j + k) j : ℂ) *
      gammaPoleCovariantJetValue branch j x *
        gammaPoleCovariantJetValue branch k x

theorem gammaPoleBinomialJetDefect_eq_scaled_simplePole
    (branch j k : ℕ) (x : ℂ) :
    gammaPoleBinomialJetDefect branch j k x =
      (reciprocalGammaFactorialScale branch)⁻¹ ^ (j + k) *
        simplePoleBinomialJetDefect (gammaPoleRegularUnit branch) j k x := by
  simp only [gammaPoleBinomialJetDefect, gammaPoleCovariantJetValue,
    simplePoleBinomialJetDefect]
  rw [pow_add]
  ring

theorem meromorphicAt_gammaPoleBinomialJetDefect (branch j k : ℕ) :
    MeromorphicAt (gammaPoleBinomialJetDefect branch j k) 0 := by
  exact (meromorphicAt_gammaPoleCovariantJetValue branch 0).mul
      (meromorphicAt_gammaPoleCovariantJetValue branch (j + k)) |>.sub
    ((analyticAt_const.meromorphicAt.mul
      (meromorphicAt_gammaPoleCovariantJetValue branch j)).mul
        (meromorphicAt_gammaPoleCovariantJetValue branch k))

/-- Gamma value reflection of the universal one-grade descent. -/
theorem tendsto_pow_add_one_mul_gammaPoleBinomialJetDefect
    (branch j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    Tendsto
      (fun x : ℂ => x ^ (j + k + 1) * gammaPoleBinomialJetDefect branch j k x)
      (𝓝[≠] 0)
      (𝓝 (gammaPoleJetPrincipalCoefficient branch (j + k) *
        gammaPoleJetRegularRemainder branch 0 0)) := by
  have hlim := tendsto_pow_add_one_mul_simplePoleBinomialJetDefect
    (gammaPoleRegularUnit_analyticAt_zero branch) j k hj hk
  let s : ℂ := (reciprocalGammaFactorialScale branch)⁻¹ ^ (j + k)
  have hscale : Tendsto
      (fun x : ℂ => s *
        (x ^ (j + k + 1) *
          simplePoleBinomialJetDefect (gammaPoleRegularUnit branch) j k x))
      (𝓝[≠] 0)
      (𝓝 (s *
        (simplePoleJetPrincipalCoefficient (gammaPoleRegularUnit branch) (j + k) *
          simplePoleJetRegularRemainder (gammaPoleRegularUnit branch) 0 0))) :=
    tendsto_const_nhds.mul hlim
  have htarget :
      (reciprocalGammaFactorialScale branch)⁻¹ ^ (j + k) *
          (simplePoleJetPrincipalCoefficient (gammaPoleRegularUnit branch) (j + k) *
            simplePoleJetRegularRemainder (gammaPoleRegularUnit branch) 0 0) =
        gammaPoleJetPrincipalCoefficient branch (j + k) *
          gammaPoleJetRegularRemainder branch 0 0 := by
    simp [simplePoleJetPrincipalCoefficient, simplePoleJetRegularRemainder,
      gammaPoleJetPrincipalCoefficient, gammaPoleJetRegularRemainder,
      gammaPoleRegularUnit_zero]
    ring
  rw [← htarget]
  exact hscale.congr' (Filter.Eventually.of_forall fun x => by
    dsimp [s]
    rw [gammaPoleBinomialJetDefect_eq_scaled_simplePole]
    ring)

theorem meromorphicOrderAt_gammaPoleBinomialJetDefect
    (branch j k : ℕ) (hj : 0 < j) (hk : 0 < k)
    (hfinite : gammaPoleJetRegularRemainder branch 0 0 ≠ 0) :
    meromorphicOrderAt (gammaPoleBinomialJetDefect branch j k) 0 =
      ((-((j + k + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  apply meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul (j + k + 1)
    (meromorphicAt_gammaPoleBinomialJetDefect branch j k)
  · exact mul_ne_zero (gammaPoleJetPrincipalCoefficient_ne_zero branch (j + k)) hfinite
  · simpa only [sub_zero] using
      tendsto_pow_add_one_mul_gammaPoleBinomialJetDefect branch j k hj hk

/-- Relative finite-part freeness detects a nonzero subprincipal survivor arbitrarily far along
the Gamma pole tower. -/
theorem exists_cofinal_gammaPoleJetRegularRemainder_zero_ne_zero (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧ gammaPoleJetRegularRemainder branch 0 0 ≠ 0 := by
  have hgerm : gammaPoleFinitePartJetGerm 0 ≠ 0 := by
    have hX : (MvPolynomial.X 0 : MvPolynomial ℕ GammaPoleRationalBase) ≠ 0 :=
      MvPolynomial.X_ne_zero 0
    have heval := gammaPoleFinitePartJetRationalEval_injective.ne hX
    simpa [gammaPoleFinitePartJetRationalEval] using heval
  by_contra hdetect
  simp only [not_exists, not_and, not_not] at hdetect
  apply hgerm
  change (↑(fun N : ℕ => gammaPoleJetRegularRemainder (N - 1) 0 0) : NatGerm) = 0
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
  exact Filter.eventually_atTop.2 ⟨B + 1, fun N hN =>
    hdetect (N - 1) (by omega)⟩

/-- On arbitrarily remote Gamma branches, the binomial top cancellation descends by exactly one
pole grade and no farther. -/
theorem exists_cofinal_meromorphicOrderAt_gammaPoleBinomialJetDefect
    (j k : ℕ) (hj : 0 < j) (hk : 0 < k) (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      meromorphicOrderAt (gammaPoleBinomialJetDefect branch j k) 0 =
        ((-((j + k + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨branch, hbranch, hfinite⟩ :=
    exists_cofinal_gammaPoleJetRegularRemainder_zero_ne_zero B
  exact ⟨branch, hbranch,
    meromorphicOrderAt_gammaPoleBinomialJetDefect branch j k hj hk hfinite⟩

/-- The same binomial packet formed from native affine Gamma derivatives. -/
def gammaAffineBinomialJetDefect (branch j k : ℕ) (x : ℂ) : ℂ :=
  iteratedDeriv 0 Complex.Gamma
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) *
    iteratedDeriv (j + k) Complex.Gamma
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) -
    (Nat.choose (j + k) j : ℂ) *
      iteratedDeriv j Complex.Gamma
        (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) *
      iteratedDeriv k Complex.Gamma
        (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)

theorem gammaAffineBinomialJetDefect_eventuallyEq_covariant (branch j k : ℕ) :
    gammaAffineBinomialJetDefect branch j k =ᶠ[𝓝[≠] 0]
      gammaPoleBinomialJetDefect branch j k := by
  filter_upwards [gammaPoleJet_eventuallyEq_covariant branch 0,
    gammaPoleJet_eventuallyEq_covariant branch (j + k),
    gammaPoleJet_eventuallyEq_covariant branch j,
    gammaPoleJet_eventuallyEq_covariant branch k] with x h0 hs hjx hkx
  simp only [gammaAffineBinomialJetDefect, gammaPoleBinomialJetDefect]
  rw [h0, hs, hjx, hkx]

/-- **Native Gamma binomial descent.**  The exact one-grade drop is visible on arbitrarily remote
actual Gamma poles, not only in the covariant model. -/
theorem exists_cofinal_meromorphicOrderAt_gammaAffineBinomialJetDefect
    (j k : ℕ) (hj : 0 < j) (hk : 0 < k) (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      meromorphicOrderAt (gammaAffineBinomialJetDefect branch j k) 0 =
        ((-((j + k + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨branch, hbranch, horder⟩ :=
    exists_cofinal_meromorphicOrderAt_gammaPoleBinomialJetDefect j k hj hk B
  refine ⟨branch, hbranch, ?_⟩
  rw [meromorphicOrderAt_congr
    (gammaAffineBinomialJetDefect_eventuallyEq_covariant branch j k)]
  exact horder

/-- The classical mixed second-jet tie is the `(j,k) = (1,1)` member of the binomial family. -/
theorem gammaAffineBinomialJetDefect_one_one (branch : ℕ) (x : ℂ) :
    gammaAffineBinomialJetDefect branch 1 1 x =
      Complex.Gamma (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) *
          iteratedDeriv 2 Complex.Gamma
            (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) -
        2 * (iteratedDeriv 1 Complex.Gamma
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) ^ (2 : ℕ) := by
  simp [gammaAffineBinomialJetDefect]
  ring

/-- **Exact local law for the mixed second-jet obstruction.**  The packet
`Γ·Γ″ - 2(Γ′)²`, previously used only through global nonidentity, has exact normalized pole order
`-3` on arbitrarily remote Gamma branches. -/
theorem exists_cofinal_meromorphicOrderAt_gammaAffineSecondJetTie (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      meromorphicOrderAt
        (fun x : ℂ =>
          Complex.Gamma (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) *
              iteratedDeriv 2 Complex.Gamma
                (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) -
            2 * (iteratedDeriv 1 Complex.Gamma
              (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) ^ (2 : ℕ)) 0 =
        ((-3 : ℤ) : WithTop ℤ) := by
  obtain ⟨branch, hbranch, horder⟩ :=
    exists_cofinal_meromorphicOrderAt_gammaAffineBinomialJetDefect
      1 1 (by omega) (by omega) B
  refine ⟨branch, hbranch, ?_⟩
  have hev :
      (fun x : ℂ =>
        Complex.Gamma (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) *
            iteratedDeriv 2 Complex.Gamma
              (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) -
          2 * (iteratedDeriv 1 Complex.Gamma
            (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) ^ (2 : ℕ)) =ᶠ[𝓝[≠] 0]
        gammaAffineBinomialJetDefect branch 1 1 :=
    Filter.Eventually.of_forall fun x =>
      (gammaAffineBinomialJetDefect_one_one branch x).symm
  rw [meromorphicOrderAt_congr hev]
  exact horder

end

end GaloisForLFunctions
