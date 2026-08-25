import GaloisForLFunctions.RHTower.PolynomialFockLocalEvaluation
import GaloisForLFunctions.RHTower.PolynomialFockPrimeBallOverlap
import GaloisForLFunctions.RHTower.PolynomialFockCriticalPrimeSampling
import GaloisForLFunctions.RHTower.PolynomialFockLowDegreeLocalEvaluation
import GaloisForLFunctions.HTGeometry.QuasinilpotentLowering

/-!
# Sharp phase transition for critical-prime polynomial Fock sampling

Tangent-scale peak vectors and exact prime-window asymptotics prove that normalized critical-prime
evaluation is Bessel exactly for `m ≥ 4`. At the quartic endpoint, cofinal coordinate tails retain
uniform operator norm, so sampler is not compact; superquartic compactness gives exact threshold
`m > 4`.
-/

open MeasureTheory Set Metric
open Filter Topology
open scoped Real

namespace RHTower

noncomputable section


theorem normSq_polynomialMomentFockKernel_upper
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) :
    ‖momentFockKernel (polynomialMomentFockData m (by linarith)) (x : ℂ)‖ ^ 2 ≤
      Real.exp (2 * polynomialFockPotential m x +
        2 * (polynomialFockLocalBregmanConstant m / m)) /
        (Real.pi * polynomialFockTangentRadius m x ^ 2) := by
  let hm2 : 2 ≤ m := by linarith
  let d : MomentFockData := polynomialMomentFockData m hm2
  let f : MomentFock := momentFockKernel d (x : ℂ)
  let W : ℂ → ℝ := polynomialMomentFockWeightedNormSq m hm2 f
  have hmean := polynomialFock_tangentRadius_weighted_mean hm hx
    (polynomialMomentFockFunction m hm2 f)
    (differentiable_polynomialMomentFockFunction m hm2 f)
  rw [polynomialMomentFockFunction_eq_evaluation] at hmean
  have hFx : polynomialMomentFockEvaluation m hm2 (x : ℂ) f =
      (‖f‖ ^ 2 : ℝ) := by
    change inner ℂ f f = (‖f‖ ^ 2 : ℝ)
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hFx, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at hmean
  have hlocal :
      (∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x), W z) ≤
        ∫ z : ℂ, W z := by
    exact MeasureTheory.setIntegral_le_integral
      (integrable_polynomialMomentFockWeightedNormSq m hm2 f)
      (Filter.Eventually.of_forall fun z =>
        polynomialMomentFockWeightedNormSq_nonneg m hm2 f z)
  have htotal : (∫ z : ℂ, W z) = ‖f‖ ^ 2 :=
    integral_polynomialMomentFockWeightedNormSq m hm2 f
  have hbound :
      Real.pi * polynomialFockTangentRadius m x ^ 2 * (‖f‖ ^ 2) ^ 2 ≤
        Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLocalBregmanConstant m / m)) * ‖f‖ ^ 2 := by
    calc
      _ ≤ Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLocalBregmanConstant m / m)) *
          ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x), W z := by
        simpa [W, polynomialMomentFockWeightedNormSq] using hmean
      _ ≤ Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLocalBregmanConstant m / m)) * ∫ z : ℂ, W z := by
        gcongr
      _ = _ := by rw [htotal]
  have hfpos : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (momentFockKernel_ne_zero d _))
  have hcancel :
      Real.pi * polynomialFockTangentRadius m x ^ 2 * ‖f‖ ^ 2 ≤
        Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLocalBregmanConstant m / m)) := by
    nlinarith
  have hden : 0 < Real.pi * polynomialFockTangentRadius m x ^ 2 :=
    mul_pos Real.pi_pos (sq_pos_of_pos (polynomialFockTangentRadius_pos (by linarith)))
  rw [div_eq_mul_inv]
  apply (le_mul_inv_iff₀ hden).2
  simpa [f, d, mul_comm, mul_left_comm, mul_assoc] using hcancel

theorem tangentVector_normalizedKernel_local_lower
    {m x y : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : |y - x| ≤ polynomialFockTangentRadius m x) :
    Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
          (m * (1 + x ^ 2) ^ (m / 2 - 1)) *
          ‖polynomialMomentFockTangentVector m (by linarith) x‖ ^ 2 ≤
      (m * (1 + y ^ 2) ^ (m / 2 - 1)) *
        ‖inner ℂ (normalizedMomentFockKernel
          (polynomialMomentFockData m (by linarith)) (y : ℂ))
          (polynomialMomentFockTangentVector m (by linarith) x)‖ ^ 2 := by
  let hm2 : 2 ≤ m := by linarith
  let d : MomentFockData := polynomialMomentFockData m hm2
  let T : MomentFock := polynomialMomentFockTangentVector m hm2 x
  let cx : ℝ := m * (1 + x ^ 2) ^ (m / 2 - 1)
  let cy : ℝ := m * (1 + y ^ 2) ^ (m / 2 - 1)
  let K : ℝ := ‖momentFockKernel d (y : ℂ)‖ ^ 2
  let U : ℝ := ‖inner ℂ (normalizedMomentFockKernel d (y : ℂ)) T‖ ^ 2
  let V : ℝ := ‖T‖ ^ 2
  let C : ℝ := polynomialFockLocalBregmanConstant m / m
  let F : ℝ := Real.exp (2 * polynomialFockRadialSlope m x * (y - x))
  have hcx : 0 < cx := by dsimp [cx]; positivity
  have hcy : 0 < cy := by dsimp [cy]; positivity
  have hK : 0 < K := by
    dsimp [K, d]
    exact sq_pos_of_pos (norm_pos_iff.mpr (momentFockKernel_ne_zero _ _))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hTid : U * K = F := by
    have hid := normSq_inner_normalizedMomentFockKernel_mul_kernelNormSq d (y : ℂ) T
    dsimp [d] at hid
    change ‖inner ℂ (normalizedMomentFockKernel
        (polynomialMomentFockData m hm2) (y : ℂ)) T‖ ^ 2 *
        ‖momentFockKernel (polynomialMomentFockData m hm2) (y : ℂ)‖ ^ 2 =
      ‖polynomialMomentFockEvaluation m hm2 (y : ℂ) T‖ ^ 2 at hid
    rw [← polynomialMomentFockFunction_eq_evaluation,
      polynomialMomentFockFunction_tangentVector,
      Complex.norm_exp, ← Real.exp_nat_mul] at hid
    have hre : (((polynomialFockRadialSlope m x : ℂ) * ((y : ℂ) - x)).re) =
        polynomialFockRadialSlope m x * (y - x) := by simp
    rw [hre] at hid
    dsimp [U, K, F, T, d]
    convert hid using 1
    all_goals ring_nf
  have hTupper : V ≤ Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / cx) := by
    simpa [V, T, cx] using normSq_polynomialMomentFockTangentVector_le m hm2 x
  have hKupper : K ≤
      Real.exp (2 * polynomialFockPotential m y + 2 * C) * (cy / Real.pi) := by
    have h := normSq_polynomialMomentFockKernel_upper hm hy
    rw [polynomialFockTangentRadius_sq (by linarith)] at h
    have hden : 0 < cy := hcy
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    dsimp [K, d, C, cy]
    convert h using 1
    all_goals field_simp
  have hbreg :
      polynomialFockPotential m y - polynomialFockPotential m x -
          polynomialFockRadialSlope m x * (y - x) ≤ C := by
    have hw : ‖((y - x : ℝ) : ℂ)‖ ≤ polynomialFockTangentRadius m x := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hxy
    have h := polynomialFockPotential_bregman_upper_tangentRadius hm hx hw
    simpa [Complex.norm_real, Real.norm_of_nonneg hy, C] using h
  have hexp :
      Real.exp (-4 * C) * cx *
          (Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / cx)) *
          (Real.exp (2 * polynomialFockPotential m y + 2 * C) * (cy / Real.pi)) ≤
        cy * F := by
    have harg :
        -4 * C - 2 * polynomialFockPotential m x +
            (2 * polynomialFockPotential m y + 2 * C) ≤
          2 * polynomialFockRadialSlope m x * (y - x) := by
      linarith
    dsimp [F]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hcx0 : cx ≠ 0 := hcx.ne'
    calc
      _ = cy * (Real.exp (-4 * C) *
          Real.exp (-2 * polynomialFockPotential m x) *
          Real.exp (2 * polynomialFockPotential m y + 2 * C)) := by
        field_simp
      _ = cy * Real.exp
          (-4 * C - 2 * polynomialFockPotential m x +
            (2 * polynomialFockPotential m y + 2 * C)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring
      _ ≤ cy * Real.exp (2 * polynomialFockRadialSlope m x * (y - x)) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hcy.le
      _ = _ := by ring
  have hprod : Real.exp (-4 * C) * cx * V * K ≤ cy * F := by
    calc
      Real.exp (-4 * C) * cx * V * K ≤
          Real.exp (-4 * C) * cx *
            (Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / cx)) * K := by
        gcongr
      _ ≤ Real.exp (-4 * C) * cx *
            (Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / cx)) *
            (Real.exp (2 * polynomialFockPotential m y + 2 * C) * (cy / Real.pi)) := by
        gcongr
      _ ≤ cy * F := hexp
  have hcancel : Real.exp (-4 * C) * cx * V ≤ cy * U := by
    apply le_of_mul_le_mul_right (a := K)
    · calc
        Real.exp (-4 * C) * cx * V * K ≤ cy * F := hprod
        _ = cy * (U * K) := by rw [hTid]
        _ = cy * U * K := by ring
    · exact hK
  simpa [cx, cy, V, U, T, d, C] using hcancel

theorem polynomialFockTangentCurvature_local_le
    {m x y : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x)
    (hxy : |y - x| ≤ polynomialFockTangentRadius m x) :
    m * (1 + y ^ 2) ^ (m / 2 - 1) ≤
      3 ^ (m / 2 - 1) * (m * (1 + x ^ 2) ^ (m / 2 - 1)) := by
  have hr : polynomialFockTangentRadius m x ≤ 1 / 2 :=
    polynomialFockTangentRadius_le_half hm
  have hyx : y ≤ x + 1 / 2 := by
    have := (abs_le.mp (hxy.trans hr)).2
    linarith
  have hy0 : 0 ≤ y := by
    have := (abs_le.mp (hxy.trans hr)).1
    linarith
  have hbase : 1 + y ^ 2 ≤ 3 * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (y - (x + 1 / 2)), sq_nonneg y, sq_nonneg x,
      mul_self_le_mul_self hy0 hyx]
  have hβ : 0 ≤ m / 2 - 1 := by linarith
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + y ^ 2) hbase hβ
  rw [Real.mul_rpow (by norm_num : 0 ≤ (3 : ℝ)) (by positivity : 0 ≤ 1 + x ^ 2)] at hp
  nlinarith [show 0 ≤ m by linarith,
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) (m / 2 - 1),
    Real.rpow_nonneg (by positivity : 0 ≤ 1 + x ^ 2) (m / 2 - 1)]

theorem tangentVector_normalizedKernel_uniform_local_lower
    {m x y : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hxy : |y - x| ≤ polynomialFockTangentRadius m x) :
    Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
        ‖polynomialMomentFockTangentVector m (by linarith) x‖ ^ 2 ≤
      3 ^ (m / 2 - 1) *
        ‖inner ℂ (normalizedMomentFockKernel
          (polynomialMomentFockData m (by linarith)) (y : ℂ))
          (polynomialMomentFockTangentVector m (by linarith) x)‖ ^ 2 := by
  let hm2 : 2 ≤ m := by linarith
  let cx : ℝ := m * (1 + x ^ 2) ^ (m / 2 - 1)
  let cy : ℝ := m * (1 + y ^ 2) ^ (m / 2 - 1)
  let V : ℝ := ‖polynomialMomentFockTangentVector m hm2 x‖ ^ 2
  let U : ℝ := ‖inner ℂ (normalizedMomentFockKernel
    (polynomialMomentFockData m hm2) (y : ℂ))
    (polynomialMomentFockTangentVector m hm2 x)‖ ^ 2
  let E : ℝ := Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m))
  let Q : ℝ := 3 ^ (m / 2 - 1)
  have hcx : 0 < cx := by dsimp [cx]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hlocal : E * cx * V ≤ cy * U := by
    simpa [E, cx, cy, V, U, hm2] using
      tangentVector_normalizedKernel_local_lower hm (le_trans zero_le_one hx) hy hxy
  have hscale : cy ≤ Q * cx := by
    simpa [cx, cy, Q] using polynomialFockTangentCurvature_local_le hm hx hxy
  have hchain : E * cx * V ≤ Q * cx * U :=
    hlocal.trans (mul_le_mul_of_nonneg_right hscale hU)
  have hcancel : E * V ≤ Q * U := by
    apply le_of_mul_le_mul_left (a := cx)
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hchain
    · exact hcx
  simpa [E, Q, V, U, hm2] using hcancel

def polynomialFockInnerWindowFactor (m : ℝ) : ℝ :=
  (Real.sqrt (m * 2 ^ (m / 2 - 1)))⁻¹

theorem polynomialFockInnerWindowFactor_pos
    {m : ℝ} (hm : 4 ≤ m) : 0 < polynomialFockInnerWindowFactor m := by
  unfold polynomialFockInnerWindowFactor
  positivity

theorem scaledCriticalPrimeFockRadius_le_tangentRadius
    {m x : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) :
    polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x ≤
      polynomialFockTangentRadius m x := by
  let β : ℝ := m / 2 - 1
  have hm0 : 0 < m := by linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hbase : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + x ^ 2) hbase hβ
  rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (sq_nonneg x)] at hp
  have hxsq : (x ^ 2) ^ β = x ^ (2 * β) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx0.le]
    norm_num
  rw [hxsq] at hp
  have hden :
      m * (1 + x ^ 2) ^ β ≤ m * (2 ^ β * x ^ (2 * β)) := by
    exact mul_le_mul_of_nonneg_left hp hm0.le
  have hleft0 : 0 ≤ polynomialFockInnerWindowFactor m *
      criticalPrimeFockRadius m x :=
    mul_nonneg (polynomialFockInnerWindowFactor_pos hm).le
      (criticalPrimeFockRadius_pos hx0).le
  have hright0 : 0 ≤ polynomialFockTangentRadius m x :=
    (polynomialFockTangentRadius_pos hm0).le
  apply (sq_le_sq₀ hleft0 hright0).mp
  rw [mul_pow, polynomialFockTangentRadius_sq hm0]
  have hfacSq : polynomialFockInnerWindowFactor m ^ 2 =
      (m * 2 ^ β)⁻¹ := by
    have hc : 0 ≤ m * 2 ^ β :=
      mul_nonneg hm0.le (Real.rpow_nonneg (by norm_num) β)
    unfold polynomialFockInnerWindowFactor
    rw [inv_pow, Real.sq_sqrt (by simpa [β] using hc)]
  rw [hfacSq, criticalPrimeFockRadius_eq_rpow hx0.le]
  rw [← Real.rpow_natCast (x ^ (1 - m / 2)) 2,
    ← Real.rpow_mul hx0.le]
  norm_num only [Nat.cast_ofNat]
  have hexp : (1 - m / 2) * 2 = -(2 * β) := by dsimp [β]; ring
  rw [hexp, Real.rpow_neg hx0.le]
  have hlowpos : 0 < m * (1 + x ^ 2) ^ β := by positivity
  have hinv := inv_anti₀ hlowpos hden
  simpa [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hinv

theorem tendsto_primeLogWindowMass_scaledCriticalPrimeFockRadius_atTop
    {m c : ℝ} (hm2 : 2 < m) (hm4 : m < 4) (hc : 0 < c) :
    Tendsto (fun x => primeLogWindowMass x
      (c * criticalPrimeFockRadius m x)) atTop atTop := by
  have hr0 : Tendsto (fun x => c * criticalPrimeFockRadius m x) atTop (nhds 0) := by
    simpa using (tendsto_criticalPrimeFockRadius_zero hm2).const_mul c
  have hrpos : ∀ᶠ x : ℝ in atTop, 0 < c * criticalPrimeFockRadius m x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hc (criticalPrimeFockRadius_pos hx)
  have hrone : ∀ᶠ x : ℝ in atTop, c * criticalPrimeFockRadius m x ≤ 1 := by
    filter_upwards [hr0.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with x hx
    have habs : |c * criticalPrimeFockRadius m x| < 1 := by
      simpa [Real.dist_eq] using hx
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) habs)
  have herr := tendsto_primeLogWindowMass_sub_main_of_admissibleRadius
    (fun x => c * criticalPrimeFockRadius m x) hrpos hrone
  have hmain : Tendsto (fun x : ℝ => 2 * x *
      (c * criticalPrimeFockRadius m x)) atTop atTop := by
    have h := (tendsto_criticalPrimeFockWindowMain_atTop hm4).const_mul_atTop hc
    simpa [criticalPrimeFockWindowMain, mul_comm, mul_left_comm, mul_assoc] using h
  refine tendsto_atTop.2 fun b => ?_
  have herrLower : ∀ᶠ x : ℝ in atTop,
      -1 < primeLogWindowMass x (c * criticalPrimeFockRadius m x) -
        2 * x * (c * criticalPrimeFockRadius m x) :=
    herr.eventually (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  filter_upwards [hmain.eventually (eventually_ge_atTop (b + 1)), herrLower]
    with x hx herror
  linarith

def criticalPrimeWindowPrimes (x r : ℝ) : Finset Nat.Primes := by
  classical
  let S : Finset ℕ :=
    (Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊).filter Nat.Prime
  let e : {n // n ∈ S} ↪ Nat.Primes :=
    ⟨fun n => (⟨n, (Finset.mem_filter.mp n.2).2⟩ : Nat.Primes),
      fun a b h => by
        apply Subtype.ext
        exact congrArg (fun p : Nat.Primes => (p : ℕ)) h⟩
  exact S.attach.map e

theorem sum_criticalPrimeSamplingWeight_windowPrimes
    (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∑ p ∈ criticalPrimeWindowPrimes x r, criticalPrimeSamplingWeight p =
      primeLogWindowMass x r := by
  classical
  rw [primeLogWindowMass_eq_sum x hr]
  unfold criticalPrimeWindowPrimes
  simp only [Finset.sum_map, criticalPrimeSamplingWeight_eq_primeLogPowWeight,
    Function.Embedding.coeFn_mk, Subtype.coe_mk]
  rw [Finset.sum_attach]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [hp]
  · simp [hp, primeLogPowWeight]

theorem criticalPrimeWindowPrimes_mem_natWindow
    {x r : ℝ} {p : Nat.Primes}
    (hp : p ∈ criticalPrimeWindowPrimes x r) :
    (p : ℕ) ∈ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊ := by
  classical
  unfold criticalPrimeWindowPrimes at hp
  simp only [Finset.mem_map] at hp
  obtain ⟨n, hn, hnp⟩ := hp
  have hval : (p : ℕ) = (n : ℕ) :=
    congrArg (fun q : Nat.Primes => (q : ℕ)) hnp.symm
  rw [hval]
  exact (Finset.mem_filter.mp n.2).1

theorem scaledWindow_tangentVector_energy_lower
    {m x : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) :
    let r := polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x
    Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
        ‖polynomialMomentFockTangentVector m (by linarith) x‖ ^ 2 *
        primeLogWindowMass x r ≤
      3 ^ (m / 2 - 1) *
        ∑ p ∈ criticalPrimeWindowPrimes x r,
          criticalPrimeSamplingWeight p *
            ‖inner ℂ (normalizedMomentFockKernel
              (polynomialMomentFockData m (by linarith))
              ((Real.log (p : ℝ) : ℝ) : ℂ))
              (polynomialMomentFockTangentVector m (by linarith) x)‖ ^ 2 := by
  classical
  dsimp only
  let hm2 : 2 ≤ m := by linarith
  let r : ℝ := polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x
  let T : Finset Nat.Primes := criticalPrimeWindowPrimes x r
  let V : ℝ := ‖polynomialMomentFockTangentVector m hm2 x‖ ^ 2
  let E : ℝ := Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m))
  let Q : ℝ := 3 ^ (m / 2 - 1)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg (polynomialFockInnerWindowFactor_pos hm).le
      (criticalPrimeFockRadius_pos (lt_of_lt_of_le zero_lt_one hx)).le
  have hrle : r ≤ polynomialFockTangentRadius m x := by
    exact scaledCriticalPrimeFockRadius_le_tangentRadius hm hx
  have hterm : ∀ p ∈ T,
      criticalPrimeSamplingWeight p * (E * V) ≤
        criticalPrimeSamplingWeight p *
          (Q * ‖inner ℂ (normalizedMomentFockKernel
            (polynomialMomentFockData m hm2)
            ((Real.log (p : ℝ) : ℝ) : ℂ))
            (polynomialMomentFockTangentVector m hm2 x)‖ ^ 2) := by
    intro p hp
    have hpwindow := criticalPrimeWindowPrimes_mem_natWindow
      (x := x) (r := r) (p := p) (by simpa [T] using hp)
    have habs : |Real.log (p : ℝ) - x| ≤ r := by
      simpa using abs_log_sub_le_of_mem_window hpwindow
    have hpone : (1 : ℝ) ≤ (p : ℕ) := by
      have hptwo : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
      linarith
    have hy : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hpone
    have hlocal := tangentVector_normalizedKernel_uniform_local_lower
      hm hx hy (habs.trans hrle)
    apply mul_le_mul_of_nonneg_left
    · simpa [E, Q, V, hm2] using hlocal
    · exact (criticalPrimeSamplingWeight_pos p).le
  have hsum := Finset.sum_le_sum hterm
  have hmass : ∑ p ∈ T, criticalPrimeSamplingWeight p = primeLogWindowMass x r := by
    simpa [T] using sum_criticalPrimeSamplingWeight_windowPrimes x hr0
  calc
    E * V * primeLogWindowMass x r =
        ∑ p ∈ T, criticalPrimeSamplingWeight p * (E * V) := by
      rw [← hmass]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ p ∈ T, criticalPrimeSamplingWeight p *
          (Q * ‖inner ℂ (normalizedMomentFockKernel
            (polynomialMomentFockData m hm2)
            ((Real.log (p : ℝ) : ℝ) : ℂ))
            (polynomialMomentFockTangentVector m hm2 x)‖ ^ 2) := hsum
    _ = Q * ∑ p ∈ T, criticalPrimeSamplingWeight p *
          ‖inner ℂ (normalizedMomentFockKernel
            (polynomialMomentFockData m hm2)
            ((Real.log (p : ℝ) : ℝ) : ℂ))
            (polynomialMomentFockTangentVector m hm2 x)‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = _ := by rfl

private theorem criticalPrimeCoordinateTail_bound
    (P : Finset Nat.Primes) (p : Nat.Primes) :
    ‖(if p ∈ P then (0 : ℂ) else 1)‖ ≤ 1 := by
  by_cases hp : p ∈ P <;> simp [hp]

def criticalPrimeCoordinateTail (P : Finset Nat.Primes) :
    CriticalPrimeEllTwo →L[ℂ] CriticalPrimeEllTwo :=
  GaloisForLFunctions.HTGeometry.LpDiagonal.lpDiag
    (fun p => if p ∈ P then (0 : ℂ) else 1) 1 zero_le_one
    (criticalPrimeCoordinateTail_bound P)

@[simp] theorem criticalPrimeCoordinateTail_apply
    (P : Finset Nat.Primes) (v : CriticalPrimeEllTwo) (p : Nat.Primes) :
    criticalPrimeCoordinateTail P v p = if p ∈ P then 0 else v p := by
  rw [criticalPrimeCoordinateTail,
    GaloisForLFunctions.HTGeometry.LpDiagonal.lpDiag_coe]
  by_cases hp : p ∈ P <;> simp [hp]

theorem norm_criticalPrimeCoordinateTail_le (P : Finset Nat.Primes) :
    ‖criticalPrimeCoordinateTail P‖ ≤ 1 :=
  GaloisForLFunctions.HTGeometry.LpDiagonal.norm_lpDiag_le _ 1 zero_le_one _

theorem tendsto_primesBelowSubtype_atTop :
    Tendsto GaloisForLFunctions.primesBelowSubtype atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro P
  refine Filter.eventually_atTop.2 ⟨P.sup (fun p : Nat.Primes => (p : ℕ)) + 1, ?_⟩
  intro N hN p hp
  rw [mem_primesBelowSubtype_iff]
  have hle : (p : ℕ) ≤ P.sup (fun q : Nat.Primes => (q : ℕ)) :=
    Finset.le_sup (f := fun q : Nat.Primes => (q : ℕ)) hp
  omega

theorem criticalPrimeCoordinateHead_tendsto_id
    (v : CriticalPrimeEllTwo) :
    Tendsto (fun N => criticalPrimeCoordinateHead
      (GaloisForLFunctions.primesBelowSubtype N) v) atTop (nhds v) := by
  have hsum := lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) v
  have hcomp := hsum.comp tendsto_primesBelowSubtype_atTop
  apply hcomp.congr'
  filter_upwards [] with N
  symm
  simpa [criticalPrimeCoordinateHead] using
    (GaloisForLFunctions.HTGeometry.LpDiagonal.lpDiag_indicator_eq_sum
      (I := Nat.Primes) (fun _ => (1 : ℂ)) 1 zero_le_one
      (GaloisForLFunctions.primesBelowSubtype N)
      (by
        intro p
        by_cases hp : p ∈ GaloisForLFunctions.primesBelowSubtype N <;> simp [hp]) v)

theorem criticalPrimeCoordinateTail_tendsto_zero
    (v : CriticalPrimeEllTwo) :
    Tendsto (fun N => criticalPrimeCoordinateTail
      (GaloisForLFunctions.primesBelowSubtype N) v) atTop (nhds 0) := by
  have hconst : Tendsto (fun _ : ℕ => v) atTop (nhds v) := tendsto_const_nhds
  have hsub := hconst.sub (criticalPrimeCoordinateHead_tendsto_id v)
  have heq : (fun N => criticalPrimeCoordinateTail
      (GaloisForLFunctions.primesBelowSubtype N) v) =
      fun N => v - criticalPrimeCoordinateHead
        (GaloisForLFunctions.primesBelowSubtype N) v := by
    funext N
    ext p
    by_cases hp : p ∈ GaloisForLFunctions.primesBelowSubtype N <;> simp [hp]
  rw [heq]
  simpa using hsub

theorem tendsto_norm_comp_of_isCompactOperator_rectangular
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Q : ℕ → F →L[ℂ] F) (hbdd : ∀ n, ‖Q n‖ ≤ 1)
    (hptw : ∀ y : F, Tendsto (fun n => Q n y) atTop (nhds 0))
    (B : E →L[ℂ] F) (hB : IsCompactOperator B) :
    Tendsto (fun n => ‖(Q n) ∘L B‖) atTop (nhds 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  set S : Set F := closure (B '' Metric.closedBall 0 1) with hS
  have hScompact : IsCompact S := hB.isCompact_closure_image_closedBall 1
  have hStb : TotallyBounded S := hScompact.totallyBounded
  obtain ⟨t, htfin, htcover⟩ :=
    (Metric.totallyBounded_iff.mp hStb) (ε / 3) (by linarith)
  have hfin : ∀ᶠ n in atTop, ∀ y ∈ htfin.toFinset, ‖Q n y‖ < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro y _
    have hy := (hptw y).norm
    rw [norm_zero] at hy
    exact hy.eventually_lt_const (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hfin
  refine ⟨N, fun n hn => ?_⟩
  have hbound : ‖(Q n) ∘L B‖ ≤ 2 * ε / 3 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun x => ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hxc : ((‖x‖ : ℂ)) ≠ 0 := by simpa using hxpos.ne'
      set u : E := ((‖x‖ : ℂ))⁻¹ • x with hu
      have hunorm : ‖u‖ = 1 := by
        rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hxpos.ne']
      have hxu : ((‖x‖ : ℂ)) • u = x := by
        rw [hu, smul_smul, mul_inv_cancel₀ hxc, one_smul]
      have hmem : B u ∈ S := by
        refine subset_closure ⟨u, ?_, rfl⟩
        simp [Metric.mem_closedBall, hunorm]
      obtain ⟨y, hy, hdist⟩ := Set.mem_iUnion₂.mp (htcover hmem)
      have hyfin : y ∈ htfin.toFinset := htfin.mem_toFinset.mpr hy
      have h1 : ‖Q n (B u)‖ ≤ ‖Q n (B u - y)‖ + ‖Q n y‖ := by
        have : Q n (B u) = Q n (B u - y) + Q n y := by
          rw [← map_add]
          congr 1
          abel
        rw [this]
        exact norm_add_le _ _
      have h2 : ‖Q n (B u - y)‖ ≤ ε / 3 := by
        refine le_trans ((Q n).le_opNorm _) ?_
        have h3 : ‖B u - y‖ < ε / 3 := by
          simpa [Metric.mem_ball, dist_eq_norm] using hdist
        calc
          ‖Q n‖ * ‖B u - y‖ ≤ 1 * ‖B u - y‖ :=
            mul_le_mul_of_nonneg_right (hbdd n) (norm_nonneg _)
          _ = ‖B u - y‖ := one_mul _
          _ ≤ ε / 3 := h3.le
      have h4 : ‖Q n y‖ < ε / 3 := hN n hn y hyfin
      have hu' : ‖(Q n) (B u)‖ ≤ 2 * ε / 3 := by linarith
      have h5 : (Q n) (B (((‖x‖ : ℂ)) • u)) =
          ((‖x‖ : ℂ)) • ((Q n) (B u)) := by rw [map_smul, map_smul]
      have hscale : ((Q n) ∘L B) x =
          ((‖x‖ : ℂ)) • ((Q n) (B u)) := by
        rw [ContinuousLinearMap.comp_apply, ← h5, hxu]
      rw [hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      calc
        ‖x‖ * ‖(Q n) (B u)‖ ≤ ‖x‖ * (2 * ε / 3) :=
          mul_le_mul_of_nonneg_left hu' (norm_nonneg _)
        _ = 2 * ε / 3 * ‖x‖ := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

theorem normSq_criticalPrimeKernelRestriction_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (k : Nat.Primes → H) (p : Nat.Primes) (f : H) :
    ‖criticalPrimeKernelRestriction k p f‖ ^ 2 =
      criticalPrimeSamplingWeight p * ‖inner ℂ (k p) f‖ ^ 2 := by
  rw [criticalPrimeKernelRestriction_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (criticalPrimeSamplingWeight_pos p).le]

theorem normSq_polynomialCriticalPrimeSamplingOperator_four_apply
    (f : MomentFock) (p : Nat.Primes) :
    ‖polynomialCriticalPrimeSamplingOperator 4 (by norm_num) f p‖ ^ 2 =
      criticalPrimeSamplingWeight p *
        ‖inner ℂ (normalizedMomentFockKernel
          (polynomialMomentFockData 4 (by norm_num))
          ((Real.log (p : ℝ) : ℝ) : ℂ)) f‖ ^ 2 := by
  rw [polynomialCriticalPrimeSamplingOperator_apply]
  exact normSq_criticalPrimeKernelRestriction_eq _ p f

theorem sum_normSq_le_coordinateTail
    (N : ℕ) (v : CriticalPrimeEllTwo) (T : Finset Nat.Primes)
    (hT : ∀ p ∈ T, N ≤ (p : ℕ)) :
    (∑ p ∈ T, ‖v p‖ ^ (2 : ℕ)) ≤
      ‖criticalPrimeCoordinateTail
          (GaloisForLFunctions.primesBelowSubtype N)
          v‖ ^ 2 := by
  let w : CriticalPrimeEllTwo := criticalPrimeCoordinateTail
    (GaloisForLFunctions.primesBelowSubtype N) v
  have hs : Summable fun p : Nat.Primes => ‖w p‖ ^ (2 : ℕ) :=
    HilbertSchmidt.summable_coe_sq w
  have hsum : (∑ p ∈ T, ‖w p‖ ^ (2 : ℕ)) ≤ ∑' p, ‖w p‖ ^ (2 : ℕ) :=
    hs.sum_le_tsum T (fun p hp => sq_nonneg _)
  have hnorm : ‖w‖ ^ 2 = ∑' p, ‖w p‖ ^ (2 : ℕ) := by
    simpa using HilbertSchmidt.lp_norm_sq_eq w
  rw [← hnorm] at hsum
  calc
    (∑ p ∈ T, ‖v p‖ ^ (2 : ℕ)) = ∑ p ∈ T, ‖w p‖ ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpnot : p ∉ GaloisForLFunctions.primesBelowSubtype N := by
          rw [mem_primesBelowSubtype_iff]
          exact not_lt.mpr (hT p hp)
        simp [w, hpnot]
    _ ≤ ‖w‖ ^ 2 := hsum
    _ = _ := by rfl

theorem criticalPrimeWindowPrimes_ge
    {N : ℕ} {x r : ℝ} (hxr : Real.log (N + 1 : ℝ) ≤ x - r)
    {p : Nat.Primes} (hp : p ∈ criticalPrimeWindowPrimes x r) :
    N ≤ (p : ℕ) := by
  have hpwindow := criticalPrimeWindowPrimes_mem_natWindow hp
  have hfloor : ⌊Real.exp (x - r)⌋₊ < (p : ℕ) := (Finset.mem_Ioc.mp hpwindow).1
  have hNreal : (N : ℝ) ≤ Real.exp (x - r) := by
    calc
      (N : ℝ) ≤ N + 1 := by norm_num
      _ = Real.exp (Real.log (N + 1 : ℝ)) := by
        rw [Real.exp_log]
        positivity
      _ ≤ Real.exp (x - r) := Real.exp_le_exp.mpr hxr
  exact (Nat.le_floor hNreal).trans hfloor.le

theorem exists_quartic_window_certificate (N : ℕ) :
    ∃ x : ℝ,
      1 ≤ x ∧
      Real.log (N + 1 : ℝ) ≤
        x - polynomialFockInnerWindowFactor 4 * criticalPrimeFockRadius 4 x ∧
      polynomialFockInnerWindowFactor 4 ≤
        primeLogWindowMass x
          (polynomialFockInnerWindowFactor 4 * criticalPrimeFockRadius 4 x) := by
  let c : ℝ := polynomialFockInnerWindowFactor 4
  have hc : 0 < c := polynomialFockInnerWindowFactor_pos (by norm_num)
  have hmass : ∀ᶠ x : ℝ in atTop,
      c < primeLogWindowMass x (c * criticalPrimeFockRadius 4 x) :=
    (tendsto_primeLogWindowMass_scaledCriticalPrimeFockRadius_four hc).eventually
      (Ioi_mem_nhds (by linarith : c < 2 * c))
  have hev : ∀ᶠ x : ℝ in atTop,
      1 ≤ x ∧ Real.log (N + 1 : ℝ) ≤
        x - c * criticalPrimeFockRadius 4 x ∧
      c ≤ primeLogWindowMass x (c * criticalPrimeFockRadius 4 x) := by
    filter_upwards [hmass,
      eventually_ge_atTop (max 1 (Real.log (N + 1 : ℝ) + 1))]
        with x hxmass hxlarge
    have hx : 1 ≤ x := le_trans (le_max_left _ _) hxlarge
    have hrhalf : c * criticalPrimeFockRadius 4 x ≤ 1 / 2 :=
      (scaledCriticalPrimeFockRadius_le_tangentRadius (by norm_num) hx).trans
        (polynomialFockTangentRadius_le_half (by norm_num))
    refine ⟨hx, ?_, hxmass.le⟩
    have hlog : Real.log (N + 1 : ℝ) + 1 ≤ x :=
      le_trans (le_max_right _ _) hxlarge
    linarith
  simpa [c] using hev.exists

def quarticCriticalPrimeSamplingTail (N : ℕ) :
    MomentFock →L[ℂ] CriticalPrimeEllTwo :=
  criticalPrimeCoordinateTail
      (GaloisForLFunctions.primesBelowSubtype N) ∘L
    polynomialCriticalPrimeSamplingOperator 4 (by norm_num)

theorem polynomialMomentFockTangentVector_ne_zero
    (x : ℝ) : polynomialMomentFockTangentVector 4 (by norm_num) x ≠ 0 := by
  intro hzero
  have hbase := polynomialMomentFockEvaluation_tangentVector_base 4 (by norm_num) x
  rw [hzero, map_zero] at hbase
  norm_num at hbase

theorem quarticCriticalPrimeSamplingTail_normSq_lower (N : ℕ) :
    Real.exp (-4 * (polynomialFockLocalBregmanConstant 4 / 4)) *
        polynomialFockInnerWindowFactor 4 ≤
      3 * ‖quarticCriticalPrimeSamplingTail N‖ ^ 2 := by
  classical
  obtain ⟨x, hx, hxr, hmass⟩ := exists_quartic_window_certificate N
  let c : ℝ := polynomialFockInnerWindowFactor 4
  let r : ℝ := c * criticalPrimeFockRadius 4 x
  let T : Finset Nat.Primes := criticalPrimeWindowPrimes x r
  let f : MomentFock := polynomialMomentFockTangentVector 4 (by norm_num) x
  let v : CriticalPrimeEllTwo :=
    polynomialCriticalPrimeSamplingOperator 4 (by norm_num) f
  let A : MomentFock →L[ℂ] CriticalPrimeEllTwo :=
    quarticCriticalPrimeSamplingTail N
  have hT : ∀ p ∈ T, N ≤ (p : ℕ) := by
    intro p hp
    apply criticalPrimeWindowPrimes_ge (p := p)
    · simpa [r, c] using hxr
    · simpa [T] using hp
  have henergy := scaledWindow_tangentVector_energy_lower
    (m := (4 : ℝ)) (x := x) (by norm_num) hx
  have hcoord :
      (∑ p ∈ T, criticalPrimeSamplingWeight p *
          ‖inner ℂ (normalizedMomentFockKernel
            (polynomialMomentFockData 4 (by norm_num))
            ((Real.log (p : ℝ) : ℝ) : ℂ)) f‖ ^ 2) =
        ∑ p ∈ T, ‖v p‖ ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro p hp
    simpa [v] using
      (normSq_polynomialCriticalPrimeSamplingOperator_four_apply f p).symm
  have htail : (∑ p ∈ T, ‖v p‖ ^ (2 : ℕ)) ≤ ‖A f‖ ^ 2 := by
    have h := sum_normSq_le_coordinateTail N v T hT
    simpa [A, quarticCriticalPrimeSamplingTail, v,
      ContinuousLinearMap.comp_apply] using h
  have henergy' :
      Real.exp (-4 * (polynomialFockLocalBregmanConstant 4 / 4)) *
          ‖f‖ ^ 2 * primeLogWindowMass x r ≤
        3 * ∑ p ∈ T, ‖v p‖ ^ (2 : ℕ) := by
    rw [← hcoord]
    have hQ : (3 : ℝ) ^ ((4 : ℝ) / 2 - 1) = 3 := by norm_num
    simpa only [c, r, T, f, hQ] using henergy
  have hleftnonneg : 0 ≤
      Real.exp (-4 * (polynomialFockLocalBregmanConstant 4 / 4)) * ‖f‖ ^ 2 := by
    positivity
  have hcert :
      Real.exp (-4 * (polynomialFockLocalBregmanConstant 4 / 4)) *
          ‖f‖ ^ 2 * c ≤ 3 * ‖A f‖ ^ 2 := by
    calc
      _ ≤ Real.exp (-4 * (polynomialFockLocalBregmanConstant 4 / 4)) *
          ‖f‖ ^ 2 * primeLogWindowMass x r :=
        mul_le_mul_of_nonneg_left (by simpa [c, r] using hmass) hleftnonneg
      _ ≤ 3 * ∑ p ∈ T, ‖v p‖ ^ (2 : ℕ) := henergy'
      _ ≤ 3 * ‖A f‖ ^ 2 := mul_le_mul_of_nonneg_left htail (by norm_num)
  have happ : ‖A f‖ ≤ ‖A‖ * ‖f‖ := A.le_opNorm f
  have happSq : ‖A f‖ ^ 2 ≤ (‖A‖ * ‖f‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 happ
  have hbound :
      Real.exp (-4 * (polynomialFockLocalBregmanConstant 4 / 4)) * c * ‖f‖ ^ 2 ≤
        (3 * ‖A‖ ^ 2) * ‖f‖ ^ 2 := by
    calc
      _ = Real.exp (-4 * (polynomialFockLocalBregmanConstant 4 / 4)) *
          ‖f‖ ^ 2 * c := by ring
      _ ≤ 3 * ‖A f‖ ^ 2 := hcert
      _ ≤ 3 * (‖A‖ * ‖f‖) ^ 2 :=
        mul_le_mul_of_nonneg_left happSq (by norm_num)
      _ = _ := by ring
  have hfpos : 0 < ‖f‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (by
      simpa [f] using polynomialMomentFockTangentVector_ne_zero x))
  have hcancel := le_of_mul_le_mul_right hbound hfpos
  simpa [c, A] using hcancel

theorem polynomialCriticalPrimeSamplingOperator_four_not_isCompactOperator :
    ¬ IsCompactOperator
      (polynomialCriticalPrimeSamplingOperator 4 (by norm_num)) := by
  intro hcompact
  have htailZero : Tendsto
      (fun N => ‖quarticCriticalPrimeSamplingTail N‖) atTop (nhds 0) := by
    have h := tendsto_norm_comp_of_isCompactOperator_rectangular
      (Q := fun N => criticalPrimeCoordinateTail
        (GaloisForLFunctions.primesBelowSubtype N))
      (fun N => norm_criticalPrimeCoordinateTail_le
        (GaloisForLFunctions.primesBelowSubtype N))
      criticalPrimeCoordinateTail_tendsto_zero
      (polynomialCriticalPrimeSamplingOperator 4 (by norm_num)) hcompact
    simpa [quarticCriticalPrimeSamplingTail] using h
  let a : ℝ := Real.exp (-4 * (polynomialFockLocalBregmanConstant 4 / 4)) *
    polynomialFockInnerWindowFactor 4
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos (Real.exp_pos _)
      (polynomialFockInnerWindowFactor_pos (by norm_num))
  have hscaledZero : Tendsto
      (fun N => 3 * ‖quarticCriticalPrimeSamplingTail N‖ ^ 2)
      atTop (nhds 0) := by
    convert tendsto_const_nhds.mul (htailZero.pow 2) using 1
    all_goals norm_num
  have hlt : ∀ᶠ N : ℕ in atTop,
      3 * ‖quarticCriticalPrimeSamplingTail N‖ ^ 2 < a :=
    hscaledZero.eventually (Iio_mem_nhds ha)
  obtain ⟨N, hN⟩ := hlt.exists
  have hlower := quarticCriticalPrimeSamplingTail_normSq_lower N
  exact (not_lt_of_ge (by simpa [a] using hlower)) hN

theorem tangentVector_normalizedKernel_local_lower_lowDegree
    {m x y : ℝ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : |y - x| ≤ polynomialFockTangentRadius m x) :
    Real.exp (-4 * (polynomialFockLowDegreeBregmanConstant m / m)) *
          (m * (1 + x ^ 2) ^ (m / 2 - 1)) *
          ‖polynomialMomentFockTangentVector m hm2 x‖ ^ 2 ≤
      (m * (1 + y ^ 2) ^ (m / 2 - 1)) *
        ‖inner ℂ (normalizedMomentFockKernel
          (polynomialMomentFockData m hm2) (y : ℂ))
          (polynomialMomentFockTangentVector m hm2 x)‖ ^ 2 := by
  let d : MomentFockData := polynomialMomentFockData m hm2
  let T : MomentFock := polynomialMomentFockTangentVector m hm2 x
  let cx : ℝ := m * (1 + x ^ 2) ^ (m / 2 - 1)
  let cy : ℝ := m * (1 + y ^ 2) ^ (m / 2 - 1)
  let K : ℝ := ‖momentFockKernel d (y : ℂ)‖ ^ 2
  let U : ℝ := ‖inner ℂ (normalizedMomentFockKernel d (y : ℂ)) T‖ ^ 2
  let V : ℝ := ‖T‖ ^ 2
  let C : ℝ := polynomialFockLowDegreeBregmanConstant m / m
  let F : ℝ := Real.exp (2 * polynomialFockRadialSlope m x * (y - x))
  have hcx : 0 < cx := by dsimp [cx]; positivity
  have hcy : 0 < cy := by dsimp [cy]; positivity
  have hK : 0 < K := by
    dsimp [K, d]
    exact sq_pos_of_pos (norm_pos_iff.mpr (momentFockKernel_ne_zero _ _))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hTid : U * K = F := by
    have hid := normSq_inner_normalizedMomentFockKernel_mul_kernelNormSq d (y : ℂ) T
    dsimp [d] at hid
    change ‖inner ℂ (normalizedMomentFockKernel
        (polynomialMomentFockData m hm2) (y : ℂ)) T‖ ^ 2 *
        ‖momentFockKernel (polynomialMomentFockData m hm2) (y : ℂ)‖ ^ 2 =
      ‖polynomialMomentFockEvaluation m hm2 (y : ℂ) T‖ ^ 2 at hid
    rw [← polynomialMomentFockFunction_eq_evaluation,
      polynomialMomentFockFunction_tangentVector,
      Complex.norm_exp, ← Real.exp_nat_mul] at hid
    have hre : (((polynomialFockRadialSlope m x : ℂ) * ((y : ℂ) - x)).re) =
        polynomialFockRadialSlope m x * (y - x) := by simp
    rw [hre] at hid
    dsimp [U, K, F, T, d]
    convert hid using 1
    all_goals ring_nf
  have hTupper : V ≤ Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / cx) := by
    simpa [V, T, cx] using normSq_polynomialMomentFockTangentVector_le m hm2 x
  have hKupper : K ≤
      Real.exp (2 * polynomialFockPotential m y + 2 * C) * (cy / Real.pi) := by
    simpa [K, d, C, cy] using
      normSq_polynomialMomentFockKernel_le_lowDegree hm2 hm4 hy
  have hbreg :
      polynomialFockPotential m y - polynomialFockPotential m x -
          polynomialFockRadialSlope m x * (y - x) ≤ C := by
    have hw : ‖((y - x : ℝ) : ℂ)‖ ≤ polynomialFockTangentRadius m x := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hxy
    have h := polynomialFockPotential_bregman_upper_tangentRadius_lowDegree
      hm2 hm4 hx hw
    simpa [Complex.norm_real, Real.norm_of_nonneg hy, C] using h
  have hexp :
      Real.exp (-4 * C) * cx *
          (Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / cx)) *
          (Real.exp (2 * polynomialFockPotential m y + 2 * C) * (cy / Real.pi)) ≤
        cy * F := by
    have harg :
        -4 * C - 2 * polynomialFockPotential m x +
            (2 * polynomialFockPotential m y + 2 * C) ≤
          2 * polynomialFockRadialSlope m x * (y - x) := by
      linarith
    dsimp [F]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hcx0 : cx ≠ 0 := hcx.ne'
    calc
      _ = cy * (Real.exp (-4 * C) *
          Real.exp (-2 * polynomialFockPotential m x) *
          Real.exp (2 * polynomialFockPotential m y + 2 * C)) := by
        field_simp
      _ = cy * Real.exp
          (-4 * C - 2 * polynomialFockPotential m x +
            (2 * polynomialFockPotential m y + 2 * C)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring
      _ ≤ cy * Real.exp (2 * polynomialFockRadialSlope m x * (y - x)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hcy.le
      _ = _ := by ring
  have hprod : Real.exp (-4 * C) * cx * V * K ≤ cy * F := by
    calc
      Real.exp (-4 * C) * cx * V * K ≤
          Real.exp (-4 * C) * cx *
            (Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / cx)) * K := by
        gcongr
      _ ≤ Real.exp (-4 * C) * cx *
            (Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / cx)) *
            (Real.exp (2 * polynomialFockPotential m y + 2 * C) * (cy / Real.pi)) := by
        gcongr
      _ ≤ cy * F := hexp
  have hcancel : Real.exp (-4 * C) * cx * V ≤ cy * U := by
    apply le_of_mul_le_mul_right (a := K)
    · calc
        Real.exp (-4 * C) * cx * V * K ≤ cy * F := hprod
        _ = cy * (U * K) := by rw [hTid]
        _ = cy * U * K := by ring
    · exact hK
  simpa [cx, cy, V, U, T, d, C] using hcancel

theorem polynomialFockTangentCurvature_local_le_lowDegree
    {m x y : ℝ} (hm2 : 2 ≤ m) (hx : 1 ≤ x)
    (hxy : |y - x| ≤ polynomialFockTangentRadius m x) :
    m * (1 + y ^ 2) ^ (m / 2 - 1) ≤
      3 ^ (m / 2 - 1) * (m * (1 + x ^ 2) ^ (m / 2 - 1)) := by
  have hr : polynomialFockTangentRadius m x ≤ 1 :=
    polynomialFockTangentRadius_le_one hm2
  have hyx : y ≤ x + 1 := by
    have := (abs_le.mp (hxy.trans hr)).2
    linarith
  have hy0 : 0 ≤ y := by
    have := (abs_le.mp (hxy.trans hr)).1
    linarith
  have hbase : 1 + y ^ 2 ≤ 3 * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (y - (x + 1)), sq_nonneg y, sq_nonneg x,
      mul_self_le_mul_self hy0 hyx]
  have hβ : 0 ≤ m / 2 - 1 := by linarith
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + y ^ 2) hbase hβ
  rw [Real.mul_rpow (by norm_num : 0 ≤ (3 : ℝ)) (by positivity : 0 ≤ 1 + x ^ 2)] at hp
  nlinarith [show 0 ≤ m by linarith,
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) (m / 2 - 1),
    Real.rpow_nonneg (by positivity : 0 ≤ 1 + x ^ 2) (m / 2 - 1)]

theorem tangentVector_normalizedKernel_uniform_local_lower_lowDegree
    {m x y : ℝ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hxy : |y - x| ≤ polynomialFockTangentRadius m x) :
    Real.exp (-4 * (polynomialFockLowDegreeBregmanConstant m / m)) *
        ‖polynomialMomentFockTangentVector m hm2 x‖ ^ 2 ≤
      3 ^ (m / 2 - 1) *
        ‖inner ℂ (normalizedMomentFockKernel
          (polynomialMomentFockData m hm2) (y : ℂ))
          (polynomialMomentFockTangentVector m hm2 x)‖ ^ 2 := by
  let cx : ℝ := m * (1 + x ^ 2) ^ (m / 2 - 1)
  let cy : ℝ := m * (1 + y ^ 2) ^ (m / 2 - 1)
  let V : ℝ := ‖polynomialMomentFockTangentVector m hm2 x‖ ^ 2
  let U : ℝ := ‖inner ℂ (normalizedMomentFockKernel
    (polynomialMomentFockData m hm2) (y : ℂ))
    (polynomialMomentFockTangentVector m hm2 x)‖ ^ 2
  let E : ℝ := Real.exp (-4 * (polynomialFockLowDegreeBregmanConstant m / m))
  let Q : ℝ := 3 ^ (m / 2 - 1)
  have hcx : 0 < cx := by dsimp [cx]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hlocal : E * cx * V ≤ cy * U := by
    simpa [E, cx, cy, V, U] using
      tangentVector_normalizedKernel_local_lower_lowDegree
        hm2 hm4 (le_trans zero_le_one hx) hy hxy
  have hscale : cy ≤ Q * cx := by
    simpa [cx, cy, Q] using
      polynomialFockTangentCurvature_local_le_lowDegree hm2 hx hxy
  have hchain : E * cx * V ≤ Q * cx * U :=
    hlocal.trans (mul_le_mul_of_nonneg_right hscale hU)
  have hcancel : E * V ≤ Q * U := by
    apply le_of_mul_le_mul_left (a := cx)
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hchain
    · exact hcx
  simpa [E, Q, V, U] using hcancel

theorem polynomialFockInnerWindowFactor_pos_of_two_le
    {m : ℝ} (hm2 : 2 ≤ m) : 0 < polynomialFockInnerWindowFactor m := by
  unfold polynomialFockInnerWindowFactor
  positivity

theorem scaledCriticalPrimeFockRadius_le_tangentRadius_of_two_le
    {m x : ℝ} (hm2 : 2 ≤ m) (hx : 1 ≤ x) :
    polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x ≤
      polynomialFockTangentRadius m x := by
  let β : ℝ := m / 2 - 1
  have hm0 : 0 < m := by linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hbase : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + x ^ 2) hbase hβ
  rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (sq_nonneg x)] at hp
  have hxsq : (x ^ 2) ^ β = x ^ (2 * β) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx0.le]
    norm_num
  rw [hxsq] at hp
  have hden :
      m * (1 + x ^ 2) ^ β ≤ m * (2 ^ β * x ^ (2 * β)) :=
    mul_le_mul_of_nonneg_left hp hm0.le
  have hleft0 : 0 ≤ polynomialFockInnerWindowFactor m *
      criticalPrimeFockRadius m x :=
    mul_nonneg (polynomialFockInnerWindowFactor_pos_of_two_le hm2).le
      (criticalPrimeFockRadius_pos hx0).le
  have hright0 : 0 ≤ polynomialFockTangentRadius m x :=
    (polynomialFockTangentRadius_pos hm0).le
  apply (sq_le_sq₀ hleft0 hright0).mp
  rw [mul_pow, polynomialFockTangentRadius_sq hm0]
  have hfacSq : polynomialFockInnerWindowFactor m ^ 2 =
      (m * 2 ^ β)⁻¹ := by
    have hc : 0 ≤ m * 2 ^ β :=
      mul_nonneg hm0.le (Real.rpow_nonneg (by norm_num) β)
    unfold polynomialFockInnerWindowFactor
    rw [inv_pow, Real.sq_sqrt (by simpa [β] using hc)]
  rw [hfacSq, criticalPrimeFockRadius_eq_rpow hx0.le]
  rw [← Real.rpow_natCast (x ^ (1 - m / 2)) 2,
    ← Real.rpow_mul hx0.le]
  norm_num only [Nat.cast_ofNat]
  have hexp : (1 - m / 2) * 2 = -(2 * β) := by dsimp [β]; ring
  rw [hexp, Real.rpow_neg hx0.le]
  have hlowpos : 0 < m * (1 + x ^ 2) ^ β := by positivity
  have hinv := inv_anti₀ hlowpos hden
  simpa [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hinv

theorem scaledWindow_tangentVector_energy_lower_lowDegree
    {m x : ℝ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hx : 1 ≤ x) :
    let r := polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x
    Real.exp (-4 * (polynomialFockLowDegreeBregmanConstant m / m)) *
        ‖polynomialMomentFockTangentVector m hm2 x‖ ^ 2 *
        primeLogWindowMass x r ≤
      3 ^ (m / 2 - 1) *
        ∑ p ∈ criticalPrimeWindowPrimes x r,
          ‖criticalPrimeKernelRestriction
            (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p
            (polynomialMomentFockTangentVector m hm2 x)‖ ^ (2 : ℕ) := by
  classical
  dsimp only
  let r : ℝ := polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x
  let T : Finset Nat.Primes := criticalPrimeWindowPrimes x r
  let V : ℝ := ‖polynomialMomentFockTangentVector m hm2 x‖ ^ 2
  let E : ℝ := Real.exp (-4 * (polynomialFockLowDegreeBregmanConstant m / m))
  let Q : ℝ := 3 ^ (m / 2 - 1)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg (polynomialFockInnerWindowFactor_pos_of_two_le hm2).le
      (criticalPrimeFockRadius_pos (lt_of_lt_of_le zero_lt_one hx)).le
  have hrle : r ≤ polynomialFockTangentRadius m x :=
    scaledCriticalPrimeFockRadius_le_tangentRadius_of_two_le hm2 hx
  have hterm : ∀ p ∈ T,
      criticalPrimeSamplingWeight p * (E * V) ≤
        Q * ‖criticalPrimeKernelRestriction
          (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p
          (polynomialMomentFockTangentVector m hm2 x)‖ ^ (2 : ℕ) := by
    intro p hp
    have hpwindow := criticalPrimeWindowPrimes_mem_natWindow
      (x := x) (r := r) (p := p) (by simpa [T] using hp)
    have habs : |Real.log (p : ℝ) - x| ≤ r := by
      simpa using abs_log_sub_le_of_mem_window hpwindow
    have hpone : (1 : ℝ) ≤ (p : ℕ) := by
      have hptwo : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
      linarith
    have hy : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hpone
    have hlocal := tangentVector_normalizedKernel_uniform_local_lower_lowDegree
      hm2 hm4 hx hy (habs.trans hrle)
    have hcoord := normSq_criticalPrimeKernelRestriction_eq
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p
      (polynomialMomentFockTangentVector m hm2 x)
    rw [hcoord]
    calc
      criticalPrimeSamplingWeight p * (E * V) =
          criticalPrimeSamplingWeight p * E * V := by ring
      _ ≤ criticalPrimeSamplingWeight p *
          (Q * ‖inner ℂ (normalizedMomentFockKernel
            (polynomialMomentFockData m hm2)
            ((Real.log (p : ℝ) : ℝ) : ℂ))
            (polynomialMomentFockTangentVector m hm2 x)‖ ^ 2) := by
        have hw := criticalPrimeSamplingWeight_pos p
        nlinarith
      _ = Q * (criticalPrimeSamplingWeight p *
          ‖inner ℂ (normalizedMomentFockKernel
            (polynomialMomentFockData m hm2)
            ((Real.log (p : ℝ) : ℝ) : ℂ))
            (polynomialMomentFockTangentVector m hm2 x)‖ ^ 2) := by ring
  have hsum := Finset.sum_le_sum hterm
  have hmass : ∑ p ∈ T, criticalPrimeSamplingWeight p = primeLogWindowMass x r := by
    simpa [T] using sum_criticalPrimeSamplingWeight_windowPrimes x hr0
  calc
    E * V * primeLogWindowMass x r =
        ∑ p ∈ T, criticalPrimeSamplingWeight p * (E * V) := by
      rw [← hmass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ p ∈ T, Q *
        ‖criticalPrimeKernelRestriction
          (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p
          (polynomialMomentFockTangentVector m hm2 x)‖ ^ (2 : ℕ) := hsum
    _ = Q * ∑ p ∈ T,
        ‖criticalPrimeKernelRestriction
          (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p
          (polynomialMomentFockTangentVector m hm2 x)‖ ^ (2 : ℕ) := by
      rw [Finset.mul_sum]
    _ = _ := by rfl

def HasPolynomialCriticalPrimeBesselBound
    (m : ℝ) (hm2 : 2 ≤ m) : Prop :=
  ∃ B : ℝ, ∀ (f : MomentFock) (T : Finset Nat.Primes),
    (∑ p ∈ T, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p f‖ ^ (2 : ℕ)) ≤
      B * ‖f‖ ^ 2

theorem hasPolynomialCriticalPrimeBesselBound_of_four_le
    {m : ℝ} (hm4 : 4 ≤ m) :
    HasPolynomialCriticalPrimeBesselBound m (by linarith) := by
  refine ⟨polynomialCriticalPrimeBesselBound m hm4, ?_⟩
  intro f T
  simpa using sum_normSq_criticalPrimeKernelRestriction_polynomial_le_canonical hm4 f T

theorem not_hasPolynomialCriticalPrimeBesselBound_of_lt_four
    {m : ℝ} (hm2 : 2 < m) (hm4 : m < 4) :
    ¬ HasPolynomialCriticalPrimeBesselBound m hm2.le := by
  rintro ⟨B, hB⟩
  let c : ℝ := polynomialFockInnerWindowFactor m
  let E : ℝ := Real.exp (-4 * (polynomialFockLowDegreeBregmanConstant m / m))
  let Q : ℝ := 3 ^ (m / 2 - 1)
  have hc : 0 < c := polynomialFockInnerWindowFactor_pos_of_two_le hm2.le
  have hE : 0 < E := by dsimp [E]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hmassEventually : ∀ᶠ x : ℝ in atTop,
      (Q * B + 1) / E ≤
        primeLogWindowMass x (c * criticalPrimeFockRadius m x) :=
    (tendsto_primeLogWindowMass_scaledCriticalPrimeFockRadius_atTop hm2 hm4 hc)
      (eventually_ge_atTop ((Q * B + 1) / E))
  have hexists : ∃ x : ℝ, 1 ≤ x ∧
      (Q * B + 1) / E ≤
        primeLogWindowMass x (c * criticalPrimeFockRadius m x) := by
    have hev : ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧
        (Q * B + 1) / E ≤
          primeLogWindowMass x (c * criticalPrimeFockRadius m x) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ), hmassEventually]
        with x hx hmass
      exact ⟨hx, hmass⟩
    exact hev.exists
  obtain ⟨x, hx, hmass⟩ := hexists
  let r : ℝ := c * criticalPrimeFockRadius m x
  let T : Finset Nat.Primes := criticalPrimeWindowPrimes x r
  let f : MomentFock := polynomialMomentFockTangentVector m hm2.le x
  have henergy := scaledWindow_tangentVector_energy_lower_lowDegree
    hm2.le hm4.le hx
  have hbound := hB f T
  have hchain :
      (E * primeLogWindowMass x r) * ‖f‖ ^ 2 ≤
        (Q * B) * ‖f‖ ^ 2 := by
    calc
      _ = E * ‖f‖ ^ 2 * primeLogWindowMass x r := by ring
      _ ≤ Q * ∑ p ∈ T, ‖criticalPrimeKernelRestriction
          (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2.le)) p f‖ ^
            (2 : ℕ) := by
        simpa [E, Q, c, r, T, f] using henergy
      _ ≤ Q * (B * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left hbound hQ
      _ = _ := by ring
  have hfpos : 0 < ‖f‖ ^ 2 := by
    apply sq_pos_of_pos
    rw [norm_pos_iff]
    intro hf
    have hbase := polynomialMomentFockEvaluation_tangentVector_base m hm2.le x
    rw [show polynomialMomentFockTangentVector m hm2.le x = 0 by simpa [f] using hf,
      map_zero] at hbase
    norm_num at hbase
  have hupper : E * primeLogWindowMass x r ≤ Q * B :=
    le_of_mul_le_mul_right hchain hfpos
  have hlower : Q * B + 1 ≤ E * primeLogWindowMass x r := by
    calc
      Q * B + 1 = E * ((Q * B + 1) / E) := by field_simp
      _ ≤ E * primeLogWindowMass x r := by
        apply mul_le_mul_of_nonneg_left
        · simpa [r, c] using hmass
        · exact hE.le
  linarith

theorem hasPolynomialCriticalPrimeBesselBound_iff
    {m : ℝ} (hm2 : 2 < m) :
    HasPolynomialCriticalPrimeBesselBound m hm2.le ↔ 4 ≤ m := by
  constructor
  · intro h
    by_contra hnot
    exact not_hasPolynomialCriticalPrimeBesselBound_of_lt_four hm2
      (lt_of_not_ge hnot) h
  · exact hasPolynomialCriticalPrimeBesselBound_of_four_le

theorem polynomialCriticalPrimeSamplingOperator_isCompactOperator_iff
    {m : ℝ} (hm4 : 4 ≤ m) :
    IsCompactOperator (polynomialCriticalPrimeSamplingOperator m hm4) ↔ 4 < m := by
  constructor
  · intro hcompact
    by_contra hnot
    have hm : m = 4 := le_antisymm (le_of_not_gt hnot) hm4
    subst m
    exact polynomialCriticalPrimeSamplingOperator_four_not_isCompactOperator hcompact
  · exact polynomialCriticalPrimeSamplingOperator_isCompactOperator


end

end RHTower
