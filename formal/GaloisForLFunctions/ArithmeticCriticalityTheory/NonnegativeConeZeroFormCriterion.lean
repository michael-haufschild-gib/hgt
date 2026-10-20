import GaloisForLFunctions.ArithmeticCriticalityTheory.FullZeroFormWeilPositivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.ReflectedPrimeMassAsymptotics
import GaloisForLFunctions.RHTower.WeilPhiDoobArchimedeanJumpAndHalfLineFolding

/-!
# RH on the nonnegative cone: a criterion without cancellation

The Lorentz correction of the full zero form factorises through the two exponential moments,

    Ẑ(F) = Q(F) + 2 (∫ F e^{x/2}) (∫ F e^{−x/2})        (`fullZeroForm_eq_markovEnergy_add_expMoments`),

and in Doob coordinates `Q(Φv) = E(v) − ∫ Φ cosh(x/2) v²` with the Doob jump energy
`E = E_arch + E_prime ≥ 0`. Hence, for a nonnegative profile `v`, every term of

    Ẑ(Φv) = E_arch(v) + E_prime(v) + 2 (∫ Φ v e^{x/2}) (∫ Φ v e^{−x/2}) − ∫ Φ cosh(x/2) v²

is a nonnegative functional of `v`.

* **Criterion** (`riemannHypothesis_iff_forall_nonneg_cone`). RH holds iff for every nonnegative
  `v ∈ C²_c`,
      ∫ Φ cosh(x/2) v²  ≤  E_arch(v) + E_prime(v) + 2 (∫ Φ v e^{x/2}) (∫ Φ v e^{−x/2}).
  A test of any sign is lifted into the cone by adding `M u_L`, `M = max |v|`, a multiple of the
  truncated ground state; the whole theta span is in the radical of `Ẑ`
  (`tendsto_fullZeroForm_add_translatePlateau`), so the lift does not change `Ẑ` in the limit.
* **Sharpness** (`tendsto_cone_terms_smoothPlateau`, `exists_nonneg_cone_violation`). Along the
  plateaus `u_L → 1` the jump energy tends to `0` and both the potential and the pole product tend to
  `1/2`: the constant profile is a ground state of the cone inequality, and for every `ε > 0` the
  inequality with `(1 + ε)` in front of the potential fails on the cone.

So the sign problem of RH can be posed with no signed term at all: on nonnegative profiles the
potential must be paid by the Doob jump energy together with the product of the two pole moments,
and the constant profile pays it exactly.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- `∫ F e^{x/2}`. -/
def expHalfMoment (F : ℝ → ℝ) : ℝ := ∫ x, F x * Real.exp (x / 2)

/-- `∫ F e^{−x/2}`. -/
def expNegHalfMoment (F : ℝ → ℝ) : ℝ := ∫ x, F x * Real.exp (-(x / 2))

theorem expHalfMoment_eq {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    expHalfMoment F = evenPoleMoment F + oddPoleMoment F := by
  have hc : Integrable fun x => F x * Real.cosh (x / 2) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  have hs : Integrable fun x => F x * Real.sinh (x / 2) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  unfold expHalfMoment evenPoleMoment oddPoleMoment
  rw [← integral_add hc hs]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Real.cosh_eq, Real.sinh_eq]
  ring

theorem expNegHalfMoment_eq {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    expNegHalfMoment F = evenPoleMoment F - oddPoleMoment F := by
  have hc : Integrable fun x => F x * Real.cosh (x / 2) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  have hs : Integrable fun x => F x * Real.sinh (x / 2) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  unfold expNegHalfMoment evenPoleMoment oddPoleMoment
  rw [← integral_sub hc hs]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Real.cosh_eq, Real.sinh_eq]
  ring

/-- **The Lorentz correction is the product of the two exponential moments.** -/
theorem fullZeroForm_eq_markovEnergy_add_expMoments {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    fullZeroForm F = markovEnergy (fun x => (F x : ℂ)) +
      2 * expHalfMoment F * expNegHalfMoment F := by
  unfold fullZeroForm
  rw [expHalfMoment_eq hF hFc, expNegHalfMoment_eq hF hFc]
  ring

/-- **The cone form.** For `v ∈ C²_c`,
`Ẑ(Φv) = E_arch(v) + E_prime(v) + 2 (∫Φv e^{x/2})(∫Φv e^{−x/2}) − ∫Φ cosh(x/2) v²`. -/
theorem fullZeroForm_phiDoob_eq_cone {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    fullZeroForm (phiDoobTest v) =
      phiDoobArchJumpEnergy v + (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) +
        2 * expHalfMoment (phiDoobTest v) * expNegHalfMoment (phiDoobTest v) -
        phiDoobCoshMass (fun x => v x ^ 2) := by
  rw [fullZeroForm_eq_markovEnergy_add_expMoments (contDiff_phiDoobTest hv).continuous
    (hasCompactSupport_phiDoobTest hvc), phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass hv hvc]
  ring

/-- On a nonnegative profile the pole product is nonnegative. -/
theorem expMoments_mul_nonneg {v : ℝ → ℝ} (hnn : ∀ x, 0 ≤ v x) :
    0 ≤ expHalfMoment (phiDoobTest v) * expNegHalfMoment (phiDoobTest v) := by
  have h : ∀ s : ℝ, 0 ≤ ∫ x, phiDoobTest v x * Real.exp (s * x) := fun s =>
    integral_nonneg fun x => mul_nonneg (mul_nonneg (riemannKernelReal_pos x).le (hnn x))
      (Real.exp_pos _).le
  refine mul_nonneg ?_ ?_
  · simpa [expHalfMoment, div_eq_inv_mul] using h (1 / 2)
  · simpa [expNegHalfMoment, div_eq_inv_mul, neg_mul] using h (-(1 / 2))

/-- **RH on the nonnegative cone.** RH holds iff every nonnegative `v ∈ C²_c` satisfies
`∫Φ cosh(x/2) v² ≤ E_arch(v) + E_prime(v) + 2 (∫Φv e^{x/2})(∫Φv e^{−x/2})`. -/
theorem riemannHypothesis_iff_forall_nonneg_cone :
    RiemannHypothesis ↔ ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, 0 ≤ v x) →
      phiDoobCoshMass (fun x => v x ^ 2) ≤ phiDoobArchJumpEnergy v +
        (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) +
        2 * expHalfMoment (phiDoobTest v) * expNegHalfMoment (phiDoobTest v) := by
  rw [riemannHypothesis_iff_forall_fullZeroForm_nonneg]
  constructor
  · intro h v hv hvc _
    have := h v hv hvc
    rw [fullZeroForm_phiDoob_eq_cone hv hvc] at this
    linarith
  · intro h v hv hvc
    -- lift `v` into the cone by a multiple of the truncated ground state
    obtain ⟨M, hM⟩ := hvc.exists_bound_of_continuous hv.continuous
    obtain ⟨R, hR⟩ := hvc.isCompact.isBounded.subset_closedBall (0 : ℝ)
    set s : Finset (Fin 1) := Finset.univ
    have hlim := tendsto_fullZeroForm_add_translatePlateau s (fun _ => |M|) (fun _ => 0) hv hvc
    have hspan : ∀ L y, translateSpan s (fun _ => |M|) (fun _ => 0) y * smoothPlateau L y + v y =
        |M| * smoothPlateau L y + v y := fun L y => by
      simp [s, translateSpan, translateGroundState_zero]
    simp_rw [hspan] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop R] with L hL
    have hw : ContDiff ℝ 2 fun y => |M| * smoothPlateau L y + v y :=
      (contDiff_const.mul (contDiff_smoothPlateau L)).add hv
    have hwc : HasCompactSupport fun y => |M| * smoothPlateau L y + v y :=
      ((hasCompactSupport_smoothPlateau L).mul_left).add hvc
    have hnn : ∀ y, 0 ≤ |M| * smoothPlateau L y + v y := by
      intro y
      by_cases hy : y ∈ tsupport v
      · have hyR : |y| ≤ L := by
          have := hR hy
          rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
          linarith
        rw [smoothPlateau_eq_one hyR, mul_one]
        have := hM y
        rw [Real.norm_eq_abs] at this
        linarith [neg_abs_le (v y), abs_nonneg M, le_abs_self M]
      · rw [image_eq_zero_of_notMem_tsupport hy, add_zero]
        exact mul_nonneg (abs_nonneg M) (smoothPlateau_nonneg L y)
    have := h _ hw hwc hnn
    rw [fullZeroForm_phiDoob_eq_cone hw hwc]
    linarith

/-! ### Sharpness: the constant profile -/

/-- Along the plateaus `u_L → 1`, the potential `∫Φ cosh(x/2) u_L²` tends to `1/2`. -/
theorem tendsto_phiDoobCoshMass_smoothPlateau_sq :
    Tendsto (fun L => phiDoobCoshMass (fun x => smoothPlateau L x ^ 2)) atTop (𝓝 (1 / 2)) := by
  rw [← RHTower.integral_riemannKernelReal_cosh_half]
  unfold phiDoobCoshMass phiDoobTest
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => riemannKernelReal x * Real.cosh (x / 2)) ?_ ?_
    integrable_riemannKernelReal_mul_cosh_half ?_
  · exact Eventually.of_forall fun L => ((continuous_riemannKernelReal.mul
      ((contDiff_smoothPlateau L).continuous.pow 2)).mul (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun L => Eventually.of_forall fun x => ?_
    have h0 := smoothPlateau_nonneg L x
    have h1 := smoothPlateau_le_one L x
    have hΦ := (riemannKernelReal_pos x).le
    have hc := (Real.cosh_pos (x / 2)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : smoothPlateau L x ^ 2 ≤ 1 := by nlinarith
    calc riemannKernelReal x * smoothPlateau L x ^ 2 * Real.cosh (x / 2)
        ≤ riemannKernelReal x * 1 * Real.cosh (x / 2) := by gcongr
      _ = _ := by ring
  · refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop |x|] with L hL
    rw [smoothPlateau_eq_one hL]
    ring

/-- **The constant profile saturates the cone inequality.** Along `u_L`: the jump energy tends to
`0`, and both the pole product and the potential tend to `1/2`. -/
theorem tendsto_cone_terms_smoothPlateau :
    Tendsto (fun L => phiDoobArchJumpEnergy (smoothPlateau L) +
        ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump (smoothPlateau L) n x) atTop (𝓝 0) ∧
      Tendsto (fun L => 2 * expHalfMoment (phiDoobTest (smoothPlateau L)) *
        expNegHalfMoment (phiDoobTest (smoothPlateau L))) atTop (𝓝 (1 / 2)) ∧
      Tendsto (fun L => phiDoobCoshMass (fun x => smoothPlateau L x ^ 2)) atTop (𝓝 (1 / 2)) := by
  have hP := tendsto_phiDoobCoshMass_smoothPlateau_sq
  have hQ := tendsto_markovEnergy_phiDoob_smoothPlateau
  have hC := tendsto_evenPoleMoment_phiDoob_smoothPlateau
  have hS : ∀ L, oddPoleMoment (phiDoobTest (smoothPlateau L)) = 0 := fun L =>
    oddPoleMoment_eq_zero_of_even fun x => by
      unfold phiDoobTest
      rw [riemannKernelReal_neg', smoothPlateau_neg]
  have hcont : ∀ L, Continuous (phiDoobTest (smoothPlateau L)) := fun L =>
    (contDiff_phiDoobTest (contDiff_smoothPlateau L)).continuous
  have hcpt : ∀ L, HasCompactSupport (phiDoobTest (smoothPlateau L)) := fun L =>
    hasCompactSupport_phiDoobTest (hasCompactSupport_smoothPlateau L)
  refine ⟨?_, ?_, hP⟩
  · have h := hQ.add hP
    rw [show -(1 / 2 : ℝ) + 1 / 2 = 0 by norm_num] at h
    refine h.congr fun L => ?_
    rw [phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass (contDiff_smoothPlateau L)
      (hasCompactSupport_smoothPlateau L)]
    ring
  · have h := (hC.mul hC).const_mul 2
    rw [show (2 : ℝ) * (1 / 2 * (1 / 2)) = 1 / 2 by norm_num] at h
    refine h.congr fun L => ?_
    rw [expHalfMoment_eq (hcont L) (hcpt L), expNegHalfMoment_eq (hcont L) (hcpt L), hS L]
    ring

/-- **No multiplicative slack on the cone.** For every `ε > 0` some nonnegative `v ∈ C²_c` has
`(1 + ε) ∫Φ cosh(x/2) v² > E_arch(v) + E_prime(v) + 2 (∫Φv e^{x/2})(∫Φv e^{−x/2})`. -/
theorem exists_nonneg_cone_violation {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧ (∀ x, 0 ≤ v x) ∧
      phiDoobArchJumpEnergy v + (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) +
          2 * expHalfMoment (phiDoobTest v) * expNegHalfMoment (phiDoobTest v) <
        (1 + ε) * phiDoobCoshMass (fun x => v x ^ 2) := by
  obtain ⟨hJ, hE, hP⟩ := tendsto_cone_terms_smoothPlateau
  have h := (hP.const_mul (1 + ε)).sub (hJ.add hE)
  rw [show (1 + ε) * (1 / 2) - (0 + 1 / 2) = ε / 2 by ring] at h
  obtain ⟨L, hL⟩ := (h.eventually (lt_mem_nhds (half_pos hε))).exists
  exact ⟨smoothPlateau L, contDiff_smoothPlateau L, hasCompactSupport_smoothPlateau L,
    smoothPlateau_nonneg L, by linarith⟩

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
