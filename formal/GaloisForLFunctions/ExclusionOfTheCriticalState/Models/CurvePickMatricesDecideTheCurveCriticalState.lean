import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.CurveCriticalStatesAndStepanovExclusion
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekBoundedPacketCountableTomography

/-!
# Curve Pick matrices decide the curve critical state

Function-field calibration of the Pick form of the critical ratio. For a curve datum `D` with
Frobenius roots in `q^{-4} < |β| < q^4` the curve probes `g_p(m) = q^{-pm}` (`p ≥ 5`) are the
profiles `e^{pu}` sampled at `u = −m log q`, and the curve Pick matrices are
`(B_D(g_m, g_n) + a W₈(g_m, g_n))_{m,n ≥ 5}`.

* **Density** (`exists_curveProbeSum_near`). In the weighted `ℓ²` of `H_D` the probes are dense: a
  vector orthogonal to all of them is a bounded power series vanishing at `q^{−1}, q^{−2}, …`
  (`boundedPowerSeries_coeff_eq_zero_of_zeroSequence`).
* **The Pick form decides the confined curve form** (`curvePick_nonneg_iff`). `B_D + aW₈ ≥ 0` on
  `H_D` iff every curve Pick matrix is positive semidefinite: `B_D` reads finitely many Laplace values,
  each a bounded functional of the weighted `ℓ²` vector.
* **Calibration.** The Frobenius roots are unitary (RH for the curve) iff the bare curve Pick
  matrices are positive semidefinite (`unitary_iff_curvePick_nonneg`); otherwise the ground-state
  constant `a*` is the least `a` at which all curve Pick matrices are positive semidefinite
  (`isLeast_curvePick_groundConstant`), and it is at most `Σ_{|β_i| ≠ 1} C_{β_i} C_{β_i⁻¹}`
  (`curveGroundConstant_le_offLineWeight`), the function-field form of the bound of the critical ratio
  by the off-line zeros. For cubic Kummer data (native Stepanov) all curve Pick
  matrices are positive semidefinite (`cubicKummer_curvePick_nonneg`). For `ζ` the same statements
  need control of the Gamma energy; over a function field the density is the identity theorem for
  power series.
-/

noncomputable section
open Complex Filter Topology
open scoped ComplexConjugate lp

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
namespace CurveModels
open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-! ### Curve probes and the weighted vector -/

/-- The curve probe at the node `p`: `g_p(m) = q^{-pm}`. -/
def curveProbe (p : ℕ) : ℕ → ℝ := fun m => ((D.q ^ p)⁻¹) ^ m

theorem curveProbe_ratio {p : ℕ} (hp : 5 ≤ p) :
    0 < (D.q ^ p)⁻¹ * D.q ^ 4 ∧ (D.q ^ p)⁻¹ * D.q ^ 4 < 1 := by
  have hq := D.one_lt_q
  have hqp : 0 < D.q ^ p := q_pow_pos D p
  refine ⟨mul_pos (inv_pos.mpr hqp) (q_pow_pos D 4), ?_⟩
  rw [inv_mul_lt_one₀ hqp]
  exact pow_lt_pow_right₀ hq (by omega)

theorem curveEnergyDomain_curveProbe {p : ℕ} (hp : 5 ≤ p) :
    CurveEnergyDomain D (curveProbe D p) := by
  obtain ⟨h0, h1⟩ := curveProbe_ratio D hp
  have hs := summable_geometric_of_lt_one (sq_nonneg ((D.q ^ p)⁻¹ * D.q ^ 4))
    (by nlinarith : ((D.q ^ p)⁻¹ * D.q ^ 4) ^ 2 < 1)
  refine hs.congr fun m => ?_
  simp only [curveProbe]
  ring

/-- The weighted coordinates `f(m) q^{4m}`: `W₈(f) = Σ_m (f(m) q^{4m})²`. -/
def curveVecCoord (f : ℕ → ℝ) (m : ℕ) : ℝ := f m * D.q ^ (4 * m)

theorem memℓp_curveVecCoord {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) :
    Memℓp (curveVecCoord D f) 2 := by
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  refine hf.congr fun m => ?_
  rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, curveVecCoord]
  ring

/-- The profile as a vector of `ℓ²`. -/
def curveVec {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) : ℓ²(ℕ, ℝ) :=
  ⟨curveVecCoord D f, memℓp_curveVecCoord D hf⟩

theorem curveVec_apply {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) (m : ℕ) :
    curveVec D hf m = f m * D.q ^ (4 * m) := rfl

theorem norm_curveVec_sq {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) :
    ‖curveVec D hf‖ ^ 2 = curveConfinementMass D f := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (curveVec D hf)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h, curveConfinementMass, curveConfinementPair]
  refine tsum_congr fun m => ?_
  rw [curveVec_apply, Real.norm_eq_abs, sq_abs]
  ring

theorem curveVec_sub {f g : ℕ → ℝ} (hf : CurveEnergyDomain D f) (hg : CurveEnergyDomain D g)
    (m : ℕ) : (curveVec D hf - curveVec D hg) m = (f m - g m) * D.q ^ (4 * m) := by
  rw [lp.coeFn_sub, Pi.sub_apply, curveVec_apply, curveVec_apply]
  ring

/-! ### The Laplace values are bounded functionals -/

theorem curveLaplace_term (f : ℕ → ℝ) (z : ℂ) (m : ℕ) :
    (f m : ℂ) * (z⁻¹) ^ m = (curveVecCoord D f m : ℂ) * ((D.q ^ 4 * z)⁻¹) ^ m := by
  have hq : ((D.q : ℂ) ^ 4) ≠ 0 := pow_ne_zero 4 (Complex.ofReal_ne_zero.mpr (q_pos D).ne')
  have key : ((D.q : ℂ) ^ 4) ^ m * (((D.q : ℂ) ^ 4)⁻¹) ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hq, one_pow]
  unfold curveVecCoord
  rw [show ((D.q : ℂ) ^ 4 * z)⁻¹ ^ m = ((D.q : ℂ) ^ 4)⁻¹ ^ m * z⁻¹ ^ m by rw [mul_inv, mul_pow],
    show ((f m * D.q ^ (4 * m) : ℝ) : ℂ) = (f m : ℂ) * ((D.q : ℂ) ^ 4) ^ m by
      push_cast; rw [pow_mul]]
  calc (f m : ℂ) * z⁻¹ ^ m = (f m : ℂ) * (((D.q : ℂ) ^ 4) ^ m * ((D.q : ℂ) ^ 4)⁻¹ ^ m) * z⁻¹ ^ m := by
        rw [key, mul_one]
    _ = _ := by ring

theorem curveLaplace_eq_tsum_curveVecCoord (f : ℕ → ℝ) (z : ℂ) :
    curveLaplace f z = ∑' m, (curveVecCoord D f m : ℂ) * ((D.q ^ 4 * z)⁻¹) ^ m :=
  tsum_congr (curveLaplace_term D f z)

/-- `|Σ_m x_m ζ^m| ≤ ‖x‖₂ (Σ_m |ζ|^{2m})^{1/2}`. -/
theorem norm_tsum_mul_pow_le (x : ℓ²(ℕ, ℝ)) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖∑' m, (x m : ℂ) * ζ ^ m‖ ≤
      ‖x‖ * (∑' m : ℕ, (‖ζ‖ ^ m) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have hρ0 : 0 ≤ ‖ζ‖ := norm_nonneg _
  have hx2 := (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  simp only [ENNReal.toReal_ofNat] at hx2
  have hy2 : Summable fun m : ℕ => (‖ζ‖ ^ m) ^ (2 : ℝ) := by
    have := summable_geometric_of_lt_one (sq_nonneg ‖ζ‖) (by nlinarith : ‖ζ‖ ^ 2 < 1)
    refine this.congr fun m => ?_
    rw [Real.rpow_two, ← pow_mul, ← pow_mul, mul_comm]
  obtain ⟨hs, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.HolderConjugate.two_two) (fun m => norm_nonneg (x m)) (fun m => pow_nonneg hρ0 m)
    hx2 hy2
  have hnorm : ∀ m, ‖(x m : ℂ) * ζ ^ m‖ = ‖x m‖ * ‖ζ‖ ^ m := fun m => by
    rw [norm_mul, norm_pow, Complex.norm_real]
  have hs' : Summable fun m => ‖(x m : ℂ) * ζ ^ m‖ := hs.congr fun m => (hnorm m).symm
  calc ‖∑' m, (x m : ℂ) * ζ ^ m‖ ≤ ∑' m, ‖(x m : ℂ) * ζ ^ m‖ := norm_tsum_le_tsum_norm hs'
    _ = ∑' m, ‖x m‖ * ‖ζ‖ ^ m := tsum_congr hnorm
    _ ≤ (∑' m, ‖x m‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑' m : ℕ, (‖ζ‖ ^ m) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        hle
    _ = ‖x‖ * (∑' m : ℕ, (‖ζ‖ ^ m) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) x]
        simp only [ENNReal.toReal_ofNat]

/-- The Laplace value at `z` moves by at most `C_z ‖Δ‖₂`. -/
theorem norm_curveLaplace_sub_le {f g : ℕ → ℝ} (hf : CurveEnergyDomain D f)
    (hg : CurveEnergyDomain D g) {z : ℂ} (hz : (D.q ^ 4)⁻¹ < ‖z‖) :
    ‖curveLaplace f z - curveLaplace g z‖ ≤
      ‖curveVec D hf - curveVec D hg‖ *
        (∑' m : ℕ, (‖(D.q ^ 4 * z)⁻¹‖ ^ m) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have hz0 : z ≠ 0 := fun h => by
    rw [h, norm_zero] at hz; exact (not_lt.mpr (inv_pos.mpr (q_pow_pos D 4)).le) hz
  have hζ : ‖(D.q ^ 4 * z)⁻¹‖ < 1 := by
    rw [norm_inv, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (q_pos D).le]
    have h4 := q_pow_pos D 4
    rw [inv_lt_one₀ (by positivity)]
    calc 1 = D.q ^ 4 * (D.q ^ 4)⁻¹ := (mul_inv_cancel₀ h4.ne').symm
      _ < D.q ^ 4 * ‖z‖ := mul_lt_mul_of_pos_left hz h4
  have hsf' := (summable_curveLaplace D hf hz).congr (curveLaplace_term D f z)
  have hsg' := (summable_curveLaplace D hg hz).congr (curveLaplace_term D g z)
  rw [curveLaplace_eq_tsum_curveVecCoord D f z, curveLaplace_eq_tsum_curveVecCoord D g z,
    ← hsf'.tsum_sub hsg']
  have hfun : (fun m => (curveVecCoord D f m : ℂ) * ((D.q ^ 4 * z)⁻¹) ^ m -
      (curveVecCoord D g m : ℂ) * ((D.q ^ 4 * z)⁻¹) ^ m) =
      fun m => (((curveVec D hf - curveVec D hg) m : ℝ) : ℂ) * ((D.q ^ 4 * z)⁻¹) ^ m := by
    funext m
    rw [curveVec_sub]
    unfold curveVecCoord
    push_cast
    ring
  rw [hfun]
  exact norm_tsum_mul_pow_le (curveVec D hf - curveVec D hg) hζ

/-! ### Density of the curve probes -/

theorem curveVec_curveProbe_apply (p m : ℕ) :
    curveVec D (curveEnergyDomain_curveProbe D (show 5 ≤ p + 5 by omega)) m =
      ((D.q ^ (p + 5))⁻¹ * D.q ^ 4) ^ m := by
  rw [curveVec_apply, curveProbe, mul_pow, ← pow_mul, mul_comm 4 m]

/-- **The curve probes are dense.** A vector orthogonal to every `g_{p+5}` is the coefficient sequence
of a bounded power series vanishing at `q^{−1}, q^{−2}, …`, hence zero. -/
theorem curveProbe_span_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range fun p : ℕ =>
      curveVec D (curveEnergyDomain_curveProbe D (show 5 ≤ p + 5 by omega))))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro a ha
  have hq := D.one_lt_q
  have hz : ∀ p : ℕ, ∑' m, a m * ((D.q ^ (p + 5))⁻¹ * D.q ^ 4) ^ m = 0 := by
    intro p
    have h := (Submodule.mem_orthogonal _ a).mp ha _ (Submodule.subset_span ⟨p, rfl⟩)
    rw [lp.inner_eq_tsum] at h
    rw [← h]
    refine tsum_congr fun m => ?_
    rw [curveVec_curveProbe_apply, RCLike.inner_apply, conj_trivial]
  have hzero := _root_.RHTower.boundedPowerSeries_coeff_eq_zero_of_zeroSequence
    (c := fun m => a m) (C := ‖a‖) (q := fun p => (D.q ^ (p + 5))⁻¹ * D.q ^ 4)
    (fun n => by
      simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) a n)
    (fun p => (curveProbe_ratio D (show 5 ≤ p + 5 by omega)).1)
    (fun p => by
      rw [abs_of_pos (curveProbe_ratio D (show 5 ≤ p + 5 by omega)).1]
      exact (curveProbe_ratio D (show 5 ≤ p + 5 by omega)).2)
    (by
      have h0 : Tendsto (fun p : ℕ => (D.q⁻¹) ^ p * ((D.q ^ 5)⁻¹ * D.q ^ 4)) atTop
          (𝓝 (0 * ((D.q ^ 5)⁻¹ * D.q ^ 4))) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (q_pos D).le)
          (inv_lt_one_of_one_lt₀ hq)).mul_const _
      rw [zero_mul] at h0
      refine h0.congr fun p => ?_
      rw [pow_add, mul_inv, inv_pow]
      ring)
    hz
  ext m
  exact hzero m

/-- The probe sum `Σ_k c_k g_{k+5}`. -/
def curveProbeSum {N : ℕ} (c : Fin N → ℝ) : ℕ → ℝ := fun m => ∑ k, c k * curveProbe D (k + 5) m

theorem curveEnergyDomain_finsetSum {κ : Type*} (s : Finset κ) {F : κ → ℕ → ℝ}
    (hF : ∀ i, CurveEnergyDomain D (F i)) (c : κ → ℝ) :
    CurveEnergyDomain D (fun m => ∑ i ∈ s, c i * F i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using curveEnergyDomain_zero D
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    exact curveEnergyDomain_add D (curveEnergyDomain_const_mul D (hF b) (c b)) ih

theorem curveEnergyDomain_curveProbeSum {N : ℕ} (c : Fin N → ℝ) :
    CurveEnergyDomain D (curveProbeSum D c) :=
  curveEnergyDomain_finsetSum D _ (fun k => curveEnergyDomain_curveProbe D (by omega)) c

theorem curveVec_curveProbeSum {N : ℕ} (c : Fin N → ℝ) :
    curveVec D (curveEnergyDomain_curveProbeSum D c) =
      ∑ k : Fin N, c k • curveVec D (curveEnergyDomain_curveProbe D (show 5 ≤ (k : ℕ) + 5 by omega)) := by
  ext m
  simp only [curveVec_apply, curveProbeSum, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Approximation by curve probe sums** in the weighted `ℓ²` norm. -/
theorem exists_curveProbeSum_near {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (c : Fin N → ℝ),
      ‖curveVec D (curveEnergyDomain_curveProbeSum D c) - curveVec D hf‖ < δ := by
  classical
  have hd := Submodule.topologicalClosure_eq_top_iff.mpr (curveProbe_span_orthogonal_eq_bot D)
  have ht : curveVec D hf ∈ closure ((Submodule.span ℝ (Set.range fun p : ℕ =>
      curveVec D (curveEnergyDomain_curveProbe D (show 5 ≤ p + 5 by omega)))) :
        Set (ℓ²(ℕ, ℝ))) := by
    rw [← Submodule.topologicalClosure_coe, hd, Submodule.top_coe]
    exact Set.mem_univ _
  obtain ⟨v, hv, hvt⟩ := Metric.mem_closure_iff.mp ht δ hδ
  obtain ⟨c', rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  set N := c'.support.sup id + 1
  refine ⟨N, fun k => c' k, ?_⟩
  rw [curveVec_curveProbeSum]
  have hsub : c'.support ⊆ Finset.range N := fun p hp => by
    have := Finset.le_sup (f := id) hp
    rw [Finset.mem_range]
    simp only [id] at this
    omega
  have hsum : (∑ k : Fin N, c' k • curveVec D
      (curveEnergyDomain_curveProbe D (show 5 ≤ (k : ℕ) + 5 by omega))) =
      c'.sum fun p a => a • curveVec D (curveEnergyDomain_curveProbe D (show 5 ≤ p + 5 by omega)) := by
    rw [Finsupp.sum_of_support_subset c' hsub
      (fun p a => a • curveVec D (curveEnergyDomain_curveProbe D (show 5 ≤ p + 5 by omega)))
      (fun p _ => zero_smul ℝ _)]
    exact Fin.sum_univ_eq_sum_range
      (fun p => c' p • curveVec D (curveEnergyDomain_curveProbe D (show 5 ≤ p + 5 by omega))) N
  rw [hsum]
  rwa [dist_comm, dist_eq_norm] at hvt

/-! ### The curve Pick form -/

theorem curveBareForm_finsetSum_left (hD : InFourStrip D) {κ : Type*} (s : Finset κ)
    {F : κ → ℕ → ℝ} (hF : ∀ i, CurveEnergyDomain D (F i)) (c : κ → ℝ) (g : ℕ → ℝ) :
    curveBareForm D (fun m => ∑ i ∈ s, c i * F i m) g = ∑ i ∈ s, c i * curveBareForm D (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := curveBareForm_smul_left D 0 g g
    simp only [zero_mul] at h
    simpa only [Finset.sum_empty] using h
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    rw [curveBareForm_add_left D hD (curveEnergyDomain_const_mul D (hF b) (c b))
      (curveEnergyDomain_finsetSum D s hF c), curveBareForm_smul_left, ih]

theorem curveConfinementPair_finsetSum_left {κ : Type*} (s : Finset κ) {F : κ → ℕ → ℝ}
    (hF : ∀ i, CurveEnergyDomain D (F i)) (c : κ → ℝ) {g : ℕ → ℝ} (hg : CurveEnergyDomain D g) :
    curveConfinementPair D (fun m => ∑ i ∈ s, c i * F i m) g =
      ∑ i ∈ s, c i * curveConfinementPair D (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := curveConfinementPair_smul_left D 0 g g
    simp only [zero_mul] at h
    simpa only [Finset.sum_empty] using h
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    rw [curveConfinementPair_add_left D (curveEnergyDomain_const_mul D (hF b) (c b))
      (curveEnergyDomain_finsetSum D s hF c) hg, curveConfinementPair_smul_left, ih]

/-- The curve Pick form on the nodes `5, …, N + 4`: the quadratic form of
`(B_D(g_m, g_n) + a W₈(g_m, g_n))`. -/
def curvePickForm (a : ℝ) {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ j, ∑ k, c j * c k * (curveBareForm D (curveProbe D (j + 5)) (curveProbe D (k + 5)) +
    a * curveConfinementPair D (curveProbe D (j + 5)) (curveProbe D (k + 5)))

/-- The curve Pick form is the confined curve form of the probe sum. -/
theorem curvePickForm_eq (hD : InFourStrip D) (a : ℝ) {N : ℕ} (c : Fin N → ℝ) :
    curvePickForm D a c = curveBareForm D (curveProbeSum D c) (curveProbeSum D c) +
      a * curveConfinementMass D (curveProbeSum D c) := by
  have hg : ∀ k : Fin N, CurveEnergyDomain D (curveProbe D (k + 5)) := fun k =>
    curveEnergyDomain_curveProbe D (by omega)
  have hP := curveEnergyDomain_curveProbeSum D c
  have hB : curveBareForm D (curveProbeSum D c) (curveProbeSum D c) =
      ∑ j, ∑ k, c j * c k * curveBareForm D (curveProbe D (j + 5)) (curveProbe D (k + 5)) := by
    have e : curveProbeSum D c = fun m => ∑ k, c k * curveProbe D (k + 5) m := rfl
    rw [e, curveBareForm_finsetSum_left D hD _ hg c]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [curveBareForm_comm D hD (f := curveProbe D (j + 5))
      (g := fun m => ∑ k, c k * curveProbe D (k + 5) m) (hg j) hP,
      curveBareForm_finsetSum_left D hD _ hg c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [curveBareForm_comm D hD (hg k) (hg j)]
    ring
  have hW : curveConfinementMass D (curveProbeSum D c) =
      ∑ j, ∑ k, c j * c k * curveConfinementPair D (curveProbe D (j + 5)) (curveProbe D (k + 5)) := by
    have e : curveProbeSum D c = fun m => ∑ k, c k * curveProbe D (k + 5) m := rfl
    unfold curveConfinementMass
    rw [e, curveConfinementPair_finsetSum_left D _ hg c (g := fun m => ∑ k, c k * curveProbe D (k + 5) m) hP]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [curveConfinementPair_comm, curveConfinementPair_finsetSum_left D _ hg c (hg j),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [curveConfinementPair_comm]
    ring
  rw [hB, hW, Finset.mul_sum, ← Finset.sum_add_distrib]
  unfold curvePickForm
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The Pick form decides the confined curve form -/

/-- A product moves by at most `ε(‖B‖ + ε + ‖A‖)` when both factors move by `ε`. -/
theorem re_mul_le (A B A' B' : ℂ) {ε : ℝ} (hA : ‖A' - A‖ ≤ ε) (hB : ‖B' - B‖ ≤ ε) :
    (A' * B').re ≤ (A * B).re + ε * (‖B‖ + ε + ‖A‖) := by
  have h1 : A' * B' - A * B = (A' - A) * B' + A * (B' - B) := by ring
  have hB' : ‖B'‖ ≤ ‖B‖ + ε := by
    have := norm_le_insert' B' B; linarith [norm_sub_rev B' B]
  have h2 : ‖A' * B' - A * B‖ ≤ ε * (‖B‖ + ε) + ‖A‖ * ε := by
    rw [h1]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul hA hB' (norm_nonneg _) ((norm_nonneg _).trans hA)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hB (norm_nonneg _)
  have h3 := Complex.re_le_norm (A' * B' - A * B)
  simp only [Complex.sub_re] at h3
  nlinarith

/-- **The curve Pick matrices decide the confined curve form.** For every `a`, all curve Pick
matrices on the nodes `5, 6, …` are positive semidefinite iff `B_D + aW₈ ≥ 0` on `H_D`. -/
theorem curvePick_nonneg_iff (hD : InFourStrip D) (a : ℝ) :
    (∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ curvePickForm D a c) ↔
      ∀ h : ℕ → ℝ, CurveEnergyDomain D h →
        0 ≤ curveBareForm D h h + a * curveConfinementMass D h := by
  constructor
  · intro hP h hh
    -- Laplace constants at the roots and their inverses
    have hz1 : ∀ i, (D.q ^ 4)⁻¹ < ‖D.β i‖ := inv_q_four_lt_norm_β D hD
    have hz2 : ∀ i, (D.q ^ 4)⁻¹ < ‖(D.β i)⁻¹‖ := fun i => by
      rw [← β_fePerm_eq_inv]; exact inv_q_four_lt_norm_β D hD _
    set Cz : ℂ → ℝ := fun z => (∑' m : ℕ, (‖(D.q ^ 4 * z)⁻¹‖ ^ m) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
    have hCz : ∀ z, 0 ≤ Cz z := fun z => Real.rpow_nonneg (tsum_nonneg fun m =>
      Real.rpow_nonneg (pow_nonneg (norm_nonneg _) m) _) _
    set C : ℝ := ∑ i : ι, (Cz (D.β i) + Cz (D.β i)⁻¹)
    have hC1 : ∀ i, Cz (D.β i) ≤ C := fun i => by
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => Cz (D.β i) + Cz (D.β i)⁻¹)
        (fun i _ => add_nonneg (hCz _) (hCz _)) (Finset.mem_univ i))
      linarith [hCz (D.β i)⁻¹]
    have hC2 : ∀ i, Cz (D.β i)⁻¹ ≤ C := fun i => by
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => Cz (D.β i) + Cz (D.β i)⁻¹)
        (fun i _ => add_nonneg (hCz _) (hCz _)) (Finset.mem_univ i))
      linarith [hCz (D.β i)]
    have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => add_nonneg (hCz _) (hCz _)
    set M : ℝ := ∑ i : ι, (‖curveLaplace h (D.β i)⁻¹‖ + ‖curveLaplace h (D.β i)‖)
    have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => by positivity
    set K : ℝ := C * (M + (Fintype.card ι : ℝ) * C) + |a| * (2 * ‖curveVec D hh‖ + 1)
    have hK : 0 ≤ K := by positivity
    have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        -(K * δ) ≤ curveBareForm D h h + a * curveConfinementMass D h := by
      intro δ hδ hδ1
      obtain ⟨N, c, hc⟩ := exists_curveProbeSum_near D hh hδ
      have hPd := curveEnergyDomain_curveProbeSum D c
      set d := ‖curveVec D hPd - curveVec D hh‖
      have hd : d ≤ δ := hc.le
      -- the bare form moves by at most `δ C (M + |ι| C)`
      have hBterm : ∀ i : ι,
          (curveLaplace (curveProbeSum D c) (D.β i) * curveLaplace (curveProbeSum D c) (D.β i)⁻¹).re ≤
          (curveLaplace h (D.β i) * curveLaplace h (D.β i)⁻¹).re +
            C * δ * (‖curveLaplace h (D.β i)⁻¹‖ + C * δ + ‖curveLaplace h (D.β i)‖) := fun i =>
        re_mul_le _ _ _ _
          ((norm_curveLaplace_sub_le D hPd hh (hz1 i)).trans
            (by nlinarith [hC1 i, hCz (D.β i), norm_nonneg (curveVec D hPd - curveVec D hh)]))
          ((norm_curveLaplace_sub_le D hPd hh (hz2 i)).trans
            (by nlinarith [hC2 i, hCz (D.β i)⁻¹, norm_nonneg (curveVec D hPd - curveVec D hh)]))
      have hBsum : curveBareForm D (curveProbeSum D c) (curveProbeSum D c) ≤
          curveBareForm D h h + C * δ * (M + (Fintype.card ι : ℝ) * C) := by
        unfold curveBareForm
        rw [Complex.re_sum, Complex.re_sum]
        have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hBterm i
        rw [Finset.sum_add_distrib] at hs
        have hle : ∑ i : ι, C * δ * (‖curveLaplace h (D.β i)⁻¹‖ + C * δ +
            ‖curveLaplace h (D.β i)‖) ≤ C * δ * (M + (Fintype.card ι : ℝ) * C) := by
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ∑ i : ι, (‖curveLaplace h (D.β i)⁻¹‖ + C * δ + ‖curveLaplace h (D.β i)‖)
              = (∑ i : ι, (‖curveLaplace h (D.β i)⁻¹‖ + ‖curveLaplace h (D.β i)‖)) +
                  ∑ _i : ι, C * δ := by
                rw [← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl fun i _ => by ring
            _ = M + (Fintype.card ι : ℝ) * (C * δ) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            _ ≤ M + (Fintype.card ι : ℝ) * C := by
                have : C * δ ≤ C := by nlinarith
                have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
                nlinarith
        linarith
      -- the confinement moves by at most `δ (2‖h‖ + 1)`
      have hmass : |curveConfinementMass D (curveProbeSum D c) - curveConfinementMass D h| ≤
          δ * (2 * ‖curveVec D hh‖ + 1) := by
        rw [← norm_curveVec_sq D hPd, ← norm_curveVec_sq D hh]
        have h1 := abs_norm_sub_norm_le (curveVec D hPd) (curveVec D hh)
        have h2 : ‖curveVec D hPd‖ ≤ ‖curveVec D hh‖ + δ := by
          have := norm_le_insert' (curveVec D hPd) (curveVec D hh); linarith
        rw [sq_sub_sq, abs_mul]
        have h3 : |‖curveVec D hPd‖ + ‖curveVec D hh‖| ≤ 2 * ‖curveVec D hh‖ + 1 := by
          rw [abs_of_nonneg (by positivity)]; linarith
        calc |‖curveVec D hPd‖ + ‖curveVec D hh‖| * |‖curveVec D hPd‖ - ‖curveVec D hh‖|
            ≤ (2 * ‖curveVec D hh‖ + 1) * δ :=
              mul_le_mul h3 (h1.trans hd) (abs_nonneg _) (by positivity)
          _ = δ * (2 * ‖curveVec D hh‖ + 1) := by ring
      have ha : a * curveConfinementMass D (curveProbeSum D c) ≤
          a * curveConfinementMass D h + |a| * (δ * (2 * ‖curveVec D hh‖ + 1)) := by
        have := abs_le.mp hmass
        rcases le_or_gt 0 a with h0 | h0
        · rw [abs_of_nonneg h0]; nlinarith
        · rw [abs_of_neg h0]; nlinarith
      have h0 := hP N c
      rw [curvePickForm_eq D hD a c] at h0
      have hKd : K * δ = C * δ * (M + (Fintype.card ι : ℝ) * C) +
          |a| * (δ * (2 * ‖curveVec D hh‖ + 1)) := by simp only [K]; ring
      linarith
    by_contra hneg
    have hlt := not_le.mp hneg
    set Q := curveBareForm D h h + a * curveConfinementMass D h
    set δ := min 1 (-Q / (2 * (K + 1)))
    have hδ : 0 < δ := lt_min one_pos (by apply div_pos <;> linarith)
    have hk := key δ hδ (min_le_left _ _)
    have h1 : K * δ ≤ K * (-Q / (2 * (K + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK
    have h3 : K * (-Q / (2 * (K + 1))) < -Q := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  · intro hQ N c
    rw [curvePickForm_eq D hD a c]
    exact hQ _ (curveEnergyDomain_curveProbeSum D c)

/-! ### Calibration -/

/-- **RH for the curve in Pick form.** The Frobenius roots are unitary iff every bare curve Pick
matrix on the nodes `5, 6, …` is positive semidefinite. -/
theorem unitary_iff_curvePick_nonneg (hD : InFourStrip D) :
    (∀ i, ‖D.β i‖ = 1) ↔ ∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ curvePickForm D 0 c := by
  rw [curvePick_nonneg_iff D hD 0]
  constructor
  · intro hU h _
    rw [zero_mul, add_zero, curveBareForm_eq_sum_norm_sq_of_unitary D hU]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · intro hpos
    by_contra hnot
    obtain ⟨a, f, hmass, hcrit, -⟩ := exists_curveGroundState_of_not_unitary D hD hnot
    have hself := hcrit.2.2.2 f hcrit.2.1
    have h0 := hpos f hcrit.2.1
    unfold curveConfinementMass at hmass
    rw [hmass] at hself
    have := hcrit.1
    linarith

/-- **The curve critical constant in Pick form.** Off curve RH the ground-state constant `a*` is the
least `a` at which every curve Pick matrix `(B_D(g_m, g_n) + a W₈(g_m, g_n))_{m,n ≥ 5}` is positive
semidefinite. -/
theorem isLeast_curvePick_groundConstant (hD : InFourStrip D) (hnot : ¬ ∀ i, ‖D.β i‖ = 1) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      IsLeast {a : ℝ | ∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ curvePickForm D a c} a₀ := by
  obtain ⟨a₀, f, hmass, hcrit, hvar⟩ := exists_curveGroundState_of_not_unitary D hD hnot
  refine ⟨a₀, hcrit.1, (curvePick_nonneg_iff D hD a₀).mpr hvar, fun a ha => ?_⟩
  have h1 := (curvePick_nonneg_iff D hD a).mp ha f hcrit.2.1
  have hself := hcrit.2.2.2 f hcrit.2.1
  rw [hmass] at h1
  unfold curveConfinementMass at hmass
  rw [hmass] at hself
  linarith

/-- For unitary roots every curve Pick matrix is positive semidefinite at every `a ≥ 0`. -/
theorem curvePick_nonneg_of_unitary (hD : InFourStrip D) (hU : ∀ i, ‖D.β i‖ = 1) {a : ℝ}
    (ha : 0 ≤ a) (N : ℕ) (c : Fin N → ℝ) : 0 ≤ curvePickForm D a c := by
  refine (curvePick_nonneg_iff D hD a).mpr (fun h _ => ?_) N c
  rw [curveBareForm_eq_sum_norm_sq_of_unitary D hU]
  exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (mul_nonneg ha (curveConfinementMass_nonneg D h))

#print axioms curvePick_nonneg_iff
#print axioms unitary_iff_curvePick_nonneg
#print axioms isLeast_curvePick_groundConstant


/-! ### The non-unitary roots bound the ground constant -/

/-- The Laplace constant `C_z = (Σ_m |q^{-4}z^{-1}|^{2m})^{1/2}`: `|L_D f(z)| ≤ C_z ‖f‖_{W₈}`. -/
def curveLaplaceConst (z : ℂ) : ℝ :=
  (∑' m : ℕ, (‖(D.q ^ 4 * z)⁻¹‖ ^ m) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))

theorem norm_curveLaplace_le {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) {z : ℂ}
    (hz : (D.q ^ 4)⁻¹ < ‖z‖) :
    ‖curveLaplace f z‖ ≤ ‖curveVec D hf‖ * curveLaplaceConst D z := by
  have h := norm_curveLaplace_sub_le D hf (curveEnergyDomain_zero D) hz
  have h0 : curveLaplace (fun _ => (0 : ℝ)) z = 0 := by simp [curveLaplace]
  have hv : curveVec D (curveEnergyDomain_zero D) = 0 := by
    ext m; simp [curveVec_apply]
  rw [h0, sub_zero, hv, sub_zero] at h
  exact h

/-- The weight of a root: `C_β C_{β⁻¹}` if `|β| ≠ 1`, `0` if `|β| = 1`. -/
def curveOffLineWeight (i : ι) : ℝ :=
  if ‖D.β i‖ = 1 then 0 else curveLaplaceConst D (D.β i) * curveLaplaceConst D (D.β i)⁻¹

theorem curveLaplaceConst_nonneg (z : ℂ) : 0 ≤ curveLaplaceConst D z :=
  Real.rpow_nonneg (tsum_nonneg fun m => Real.rpow_nonneg (pow_nonneg (norm_nonneg _) m) _) _

/-- **The bare curve form is at least minus the non-unitary weight**: unitary roots contribute
`|L_D f(β)|² ≥ 0`, a non-unitary root at least `−C_β C_{β⁻¹} W₈(f)`. -/
theorem curveBareForm_ge (hD : InFourStrip D) {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) :
    -((∑ i, curveOffLineWeight D i) * curveConfinementMass D f) ≤ curveBareForm D f f := by
  have hz1 : ∀ i, (D.q ^ 4)⁻¹ < ‖D.β i‖ := inv_q_four_lt_norm_β D hD
  have hz2 : ∀ i, (D.q ^ 4)⁻¹ < ‖(D.β i)⁻¹‖ := fun i => by
    rw [← β_fePerm_eq_inv]; exact inv_q_four_lt_norm_β D hD _
  unfold curveBareForm
  rw [Complex.re_sum, ← norm_curveVec_sq D hf, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold curveOffLineWeight
  split_ifs with hU
  · have hinv : (D.β i)⁻¹ = conj (D.β i) := by
      have h1 : D.β i * conj (D.β i) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hU]; norm_num
      exact (eq_inv_of_mul_eq_one_right h1).symm
    rw [hinv, ← curveLaplace_conj f (D.β i), Complex.mul_conj, Complex.ofReal_re, zero_mul,
      neg_zero]
    exact Complex.normSq_nonneg _
  · have hA := norm_curveLaplace_le D hf (hz1 i)
    have hB := norm_curveLaplace_le D hf (hz2 i)
    have hre := (abs_le.mp (Complex.abs_re_le_norm
      (curveLaplace f (D.β i) * curveLaplace f (D.β i)⁻¹))).1
    rw [norm_mul] at hre
    have hprod : ‖curveLaplace f (D.β i)‖ * ‖curveLaplace f (D.β i)⁻¹‖ ≤
        curveLaplaceConst D (D.β i) * curveLaplaceConst D (D.β i)⁻¹ * ‖curveVec D hf‖ ^ 2 := by
      calc ‖curveLaplace f (D.β i)‖ * ‖curveLaplace f (D.β i)⁻¹‖
          ≤ (‖curveVec D hf‖ * curveLaplaceConst D (D.β i)) *
              (‖curveVec D hf‖ * curveLaplaceConst D (D.β i)⁻¹) :=
            mul_le_mul hA hB (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (curveLaplaceConst_nonneg D _))
        _ = _ := by ring
    linarith

/-- **The non-unitary roots bound the curve ground constant.** Off curve RH, the least ratio at which
all curve Pick matrices are positive semidefinite is at most `Σ_{|β_i| ≠ 1} C_{β_i} C_{β_i⁻¹}` — the
function-field calibration of the lower bound of the critical ratio by the off-line zeros. -/
theorem curveGroundConstant_le_offLineWeight (hD : InFourStrip D) (hnot : ¬ ∀ i, ‖D.β i‖ = 1) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      IsLeast {a : ℝ | ∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ curvePickForm D a c} a₀ ∧
      a₀ ≤ ∑ i, curveOffLineWeight D i := by
  obtain ⟨a₀, ha₀, hleast⟩ := isLeast_curvePick_groundConstant D hD hnot
  refine ⟨a₀, ha₀, hleast, hleast.2 ?_⟩
  refine (curvePick_nonneg_iff D hD _).mpr fun h hh => ?_
  have := curveBareForm_ge D hD hh
  linarith

#print axioms curveGroundConstant_le_offLineWeight

section CubicKummer
open ExponentDynamicsOfTheCriticalStrip
open GaloisForLFunctions.RHTower.Hyperelliptic (rootEnum)

variable {F : Type*} [Field F] [Fintype F]

/-- **The function-field probe form of RH is a theorem.** For the cubic Kummer datum of a cubic
character (native Stepanov) every curve Pick matrix is positive semidefinite at every `a ≥ 0`. -/
theorem cubicKummer_curvePick_nonneg {χ : MulChar F ℂ} (hχ : χ ≠ 1) (hχ3 : χ ^ 3 = 1) {NF : ℕ}
    (hqF : Fintype.card F = 3 * NF + 1) {P : Polynomial F} (hsq : Squarefree P) (hsplit : P.Splits)
    (hm : 0 < P.natDegree) (hχm : χ ^ P.natDegree ≠ 1) {a : ℝ} (ha : 0 ≤ a) (N : ℕ)
    (c : Fin N → ℝ) :
    0 ≤ curvePickForm (cubicKummerDatum hχ hχ3 hqF hsq hsplit hm hχm) a c := by
  set D := cubicKummerDatum hχ hχ3 hqF hsq hsplit hm hχm
  have hrh := (riemannHypothesis_cubicCharacter.{_, 0} hχ hχ3 hqF hsq hsplit hm hχm).2.1
  have hsq_pos : 0 < Real.sqrt (Fintype.card F) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hnorm1 : ∀ i : Fin (lRootsC χ P).toList.length,
      ‖rootEnum (lRootsC χ P) i / (Real.sqrt (Fintype.card F) : ℂ)‖ = 1 := fun i => by
    have hmem : rootEnum (lRootsC χ P) i ∈ lRootsC χ P :=
      Multiset.mem_toList.mp (List.get_mem _ _)
    rw [norm_div, hrh _ hmem, Complex.norm_real, Real.norm_of_nonneg hsq_pos.le,
      div_self hsq_pos.ne']
  have hU : ∀ x, ‖D.β x‖ = 1 := by
    intro x
    cases x with
    | inl i => exact hnorm1 i
    | inr i =>
      show ‖conj (rootEnum (lRootsC χ P) i / (Real.sqrt (Fintype.card F) : ℂ))‖ = 1
      rw [Complex.norm_conj]
      exact hnorm1 i
  have hD : InFourStrip D := fun x => by
    rw [hU x]
    exact one_lt_pow₀ D.one_lt_q (by norm_num)
  exact curvePick_nonneg_of_unitary D hD hU ha N c

end CubicKummer

#print axioms cubicKummer_curvePick_nonneg

end CurveModels
end GaloisForLFunctions.ExclusionOfTheCriticalState
