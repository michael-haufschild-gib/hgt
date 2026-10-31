import GaloisForLFunctions.AdelicKreinGeometry.WeilsArchimedeanStateCountsTheZeros
import GaloisForLFunctions.HTGeometry.GammaShiftConfluentCasoratian

/-!
# Jordan pair kernels on the positive rational dilations

A multiple off-line zero of multiplicity `m = d + 1` in a contour correlation on `ℚ_{>0}` produces a
polynomial-exponential **Jordan pair kernel**

`J_{w, P}(v) = P(log v) e^{−i w log v} + conj(P(−log v)) e^{−i w̄ log v}`

with `deg P = d`. Unlike a scalar hyperbolic pair (`d = 0`), whose negative index is `1` regardless
of zero multiplicity, `J_{w, P}` carries the full `d + 1` Jordan chain of `(log v)^j e^{−i w log v}`.

* **Exact signature formula** (`negIndex_sum_jordanPairKernel_eq`): for distinct lower-half-plane
  frequencies `u_i` (`Im u_i < 0`) and nonzero polynomials `P_i`,
  `κ(∑_i J_{u_i, P_i}) = ∑_i (deg P_i + 1)`.
  * Upper bound (`negIndex_sum_jordanPairKernel_le`): expanding `(y_b − y_a)^r` expresses the Gram
    form through the `∑_i (deg P_i + 1)` jet functionals `c ↦ ∑_b c_b (log x_b)^j e^{−i u_i log x_b}`,
    so the form vanishes on their common kernel.
  * Lower bound (`le_negIndex_sum_jordanPairKernel`): on a fine cyclic subgroup `⟨u₀⟩` separating the
    `2κ` exponential nodes `e^{−i u_i log u₀}, e^{−i ū_i log u₀}`, the confluent exponential-polynomial
    jet matrix factors the confluent polynomial jet matrix of `GammaShiftConfluentCasoratian`, hence is
    invertible. Scaling dual jet coordinates by `(n + 1)^j` against `(n + 1)^{−(d_i − l)}` sends the
    compressed Gram matrices entrywise to a strictly negative diagonal matrix of rank
    `∑_i (deg P_i + 1)`.
* **Sub-boost growth** (`jordanPairKernel_subBoost`, `negIndex_archGlue_sum_jordanPairKernel_eq`):
  when `|Im u_i| < 1/2`, every polynomial-exponential term grows slower than `v^{1/2}` along `2^N`,
  so gluing to the archimedean successor `−c|b|` (`c > 0`) has index `∑_i (deg P_i + 1) + 1`.
-/

open Complex Matrix Polynomial Finset Filter Topology
open scoped ComplexConjugate BigOperators
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Logarithm identities on `ℚ_{>0}` -/

@[simp]
theorem logPos_one : logPos 1 = 0 := by
  simp [logPos]

theorem logPos_mul (u v : posUnits) : logPos (u * v) = logPos u + logPos v := by
  have hu : (0 : ℝ) < (((u : ℚˣ) : ℚ) : ℝ) := posUnits_val_pos u
  have hv : (0 : ℝ) < (((v : ℚˣ) : ℚ) : ℝ) := posUnits_val_pos v
  simp only [logPos, Subgroup.coe_mul, Units.val_mul]
  push_cast
  exact Real.log_mul hu.ne' hv.ne'

theorem logPos_inv (u : posUnits) : logPos u⁻¹ = -logPos u := by
  simpa [logPos_one, zero_sub] using logPos_inv_mul u 1

theorem logPos_pow (u : posUnits) (k : ℕ) : logPos (u ^ k) = (k : ℝ) * logPos u := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, logPos_mul, ih]
      push_cast
      ring

/-! ### Forward polynomial-exponential modes and Jordan pair kernels -/

/-- One forward polynomial-exponential dilation mode `P(log v) e^{−i w log v}`. -/
def jordanForward (w : ℂ) (P : ℂ[X]) (v : posUnits) : ℂ :=
  P.eval (logPos v : ℂ) * cexp (-I * w * (logPos v : ℂ))

/-- The Hermitian **Jordan pair kernel** `P(log v) e^{−i w log v} + conj(P(−log v)) e^{−i w̄ log v}`
on `ℚ_{>0}`. -/
def jordanPairKernel (w : ℂ) (P : ℂ[X]) (v : posUnits) : ℂ :=
  jordanForward w P v + conj (jordanForward w P v⁻¹)

theorem jordanPairKernel_apply (w : ℂ) (P : ℂ[X]) (v : posUnits) :
    jordanPairKernel w P v =
      P.eval (logPos v : ℂ) * cexp (-I * w * (logPos v : ℂ)) +
        conj (P.eval (-(logPos v : ℂ))) * cexp (-I * conj w * (logPos v : ℂ)) := by
  simp only [jordanPairKernel, jordanForward, logPos_inv, Complex.ofReal_neg, map_mul,
    ← Complex.exp_conj]
  congr 2
  simp only [map_neg, conj_I, Complex.conj_ofReal]
  ring

theorem isHermKernel_jordanPairKernel (w : ℂ) (P : ℂ[X]) :
    IsHermKernel (jordanPairKernel w P) := fun v => by
  simp only [jordanPairKernel, inv_inv, map_add, conj_conj, add_comm]

theorem isHermKernel_sum_jordanPairKernel {α : Type*} (S : Finset α) (w : α → ℂ) (P : α → ℂ[X]) :
    IsHermKernel (fun v => ∑ i ∈ S, jordanPairKernel (w i) (P i) v) := fun v => by
  simp only [map_sum, isHermKernel_jordanPairKernel _ _ v]

/-! ### Sub-boost growth along `2^N` -/

private theorem tendsto_linear_pow_mul_exp_neg (j : ℕ) {c : ℝ} (hc : 0 < c) (a : ℝ) :
    Tendsto (fun N : ℕ => ((N : ℝ) * Real.log 2 + a) ^ j *
      Real.exp (-((N : ℝ) * Real.log 2) * c)) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : Tendsto (fun N : ℕ => c * ((N : ℝ) * Real.log 2)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hlog2).const_mul_atTop hc
  have hbase : ∀ q : ℕ, Tendsto (fun N : ℕ =>
      (c * ((N : ℝ) * Real.log 2)) ^ q * Real.exp (-(c * ((N : ℝ) * Real.log 2)))) atTop (𝓝 0) :=
    fun q => (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero q).comp hx
  have hterm : ∀ q : ℕ, Tendsto (fun N : ℕ =>
      ((j.choose q : ℝ) * c⁻¹ ^ q * a ^ (j - q)) *
        ((c * ((N : ℝ) * Real.log 2)) ^ q * Real.exp (-(c * ((N : ℝ) * Real.log 2)))))
      atTop (𝓝 0) := fun q => by
    simpa using (hbase q).const_mul ((j.choose q : ℝ) * c⁻¹ ^ q * a ^ (j - q))
  have hsum := tendsto_finsetSum (Finset.range (j + 1)) fun q _ => hterm q
  rw [Finset.sum_const_zero] at hsum
  refine hsum.congr fun N => ?_
  have hsplit : (N : ℝ) * Real.log 2 + a = c⁻¹ * (c * ((N : ℝ) * Real.log 2)) + a := by
    field_simp
  rw [hsplit, add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_pow, show -((N : ℝ) * Real.log 2) * c = -(c * ((N : ℝ) * Real.log 2)) by ring]
  ring

private theorem jordanForward_subBoost_of_im_lt {w : ℂ} (hw : w.im < 1 / 2) (P : ℂ[X])
    (a : ℝ) (s : ℝ) (hs : |s| = 1) :
    Tendsto (fun N : ℕ => P.eval (((s * ((N : ℝ) * Real.log 2 + a) : ℝ) : ℂ)) *
      cexp (-I * w * (((N : ℝ) * Real.log 2 + a : ℝ) : ℂ)) *
      ((Real.exp (-((N : ℝ) * Real.log 2) / 2) : ℝ) : ℂ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hc : 0 < 1 / 2 - w.im := by linarith
  have hterm : ∀ r : ℕ, Tendsto (fun N : ℕ =>
      ‖P.coeff r‖ * Real.exp (a * w.im) *
        (|(N : ℝ) * Real.log 2 + a| ^ r * Real.exp (-((N : ℝ) * Real.log 2) * (1 / 2 - w.im))))
      atTop (𝓝 0) := fun r => by
    have h0 := tendsto_linear_pow_mul_exp_neg r hc a
    have habs : Tendsto (fun N : ℕ =>
        |(N : ℝ) * Real.log 2 + a| ^ r * Real.exp (-((N : ℝ) * Real.log 2) * (1 / 2 - w.im)))
        atTop (𝓝 0) := by
      have hpos : Tendsto (fun N : ℕ => (N : ℝ) * Real.log 2 + a) atTop atTop :=
        (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos (by norm_num))).atTop_add
          tendsto_const_nhds
      refine h0.congr' ?_
      filter_upwards [hpos.eventually_ge_atTop 0] with N hN
      rw [abs_of_nonneg hN]
    simpa using habs.const_mul (‖P.coeff r‖ * Real.exp (a * w.im))
  have hsum := tendsto_finsetSum (Finset.range (P.natDegree + 1)) fun r _ => hterm r
  rw [Finset.sum_const_zero] at hsum
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hsum
  set y : ℝ := (N : ℝ) * Real.log 2 + a
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, hs,
    one_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp : (-I * w * (y : ℂ)).re + -((N : ℝ) * Real.log 2) / 2 =
      a * w.im + -((N : ℝ) * Real.log 2) * (1 / 2 - w.im) := by
    have hre : (-I * w * (y : ℂ)).re = w.im * y := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    dsimp only [y]
    ring
  have hexp_mul : Real.exp ((-I * w * (y : ℂ)).re) * Real.exp (-((N : ℝ) * Real.log 2) / 2) =
      Real.exp (a * w.im) * Real.exp (-((N : ℝ) * Real.log 2) * (1 / 2 - w.im)) := by
    rw [← Real.exp_add, hexp, Real.exp_add]
  exact le_of_eq (by linear_combination ‖P.coeff r‖ * |y| ^ r * hexp_mul)

/-- **Jordan pair kernels in the open strip `|Im w| < 1/2` are sub-boost along `2^N`.** -/
theorem jordanPairKernel_subBoost {w : ℂ} (hw : |w.im| < 1 / 2) (P : ℂ[X]) (u : posUnits) :
    Tendsto (fun N : ℕ => jordanPairKernel w P (twoPos ^ N * u) *
      (((((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨hw1, hw2⟩ := abs_lt.mp hw
  set a : ℝ := logPos u
  have hlog : ∀ N : ℕ, logPos (twoPos ^ N * u) = (N : ℝ) * Real.log 2 + a := fun N => by
    rw [logPos_mul, logPos_pow]
    have h2 : logPos twoPos = Real.log 2 := by simp [logPos, twoPos]
    rw [h2]
  have hpow : ∀ N : ℕ, ((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) =
      Real.exp (-((N : ℝ) * Real.log 2) / 2) := fun N => by
    rw [twoPos_pow_val, Real.rpow_def_of_pos (by positivity), Real.log_pow]
    congr 1
    ring
  have h1 := jordanForward_subBoost_of_im_lt hw2 P a 1 (by norm_num)
  have hwc : (conj w).im < 1 / 2 := by rw [Complex.conj_im]; linarith
  let Pconj : ℂ[X] := P.map (starRingEnd ℂ)
  have h2 := jordanForward_subBoost_of_im_lt hwc Pconj a (-1) (by norm_num)
  have hadd := h1.add h2
  rw [add_zero] at hadd
  refine hadd.congr fun N => ?_
  rw [jordanPairKernel_apply, hlog N, hpow N, add_mul]
  congr 1
  · simp [one_mul]
  · set b : ℝ := (N : ℝ) * Real.log 2 + a
    have hp : conj (P.eval (-(b : ℂ))) = Pconj.eval (((-1 * b : ℝ) : ℂ)) := by
      have harg : ((-1 * b : ℝ) : ℂ) = conj (-(b : ℂ)) := by
        rw [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, map_neg,
          Complex.conj_ofReal]
      rw [Polynomial.eval_map, harg, Polynomial.eval₂_at_apply]
    rw [hp]

theorem sum_jordanPairKernel_subBoost {α : Type*} (S : Finset α) {w : α → ℂ}
    (hw : ∀ i ∈ S, |(w i).im| < 1 / 2) (P : α → ℂ[X]) (u : posUnits) :
    Tendsto (fun N : ℕ => (∑ i ∈ S, jordanPairKernel (w i) (P i) (twoPos ^ N * u)) *
      (((((((twoPos ^ N : posUnits) : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      atTop (𝓝 0) := by
  have h := tendsto_finsetSum S fun i hi => jordanPairKernel_subBoost (hw i hi) (P i) u
  rw [Finset.sum_const_zero] at h
  exact h.congr fun N => (Finset.sum_mul _ _ _).symm

/-! ### Bilinear expansion of the Gram form and the upper bound -/

/-- The `j`-th polynomial-exponential jet functional `c ↦ ∑_b c_b (log x_b)^j e^{−i w log x_b}`. -/
def expPolyEval (w : ℂ) (j : ℕ) {ι : Type*} [Fintype ι] (x : ι → posUnits) :
    (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun c := ∑ b, c b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))
  map_add' c d := by simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' t c := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

theorem expPolyEval_apply (w : ℂ) (j : ℕ) {ι : Type*} [Fintype ι] (x : ι → posUnits) (c : ι → ℂ) :
    expPolyEval w j x c =
      ∑ b, c b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ)) := rfl

/-- Bilinear Toeplitz expansion of `jordanForward w P`: expanding `(y_b − y_a)^r` factors the double
sum through `expPolyEval w j` and `expPolyEval (conj w) (r − j)`. -/
theorem bilinear_jordanForward (w : ℂ) (P : ℂ[X]) {ι : Type*} [Fintype ι] (x : ι → posUnits)
    (c₁ c₂ : ι → ℂ) :
    (∑ a, ∑ b, conj (c₁ a) * jordanForward w P ((x a)⁻¹ * x b) * c₂ b) =
      ∑ r ∈ Finset.range (P.natDegree + 1), P.coeff r *
        ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (expPolyEval (conj w) (r - j) x c₁) * expPolyEval w j x c₂ := by
  have hterm : ∀ a b, conj (c₁ a) * jordanForward w P ((x a)⁻¹ * x b) * c₂ b =
      ∑ r ∈ Finset.range (P.natDegree + 1), P.coeff r *
        ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
          (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))) := by
    intro a b
    simp only [jordanForward, logPos_inv_mul, Complex.ofReal_sub, Polynomial.eval_eq_sum_range]
    rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hexp : cexp (-I * w * ((logPos (x b) : ℂ) - (logPos (x a) : ℂ))) =
        conj (cexp (-I * conj w * (logPos (x a) : ℂ))) *
          cexp (-I * w * (logPos (x b) : ℂ)) := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_mul, map_neg, conj_I, conj_conj, Complex.conj_ofReal]
      ring
    have hpow : ((logPos (x b) : ℂ) - (logPos (x a) : ℂ)) ^ r =
        ∑ j ∈ Finset.range (r + 1),
          (logPos (x b) : ℂ) ^ j * (-(logPos (x a) : ℂ)) ^ (r - j) * (r.choose j : ℂ) := by
      rw [sub_eq_add_neg, add_pow]
    rw [hpow, hexp]
    rw [show conj (c₁ a) * (P.coeff r *
        (∑ j ∈ Finset.range (r + 1),
          (logPos (x b) : ℂ) ^ j * (-(logPos (x a) : ℂ)) ^ (r - j) * (r.choose j : ℂ)) *
        (conj (cexp (-I * conj w * (logPos (x a) : ℂ))) *
          cexp (-I * w * (logPos (x b) : ℂ)))) * c₂ b =
        P.coeff r * ((∑ j ∈ Finset.range (r + 1),
          (logPos (x b) : ℂ) ^ j * (-(logPos (x a) : ℂ)) ^ (r - j) * (r.choose j : ℂ)) *
          (conj (c₁ a) * conj (cexp (-I * conj w * (logPos (x a) : ℂ))) *
            (c₂ b * cexp (-I * w * (logPos (x b) : ℂ))))) by ring]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hneg : (-(logPos (x a) : ℂ)) ^ (r - j) =
        (-1 : ℂ) ^ (r - j) * conj ((logPos (x a) : ℂ) ^ (r - j)) := by
      rw [neg_eq_neg_one_mul, mul_pow, map_pow, Complex.conj_ofReal]
    rw [hneg, map_mul, map_mul]
    ring
  have hswap₁ : (∑ a : ι, ∑ b : ι, conj (c₁ a) * jordanForward w P ((x a)⁻¹ * x b) * c₂ b) =
      ∑ r ∈ Finset.range (P.natDegree + 1), ∑ a : ι, ∑ b : ι,
        P.coeff r * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
          (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))) := by
    calc (∑ a : ι, ∑ b : ι, conj (c₁ a) * jordanForward w P ((x a)⁻¹ * x b) * c₂ b)
        = ∑ a : ι, ∑ b : ι, ∑ r ∈ Finset.range (P.natDegree + 1),
            P.coeff r * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
              conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
              (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))) := by
          simp_rw [hterm]
      _ = ∑ a : ι, ∑ r ∈ Finset.range (P.natDegree + 1), ∑ b : ι,
            P.coeff r * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
              conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
              (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ r ∈ Finset.range (P.natDegree + 1), ∑ a : ι, ∑ b : ι,
            P.coeff r * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
              conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
              (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))) :=
          Finset.sum_comm
  rw [hswap₁]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hpull : (∑ a : ι, ∑ b : ι,
      P.coeff r * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
        conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
        (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ)))) =
      P.coeff r * ∑ j ∈ Finset.range (r + 1), ∑ a : ι, ∑ b : ι,
        (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
          (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))) := by
    calc (∑ a : ι, ∑ b : ι,
          P.coeff r * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
            conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
            (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))))
        = P.coeff r * ∑ a : ι, ∑ b : ι, ∑ j ∈ Finset.range (r + 1),
            (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
              conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
              (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))) := by
          simp_rw [← Finset.mul_sum]
      _ = P.coeff r * ∑ a : ι, ∑ j ∈ Finset.range (r + 1), ∑ b : ι,
            (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
              conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
              (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))) := by
          congr 1
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = P.coeff r * ∑ j ∈ Finset.range (r + 1), ∑ a : ι, ∑ b : ι,
            (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
              conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
              (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))) := by
          congr 1
          exact Finset.sum_comm
  rw [hpull]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hrhs : (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
      conj (expPolyEval (conj w) (r - j) x c₁) * expPolyEval w j x c₂ =
      ∑ a : ι, ∑ b : ι,
        (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) * cexp (-I * conj w * (logPos (x a) : ℂ))) *
          (c₂ b * (logPos (x b) : ℂ) ^ j * cexp (-I * w * (logPos (x b) : ℂ))) := by
    rw [expPolyEval_apply, expPolyEval_apply, map_sum]
    have h1 : (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
        (∑ a : ι, conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) *
          cexp (-I * conj w * (logPos (x a) : ℂ)))) =
        ∑ a : ι, (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (c₁ a * (logPos (x a) : ℂ) ^ (r - j) *
            cexp (-I * conj w * (logPos (x a) : ℂ))) := Finset.mul_sum _ _ _
    rw [h1, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
  exact hrhs.symm

/-- Bilinear Toeplitz identity for `jordanPairKernel w P`. -/
theorem bilinear_jordanPairKernel (w : ℂ) (P : ℂ[X]) {ι : Type*} [Fintype ι] (x : ι → posUnits)
    (c₁ c₂ : ι → ℂ) :
    (∑ a, ∑ b, conj (c₁ a) * jordanPairKernel w P ((x a)⁻¹ * x b) * c₂ b) =
      (∑ r ∈ Finset.range (P.natDegree + 1), P.coeff r *
        ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (expPolyEval (conj w) (r - j) x c₁) * expPolyEval w j x c₂) +
      conj (∑ r ∈ Finset.range (P.natDegree + 1), P.coeff r *
        ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (expPolyEval (conj w) (r - j) x c₂) * expPolyEval w j x c₁) := by
  have hsplit : (∑ a, ∑ b, conj (c₁ a) * jordanPairKernel w P ((x a)⁻¹ * x b) * c₂ b) =
      (∑ a, ∑ b, conj (c₁ a) * jordanForward w P ((x a)⁻¹ * x b) * c₂ b) +
        (∑ a, ∑ b, conj (c₁ a) * conj (jordanForward w P (((x a)⁻¹ * x b)⁻¹)) * c₂ b) := by
    simp only [jordanPairKernel, mul_add, add_mul, Finset.sum_add_distrib]
  have hanti : (∑ a, ∑ b, conj (c₁ a) * conj (jordanForward w P (((x a)⁻¹ * x b)⁻¹)) * c₂ b) =
      conj (∑ b, ∑ a, conj (c₂ b) * jordanForward w P ((x b)⁻¹ * x a) * c₁ a) := by
    rw [map_sum]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hinv : ((x b)⁻¹ * x a)⁻¹ = (x a)⁻¹ * x b := by group
    rw [hinv, map_mul, map_mul, conj_conj]
    ring
  rw [hsplit, hanti, bilinear_jordanForward w P x c₁ c₂, bilinear_jordanForward w P x c₂ c₁]

theorem hermQuad_gram_jordanPairKernel (w : ℂ) (P : ℂ[X]) {ι : Type*} [Fintype ι]
    (x : ι → posUnits) (c : ι → ℂ) :
    hermQuad (HeckeKreinToeplitz.gram (jordanPairKernel w P) x) c =
      2 * (∑ r ∈ Finset.range (P.natDegree + 1), P.coeff r *
        ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (expPolyEval (conj w) (r - j) x c) * expPolyEval w j x c).re := by
  rw [hermQuad_gram, bilinear_jordanPairKernel, Complex.add_re, Complex.conj_re]
  ring

/-- **Upper bound of the Jordan signature formula**: a sum of Jordan pair kernels `J_{u_i, P_i}` has
negative index at most `∑_i (deg P_i + 1)`. -/
theorem negIndex_sum_jordanPairKernel_le {κ : ℕ} (u : Fin κ → ℂ) (P : Fin κ → ℂ[X]) :
    negIndex (fun v => ∑ i : Fin κ, jordanPairKernel (u i) (P i) v) ≤
      ((∑ i : Fin κ, ((P i).natDegree + 1) : ℕ) : ℕ∞) := by
  rw [negIndex_le_iff]
  intro n x
  let Slot := Σ i : Fin κ, Fin ((P i).natDegree + 1)
  have hcard : Fintype.card Slot = ∑ i : Fin κ, ((P i).natDegree + 1) := by
    simp [Slot]
  refine Nat.cast_le.mpr (hcard ▸ ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _
    (fun q : Slot => expPolyEval (u q.1) (q.2 : ℕ) x) fun c hc => ?_)
  rw [hermQuad_gram_sum]
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin κ)),
      hermQuad (gram (jordanPairKernel (u i) (P i)) x) c = 0 := by
    intro i _
    rw [hermQuad_gram_jordanPairKernel]
    have hs : (∑ r ∈ Finset.range ((P i).natDegree + 1), (P i).coeff r *
        ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (expPolyEval (conj (u i)) (r - j) x c) * expPolyEval (u i) j x c) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      have hr' : r < (P i).natDegree + 1 := Finset.mem_range.mp hr
      have hj0 : (∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (expPolyEval (conj (u i)) (r - j) x c) * expPolyEval (u i) j x c) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj' : j < (P i).natDegree + 1 :=
          lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hr'
        have hcj : expPolyEval (u i) j x c = 0 := hc ⟨i, ⟨j, hj'⟩⟩
        rw [hcj, mul_zero]
      rw [hj0, mul_zero]
    rw [hs, Complex.zero_re, mul_zero]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]

/-! ### Separating rational slope and confluent exponential-polynomial Vandermonde -/

/-- A positive rational slope `(n + 2)/(n + 1)` with arbitrarily small positive logarithm separates
any finite injective family of complex frequencies under `w ↦ e^{−i w log u₀}`. -/
theorem exists_posUnits_exp_injective {r : ℕ} (z : Fin r → ℂ) (hz : Function.Injective z) :
    ∃ u₀ : posUnits, 0 < logPos u₀ ∧
      Function.Injective (fun s : Fin r => cexp (-I * z s * (logPos u₀ : ℂ))) := by
  classical
  set M : ℝ := ∑ a : Fin r, ∑ b : Fin r, ‖z a - z b‖
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨n, hn⟩ := exists_nat_gt (M / Real.pi)
  let q : ℚ := ((n : ℚ) + 2) / ((n : ℚ) + 1)
  have hqpos : (0 : ℚ) < q := by positivity
  let u₀ : posUnits := ⟨Units.mk0 q hqpos.ne', hqpos⟩
  have hqgt1 : (1 : ℝ) < ((q : ℚ) : ℝ) := by
    dsimp only [q]
    push_cast
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hqle : ((q : ℚ) : ℝ) ≤ 1 + 1 / ((n : ℝ) + 1) := by
    dsimp only [q]
    push_cast
    apply le_of_eq
    field_simp
    ring
  have hs0_pos : 0 < logPos u₀ := by
    dsimp only [logPos, u₀]
    rw [Units.val_mk0]
    exact Real.log_pos hqgt1
  have hs0_le : logPos u₀ ≤ 1 / ((n : ℝ) + 1) := by
    dsimp only [logPos, u₀]
    rw [Units.val_mk0]
    exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  refine ⟨u₀, hs0_pos, fun a b hab => ?_⟩
  by_contra hne
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hab
  have hdiff : -I * (z a - z b) * (logPos u₀ : ℂ) = (m : ℂ) * (2 * Real.pi * I) := by
    linear_combination hm
  have hnorm := congrArg norm hdiff
  simp only [norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs0_pos, Complex.norm_intCast, Complex.norm_ofNat, abs_of_pos Real.pi_pos] at hnorm
  have hle1 : ‖z a - z b‖ ≤ ∑ b' : Fin r, ‖z a - z b'‖ :=
    Finset.single_le_sum (f := fun b' : Fin r => ‖z a - z b'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ b)
  have hle2 : (∑ b' : Fin r, ‖z a - z b'‖) ≤ M :=
    Finset.single_le_sum (f := fun a' : Fin r => ∑ b' : Fin r, ‖z a' - z b'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have hleM : ‖z a - z b‖ ≤ M := hle1.trans hle2
  have hlt_pi : ‖z a - z b‖ * logPos u₀ < Real.pi := by
    have hn' : M < ((n : ℝ) + 1) * Real.pi := by
      have := (div_lt_iff₀ Real.pi_pos).mp hn
      linarith [Real.pi_pos]
    calc ‖z a - z b‖ * logPos u₀
        ≤ M * (1 / ((n : ℝ) + 1)) := mul_le_mul hleM hs0_le hs0_pos.le hM0
      _ = M / ((n : ℝ) + 1) := by ring
      _ < Real.pi := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  have hm0 : m = 0 := by
    by_contra hm_ne
    have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm_ne
    have : 2 * Real.pi ≤ |(m : ℝ)| * (2 * Real.pi) := by nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]
  rw [hm0] at hnorm
  simp only [Int.cast_zero, abs_zero, zero_mul] at hnorm
  have hza : z a - z b = 0 :=
    norm_eq_zero.mp (mul_eq_zero.mp hnorm |>.resolve_right hs0_pos.ne')
  exact hne (hz (sub_eq_zero.mp hza))

/-- Falling-factorial polynomial `X (X − 1) ⋯ (X − m + 1)`. -/
private def fallingPoly : ℕ → ℂ[X]
  | 0 => 1
  | m + 1 => (X - C (m : ℂ)) * fallingPoly m

private theorem fallingPoly_monic : ∀ m : ℕ, (fallingPoly m).Monic
  | 0 => monic_one
  | m + 1 => (monic_X_sub_C _).mul (fallingPoly_monic m)

private theorem fallingPoly_natDegree : ∀ m : ℕ, (fallingPoly m).natDegree = m
  | 0 => natDegree_one
  | m + 1 => by
      rw [fallingPoly, (monic_X_sub_C _).natDegree_mul (fallingPoly_monic m),
        natDegree_X_sub_C, fallingPoly_natDegree m]
      omega

/-- Exact identity relating iterated polynomial derivatives of `X^k` to `fallingPoly m(k) z^k`. -/
private theorem iterate_derivative_X_pow_eval_mul_pow (m k : ℕ) (z : ℂ) :
    ((derivative^[m]) ((X : ℂ[X]) ^ k)).eval z * z ^ m =
      (fallingPoly m).eval (k : ℂ) * z ^ k := by
  induction m generalizing z with
  | zero => simp [fallingPoly]
  | succ m ih =>
      set Q : ℂ[X] := (derivative^[m]) ((X : ℂ[X]) ^ k)
      have hpow_mul : ∀ n : ℕ, ∀ w : ℂ, ((n : ℂ) * w ^ (n - 1)) * w = (n : ℂ) * w ^ n := by
        intro n w
        cases n with
        | zero => simp
        | succ n' => simp [pow_succ]; ring
      have hdL : HasDerivAt (fun w : ℂ => Q.eval w * w ^ m)
          ((derivative Q).eval z * z ^ m + Q.eval z * ((m : ℂ) * z ^ (m - 1))) z :=
        (Q.hasDerivAt z).mul (hasDerivAt_pow m z)
      have hdR : HasDerivAt (fun w : ℂ => (fallingPoly m).eval (k : ℂ) * w ^ k)
          ((fallingPoly m).eval (k : ℂ) * ((k : ℂ) * z ^ (k - 1))) z :=
        (hasDerivAt_pow k z).const_mul _
      have heq_fun : (fun w : ℂ => Q.eval w * w ^ m) =
          (fun w : ℂ => (fallingPoly m).eval (k : ℂ) * w ^ k) := funext ih
      have hderiv_eq : (derivative Q).eval z * z ^ m + Q.eval z * ((m : ℂ) * z ^ (m - 1)) =
          (fallingPoly m).eval (k : ℂ) * ((k : ℂ) * z ^ (k - 1)) :=
        hdL.unique (heq_fun ▸ hdR)
      have hmulz := congrArg (· * z) hderiv_eq
      have h1 : (Q.eval z * ((m : ℂ) * z ^ (m - 1))) * z =
          (m : ℂ) * ((fallingPoly m).eval (k : ℂ) * z ^ k) := by
        calc (Q.eval z * ((m : ℂ) * z ^ (m - 1))) * z
            = Q.eval z * (((m : ℂ) * z ^ (m - 1)) * z) := by ring
          _ = Q.eval z * ((m : ℂ) * z ^ m) := by rw [hpow_mul]
          _ = (m : ℂ) * (Q.eval z * z ^ m) := by ring
          _ = (m : ℂ) * ((fallingPoly m).eval (k : ℂ) * z ^ k) := by rw [ih z]
      have h2 : ((fallingPoly m).eval (k : ℂ) * ((k : ℂ) * z ^ (k - 1))) * z =
          (k : ℂ) * ((fallingPoly m).eval (k : ℂ) * z ^ k) := by
        calc ((fallingPoly m).eval (k : ℂ) * ((k : ℂ) * z ^ (k - 1))) * z
            = (fallingPoly m).eval (k : ℂ) * (((k : ℂ) * z ^ (k - 1)) * z) := by ring
          _ = (fallingPoly m).eval (k : ℂ) * ((k : ℂ) * z ^ k) := by rw [hpow_mul]
          _ = (k : ℂ) * ((fallingPoly m).eval (k : ℂ) * z ^ k) := by ring
      rw [add_mul, h1, h2] at hmulz
      rw [Function.iterate_succ_apply', fallingPoly, eval_mul, eval_sub, eval_X, eval_C]
      change (derivative Q).eval z * z ^ (m + 1) = _
      rw [pow_succ]
      linear_combination hmulz

/-- The confluent exponential-polynomial Vandermonde matrix at `(lam, mult, s₀)`. -/
def expPolyJetMatrix {r : ℕ} (lam : Fin r → ℂ) (mult : Fin r → ℕ) (s₀ : ℝ) :
    Matrix (Fin (∑ s, mult s)) (Fin (∑ s, mult s)) ℂ :=
  fun p k =>
    ((k : ℂ) * (s₀ : ℂ)) ^ gammaJetSlotOrder mult p *
      (lam (gammaJetSlotNode mult p)) ^ (k : ℕ)

/-- **Invertibility of the confluent exponential-polynomial Vandermonde matrix.** -/
theorem det_expPolyJetMatrix_ne_zero {r : ℕ} {lam : Fin r → ℂ} (hlam : Function.Injective lam)
    (hne : ∀ s, lam s ≠ 0) (mult : Fin r → ℕ) {s₀ : ℝ} (hs₀ : s₀ ≠ 0) :
    (expPolyJetMatrix lam mult s₀).det ≠ 0 := by
  classical
  set N := ∑ s, mult s
  set V := confluentPolynomialJetMatrix lam mult (fun k : Fin N => (X : ℂ[X]) ^ (k : ℕ))
  let B : Matrix (Fin N) (Fin N) ℂ := fun p q =>
    if gammaJetSlotNode mult p = gammaJetSlotNode mult q then
      (lam (gammaJetSlotNode mult p))⁻¹ ^ gammaJetSlotOrder mult p *
        (fallingPoly (gammaJetSlotOrder mult p)).coeff (gammaJetSlotOrder mult q) *
        (s₀ : ℂ)⁻¹ ^ gammaJetSlotOrder mult q
    else 0
  have hVBW : V = B * expPolyJetMatrix lam mult s₀ := by
    ext p k
    simp only [V, confluentPolynomialJetMatrix, polynomialJetEvalMatrix, Matrix.mul_apply, B,
      expPolyJetMatrix]
    set s := gammaJetSlotNode mult p
    set m := gammaJetSlotOrder mult p
    have hz : lam s ≠ 0 := hne s
    have hid := iterate_derivative_X_pow_eval_mul_pow m (k : ℕ) (lam s)
    have hval : ((derivative^[m]) ((X : ℂ[X]) ^ (k : ℕ))).eval (lam s) =
        (lam s)⁻¹ ^ m * (fallingPoly m).eval (k : ℂ) * (lam s) ^ (k : ℕ) := by
      have hpow_ne : (lam s) ^ m ≠ 0 := pow_ne_zero _ hz
      apply mul_right_cancel₀ hpow_ne
      calc ((derivative^[m]) ((X : ℂ[X]) ^ (k : ℕ))).eval (lam s) * (lam s) ^ m
          = (fallingPoly m).eval (k : ℂ) * (lam s) ^ (k : ℕ) := hid
        _ = ((lam s)⁻¹ * lam s) ^ m * ((fallingPoly m).eval (k : ℂ) * (lam s) ^ (k : ℕ)) := by
            rw [inv_mul_cancel₀ hz, one_pow, one_mul]
        _ = (lam s)⁻¹ ^ m * (fallingPoly m).eval (k : ℂ) * (lam s) ^ (k : ℕ) * (lam s) ^ m := by
            rw [mul_pow]; ring
    rw [hval]
    have hm_lt : (fallingPoly m).natDegree < mult s := by
      rw [fallingPoly_natDegree]
      exact (gammaJetSlotOrderIso mult p).2.isLt
    have heval_sum : (fallingPoly m).eval (k : ℂ) =
        ∑ j : Fin (mult s), (fallingPoly m).coeff (j : ℕ) * (k : ℂ) ^ (j : ℕ) := by
      conv_lhs => rw [(fallingPoly m).as_sum_range' (mult s) hm_lt]
      rw [eval_finsetSum, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun j _ => Polynomial.eval_monomial
    rw [heval_sum, Finset.mul_sum, Finset.sum_mul]
    let emb : Fin (mult s) → Fin N := fun j => (gammaJetSlotOrderIso mult).symm (toLex ⟨s, j⟩)
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb))]
    · rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hemb : gammaJetSlotOrderIso mult (emb j) = toLex ⟨s, j⟩ :=
          (gammaJetSlotOrderIso mult).apply_symm_apply _
        have hnode : gammaJetSlotNode mult (emb j) = s := by
          dsimp [gammaJetSlotNode]
          rw [hemb]
          rfl
        have hord : gammaJetSlotOrder mult (emb j) = (j : ℕ) := by
          dsimp [gammaJetSlotOrder]
          rw [hemb]
          rfl
        have hnode' : s = gammaJetSlotNode mult (emb j) := hnode.symm
        rw [if_pos hnode', hnode, hord]
        have hs₀' : (s₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs₀
        rw [mul_pow]
        have hsc : (s₀ : ℂ)⁻¹ ^ (j : ℕ) * ((k : ℂ) ^ (j : ℕ) * (s₀ : ℂ) ^ (j : ℕ)) =
            (k : ℂ) ^ (j : ℕ) := by
          calc (s₀ : ℂ)⁻¹ ^ (j : ℕ) * ((k : ℂ) ^ (j : ℕ) * (s₀ : ℂ) ^ (j : ℕ))
              = ((s₀ : ℂ)⁻¹ * (s₀ : ℂ)) ^ (j : ℕ) * (k : ℂ) ^ (j : ℕ) := by rw [mul_pow]; ring
            _ = (k : ℂ) ^ (j : ℕ) := by rw [inv_mul_cancel₀ hs₀', one_pow, one_mul]
        calc (lam s)⁻¹ ^ m * ((fallingPoly m).coeff (j : ℕ) * (k : ℂ) ^ (j : ℕ)) *
              (lam s) ^ (k : ℕ)
            = (lam s)⁻¹ ^ m * (fallingPoly m).coeff (j : ℕ) *
                ((s₀ : ℂ)⁻¹ ^ (j : ℕ) * ((k : ℂ) ^ (j : ℕ) * (s₀ : ℂ) ^ (j : ℕ))) *
                (lam s) ^ (k : ℕ) := by rw [hsc]; ring
          _ = _ := by ring
      · intro j₁ _ j₂ _ heq
        have h1 := congrArg (fun x => ofLex (gammaJetSlotOrderIso mult x)) heq
        simp only [emb, OrderIso.apply_symm_apply, ofLex_toLex] at h1
        exact eq_of_heq (Sigma.mk.inj_iff.mp h1).2
    · intro q _ hq
      have hne_node : s ≠ gammaJetSlotNode mult q := by
        intro heq
        apply hq
        rcases hx : ofLex (gammaJetSlotOrderIso mult q) with ⟨s', j'⟩
        have hs' : s' = s := (congrArg Sigma.fst hx).symm.trans heq.symm
        subst hs'
        refine Finset.mem_image.mpr ⟨j', Finset.mem_univ _, ?_⟩
        simp only [emb, ← hx, toLex_ofLex, OrderIso.symm_apply_apply]
      rw [if_neg hne_node, zero_mul]
  have hVdet : V.det ≠ 0 := by
    rw [det_confluentPolynomialJetMatrix lam mult _ (fun k => natDegree_X_pow (k : ℕ))
      (fun k => monic_X_pow (k : ℕ))]
    refine mul_ne_zero ?_ ?_
    · refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun m _ => ?_
      exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    · refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      have hij : j ≠ i := (Finset.mem_Ioi.mp hj).ne'
      exact pow_ne_zero _ (sub_ne_zero.mpr (hlam.ne hij))
  intro hW0
  rw [hVBW, Matrix.det_mul, hW0, mul_zero] at hVdet
  exact hVdet rfl

/-! ### Lower bound and exact signature theorem -/

/-- **Lower bound of the Jordan signature formula**: for distinct lower-half-plane frequencies
`u_i` (`Im u_i < 0`) and nonzero polynomials `P_i`, `∑_i (deg P_i + 1) ≤ κ(∑_i J_{u_i, P_i})`. -/
theorem le_negIndex_sum_jordanPairKernel {κ : ℕ} {u : Fin κ → ℂ} (hu_inj : Function.Injective u)
    (hu_im : ∀ i, (u i).im < 0) {P : Fin κ → ℂ[X]} (hP : ∀ i, P i ≠ 0) :
    ((∑ i : Fin κ, ((P i).natDegree + 1) : ℕ) : ℕ∞) ≤
      negIndex (fun v => ∑ i : Fin κ, jordanPairKernel (u i) (P i) v) := by
  classical
  set K : posUnits → ℂ := fun v => ∑ i : Fin κ, jordanPairKernel (u i) (P i) v
  let freq : Fin (κ + κ) → ℂ := Sum.elim u (fun i => conj (u i)) ∘ finSumFinEquiv.symm
  have hfreq_inj : Function.Injective freq := by
    refine Function.Injective.comp ?_ finSumFinEquiv.symm.injective
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (hu_inj h)
    · exfalso
      have him := congrArg Complex.im h
      simp only [Sum.elim_inl, Sum.elim_inr, Complex.conj_im] at him
      linarith [hu_im i, hu_im j]
    · exfalso
      have him := congrArg Complex.im h
      simp only [Sum.elim_inl, Sum.elim_inr, Complex.conj_im] at him
      linarith [hu_im i, hu_im j]
    · dsimp only [Sum.elim_inr] at h
      exact congrArg Sum.inr (hu_inj ((starRingEnd ℂ).injective h))
  obtain ⟨u₀, hs₀_pos, hlam_inj⟩ := exists_posUnits_exp_injective freq hfreq_inj
  set s₀ : ℝ := logPos u₀
  set lam : Fin (κ + κ) → ℂ := fun s => cexp (-I * freq s * (s₀ : ℂ))
  have hlam_ne : ∀ s, lam s ≠ 0 := fun s => Complex.exp_ne_zero _
  let mult : Fin (κ + κ) → ℕ :=
    Sum.elim (fun i => (P i).natDegree + 1) (fun i => (P i).natDegree + 1) ∘ finSumFinEquiv.symm
  set N := ∑ s : Fin (κ + κ), mult s
  let x : Fin N → posUnits := fun k => u₀ ^ (k : ℕ)
  set W := expPolyJetMatrix lam mult s₀
  have hWdet : W.det ≠ 0 := det_expPolyJetMatrix_ne_zero hlam_inj hlam_ne mult hs₀_pos.ne'
  have hWW : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W (isUnit_iff_ne_zero.mpr hWdet)
  have hW_eval : ∀ (p : Fin N) (c : Fin N → ℂ),
      (W *ᵥ c) p =
        expPolyEval (freq (gammaJetSlotNode mult p)) (gammaJetSlotOrder mult p) x c := by
    intro p c
    simp only [W, expPolyJetMatrix, Matrix.mulVec, dotProduct, expPolyEval_apply, x, logPos_pow,
      lam]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [s₀]
    rw [← Complex.exp_nat_mul]
    push_cast
    rw [mul_pow]
    ring_nf
  let Slot := Σ i : Fin κ, Fin ((P i).natDegree + 1)
  have hcard : Fintype.card Slot = ∑ i : Fin κ, ((P i).natDegree + 1) := by simp [Slot]
  let antiCoeff (i : Fin κ) (l : ℕ) : ℂ :=
    (P i).coeff (P i).natDegree * (-1 : ℂ) ^ l * (((P i).natDegree).choose ((P i).natDegree - l) : ℂ)
  have hanti_ne : ∀ (i : Fin κ) (l : ℕ), l ≤ (P i).natDegree → antiCoeff i l ≠ 0 := by
    intro i l hl
    dsimp only [antiCoeff]
    have hlead : (P i).coeff (P i).natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (hP i)
    have hch : 0 < ((P i).natDegree).choose ((P i).natDegree - l) :=
      Nat.choose_pos (Nat.sub_le _ _)
    exact mul_ne_zero (mul_ne_zero hlead (pow_ne_zero _ (by norm_num)))
      (Nat.cast_ne_zero.mpr hch.ne')
  let Target : ℕ → Matrix (Fin N) Slot ℂ := fun n p q =>
    match hsum : finSumFinEquiv.symm (gammaJetSlotNode mult p) with
    | Sum.inl i =>
        if q.1 = i ∧ (q.2 : ℕ) = gammaJetSlotOrder mult p then
          (((n : ℝ) + 1 : ℝ) : ℂ) ^ gammaJetSlotOrder mult p
        else 0
    | Sum.inr i =>
        if q.1 = i ∧ (q.2 : ℕ) = (P i).natDegree - gammaJetSlotOrder mult p then
          -((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^ ((P i).natDegree - gammaJetSlotOrder mult p) *
            (antiCoeff i (gammaJetSlotOrder mult p) /
              (‖antiCoeff i (gammaJetSlotOrder mult p)‖ : ℂ))
        else 0
  let S : ℕ → Matrix (Fin N) Slot ℂ := fun n => W⁻¹ * Target n
  have hcol_eval : ∀ n (q : Slot) (s : Fin (κ + κ)) (j : ℕ) (hj : j < mult s),
      expPolyEval (freq s) j x (fun k => S n k q) =
        Target n ((gammaJetSlotOrderIso mult).symm (toLex ⟨s, ⟨j, hj⟩⟩)) q := by
    intro n q s j hj
    set p : Fin N := (gammaJetSlotOrderIso mult).symm (toLex ⟨s, ⟨j, hj⟩⟩)
    have hp : gammaJetSlotOrderIso mult p = toLex ⟨s, ⟨j, hj⟩⟩ :=
      (gammaJetSlotOrderIso mult).apply_symm_apply _
    have hnode : gammaJetSlotNode mult p = s := by
      dsimp [gammaJetSlotNode]; rw [hp]; rfl
    have hord : gammaJetSlotOrder mult p = j := by
      dsimp [gammaJetSlotOrder]; rw [hp]; rfl
    rw [← hnode, ← hord, ← hW_eval p (fun k => S n k q)]
    have hmul : (W *ᵥ fun k => S n k q) p = ((W * (W⁻¹ * Target n)) p q) := by
      simp [S, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hmul, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have heval_L : ∀ n (q : Slot) (i : Fin κ) (j : ℕ) (hj : j < (P i).natDegree + 1),
      expPolyEval (u i) j x (fun k => S n k q) =
        if q.1 = i ∧ (q.2 : ℕ) = j then (((n : ℝ) + 1 : ℝ) : ℂ) ^ j else 0 := by
    intro n q i j hj
    set s := finSumFinEquiv (Sum.inl i)
    have hms : mult s = (P i).natDegree + 1 := by
      dsimp only [mult, s, Function.comp_apply]
      rw [Equiv.symm_apply_apply]
      rfl
    have hfs : freq s = u i := by
      dsimp only [freq, s, Function.comp_apply]
      rw [Equiv.symm_apply_apply]
      rfl
    rw [← hfs, hcol_eval n q s j (hms ▸ hj)]
    set p := (gammaJetSlotOrderIso mult).symm (toLex ⟨s, ⟨j, hms ▸ hj⟩⟩)
    have hp : gammaJetSlotOrderIso mult p = toLex ⟨s, ⟨j, hms ▸ hj⟩⟩ :=
      (gammaJetSlotOrderIso mult).apply_symm_apply _
    have hnode : finSumFinEquiv.symm (gammaJetSlotNode mult p) = Sum.inl i := by
      have hp' : gammaJetSlotNode mult p = s := by dsimp [gammaJetSlotNode]; rw [hp]; rfl
      rw [hp']
      exact Equiv.symm_apply_apply finSumFinEquiv (Sum.inl i)
    have hord : gammaJetSlotOrder mult p = j := by
      dsimp [gammaJetSlotOrder]; rw [hp]; rfl
    dsimp only [Target]
    rw [hnode, hord]
  have heval_R : ∀ n (q : Slot) (i : Fin κ) (l : ℕ) (hl : l < (P i).natDegree + 1),
      expPolyEval (conj (u i)) l x (fun k => S n k q) =
        if q.1 = i ∧ (q.2 : ℕ) = (P i).natDegree - l then
          -((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^ ((P i).natDegree - l) *
            (antiCoeff i l / (‖antiCoeff i l‖ : ℂ))
        else 0 := by
    intro n q i l hl
    set s := finSumFinEquiv (Sum.inr i)
    have hms : mult s = (P i).natDegree + 1 := by
      dsimp only [mult, s, Function.comp_apply]
      rw [Equiv.symm_apply_apply]
      rfl
    have hfs : freq s = conj (u i) := by
      dsimp only [freq, s, Function.comp_apply]
      rw [Equiv.symm_apply_apply]
      rfl
    rw [← hfs, hcol_eval n q s l (hms ▸ hl)]
    set p := (gammaJetSlotOrderIso mult).symm (toLex ⟨s, ⟨l, hms ▸ hl⟩⟩)
    have hp : gammaJetSlotOrderIso mult p = toLex ⟨s, ⟨l, hms ▸ hl⟩⟩ :=
      (gammaJetSlotOrderIso mult).apply_symm_apply _
    have hnode : finSumFinEquiv.symm (gammaJetSlotNode mult p) = Sum.inr i := by
      have hp' : gammaJetSlotNode mult p = s := by dsimp [gammaJetSlotNode]; rw [hp]; rfl
      rw [hp']
      exact Equiv.symm_apply_apply finSumFinEquiv (Sum.inr i)
    have hord : gammaJetSlotOrder mult p = l := by
      dsimp [gammaJetSlotOrder]; rw [hp]; rfl
    dsimp only [Target]
    rw [hnode, hord]
  -- Evaluate the forward bilinear block on two columns `q₁, q₂`
  have hforward_col : ∀ n (i : Fin κ) (q₁ q₂ : Slot),
      (∑ r ∈ Finset.range ((P i).natDegree + 1), (P i).coeff r *
        ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (expPolyEval (conj (u i)) (r - j) x (fun k => S n k q₁)) *
          expPolyEval (u i) j x (fun k => S n k q₂)) =
        if h₁ : q₁.1 = i then
          if h₂ : q₂.1 = i then
            if (q₂.2 : ℕ) ≤ (q₁.2 : ℕ) then
              (let r := (P i).natDegree + (q₂.2 : ℕ) - (q₁.2 : ℕ);
               let l := (P i).natDegree - (q₁.2 : ℕ);
               -(P i).coeff r * (r.choose (q₂.2 : ℕ) : ℂ) * (-1 : ℂ) ^ l *
                 (conj (antiCoeff i l) / (‖antiCoeff i l‖ : ℂ)) *
                 ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^ ((q₁.2 : ℕ) - (q₂.2 : ℕ)))
            else 0
          else 0
        else 0 := by
    intro n i q₁ q₂
    set d := (P i).natDegree
    have hterm : ∀ r ∈ Finset.range (d + 1),
        (P i).coeff r * (∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
          conj (expPolyEval (conj (u i)) (r - j) x (fun k => S n k q₁)) *
          expPolyEval (u i) j x (fun k => S n k q₂)) =
        if q₁.1 = i ∧ q₂.1 = i ∧ (q₂.2 : ℕ) ≤ r ∧ d - (r - (q₂.2 : ℕ)) = (q₁.2 : ℕ) then
          (let l := r - (q₂.2 : ℕ);
           -(P i).coeff r * (r.choose (q₂.2 : ℕ) : ℂ) * (-1 : ℂ) ^ l *
             (conj (antiCoeff i l) / (‖antiCoeff i l‖ : ℂ)) *
             ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^ ((q₁.2 : ℕ) - (q₂.2 : ℕ)))
        else 0 := by
      intro r hr
      have hrd : r < d + 1 := Finset.mem_range.mp hr
      by_cases hcond : q₁.1 = i ∧ q₂.1 = i ∧ (q₂.2 : ℕ) ≤ r ∧ d - (r - (q₂.2 : ℕ)) = (q₁.2 : ℕ)
      · rw [if_pos hcond]
        obtain ⟨hq₁, hq₂, hjr, hdl⟩ := hcond
        rw [Finset.sum_eq_single (q₂.2 : ℕ)]
        · have hjd : (q₂.2 : ℕ) < d + 1 := lt_of_le_of_lt hjr hrd
          have hld : r - (q₂.2 : ℕ) < d + 1 := by omega
          rw [heval_L n q₂ i (q₂.2 : ℕ) hjd, heval_R n q₁ i (r - (q₂.2 : ℕ)) hld,
            if_pos ⟨hq₁, hdl.symm⟩, if_pos ⟨hq₂, rfl⟩]
          have hle_j : (q₂.2 : ℕ) ≤ (q₁.2 : ℕ) := by
            have h1 : (q₁.2 : ℕ) < d + 1 := hq₁ ▸ q₁.2.isLt
            omega
          have hpow : ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^ (q₁.2 : ℕ) *
              (((n : ℝ) + 1 : ℝ) : ℂ) ^ (q₂.2 : ℕ) =
              ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^ ((q₁.2 : ℕ) - (q₂.2 : ℕ)) := by
            have hpos : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
              exact_mod_cast (by positivity : (0 : ℝ) < (n : ℝ) + 1).ne'
            have hinv_c : ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ)⁻¹ := by
              push_cast; rfl
            rw [hinv_c]
            have hsplit : (q₁.2 : ℕ) = ((q₁.2 : ℕ) - (q₂.2 : ℕ)) + (q₂.2 : ℕ) := by omega
            nth_rw 1 [hsplit]
            rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hpos, one_pow, mul_one]
          rw [hdl]
          simp only [map_neg, map_mul, map_pow, map_div₀, Complex.conj_ofReal]
          linear_combination -(P i).coeff r * (r.choose (q₂.2 : ℕ) : ℂ) *
            (-1 : ℂ) ^ (r - (q₂.2 : ℕ)) *
            (conj (antiCoeff i (r - (q₂.2 : ℕ))) / (‖antiCoeff i (r - (q₂.2 : ℕ))‖ : ℂ)) * hpow
        · intro j hj hjne
          have hjd : j < d + 1 := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hrd
          rw [heval_L n q₂ i j hjd, if_neg (fun h => hjne h.2.symm), mul_zero]
        · intro hj
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hjr)) hj
      · rw [if_neg hcond]
        have hs0 : (∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
            conj (expPolyEval (conj (u i)) (r - j) x (fun k => S n k q₁)) *
            expPolyEval (u i) j x (fun k => S n k q₂)) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hjd : j < d + 1 := lt_of_le_of_lt hjr hrd
          have hld : r - j < d + 1 := by omega
          rw [heval_L n q₂ i j hjd, heval_R n q₁ i (r - j) hld]
          by_cases hL : q₂.1 = i ∧ (q₂.2 : ℕ) = j
          · by_cases hR : q₁.1 = i ∧ (q₁.2 : ℕ) = d - (r - j)
            · exfalso
              apply hcond
              refine ⟨hR.1, hL.1, hL.2 ▸ hjr, ?_⟩
              rw [hL.2, hR.2]
            · rw [if_neg hR, map_zero, mul_zero, zero_mul]
          · rw [if_neg hL, mul_zero]
        rw [hs0, mul_zero]
    rw [Finset.sum_congr rfl hterm]
    by_cases h₁ : q₁.1 = i
    · rw [dif_pos h₁]
      by_cases h₂ : q₂.1 = i
      · rw [dif_pos h₂]
        have hq₁lt : (q₁.2 : ℕ) < d + 1 := h₁ ▸ q₁.2.isLt
        have hq₂lt : (q₂.2 : ℕ) < d + 1 := h₂ ▸ q₂.2.isLt
        by_cases hle : (q₂.2 : ℕ) ≤ (q₁.2 : ℕ)
        · rw [if_pos hle]
          set r₀ := d + (q₂.2 : ℕ) - (q₁.2 : ℕ)
          rw [Finset.sum_eq_single r₀]
          · have hr₀_cond : q₁.1 = i ∧ q₂.1 = i ∧ (q₂.2 : ℕ) ≤ r₀ ∧
                d - (r₀ - (q₂.2 : ℕ)) = (q₁.2 : ℕ) := by
              refine ⟨h₁, h₂, by omega, by omega⟩
            rw [if_pos hr₀_cond]
            have hl_eq : r₀ - (q₂.2 : ℕ) = d - (q₁.2 : ℕ) := by omega
            simp only [hl_eq]
          · intro r hr hrne
            have hrd : r < d + 1 := Finset.mem_range.mp hr
            rw [if_neg]
            rintro ⟨-, -, hjr, hdl⟩
            apply hrne
            omega
          · intro hr₀
            exact absurd (Finset.mem_range.mpr (by omega)) hr₀
        · rw [if_neg hle]
          refine Finset.sum_eq_zero fun r hr => ?_
          have hrd : r < d + 1 := Finset.mem_range.mp hr
          rw [if_neg]
          rintro ⟨-, -, hjr, hdl⟩
          omega
      · rw [dif_neg h₂]
        refine Finset.sum_eq_zero fun r _ => ?_
        rw [if_neg (fun h => h₂ h.2.1)]
    · rw [dif_neg h₁]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg (fun h => h₁ h.1)]
  -- Compressed Hermitian matrices `H n = (S n)ᴴ * gram K x * (S n)` converge to a negative diagonal
  let H : ℕ → Matrix Slot Slot ℂ := fun n => (S n)ᴴ * HeckeKreinToeplitz.gram K x * S n
  let diagVal : Slot → ℝ := fun q =>
    -2 * ‖antiCoeff q.1 ((P q.1).natDegree - (q.2 : ℕ))‖
  let H₀ : Matrix Slot Slot ℂ := Matrix.diagonal fun q => ((diagVal q : ℝ) : ℂ)
  have hdiag_neg : ∀ q : Slot, diagVal q < 0 := by
    intro q
    have hl : (P q.1).natDegree - (q.2 : ℕ) ≤ (P q.1).natDegree := Nat.sub_le _ _
    have hpos : 0 < ‖antiCoeff q.1 ((P q.1).natDegree - (q.2 : ℕ))‖ :=
      norm_pos_iff.mpr (hanti_ne q.1 _ hl)
    dsimp only [diagVal]
    linarith
  have hH_entry : ∀ n (q₁ q₂ : Slot),
      H n q₁ q₂ = ∑ i : Fin κ,
        ((∑ r ∈ Finset.range ((P i).natDegree + 1), (P i).coeff r *
            ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
              conj (expPolyEval (conj (u i)) (r - j) x (fun k => S n k q₁)) *
              expPolyEval (u i) j x (fun k => S n k q₂)) +
         conj (∑ r ∈ Finset.range ((P i).natDegree + 1), (P i).coeff r *
            ∑ j ∈ Finset.range (r + 1), (r.choose j : ℂ) * (-1 : ℂ) ^ (r - j) *
              conj (expPolyEval (conj (u i)) (r - j) x (fun k => S n k q₂)) *
              expPolyEval (u i) j x (fun k => S n k q₁))) := by
    intro n q₁ q₂
    have heq : H n q₁ q₂ =
        ∑ a : Fin N, ∑ b : Fin N, conj (S n a q₁) * K ((x a)⁻¹ * x b) * S n b q₂ := by
      simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, HeckeKreinToeplitz.gram,
        Complex.star_def, Finset.sum_mul]
      rw [Finset.sum_comm]
    have hswap : (∑ a : Fin N, ∑ b : Fin N, conj (S n a q₁) * K ((x a)⁻¹ * x b) * S n b q₂) =
        ∑ i : Fin κ, ∑ a : Fin N, ∑ b : Fin N,
          conj (S n a q₁) * jordanPairKernel (u i) (P i) ((x a)⁻¹ * x b) * S n b q₂ := by
      calc (∑ a : Fin N, ∑ b : Fin N, conj (S n a q₁) * K ((x a)⁻¹ * x b) * S n b q₂)
          = ∑ a : Fin N, ∑ b : Fin N, ∑ i : Fin κ,
              conj (S n a q₁) * jordanPairKernel (u i) (P i) ((x a)⁻¹ * x b) * S n b q₂ := by
            simp only [K, Finset.mul_sum, Finset.sum_mul]
        _ = ∑ a : Fin N, ∑ i : Fin κ, ∑ b : Fin N,
              conj (S n a q₁) * jordanPairKernel (u i) (P i) ((x a)⁻¹ * x b) * S n b q₂ :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ i : Fin κ, ∑ a : Fin N, ∑ b : Fin N,
              conj (S n a q₁) * jordanPairKernel (u i) (P i) ((x a)⁻¹ * x b) * S n b q₂ :=
            Finset.sum_comm
    rw [heq, hswap]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact bilinear_jordanPairKernel (u i) (P i) x (fun k => S n k q₁) (fun k => S n k q₂)
  have hconv : ∀ q₁ q₂ : Slot, Tendsto (fun n => H n q₁ q₂) atTop (𝓝 (H₀ q₁ q₂)) := by
    intro q₁ q₂
    simp_rw [hH_entry, hforward_col]
    by_cases hq : q₁ = q₂
    · subst hq
      rcases q₁ with ⟨i₀, j₀⟩
      have hconst : ∀ n, (∑ i : Fin κ,
          ((if h₁ : (⟨i₀, j₀⟩ : Slot).1 = i then
              if h₂ : (⟨i₀, j₀⟩ : Slot).1 = i then
                if ((⟨i₀, j₀⟩ : Slot).2 : ℕ) ≤ ((⟨i₀, j₀⟩ : Slot).2 : ℕ) then
                  (let r := (P i).natDegree + ((⟨i₀, j₀⟩ : Slot).2 : ℕ) -
                      ((⟨i₀, j₀⟩ : Slot).2 : ℕ);
                   let l := (P i).natDegree - ((⟨i₀, j₀⟩ : Slot).2 : ℕ);
                   -(P i).coeff r * (r.choose ((⟨i₀, j₀⟩ : Slot).2 : ℕ) : ℂ) * (-1 : ℂ) ^ l *
                     (conj (antiCoeff i l) / (‖antiCoeff i l‖ : ℂ)) *
                     ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^
                       (((⟨i₀, j₀⟩ : Slot).2 : ℕ) - ((⟨i₀, j₀⟩ : Slot).2 : ℕ)))
                else 0
              else 0
            else 0) +
           conj (if h₁ : (⟨i₀, j₀⟩ : Slot).1 = i then
              if h₂ : (⟨i₀, j₀⟩ : Slot).1 = i then
                if ((⟨i₀, j₀⟩ : Slot).2 : ℕ) ≤ ((⟨i₀, j₀⟩ : Slot).2 : ℕ) then
                  (let r := (P i).natDegree + ((⟨i₀, j₀⟩ : Slot).2 : ℕ) -
                      ((⟨i₀, j₀⟩ : Slot).2 : ℕ);
                   let l := (P i).natDegree - ((⟨i₀, j₀⟩ : Slot).2 : ℕ);
                   -(P i).coeff r * (r.choose ((⟨i₀, j₀⟩ : Slot).2 : ℕ) : ℂ) * (-1 : ℂ) ^ l *
                     (conj (antiCoeff i l) / (‖antiCoeff i l‖ : ℂ)) *
                     ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^
                       (((⟨i₀, j₀⟩ : Slot).2 : ℕ) - ((⟨i₀, j₀⟩ : Slot).2 : ℕ)))
                else 0
              else 0
            else 0))) = H₀ ⟨i₀, j₀⟩ ⟨i₀, j₀⟩ := by
        intro n
        rw [Finset.sum_eq_single i₀]
        · dsimp only
          simp only [↓reduceDIte, le_rfl, ↓reduceIte, Nat.add_sub_cancel, Nat.sub_self, pow_zero,
            mul_one, H₀, Matrix.diagonal_apply_eq, diagVal]
          set l := (P i₀).natDegree - (j₀ : ℕ)
          have hsub : (P i₀).natDegree - l = (j₀ : ℕ) := by
            have := j₀.isLt; omega
          have hac : -(P i₀).coeff (P i₀).natDegree * (((P i₀).natDegree).choose (j₀ : ℕ) : ℂ) *
              (-1 : ℂ) ^ l = -antiCoeff i₀ l := by
            dsimp only [antiCoeff]
            rw [hsub]
            ring
          rw [hac]
          have hne_ac : (‖antiCoeff i₀ l‖ : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hanti_ne i₀ l (Nat.sub_le _ _)))
          have hnorm_sq : antiCoeff i₀ l * conj (antiCoeff i₀ l) =
              ((‖antiCoeff i₀ l‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          have hval : -antiCoeff i₀ l * (conj (antiCoeff i₀ l) / (‖antiCoeff i₀ l‖ : ℂ)) =
              ((-‖antiCoeff i₀ l‖ : ℝ) : ℂ) := by
            calc -antiCoeff i₀ l * (conj (antiCoeff i₀ l) / (‖antiCoeff i₀ l‖ : ℂ))
                = -(antiCoeff i₀ l * conj (antiCoeff i₀ l)) / (‖antiCoeff i₀ l‖ : ℂ) := by ring
              _ = -((‖antiCoeff i₀ l‖ ^ 2 : ℝ) : ℂ) / (‖antiCoeff i₀ l‖ : ℂ) := by rw [hnorm_sq]
              _ = ((-‖antiCoeff i₀ l‖ : ℝ) : ℂ) := by
                  push_cast
                  field_simp
          rw [hval, Complex.conj_ofReal]
          push_cast
          ring
        · intro i _ hi
          simp [dif_neg (Ne.symm hi)]
        · intro hi
          exact absurd (Finset.mem_univ _) hi
      simp_rw [hconst]
      exact tendsto_const_nhds
    · have hH₀_off : H₀ q₁ q₂ = 0 := Matrix.diagonal_apply_ne _ hq
      rw [hH₀_off]
      have hinv0 : Tendsto (fun n : ℕ => ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
        have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
        simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hr
      have hpow0 : ∀ m : ℕ, 1 ≤ m →
          Tendsto (fun n : ℕ => ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^ m) atTop (𝓝 0) := by
        intro m hm
        obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        simpa [zero_pow (Nat.succ_ne_zero m')] using hinv0.pow (m' + 1)
      have hsum0 := tendsto_finsetSum (Finset.univ : Finset (Fin κ)) fun i _ => by
        show Tendsto (fun n : ℕ =>
          (if h₁ : q₁.1 = i then
            if h₂ : q₂.1 = i then
              if (q₂.2 : ℕ) ≤ (q₁.2 : ℕ) then
                (let r := (P i).natDegree + (q₂.2 : ℕ) - (q₁.2 : ℕ);
                 let l := (P i).natDegree - (q₁.2 : ℕ);
                 -(P i).coeff r * (r.choose (q₂.2 : ℕ) : ℂ) * (-1 : ℂ) ^ l *
                   (conj (antiCoeff i l) / (‖antiCoeff i l‖ : ℂ)) *
                   ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^ ((q₁.2 : ℕ) - (q₂.2 : ℕ)))
              else 0
            else 0
          else 0) +
          conj (if h₁ : q₂.1 = i then
            if h₂ : q₁.1 = i then
              if (q₁.2 : ℕ) ≤ (q₂.2 : ℕ) then
                (let r := (P i).natDegree + (q₁.2 : ℕ) - (q₂.2 : ℕ);
                 let l := (P i).natDegree - (q₂.2 : ℕ);
                 -(P i).coeff r * (r.choose (q₁.2 : ℕ) : ℂ) * (-1 : ℂ) ^ l *
                   (conj (antiCoeff i l) / (‖antiCoeff i l‖ : ℂ)) *
                   ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ^ ((q₂.2 : ℕ) - (q₁.2 : ℕ)))
              else 0
            else 0
          else 0)) atTop (𝓝 0)
        by_cases h₁ : q₁.1 = i
        · by_cases h₂ : q₂.1 = i
          · have hj_ne : (q₁.2 : ℕ) ≠ (q₂.2 : ℕ) := by
              intro heq
              apply hq
              rcases q₁ with ⟨i₁, j₁⟩
              rcases q₂ with ⟨i₂, j₂⟩
              dsimp only at h₁ h₂ heq
              subst h₁; subst h₂
              exact Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq (Fin.ext heq)⟩
            simp only [dif_pos h₁, dif_pos h₂]
            rcases lt_or_gt_of_ne hj_ne with hlt | hgt
            · have hle1 : ¬ (q₂.2 : ℕ) ≤ (q₁.2 : ℕ) := not_le.mpr hlt
              have hle2 : (q₁.2 : ℕ) ≤ (q₂.2 : ℕ) := hlt.le
              simp only [if_neg hle1, if_pos hle2, zero_add]
              have hm1 : 1 ≤ (q₂.2 : ℕ) - (q₁.2 : ℕ) := by omega
              have ht := (hpow0 _ hm1).const_mul
                (-(P i).coeff ((P i).natDegree + (q₁.2 : ℕ) - (q₂.2 : ℕ)) *
                  (((P i).natDegree + (q₁.2 : ℕ) - (q₂.2 : ℕ)).choose (q₁.2 : ℕ) : ℂ) *
                  (-1 : ℂ) ^ ((P i).natDegree - (q₂.2 : ℕ)) *
                  (conj (antiCoeff i ((P i).natDegree - (q₂.2 : ℕ))) /
                    (‖antiCoeff i ((P i).natDegree - (q₂.2 : ℕ))‖ : ℂ)))
              rw [mul_zero] at ht
              simpa [Function.comp_def, mul_assoc] using (Complex.continuous_conj.tendsto 0).comp ht
            · have hle1 : (q₂.2 : ℕ) ≤ (q₁.2 : ℕ) := hgt.le
              have hle2 : ¬ (q₁.2 : ℕ) ≤ (q₂.2 : ℕ) := not_le.mpr hgt
              simp only [if_pos hle1, if_neg hle2, map_zero, add_zero]
              have hm1 : 1 ≤ (q₁.2 : ℕ) - (q₂.2 : ℕ) := by omega
              have ht := (hpow0 _ hm1).const_mul
                (-(P i).coeff ((P i).natDegree + (q₂.2 : ℕ) - (q₁.2 : ℕ)) *
                  (((P i).natDegree + (q₂.2 : ℕ) - (q₁.2 : ℕ)).choose (q₂.2 : ℕ) : ℂ) *
                  (-1 : ℂ) ^ ((P i).natDegree - (q₁.2 : ℕ)) *
                  (conj (antiCoeff i ((P i).natDegree - (q₁.2 : ℕ))) /
                    (‖antiCoeff i ((P i).natDegree - (q₁.2 : ℕ))‖ : ℂ)))
              simpa [mul_assoc] using ht
          · simp [dif_pos h₁, dif_neg h₂]
        · simp [dif_neg h₁]
      simpa using hsum0
  have hH₀_herm : H₀.IsHermitian := by
    ext q₁ q₂
    by_cases h : q₁ = q₂
    · subst h; simp [H₀]
    · simp [H₀, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  have hH₀_idx : Fintype.card Slot ≤ hermNegIndex H₀ := by
    refine card_le_hermNegIndex_of_forall_neg H₀ LinearMap.id fun a ha => ?_
    rw [LinearMap.id_apply]
    have hquad : hermQuad H₀ a = ∑ q : Slot, diagVal q * ‖a q‖ ^ 2 := by
      simp only [hermQuad, H₀, Matrix.mulVec_diagonal, dotProduct, Complex.re_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have : star (a q) * (((diagVal q : ℝ) : ℂ) * a q) =
          ((diagVal q * ‖a q‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, show conj (a q) * (((diagVal q : ℝ) : ℂ) * a q) =
          ((diagVal q : ℝ) : ℂ) * (a q * conj (a q)) by ring, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
        push_cast; ring
      rw [Pi.star_apply, this, Complex.ofReal_re]
    rw [hquad]
    obtain ⟨q₀, hq₀⟩ := Function.ne_iff.mp ha
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q₀)]
    refine add_lt_of_lt_of_nonpos
      (mul_neg_of_neg_of_pos (hdiag_neg q₀) (pow_pos (norm_pos_iff.mpr hq₀) 2))
      (Finset.sum_nonpos fun q _ => mul_nonpos_of_nonpos_of_nonneg (hdiag_neg q).le (sq_nonneg _))
  obtain ⟨n, hn⟩ := (eventually_le_hermNegIndex hH₀_herm hconv).exists
  have hcomp : hermNegIndex (H n) ≤ hermNegIndex (HeckeKreinToeplitz.gram K x) :=
    hermNegIndex_le_of_hermQuad_eq _ _ (Matrix.mulVecLin (S n)) fun a => by
      rw [Matrix.mulVecLin_apply, ← HTGeometry.hermQuad_rect_conjugate]
  have hfin : ∑ i : Fin κ, ((P i).natDegree + 1) ≤ hermNegIndex (HeckeKreinToeplitz.gram K x) :=
    (hcard ▸ hH₀_idx).trans (hn.trans hcomp)
  exact (Nat.cast_le.mpr hfin).trans (hermNegIndex_gram_le_negIndex K x)

/-- **Exact signature theorem for Jordan pair kernels**: for distinct lower-half-plane frequencies
`u_i` (`Im u_i < 0`) and nonzero polynomials `P_i`,
`κ(∑_i J_{u_i, P_i}) = ∑_i (deg P_i + 1)`. -/
theorem negIndex_sum_jordanPairKernel_eq {κ : ℕ} {u : Fin κ → ℂ} (hu_inj : Function.Injective u)
    (hu_im : ∀ i, (u i).im < 0) {P : Fin κ → ℂ[X]} (hP : ∀ i, P i ≠ 0) :
    negIndex (fun v => ∑ i : Fin κ, jordanPairKernel (u i) (P i) v) =
      ((∑ i : Fin κ, ((P i).natDegree + 1) : ℕ) : ℕ∞) :=
  le_antisymm (negIndex_sum_jordanPairKernel_le u P)
    (le_negIndex_sum_jordanPairKernel hu_inj hu_im hP)

/-- Finset version of `negIndex_sum_jordanPairKernel_eq`. -/
theorem negIndex_finset_sum_jordanPairKernel_eq {S : Finset ℂ} (hS_im : ∀ u ∈ S, u.im < 0)
    {P : ℂ → ℂ[X]} (hP : ∀ u ∈ S, P u ≠ 0) :
    negIndex (fun v => ∑ u ∈ S, jordanPairKernel u (P u) v) =
      ((∑ u ∈ S, ((P u).natDegree + 1) : ℕ) : ℕ∞) := by
  classical
  let e : Fin S.card ≃ S := S.equivFin.symm
  have hinj : Function.Injective (fun i : Fin S.card => (e i : ℂ)) :=
    fun i j h => e.injective (Subtype.ext h)
  have heq : (fun v => ∑ u ∈ S, jordanPairKernel u (P u) v) =
      (fun v => ∑ i : Fin S.card, jordanPairKernel (e i : ℂ) (P (e i : ℂ)) v) := by
    funext v
    rw [← Finset.sum_coe_sort S]
    exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  have hdeg : (∑ u ∈ S, ((P u).natDegree + 1)) =
      ∑ i : Fin S.card, ((P (e i : ℂ)).natDegree + 1) := by
    rw [← Finset.sum_coe_sort S]
    exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  rw [heq, hdeg]
  exact negIndex_sum_jordanPairKernel_eq hinj (fun i => hS_im _ (e i).2)
    (fun i => hP _ (e i).2)

/-- **Archimedean gluing of strip Jordan pair kernels**: when every `u ∈ S` satisfies
`-1/2 < Im u < 0` and `P u ≠ 0`, gluing `∑_{u ∈ S} J_{u, P_u}` to `−c|b|` (`c > 0`) has negative
index `∑_{u ∈ S} (deg P_u + 1) + 1`. -/
theorem negIndex_archGlue_finset_sum_jordanPairKernel_eq {S : Finset ℂ}
    (hS_neg : ∀ u ∈ S, u.im < 0) (hS_strip : ∀ u ∈ S, |(u).im| < 1 / 2)
    {P : ℂ → ℂ[X]} (hP : ∀ u ∈ S, P u ≠ 0) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue (fun v => ∑ u ∈ S, jordanPairKernel u (P u) v) c) =
      ((∑ u ∈ S, ((P u).natDegree + 1) + 1 : ℕ) : ℕ∞) := by
  rw [negIndex_archGlue_eq_of_subBoost
    (isHermKernel_sum_jordanPairKernel S (fun u => u) P) hc (fun N => twoPos ^ N)
    tendsto_twoPos_pow_rpow (sum_jordanPairKernel_subBoost S hS_strip P),
    negIndex_finset_sum_jordanPairKernel_eq hS_neg hP]
  push_cast
  rfl

end GaloisForLFunctions.AdelicKreinGeometry
