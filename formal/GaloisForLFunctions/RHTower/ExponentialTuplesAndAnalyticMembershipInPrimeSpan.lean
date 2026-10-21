import GaloisForLFunctions.RHTower.HardyDiscTuplesAndJointPechersky
import GaloisForLFunctions.RHTower.AnalyticOnLargerDiscLiesInHardyDisc
import GaloisForLFunctions.HTGeometry.HardyDiskMultiplier
import GaloisForLFunctions.HTGeometry.HardyDiskCyclic

/-!
# Exponential tuples, and which tuples lie in the closed span of the prime tuples

For real `ξ` the *exponential tuple* `E_ξ = (expVector (z i) (ρ i) ξ)_i` consists of the
Hardy-space elements of the functions `q ↦ e^{−(z i + ρ i q) ξ}` on the discs; the prime tuple
`u_p` is `E_{log p}`.  Its pairing with a tuple `e` is `F_e(ξ)` (`inner_expTuple`), so a tuple
orthogonal to all prime tuples — which has `F_e ≡ 0` by the divergence lemma — is orthogonal to
every `E_ξ`.  Hence **every exponential tuple lies in `primeSpan`** (`expTuple_mem_primeSpan`),
and so does everything that is approximated by their linear combinations.

Two approximation steps follow.

* Scaled `k`-th finite differences of `ξ ↦ e^{c₀ ξ} E_ξ` at `ξ = 0` converge to the monomial tuple
  of `q ↦ (z i + ρ i q − c₀)^k`, uniformly on circles of radius `R > 1` in the disc coordinate
  (`norm_expDiffQuot_pow_sub_le`), hence in the Hardy norm (`monoTuple_mem_primeSpan`).
* Taylor polynomials of a function `F` analytic on a disc `ball c₀ R₀` containing all the closed
  discs `closedBall (z i) (ρ i R)`, `R > 1`, converge uniformly there, hence the tuple of `F` lies
  in `primeSpan` (`mem_primeSpan_of_differentiableOn_ball`,
  `exists_mem_primeSpan_of_differentiableOn_ball`).

The transfer from circle bounds to the Hardy norm is Cauchy's coefficient estimate
(`norm_le_of_hardyFun_eq_of_circle_bound`).  The module ends with the elementary fact that finitely
many closed discs of a half plane lie in a disc of that half plane
(`exists_ball_re_gt_of_forall_lt`, `exists_ball_re_lt_of_forall_lt`), which is how a target that is
analytic only on a half plane is fed to the Taylor step.
-/

open Complex Filter Topology Finset Metric
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

variable {ι : Type*} [Fintype ι]

/-! ## Linearity of the Hardy function -/

theorem hardyFun_sub_apply (a b : HardyDisk) {q : ℂ} (hq : ‖q‖ < 1) :
    hardyFun (a - b) q = hardyFun a q - hardyFun b q := by
  rw [← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq,
    ← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq,
    ← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq, inner_sub_right]

theorem hardyFun_sum_apply {κ : Type*} (s : Finset κ) (L : κ → HardyDisk) {q : ℂ}
    (hq : ‖q‖ < 1) :
    hardyFun (∑ j ∈ s, L j) q = ∑ j ∈ s, hardyFun (L j) q := by
  rw [← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq, inner_sum]
  exact sum_congr rfl fun j _ => GaloisForLFunctions.HTGeometry.inner_hardyKernel hq _

/-! ## Cauchy's estimate for the Hardy norm -/

/-- The constant `(1 − R^{−2})^{−1/2}` bounding the Hardy norm by a circle bound at radius `R`. -/
def hardyCircleConst (R : ℝ) : ℝ := Real.sqrt ((1 - R⁻¹ ^ 2)⁻¹)

theorem inv_sq_lt_one_of_one_lt {R : ℝ} (hR : 1 < R) : R⁻¹ ^ 2 < 1 := by
  have h1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have h0 : 0 ≤ R⁻¹ := by positivity
  nlinarith

theorem hardyCircleConst_pos {R : ℝ} (hR : 1 < R) : 0 < hardyCircleConst R := by
  unfold hardyCircleConst
  apply Real.sqrt_pos.mpr
  apply inv_pos.mpr
  linarith [inv_sq_lt_one_of_one_lt hR]

/-- **Cauchy's estimate for the Hardy norm.**  If `hardyFun L` agrees on the unit disc with a
function `g` analytic on `closedBall 0 R`, `R > 1`, with `‖g‖ ≤ B` on the circle `|q| = R`, then
`‖L‖ ≤ B · hardyCircleConst R`. -/
theorem norm_le_of_hardyFun_eq_of_circle_bound {L : HardyDisk} {g : ℂ → ℂ} {R B : ℝ}
    (hR : 1 < R) (hg : DifferentiableOn ℂ g (closedBall 0 R))
    (hB : ∀ θ : ℝ, ‖g (circleMap 0 R θ)‖ ≤ B)
    (hL : ∀ q : ℂ, ‖q‖ < 1 → hardyFun L q = g q) :
    ‖L‖ ≤ B * hardyCircleConst R := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hR0 : 0 < R := by linarith
  have hinv : R⁻¹ ^ 2 < 1 := inv_sq_lt_one_of_one_lt hR
  have hLeq : L = hardyDiskOfAnalytic g hR hB := by
    refine hardyDisk_ext fun q hq => ?_
    rw [hL q hq, hardyFun_hardyDiskOfAnalytic hR hg hB hq]
  have hgeom := summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ R⁻¹ ^ 2) hinv
  have hle : ∀ n, ‖(hardyDiskOfAnalytic g hR hB) n‖ ^ 2 ≤ B ^ 2 * (R⁻¹ ^ 2) ^ n := fun n => by
    rw [hardyDiskOfAnalytic_apply]
    calc ‖cauchyCoeff g R n‖ ^ 2 ≤ (B * R⁻¹ ^ n) ^ 2 := by
          gcongr
          exact norm_cauchyCoeff_le_of_circle_bound hR0 hB n
      _ = B ^ 2 * (R⁻¹ ^ 2) ^ n := by ring
  have hsum : Summable fun n => ‖(hardyDiskOfAnalytic g hR hB) n‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle (hgeom.mul_left _)
  have hsq : ‖L‖ ^ 2 ≤ B ^ 2 * (1 - R⁻¹ ^ 2)⁻¹ := by
    rw [hLeq, hardyDisk_norm_sq]
    calc ∑' n, ‖(hardyDiskOfAnalytic g hR hB) n‖ ^ 2
        ≤ ∑' n, B ^ 2 * (R⁻¹ ^ 2) ^ n := hsum.tsum_le_tsum hle (hgeom.mul_left _)
      _ = B ^ 2 * (1 - R⁻¹ ^ 2)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hinv]
  have hc0 : 0 ≤ (1 - R⁻¹ ^ 2)⁻¹ := inv_nonneg.mpr (by linarith)
  have hrhs : (B * hardyCircleConst R) ^ 2 = B ^ 2 * (1 - R⁻¹ ^ 2)⁻¹ := by
    rw [mul_pow, hardyCircleConst, Real.sq_sqrt hc0]
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hB0 (hardyCircleConst_pos hR).le)
    two_ne_zero, hrhs]
  exact hsq

/-! ## Approximation in a closed submodule through circle bounds -/

/-- A tuple lies in a closed submodule `V` once, for every `ε > 0`, some `s ∈ V` has `t − s`
represented on every disc by a function analytic on `closedBall 0 R`, `R > 1`, and bounded by `ε`
on the circle `|q| = R`. -/
theorem mem_of_forall_exists_circle_approx {V : Submodule ℂ (DiscTuple ι)}
    (hV : IsClosed (V : Set (DiscTuple ι))) {R : ℝ} (hR : 1 < R) {t : DiscTuple ι}
    (h : ∀ ε > 0, ∃ s ∈ V, ∃ g : ι → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (g i) (closedBall 0 R)) ∧
      (∀ i, ∀ θ : ℝ, ‖g i (circleMap 0 R θ)‖ ≤ ε) ∧
      ∀ i, ∀ q : ℂ, ‖q‖ < 1 → hardyFun ((t - s) i) q = g i q) :
    t ∈ V := by
  have hK := hardyCircleConst_pos hR
  set K := hardyCircleConst R with hKdef
  rw [← SetLike.mem_coe, ← hV.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  set c : ℝ := (Fintype.card ι : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  set ε' : ℝ := ε / ((c + 1) * (K + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨s, hs, g, hg, hgB, hgt⟩ := h ε' hε'pos
  refine ⟨s, hs, ?_⟩
  rw [dist_eq_norm]
  have hcomp : ∀ i, ‖(t - s) i‖ ≤ ε' * K := fun i =>
    norm_le_of_hardyFun_eq_of_circle_bound hR (hg i) (hgB i) (hgt i)
  have hsq : ‖t - s‖ ^ 2 ≤ c * (ε' * K) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ i, ‖(t - s) i‖ ^ 2 ≤ ∑ _i : ι, (ε' * K) ^ 2 :=
          sum_le_sum fun i _ => by gcongr; exact hcomp i
      _ = c * (ε' * K) ^ 2 := by rw [sum_const, card_univ, nsmul_eq_mul]
  have h1 : K ^ 2 * c < ((c + 1) * (K + 1)) ^ 2 := by
    have : ((c + 1) * (K + 1)) ^ 2 - K ^ 2 * c = K ^ 2 * (c ^ 2 + c + 1) + (c + 1) ^ 2 * (2 * K + 1) := by
      ring
    nlinarith [sq_nonneg K, sq_nonneg (c + 1), mul_pos hK hK]
  have hlt : c * (ε' * K) ^ 2 < ε ^ 2 := by
    rw [hε']
    calc c * (ε / ((c + 1) * (K + 1)) * K) ^ 2
        = ε ^ 2 * ((K ^ 2 * c) / ((c + 1) * (K + 1)) ^ 2) := by
          field_simp
      _ < ε ^ 2 * 1 := by
          gcongr
          rwa [div_lt_one (by positivity)]
      _ = ε ^ 2 := mul_one _
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).mp (hsq.trans_lt hlt)

/-! ## Exponential vectors and tuples -/

/-- Coefficients of the exponential vector `q ↦ e^{−(z + ρ q) ξ}`, `ξ` real:
`e^{−zξ} (−ρξ)^k / k!`. -/
def expVectorCoeff (z : ℂ) (ρ ξ : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (-(z * ξ)) * (((-(ρ * ξ)) ^ k / k.factorial : ℝ) : ℂ)

theorem norm_expVectorCoeff (z : ℂ) (ρ ξ : ℝ) (k : ℕ) :
    ‖expVectorCoeff z ρ ξ k‖ = Real.exp (-(z.re * ξ)) * (|ρ * ξ| ^ k / k.factorial) := by
  rw [expVectorCoeff, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_pow, abs_neg, Nat.abs_cast]
  congr 2
  simp [Complex.mul_re]

theorem summable_norm_expVectorCoeff_sq (z : ℂ) (ρ ξ : ℝ) :
    Summable (fun k => ‖expVectorCoeff z ρ ξ k‖ ^ 2) := by
  set t : ℝ := |ρ * ξ| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (((Real.summable_pow_div_factorial t).mul_left (Real.exp t)).mul_left
      ((Real.exp (-(z.re * ξ))) ^ 2))
  rw [norm_expVectorCoeff, mul_pow, ← ht]
  gcongr
  calc (t ^ k / k.factorial) ^ 2 = (t ^ k / k.factorial) * (t ^ k / k.factorial) := sq _
    _ ≤ Real.exp t * (t ^ k / k.factorial) := by
        gcongr
        exact Real.pow_div_factorial_le_exp t ht0 k

theorem memℓp_expVectorCoeff (z : ℂ) (ρ ξ : ℝ) : Memℓp (expVectorCoeff z ρ ξ) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine (summable_norm_expVectorCoeff_sq z ρ ξ).congr fun k => ?_
  rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The exponential vector: the Hardy-space element of `q ↦ e^{−(z + ρ q) ξ}`. -/
def expVector (z : ℂ) (ρ ξ : ℝ) : HardyDisk :=
  ⟨expVectorCoeff z ρ ξ, memℓp_expVectorCoeff z ρ ξ⟩

theorem expVector_apply (z : ℂ) (ρ ξ : ℝ) (k : ℕ) :
    (expVector z ρ ξ) k = expVectorCoeff z ρ ξ k := rfl

/-- **The exponential vector represents `q ↦ e^{−(z + ρ q) ξ}`** (on the whole plane). -/
theorem hardyFun_expVector (z : ℂ) (ρ ξ : ℝ) (q : ℂ) :
    hardyFun (expVector z ρ ξ) q = Complex.exp (-((z + ρ * q) * ξ)) := by
  have hexp : HasSum (fun k : ℕ => (-(ρ : ℂ) * q * ξ) ^ k / k.factorial)
      (Complex.exp (-(ρ : ℂ) * q * ξ)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hterm : ∀ k : ℕ, (expVector z ρ ξ) k * q ^ k
      = Complex.exp (-(z * ξ)) * ((-(ρ : ℂ) * q * ξ) ^ k / k.factorial) := fun k => by
    rw [expVector_apply, expVectorCoeff]
    push_cast
    ring
  unfold hardyFun
  simp_rw [hterm]
  rw [tsum_mul_left, hexp.tsum_eq, ← Complex.exp_add]
  congr 1
  ring

/-- The pairing of the exponential vector with `e` is `e^{−conj(z) ξ} Φ_e(ξ)`. -/
theorem inner_expVector (z : ℂ) (ρ ξ : ℝ) (e : HardyDisk) :
    ⟪expVector z ρ ξ, e⟫_ℂ = Complex.exp (-(conj z) * ξ) * coefficientTransform ρ e ξ := by
  rw [lp.inner_eq_tsum, coefficientTransform, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [RCLike.inner_apply, expVector_apply, expVectorCoeff, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal]
  push_cast
  simp only [neg_mul]
  ring

/-- The exponential tuple `E_ξ = (expVector (z i) (ρ i) ξ)_i`. -/
def expTuple (z : ι → ℂ) (ρ : ι → ℝ) (ξ : ℝ) : DiscTuple ι :=
  WithLp.toLp 2 fun i => expVector (z i) (ρ i) ξ

theorem expTuple_apply (z : ι → ℂ) (ρ : ι → ℝ) (ξ : ℝ) (i : ι) :
    expTuple z ρ ξ i = expVector (z i) (ρ i) ξ := rfl

/-- **The pairing with an exponential tuple is `F_e(ξ)`.** -/
theorem inner_expTuple (z : ι → ℂ) (ρ : ι → ℝ) (ξ : ℝ) (e : DiscTuple ι) :
    ⟪expTuple z ρ ξ, e⟫_ℂ = tuplePairing z ρ e ξ := by
  rw [PiLp.inner_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [expTuple_apply, inner_expVector]

/-- **Every exponential tuple lies in the closed span of the prime tuples.** -/
theorem expTuple_mem_primeSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) (ξ : ℝ) :
    expTuple z ρ ξ ∈ primeSpan z hρ := by
  rw [← Submodule.orthogonal_orthogonal (primeSpan z hρ), Submodule.mem_orthogonal]
  intro e he
  rw [← inner_conj_symm, inner_expTuple, tuplePairing_eq_zero_of_mem_orthogonal z hρ hb hb1 he]
  simp

/-! ## Monomial vectors and tuples -/

/-- The Hardy-space element of the polynomial `q ↦ (w + ρ q)^k`. -/
def monoVector (w : ℂ) (ρ : ℝ) (k : ℕ) : HardyDisk :=
  ∑ n ∈ range (k + 1), ((k.choose n : ℂ) * w ^ (k - n) * (ρ : ℂ) ^ n) • lp.single 2 n (1 : ℂ)

theorem hardyFun_monoVector (w : ℂ) (ρ : ℝ) (k : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    hardyFun (monoVector w ρ k) q = (w + ρ * q) ^ k := by
  rw [monoVector, hardyFun_sum_apply _ _ hq]
  simp_rw [hardyFun_smul _ _ hq, hardyFun_single _ hq]
  rw [add_comm w, add_pow]
  refine sum_congr rfl fun n _ => ?_
  ring

/-- The monomial tuple of `q ↦ (z i + ρ i q − c₀)^k`. -/
def monoTuple (z : ι → ℂ) (ρ : ι → ℝ) (c₀ : ℂ) (k : ℕ) : DiscTuple ι :=
  WithLp.toLp 2 fun i => monoVector (z i - c₀) (ρ i) k

theorem monoTuple_apply (z : ι → ℂ) (ρ : ι → ℝ) (c₀ : ℂ) (k : ℕ) (i : ι) :
    monoTuple z ρ c₀ k i = monoVector (z i - c₀) (ρ i) k := rfl

theorem hardyFun_monoTuple (z : ι → ℂ) (ρ : ι → ℝ) (c₀ : ℂ) (k : ℕ) (i : ι) {q : ℂ}
    (hq : ‖q‖ < 1) :
    hardyFun (monoTuple z ρ c₀ k i) q = (z i + ρ i * q - c₀) ^ k := by
  rw [monoTuple_apply, hardyFun_monoVector _ _ _ hq]
  congr 1
  ring

/-! ## Finite differences of the exponential tuples -/

/-- The scaled `k`-th finite difference of `ξ ↦ e^{c₀ ξ} E_ξ` at `ξ = 0` with step `h`:
`(−1)^k h^{−k} Σ_{j ≤ k} C(k,j) (−1)^{k−j} e^{c₀ j h} E_{jh}`; its disc functions are
`(−1)^k ((e^{−(z i + ρ i q − c₀) h} − 1)/h)^k`. -/
def finiteDifferenceTuple (z : ι → ℂ) (ρ : ι → ℝ) (c₀ : ℂ) (k : ℕ) (h : ℝ) : DiscTuple ι :=
  ((-1) ^ k * ((h : ℂ) ^ k)⁻¹) • ∑ j ∈ range (k + 1),
    ((k.choose j : ℂ) * (-1) ^ (k - j) * Complex.exp (c₀ * (j * h))) • expTuple z ρ (j * h)

theorem finiteDifferenceTuple_mem_primeSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) (c₀ : ℂ) (k : ℕ) (h : ℝ) :
    finiteDifferenceTuple z ρ c₀ k h ∈ primeSpan z hρ :=
  Submodule.smul_mem _ _ (Submodule.sum_mem _ fun _ _ =>
    Submodule.smul_mem _ _ (expTuple_mem_primeSpan z hρ hb hb1 _))

theorem hardyFun_finiteDifferenceTuple (z : ι → ℂ) (ρ : ι → ℝ) (c₀ : ℂ) (k : ℕ) (h : ℝ) (i : ι)
    {q : ℂ} (hq : ‖q‖ < 1) :
    hardyFun (finiteDifferenceTuple z ρ c₀ k h i) q
      = (-1) ^ k * ((Complex.exp (-((z i + ρ i * q - c₀) * h)) - 1) / h) ^ k := by
  have hx : ∀ j : ℕ, Complex.exp (c₀ * (j * h)) * Complex.exp (-((z i + ρ i * q) * ((j * h : ℝ) : ℂ)))
      = (Complex.exp (-((z i + ρ i * q - c₀) * h))) ^ j := fun j => by
    rw [← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum : ∑ j ∈ range (k + 1), ((k.choose j : ℂ) * (-1) ^ (k - j) * Complex.exp (c₀ * (j * h)))
      * Complex.exp (-((z i + ρ i * q) * ((j * h : ℝ) : ℂ)))
      = (Complex.exp (-((z i + ρ i * q - c₀) * h)) - 1) ^ k := by
    rw [sub_eq_add_neg, add_pow]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_assoc, hx j]
    ring
  rw [finiteDifferenceTuple, PiLp.smul_apply, hardyFun_smul _ _ hq, WithLp.ofLp_sum,
    Finset.sum_apply, hardyFun_sum_apply _ _ hq]
  simp_rw [PiLp.smul_apply, hardyFun_smul _ _ hq, expTuple_apply, hardyFun_expVector]
  rw [hsum, div_pow]
  ring

/-! ## The finite-difference estimate -/

/-- `‖a^{k+1} − b^{k+1}‖ ≤ (k+1) M^k ‖a − b‖` for `‖a‖, ‖b‖ ≤ M`. -/
theorem norm_pow_succ_sub_pow_succ_le {a b : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (k : ℕ) :
    ‖a ^ (k + 1) - b ^ (k + 1)‖ ≤ (k + 1) * M ^ k * ‖a - b‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) ha
  induction k with
  | zero => simp
  | succ k ih =>
    have hid : a ^ (k + 1 + 1) - b ^ (k + 1 + 1)
        = a ^ (k + 1) * (a - b) + (a ^ (k + 1) - b ^ (k + 1)) * b := by ring
    have h1 : ‖a ^ (k + 1)‖ ≤ M ^ (k + 1) := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ha _
    rw [hid]
    calc ‖a ^ (k + 1) * (a - b) + (a ^ (k + 1) - b ^ (k + 1)) * b‖
        ≤ ‖a ^ (k + 1)‖ * ‖a - b‖ + ‖a ^ (k + 1) - b ^ (k + 1)‖ * ‖b‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ M ^ (k + 1) * ‖a - b‖ + ((k + 1) * M ^ k * ‖a - b‖) * M :=
          add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
            (mul_le_mul ih hb (norm_nonneg _) (by positivity))
      _ = ((k + 1 : ℕ) + 1) * M ^ (k + 1) * ‖a - b‖ := by
          push_cast
          ring

/-- **The difference quotients of the exponential.**  For `‖w‖ ≤ A`, `0 < h`, `(A + 1) h ≤ 1`:
`‖((e^{−wh} − 1)/h)^k − (−w)^k‖ ≤ k (2(A + 1))^{k+1} h`. -/
theorem norm_expDiffQuot_pow_sub_le {w : ℂ} {A h : ℝ} (hw : ‖w‖ ≤ A) (h0 : 0 < h)
    (hh : (A + 1) * h ≤ 1) (k : ℕ) :
    ‖((Complex.exp (-(w * h)) - 1) / h) ^ k - (-w) ^ k‖ ≤ k * (2 * (A + 1)) ^ (k + 1) * h := by
  have hA : 0 ≤ A := le_trans (norm_nonneg _) hw
  have hnorm : ‖-(w * (h : ℂ))‖ = ‖w‖ * h := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0.le]
  have hx : ‖-(w * (h : ℂ))‖ ≤ 1 := by
    rw [hnorm]
    calc ‖w‖ * h ≤ (A + 1) * h := by gcongr; linarith
      _ ≤ 1 := hh
  have hdq : ‖(Complex.exp (-(w * h)) - 1) / h - (-w)‖ ≤ A ^ 2 * h := by
    have h1 := Complex.norm_exp_sub_one_sub_id_le hx
    have hne : (h : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have hid : (Complex.exp (-(w * h)) - 1) / h - (-w)
        = (Complex.exp (-(w * h)) - 1 - (-(w * h))) / h := by
      field_simp
    rw [hid, norm_div, Complex.norm_real, Real.norm_of_nonneg h0.le, div_le_iff₀ h0]
    calc ‖Complex.exp (-(w * h)) - 1 - -(w * h)‖ ≤ ‖-(w * (h : ℂ))‖ ^ 2 := h1
      _ = (‖w‖ * h) ^ 2 := by rw [hnorm]
      _ ≤ (A * h) ^ 2 := by gcongr
      _ = A ^ 2 * h * h := by ring
  have hb : ‖-w‖ ≤ 2 * (A + 1) := by
    rw [norm_neg]
    linarith
  have hAh : A ^ 2 * h ≤ A := by
    calc A ^ 2 * h = A * (A * h) := by ring
      _ ≤ A * 1 := by
          gcongr
          nlinarith [hh, h0.le]
      _ = A := mul_one _
  have ha : ‖(Complex.exp (-(w * h)) - 1) / h‖ ≤ 2 * (A + 1) := by
    calc ‖(Complex.exp (-(w * h)) - 1) / h‖
        = ‖((Complex.exp (-(w * h)) - 1) / h - (-w)) + (-w)‖ := by rw [sub_add_cancel]
      _ ≤ ‖(Complex.exp (-(w * h)) - 1) / h - (-w)‖ + ‖-w‖ := norm_add_le _ _
      _ ≤ A ^ 2 * h + A := by
          rw [norm_neg]
          linarith
      _ ≤ 2 * (A + 1) := by linarith
  cases k with
  | zero => simp
  | succ k =>
    calc ‖((Complex.exp (-(w * h)) - 1) / h) ^ (k + 1) - (-w) ^ (k + 1)‖
        ≤ (k + 1) * (2 * (A + 1)) ^ k * ‖(Complex.exp (-(w * h)) - 1) / h - (-w)‖ :=
          norm_pow_succ_sub_pow_succ_le ha hb k
      _ ≤ (k + 1) * (2 * (A + 1)) ^ k * (A ^ 2 * h) := by gcongr
      _ ≤ (k + 1) * (2 * (A + 1)) ^ k * ((2 * (A + 1)) ^ 2 * h) := by
          gcongr
          nlinarith
      _ = ((k + 1 : ℕ) : ℝ) * (2 * (A + 1)) ^ (k + 1 + 1) * h := by
          push_cast
          ring

/-! ## Monomial tuples lie in the closed span -/

/-- On `‖q‖ ≤ R` the disc points satisfy `‖z i + ρ i q − c₀‖ ≤ Σ_j (‖z j − c₀‖ + ρ j R)`. -/
theorem norm_disc_point_sub_le (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (c₀ : ℂ) {R : ℝ}
    (i : ι) {q : ℂ} (hq : ‖q‖ ≤ R) :
    ‖z i + ρ i * q - c₀‖ ≤ ∑ j, (‖z j - c₀‖ + ρ j * R) := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hq
  have hρi := hρ i
  calc ‖z i + ρ i * q - c₀‖ = ‖(z i - c₀) + ρ i * q‖ := by congr 1; ring
    _ ≤ ‖z i - c₀‖ + ‖(ρ i : ℂ) * q‖ := norm_add_le _ _
    _ ≤ ‖z i - c₀‖ + ρ i * R := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ i)]
        gcongr
    _ ≤ ∑ j, (‖z j - c₀‖ + ρ j * R) :=
        Finset.single_le_sum (f := fun j => ‖z j - c₀‖ + ρ j * R)
          (fun j _ => by have := hρ j; positivity) (mem_univ i)

/-- **Monomial tuples lie in the closed span of the prime tuples.** -/
theorem monoTuple_mem_primeSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) (c₀ : ℂ) (k : ℕ) :
    monoTuple z ρ c₀ k ∈ primeSpan z hρ := by
  set A : ℝ := ∑ j, (‖z j - c₀‖ + ρ j * 2) with hA
  have hA0 : 0 ≤ A := sum_nonneg fun j _ => by have := hρ j; positivity
  set C : ℝ := k * (2 * (A + 1)) ^ (k + 1) with hC
  have hC0 : 0 ≤ C := by positivity
  refine mem_of_forall_exists_circle_approx (Submodule.isClosed_topologicalClosure _)
    (by norm_num : (1 : ℝ) < 2) fun ε hε => ?_
  set h : ℝ := min ((A + 1)⁻¹) (ε / (C + 1)) with hh
  have h0 : 0 < h := lt_min (by positivity) (by positivity)
  have hh1 : (A + 1) * h ≤ 1 := by
    calc (A + 1) * h ≤ (A + 1) * (A + 1)⁻¹ := by gcongr; exact min_le_left _ _
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hhε : C * h ≤ ε := by
    calc C * h ≤ C * (ε / (C + 1)) := by gcongr; exact min_le_right _ _
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  have hsign : ∀ u : ℂ, (-1 : ℂ) ^ k * (-u) ^ k = u ^ k := fun u => by
    rw [← mul_pow, neg_one_mul, neg_neg]
  refine ⟨finiteDifferenceTuple z ρ c₀ k h,
    finiteDifferenceTuple_mem_primeSpan z hρ hb hb1 c₀ k h,
    fun i q => (z i + ρ i * q - c₀) ^ k
      - (-1) ^ k * ((Complex.exp (-((z i + ρ i * q - c₀) * h)) - 1) / h) ^ k, ?_, ?_, ?_⟩
  · intro i
    apply Differentiable.differentiableOn
    fun_prop
  · intro i θ
    beta_reduce
    have hq : ‖circleMap 0 2 θ‖ ≤ 2 := by rw [norm_circleMap_zero, abs_of_pos (by norm_num)]
    have hw : ‖z i + ρ i * circleMap 0 2 θ - c₀‖ ≤ A := norm_disc_point_sub_le z hρ c₀ i hq
    have hest := norm_expDiffQuot_pow_sub_le hw h0 hh1 k
    have hid : (z i + ρ i * circleMap 0 2 θ - c₀) ^ k
        - (-1) ^ k * ((Complex.exp (-((z i + ρ i * circleMap 0 2 θ - c₀) * h)) - 1) / h) ^ k
        = -((-1) ^ k * (((Complex.exp (-((z i + ρ i * circleMap 0 2 θ - c₀) * h)) - 1) / h) ^ k
          - (-(z i + ρ i * circleMap 0 2 θ - c₀)) ^ k)) := by
      rw [mul_sub, neg_sub, hsign]
    rw [hid, norm_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hest.trans hhε
  · intro i q hq
    rw [PiLp.sub_apply, hardyFun_sub_apply _ _ hq, hardyFun_monoTuple _ _ _ _ _ hq,
      hardyFun_finiteDifferenceTuple _ _ _ _ _ _ hq]

/-! ## Taylor polynomials: tuples of analytic functions lie in the closed span -/

/-- Finitely many reals below `R₀` are below some `r' < R₀`. -/
theorem exists_lt_of_forall_lt {f : ι → ℝ} {R₀ : ℝ} (hf : ∀ i, f i < R₀) :
    ∃ r', r' < R₀ ∧ ∀ i, f i < r' := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨R₀ - 1, by linarith, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_max f
    exact ⟨(f i₀ + R₀) / 2, by linarith [hf i₀], fun i => by linarith [hi₀ i, hf i₀]⟩

omit [Fintype ι] in
/-- The disc coordinate maps `closedBall 0 R` into `ball c₀ R₀` when `‖z i − c₀‖ + ρ i R < R₀`. -/
theorem mapsTo_disc_coordinate (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) {c₀ : ℂ}
    {R R₀ : ℝ} (hsub : ∀ i, ‖z i - c₀‖ + ρ i * R < R₀) (i : ι) :
    Set.MapsTo (fun q : ℂ => z i + ρ i * q) (closedBall 0 R) (ball c₀ R₀) := by
  intro q hq
  have hρi := hρ i
  rw [mem_closedBall, dist_zero_right] at hq
  rw [mem_ball, dist_eq_norm]
  calc ‖z i + ρ i * q - c₀‖ = ‖(z i - c₀) + ρ i * q‖ := by congr 1; ring
    _ ≤ ‖z i - c₀‖ + ‖(ρ i : ℂ) * q‖ := norm_add_le _ _
    _ ≤ ‖z i - c₀‖ + ρ i * R := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ i)]
        gcongr
    _ < R₀ := hsub i

/-- **Tuples of functions analytic on a disc containing the discs lie in the closed span.**  If
`F` is analytic on `ball c₀ R₀`, `R > 1`, and `‖z i − c₀‖ + ρ i R < R₀` for every `i`, then every
tuple `t` with `hardyFun (t i) q = F (z i + ρ i q)` on the unit disc lies in `primeSpan`. -/
theorem mem_primeSpan_of_differentiableOn_ball (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) {R : ℝ} (hR : 1 < R) {c₀ : ℂ} {R₀ : ℝ}
    (hsub : ∀ i, ‖z i - c₀‖ + ρ i * R < R₀) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball c₀ R₀))
    {t : DiscTuple ι} (ht : ∀ i, ∀ q : ℂ, ‖q‖ < 1 → hardyFun (t i) q = F (z i + ρ i * q)) :
    t ∈ primeSpan z hρ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : t = 0 := PiLp.ext fun i => (IsEmpty.false i).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨R₀', hR₀', hR₀'lt⟩ := exists_lt_of_forall_lt hsub
  obtain ⟨r', hr', hr'lt⟩ := exists_lt_of_forall_lt hR₀'lt
  have hr'pos : 0 < r' := by
    obtain ⟨i⟩ := hι
    have h1 := hr'lt i
    have h2 := hρ i
    have h3 : 0 ≤ ‖z i - c₀‖ + ρ i * R := by positivity
    linarith
  have hR₀'pos : 0 < R₀' := by linarith
  set Rn : NNReal := ⟨R₀', hR₀'pos.le⟩ with hRn
  set rn : NNReal := ⟨r', hr'pos.le⟩ with hrn
  have hRR : ((Rn : NNReal) : ℝ) = R₀' := rfl
  have hrr : ((rn : NNReal) : ℝ) = r' := rfl
  have hFc : DifferentiableOn ℂ F (closedBall c₀ R₀') := hF.mono (closedBall_subset_ball hR₀')
  have hps : HasFPowerSeriesOnBall F (cauchyPowerSeries F c₀ R₀') c₀ Rn := by
    have := hFc.hasFPowerSeriesOnBall (R := Rn) (by rw [← NNReal.coe_pos, hRR]; exact hR₀'pos)
    simpa [hRR] using this
  have hlt : (rn : ENNReal) < Rn := by
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hRR, hrr]
    exact hr'
  have hunif := hps.tendstoUniformlyOn' hlt
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  set p := cauchyPowerSeries F c₀ R₀' with hp
  refine mem_of_forall_exists_circle_approx (Submodule.isClosed_topologicalClosure _) hR
    fun ε hε => ?_
  obtain ⟨n, hn⟩ := (hunif ε hε).exists
  refine ⟨∑ k ∈ range n, p.coeff k • monoTuple z ρ c₀ k,
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (monoTuple_mem_primeSpan z hρ hb hb1 c₀ k),
    fun i q => F (z i + ρ i * q) - ∑ k ∈ range n, p.coeff k * (z i + ρ i * q - c₀) ^ k,
    ?_, ?_, ?_⟩
  · intro i
    refine (hF.comp ((differentiableOn_const _).add ((differentiableOn_const _).mul
      differentiableOn_id)) (mapsTo_disc_coordinate z hρ hsub i)).sub ?_
    refine DifferentiableOn.fun_sum fun k _ => ?_
    exact (differentiableOn_const _).mul ((((differentiableOn_const _).add
      ((differentiableOn_const _).mul differentiableOn_id)).sub (differentiableOn_const _)).pow _)
  · intro i θ
    have hρi := hρ i
    have hq : ‖circleMap 0 R θ‖ ≤ R := by rw [norm_circleMap_zero, abs_of_pos (by linarith)]
    have hy : z i + ρ i * circleMap 0 R θ ∈ ball c₀ rn := by
      rw [mem_ball, dist_eq_norm, hrr]
      calc ‖z i + ρ i * circleMap 0 R θ - c₀‖
          = ‖(z i - c₀) + ρ i * circleMap 0 R θ‖ := by congr 1; ring
        _ ≤ ‖z i - c₀‖ + ‖(ρ i : ℂ) * circleMap 0 R θ‖ := norm_add_le _ _
        _ ≤ ‖z i - c₀‖ + ρ i * R := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ i)]
            gcongr
        _ < r' := hr'lt i
    have hps' : p.partialSum n (z i + ρ i * circleMap 0 R θ - c₀)
        = ∑ k ∈ range n, p.coeff k * (z i + ρ i * circleMap 0 R θ - c₀) ^ k := by
      unfold FormalMultilinearSeries.partialSum
      refine sum_congr rfl fun k _ => ?_
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
    have := hn _ hy
    rw [dist_eq_norm, hps'] at this
    exact this.le
  · intro i q hq
    rw [PiLp.sub_apply, hardyFun_sub_apply _ _ hq, ht i q hq, WithLp.ofLp_sum, Finset.sum_apply,
      hardyFun_sum_apply _ _ hq]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [PiLp.smul_apply, hardyFun_smul _ _ hq, hardyFun_monoTuple _ _ _ _ _ hq]

/-- **A representing tuple in the closed span.**  For `F` analytic on `ball c₀ R₀` with
`‖z i − c₀‖ + ρ i R < R₀`, `R > 1`, there is a tuple of `primeSpan` whose disc functions are
`q ↦ F (z i + ρ i q)`. -/
theorem exists_mem_primeSpan_of_differentiableOn_ball (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) {R : ℝ} (hR : 1 < R) {c₀ : ℂ} {R₀ : ℝ}
    (hsub : ∀ i, ‖z i - c₀‖ + ρ i * R < R₀) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball c₀ R₀)) :
    ∃ t ∈ primeSpan z hρ, ∀ i, ∀ q : ℂ, ‖q‖ < 1 → hardyFun (t i) q = F (z i + ρ i * q) := by
  have hdiff : ∀ i, DifferentiableOn ℂ (fun q => F (z i + ρ i * q)) (closedBall 0 R) := fun i =>
    hF.comp ((differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id))
      (mapsTo_disc_coordinate z hρ hsub i)
  have hbound : ∀ i, ∃ B, ∀ θ : ℝ, ‖F (z i + ρ i * circleMap 0 R θ)‖ ≤ B := fun i => by
    obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn
      ((hdiff i).continuousOn.mono sphere_subset_closedBall)
    exact ⟨B, fun θ => hB _ (circleMap_mem_sphere _ (by linarith) θ)⟩
  choose B hB using hbound
  refine ⟨WithLp.toLp 2 fun i => hardyDiskOfAnalytic (fun q => F (z i + ρ i * q)) hR (hB i),
    ?_, fun i q hq => hardyFun_hardyDiskOfAnalytic hR (hdiff i) (hB i) hq⟩
  exact mem_primeSpan_of_differentiableOn_ball z hρ hb hb1 hR hsub hF fun i q hq =>
    hardyFun_hardyDiskOfAnalytic hR (hdiff i) (hB i) hq

/-! ## Discs of a half plane lie in a disc of the half plane -/

/-- **A disc of the half plane `Re > α` containing finitely many closed discs.**  If
`α < Re (z i) − r i` for all `i`, there are `c₀` and `R₀` with
`‖z i − c₀‖ + r i < R₀` and `closedBall c₀ R₀ ⊆ {Re > α}`. -/
theorem exists_ball_re_gt_of_forall_lt (z : ι → ℂ) {r : ι → ℝ} {α : ℝ}
    (hα : ∀ i, α < (z i).re - r i) :
    ∃ (c₀ : ℂ) (R₀ : ℝ), (∀ i, ‖z i - c₀‖ + r i < R₀) ∧ ∀ s ∈ closedBall c₀ R₀, α < s.re := by
  obtain ⟨η, hη, hηle⟩ : ∃ η > 0, ∀ i, α + 2 * η ≤ (z i).re - r i := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_min (fun i => (z i).re - r i)
      exact ⟨((z i₀).re - r i₀ - α) / 4, by linarith [hα i₀],
        fun i => by linarith [hi₀ i, hα i₀]⟩
  set B : ℝ := ∑ i, ‖z i‖ with hB
  have hBi : ∀ i, ‖z i‖ ≤ B := fun i =>
    Finset.single_le_sum (fun j _ => norm_nonneg (z j)) (mem_univ i)
  have hB0 : 0 ≤ B := sum_nonneg fun i _ => norm_nonneg _
  set X : ℝ := B + B ^ 2 / (2 * η) + 1 with hX
  have h2η : 2 * η * (B ^ 2 / (2 * η) + 1) = B ^ 2 + 2 * η := by
    field_simp
  refine ⟨(X : ℂ), X - (α + η), fun i => ?_, fun s hs => ?_⟩
  · have hre : (z i).re ≤ B := le_trans (le_abs_self _) ((Complex.abs_re_le_norm _).trans (hBi i))
    have him : (z i).im ^ 2 ≤ B ^ 2 := by
      have h1 := (Complex.abs_im_le_norm (z i)).trans (hBi i)
      have h2 : |(z i).im| ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [sq_abs] at h2
    have hXre : B ^ 2 / (2 * η) + 1 ≤ X - (z i).re := by rw [hX]; linarith
    have hD : 0 < (X - (z i).re) + η := by
      have : 0 ≤ B ^ 2 / (2 * η) := by positivity
      linarith
    have hlt : ‖z i - X‖ < (X - (z i).re) + η := by
      rw [← pow_lt_pow_iff_left₀ (norm_nonneg _) hD.le two_ne_zero, Complex.sq_norm,
        Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, sub_zero]
      have hmul := mul_le_mul_of_nonneg_left hXre (by positivity : (0 : ℝ) ≤ 2 * η)
      nlinarith
    have := hηle i
    linarith
  · rw [mem_closedBall, dist_eq_norm] at hs
    have h1 := Complex.abs_re_le_norm (s - X)
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    linarith [(abs_le.mp h1).1]

/-- **A disc of the half plane `Re < β` containing finitely many closed discs.** -/
theorem exists_ball_re_lt_of_forall_lt (z : ι → ℂ) {r : ι → ℝ} {β : ℝ}
    (hβ : ∀ i, (z i).re + r i < β) :
    ∃ (c₀ : ℂ) (R₀ : ℝ), (∀ i, ‖z i - c₀‖ + r i < R₀) ∧ ∀ s ∈ closedBall c₀ R₀, s.re < β := by
  obtain ⟨c₀, R₀, h1, h2⟩ := exists_ball_re_gt_of_forall_lt (fun i => -z i) (r := r) (α := -β)
    (fun i => by rw [Complex.neg_re]; linarith [hβ i])
  refine ⟨-c₀, R₀, fun i => ?_, fun s hs => ?_⟩
  · have := h1 i
    rwa [show z i - -c₀ = -(-z i - c₀) by ring, norm_neg]
  · have hs' : -s ∈ closedBall c₀ R₀ := by
      rw [mem_closedBall, dist_eq_norm] at hs ⊢
      rw [show -s - c₀ = -(s - -c₀) by ring, norm_neg]
      exact hs
    have := h2 _ hs'
    rw [Complex.neg_re] at this
    linarith

end RHTower
