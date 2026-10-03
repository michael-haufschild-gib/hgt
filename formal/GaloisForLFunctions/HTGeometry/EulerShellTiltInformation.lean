import GaloisForLFunctions.HTGeometry.CausalDelayDriftWork

/-!
# Work cusp versus smooth information on the Euler shell

The Gibbs tilts `P_u(n) = n^{-σ+u}/S_m(σ-u)` of the Euler shell (**(CDW.16)**) have log-partition
`F(u) = log S_m(σ - u)` with `F' = E_{P_u}(log n)` and `F'' = Var_{P_u}(log n) > 0` (**(CDW.17)–(CDW.18)**).
The reflected log-likelihood ratio is `2u log n + F(-u) - F(u)` (**(CDW.19)**), so the Jeffreys information
is `J_m(u) = 2u(F'(u) - F'(-u))` (**(CDW.20)**), and the mean-value theorem gives
`0 < J_m(u) ≤ 4 M_{u₀} u²` with `M_{u₀} = sup_{|s| ≤ u₀} F''(s)` (**(CDW.21)–(CDW.22)**).  The paired
causal work is `4|u|/T²` for `0 < |u| ≤ T` (**(CDW.23)**), so
`𝔠_pair(u,T)/J_m(u) ≥ 1/(M_{u₀} T² |u|) → ∞` (**(CDW.24)**): `J_m = O(u²)` while `𝔠_pair = Θ(|u|)`
(**(CDW.25)**).
-/

open MeasureTheory Set Filter Topology Asymptotics

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {m : ℕ}

/-! ## Shell moments -/

/-- The shell moments `M_k(s) = Σ_{n ∈ A_m} (log n)^k n^{-s}`. -/
def eulerShellMoment (m k : ℕ) (s : ℝ) : ℝ := ∑' n : EulerShell m, Real.log (n : ℕ) ^ k * ((n : ℕ) : ℝ) ^ (-s)

theorem eulerShell_cast_pos (n : EulerShell m) : (0 : ℝ) < ((n : ℕ) : ℝ) := by
  exact_mod_cast (show 0 < (n : ℕ) by have := n.2.1; omega)

theorem eulerShell_one_le_cast (n : EulerShell m) : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by
  exact_mod_cast (show 1 ≤ (n : ℕ) by have := n.2.1; omega)

theorem log_eulerShell_nonneg (n : EulerShell m) : 0 ≤ Real.log ((n : ℕ) : ℝ) :=
  Real.log_nonneg (eulerShell_one_le_cast n)

/-- `Σ_{n ∈ A_m} (log n)^k n^{-s}` converges for `s > 1`: `log n ≤ n^ε/ε`. -/
theorem summable_eulerShellMoment (m k : ℕ) {s : ℝ} (hs : 1 < s) :
    Summable fun n : EulerShell m => Real.log (n : ℕ) ^ k * ((n : ℕ) : ℝ) ^ (-s) := by
  set ε := (s - 1) / (2 * ((k : ℝ) + 1)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by positivity)
  have hkε : (k : ℝ) * ε ≤ (s - 1) / 2 := by
    rw [hε, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ((summable_shell m (σ := s - k * ε) (by linarith)).mul_left (ε⁻¹ ^ k)).of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg (log_eulerShell_nonneg n) k) (by positivity)) fun n => ?_
  have hn := eulerShell_cast_pos n
  have hlog : Real.log ((n : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) ^ ε / ε := Real.log_le_rpow_div hn.le hε0
  have hpow : Real.log ((n : ℕ) : ℝ) ^ k ≤ (((n : ℕ) : ℝ) ^ ε / ε) ^ k :=
    pow_le_pow_left₀ (log_eulerShell_nonneg n) hlog k
  have heq : (((n : ℕ) : ℝ) ^ ε / ε) ^ k * ((n : ℕ) : ℝ) ^ (-s) =
      ε⁻¹ ^ k * ((n : ℕ) : ℝ) ^ (-(s - k * ε)) := by
    rw [div_pow, ← Real.rpow_natCast (((n : ℕ) : ℝ) ^ ε) k, ← Real.rpow_mul hn.le,
      show -(s - k * ε) = ε * k + -s by ring, Real.rpow_add hn, inv_pow]
    ring
  calc Real.log ((n : ℕ) : ℝ) ^ k * ((n : ℕ) : ℝ) ^ (-s)
      ≤ (((n : ℕ) : ℝ) ^ ε / ε) ^ k * ((n : ℕ) : ℝ) ^ (-s) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = ε⁻¹ ^ k * ((n : ℕ) : ℝ) ^ (-(s - k * ε)) := heq

theorem eulerShellMoment_zero (m : ℕ) (s : ℝ) : eulerShellMoment m 0 s = eulerShellSum m s := by
  simp [eulerShellMoment, eulerShellSum]

theorem eulerShellMoment_nonneg (m k : ℕ) (s : ℝ) : 0 ≤ eulerShellMoment m k s :=
  tsum_nonneg fun n => mul_nonneg (pow_nonneg (log_eulerShell_nonneg n) k) (by positivity)

/-- `d/du M_k(σ - u) = M_{k+1}(σ - u)` for `σ - u > 1`. -/
theorem hasDerivAt_eulerShellMoment_sub (m k : ℕ) {σ u : ℝ} (hu : 1 < σ - u) :
    HasDerivAt (fun u => eulerShellMoment m k (σ - u)) (eulerShellMoment m (k + 1) (σ - u)) u := by
  set u₁ := (u + (σ - 1)) / 2 with hu₁
  have hlt : u < u₁ := by rw [hu₁]; linarith
  have hu₁' : 1 < σ - u₁ := by rw [hu₁]; linarith
  have h := hasDerivAt_tsum_of_isPreconnected (t := Iio u₁) (y₀ := u) (y := u)
    (g := fun (n : EulerShell m) (y : ℝ) => Real.log (n : ℕ) ^ k * ((n : ℕ) : ℝ) ^ (-(σ - y)))
    (g' := fun (n : EulerShell m) (y : ℝ) => Real.log (n : ℕ) ^ (k + 1) * ((n : ℕ) : ℝ) ^ (-(σ - y)))
    (summable_eulerShellMoment m (k + 1) hu₁') isOpen_Iio isPreconnected_Iio
    (fun n y _ => by
      have hf : HasDerivAt (fun y : ℝ => -(σ - y)) 1 y := by
        refine ((hasDerivAt_id y).sub_const σ).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
        simp only [id]
        ring
      have h1 := (hf.const_rpow (eulerShell_cast_pos n)).const_mul (Real.log (n : ℕ) ^ k)
      exact h1.congr_deriv (by ring))
    (fun n y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (log_eulerShell_nonneg n) _)
        (by positivity))]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (log_eulerShell_nonneg n) _)
      exact Real.rpow_le_rpow_of_exponent_le (eulerShell_one_le_cast n) (by linarith [mem_Iio.1 hy]))
    hlt (summable_eulerShellMoment m k hu) hlt
  exact h

theorem eulerShellMoment_zero_pos (hm : 1 ≤ m) {s : ℝ} (hs : 1 < s) : 0 < eulerShellMoment m 0 s := by
  rw [eulerShellMoment_zero]
  exact eulerShellSum_pos hm hs

/-! ## Gibbs tilts and the log-partition -/

variable (m) (σ : ℝ)

/-- **(CDW.16)** The Gibbs tilt `P_u(n) = n^{-σ+u}/S_m(σ-u)`. -/
def shellTilt (u : ℝ) (n : EulerShell m) : ℝ := ((n : ℕ) : ℝ) ^ (-(σ - u)) / eulerShellSum m (σ - u)

/-- **(CDW.17)** The log-partition `F(u) = log S_m(σ - u)`. -/
def shellLogPartition (u : ℝ) : ℝ := Real.log (eulerShellSum m (σ - u))

/-- The Gibbs mean `E_{P_u}(log n)`. -/
def shellTiltMean (u : ℝ) : ℝ := ∑' n : EulerShell m, shellTilt m σ u n * Real.log (n : ℕ)

/-- The Gibbs variance `Var_{P_u}(log n)`. -/
def shellTiltVar (u : ℝ) : ℝ :=
  ∑' n : EulerShell m, shellTilt m σ u n * (Real.log (n : ℕ) - shellTiltMean m σ u) ^ 2

variable {m σ}

theorem shellTilt_pos (hm : 1 ≤ m) {u : ℝ} (hu : 1 < σ - u) (n : EulerShell m) : 0 < shellTilt m σ u n :=
  div_pos (Real.rpow_pos_of_pos (eulerShell_cast_pos n) _) (eulerShellSum_pos hm hu)

theorem hasSum_shellTilt_mul_log_pow (k : ℕ) {u : ℝ} (hu : 1 < σ - u) :
    HasSum (fun n => shellTilt m σ u n * Real.log (n : ℕ) ^ k) (eulerShellMoment m k (σ - u) / eulerShellMoment m 0 (σ - u)) := by
  rw [eulerShellMoment_zero]
  have h := ((summable_eulerShellMoment m k hu).hasSum).div_const (eulerShellSum m (σ - u))
  refine h.congr_fun fun n => ?_
  rw [shellTilt]
  ring

/-- `P_u` is a probability distribution on `A_m`. -/
theorem hasSum_shellTilt (hm : 1 ≤ m) {u : ℝ} (hu : 1 < σ - u) : HasSum (shellTilt m σ u) 1 := by
  have h := hasSum_shellTilt_mul_log_pow (m := m) 0 hu
  rw [div_self (eulerShellMoment_zero_pos hm hu).ne'] at h
  simpa using h

theorem shellTiltMean_eq {u : ℝ} (hu : 1 < σ - u) :
    shellTiltMean m σ u = eulerShellMoment m 1 (σ - u) / eulerShellMoment m 0 (σ - u) := by
  rw [shellTiltMean, ← (hasSum_shellTilt_mul_log_pow (m := m) 1 hu).tsum_eq]
  simp_rw [pow_one]

theorem shellTiltVar_eq (hm : 1 ≤ m) {u : ℝ} (hu : 1 < σ - u) :
    shellTiltVar m σ u = eulerShellMoment m 2 (σ - u) / eulerShellMoment m 0 (σ - u) -
      (eulerShellMoment m 1 (σ - u) / eulerShellMoment m 0 (σ - u)) ^ 2 := by
  have h2 := hasSum_shellTilt_mul_log_pow (m := m) 2 hu
  have h1 := hasSum_shellTilt_mul_log_pow (m := m) 1 hu
  have h0 := hasSum_shellTilt hm hu
  have hμ' := shellTiltMean_eq (m := m) hu
  have h := (h2.sub (h1.mul_left (2 * shellTiltMean m σ u))).add (h0.mul_left (shellTiltMean m σ u ^ 2))
  rw [shellTiltVar, show (∑' n, shellTilt m σ u n * (Real.log ((n : EulerShell m) : ℕ) - shellTiltMean m σ u) ^ 2) =
      ∑' n, (shellTilt m σ u n * Real.log ((n : EulerShell m) : ℕ) ^ 2 -
        2 * shellTiltMean m σ u * (shellTilt m σ u n * Real.log ((n : EulerShell m) : ℕ) ^ 1) +
        shellTiltMean m σ u ^ 2 * shellTilt m σ u n) from tsum_congr fun n => by ring, h.tsum_eq, hμ']
  ring

/-- **(CDW.18)** `F'(u) = E_{P_u}(log n)`. -/
theorem hasDerivAt_shellLogPartition (hm : 1 ≤ m) {u : ℝ} (hu : 1 < σ - u) :
    HasDerivAt (shellLogPartition m σ) (shellTiltMean m σ u) u := by
  have h := (hasDerivAt_eulerShellMoment_sub m 0 hu).log (eulerShellMoment_zero_pos hm hu).ne'
  rw [shellTiltMean_eq (m := m) hu]
  convert h using 1
  funext v
  rw [shellLogPartition, eulerShellMoment_zero]

theorem eventually_one_lt_sub {u : ℝ} (hu : 1 < σ - u) : ∀ᶠ v in 𝓝 u, 1 < σ - v :=
  (isOpen_lt continuous_const (continuous_const.sub continuous_id)).mem_nhds hu

/-- **(CDW.18)** `F''(u) = Var_{P_u}(log n)`: the Gibbs mean moves by the variance. -/
theorem hasDerivAt_shellTiltMean (hm : 1 ≤ m) {u : ℝ} (hu : 1 < σ - u) :
    HasDerivAt (shellTiltMean m σ) (shellTiltVar m σ u) u := by
  have h0 := hasDerivAt_eulerShellMoment_sub m 0 hu
  have h1 := hasDerivAt_eulerShellMoment_sub m 1 hu
  have hne := (eulerShellMoment_zero_pos hm hu).ne'
  have hq := h1.div h0 hne
  have heq : shellTiltMean m σ =ᶠ[𝓝 u] fun v => eulerShellMoment m 1 (σ - v) / eulerShellMoment m 0 (σ - v) :=
    (eventually_one_lt_sub hu).mono fun v hv => shellTiltMean_eq (m := m) hv
  refine (hq.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [shellTiltVar_eq hm hu]
  field_simp

theorem deriv_shellLogPartition (hm : 1 ≤ m) {u : ℝ} (hu : 1 < σ - u) :
    deriv (shellLogPartition m σ) u = shellTiltMean m σ u :=
  (hasDerivAt_shellLogPartition hm hu).deriv

/-- **(CDW.18)** `F'' = Var_{P_u}(log n)` as an iterated derivative. -/
theorem deriv_deriv_shellLogPartition (hm : 1 ≤ m) {u : ℝ} (hu : 1 < σ - u) :
    deriv (deriv (shellLogPartition m σ)) u = shellTiltVar m σ u := by
  have heq : deriv (shellLogPartition m σ) =ᶠ[𝓝 u] shellTiltMean m σ :=
    (eventually_one_lt_sub hu).mono fun v hv => deriv_shellLogPartition hm hv
  rw [heq.deriv_eq]
  exact (hasDerivAt_shellTiltMean hm hu).deriv

/-- **(CDW.18)** `Var_{P_u}(log n) > 0`: `log` takes two distinct values on `A_m`. -/
theorem shellTiltVar_pos (hm : 1 ≤ m) {u : ℝ} (hu : 1 < σ - u) : 0 < shellTiltVar m σ u := by
  set μ := shellTiltMean m σ u
  have hsum : Summable fun n => shellTilt m σ u n * (Real.log (n : ℕ) - μ) ^ 2 := by
    have h := (((hasSum_shellTilt_mul_log_pow (m := m) 2 hu).sub
      ((hasSum_shellTilt_mul_log_pow (m := m) 1 hu).mul_left (2 * μ))).add
      ((hasSum_shellTilt hm hu).mul_left (μ ^ 2))).summable
    exact h.congr fun n => by ring
  set n₁ : EulerShell m := ⟨2 ^ m * 3, two_pow_mul_prime_mem hm Nat.prime_three (by norm_num)⟩
  set n₂ : EulerShell m := ⟨2 ^ m * 5, two_pow_mul_prime_mem hm Nat.prime_five (by norm_num)⟩
  have hne : Real.log ((n₁ : ℕ) : ℝ) ≠ Real.log ((n₂ : ℕ) : ℝ) := by
    intro h
    have h' := Real.log_injOn_pos (Set.mem_Ioi.2 (eulerShell_cast_pos n₁))
      (Set.mem_Ioi.2 (eulerShell_cast_pos n₂)) h
    have : (2 ^ m * 3 : ℕ) = 2 ^ m * 5 := by exact_mod_cast h'
    have h2 : 0 < 2 ^ m := by positivity
    omega
  have hex : ∃ n : EulerShell m, Real.log ((n : ℕ) : ℝ) - μ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (by linarith [hall n₁, hall n₂])
  obtain ⟨n, hn⟩ := hex
  exact hsum.tsum_pos (fun k => mul_nonneg (shellTilt_pos hm hu k).le (sq_nonneg _)) n
    (mul_pos (shellTilt_pos hm hu n) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hn))))

/-! ## Reflected likelihood and Jeffreys information -/

/-- **(CDW.19)** `log(dP_u/dP_{-u})(n) = 2u log n + F(-u) - F(u)`. -/
theorem log_shellTilt_div (hm : 1 ≤ m) {u : ℝ} (hu₁ : 1 < σ - u) (hu₂ : 1 < σ + u) (n : EulerShell m) :
    Real.log (shellTilt m σ u n / shellTilt m σ (-u) n) =
      2 * u * Real.log (n : ℕ) + shellLogPartition m σ (-u) - shellLogPartition m σ u := by
  have hn := eulerShell_cast_pos n
  have hS₁ := eulerShellSum_pos hm hu₁
  have hS₂ := eulerShellSum_pos hm (show 1 < σ - -u by linarith)
  rw [shellTilt, shellTilt, Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) hS₁.ne', Real.log_div (by positivity) hS₂.ne', Real.log_rpow hn,
    Real.log_rpow hn, shellLogPartition, shellLogPartition]
  ring

/-- Discrete Kullback–Leibler divergence `D(P‖Q) = Σ_n P(n) log(P(n)/Q(n))`. -/
def shellKL (P Q : EulerShell m → ℝ) : ℝ := ∑' n, P n * Real.log (P n / Q n)

variable (m σ) in
/-- **(CDW.20)** Reflected Jeffreys information `J_m(u) = D(P_u‖P_{-u}) + D(P_{-u}‖P_u)`. -/
def shellJeffreys (u : ℝ) : ℝ :=
  shellKL (shellTilt m σ u) (shellTilt m σ (-u)) + shellKL (shellTilt m σ (-u)) (shellTilt m σ u)

theorem shellKL_tilt (hm : 1 ≤ m) {u : ℝ} (hu₁ : 1 < σ - u) (hu₂ : 1 < σ + u) :
    shellKL (shellTilt m σ u) (shellTilt m σ (-u)) =
      2 * u * shellTiltMean m σ u + shellLogPartition m σ (-u) - shellLogPartition m σ u := by
  have hℓ : HasSum (fun n => shellTilt m σ u n * Real.log (n : ℕ)) (shellTiltMean m σ u) := by
    rw [shellTiltMean_eq (m := m) hu₁]
    simpa using hasSum_shellTilt_mul_log_pow (m := m) 1 hu₁
  have h := (hℓ.mul_left (2 * u)).add ((hasSum_shellTilt hm hu₁).mul_left
    (shellLogPartition m σ (-u) - shellLogPartition m σ u))
  rw [shellKL, show (∑' n, shellTilt m σ u n * Real.log (shellTilt m σ u n / shellTilt m σ (-u) n)) =
      ∑' n, (2 * u * (shellTilt m σ u n * Real.log (n : ℕ)) +
        (shellLogPartition m σ (-u) - shellLogPartition m σ u) * shellTilt m σ u n) from
      tsum_congr fun n => by rw [log_shellTilt_div hm hu₁ hu₂]; ring, h.tsum_eq]
  ring

/-- **(CDW.20)** `J_m(u) = 2u(F'(u) - F'(-u))`. -/
theorem shellJeffreys_eq (hm : 1 ≤ m) {u : ℝ} (hu₁ : 1 < σ - u) (hu₂ : 1 < σ + u) :
    shellJeffreys m σ u = 2 * u * (shellTiltMean m σ u - shellTiltMean m σ (-u)) := by
  have h₁ := shellKL_tilt hm hu₁ hu₂
  have h₂ := shellKL_tilt (σ := σ) hm (u := -u) (by linarith) (by linarith)
  rw [neg_neg] at h₂
  rw [shellJeffreys, h₁, h₂]
  ring

/-! ## The mean-value bound -/

variable (m σ) in
/-- **(CDW.21)** `M_{u₀} = sup_{|s| ≤ u₀} F''(s)`. -/
def shellVarSup (u₀ : ℝ) : ℝ := sSup (shellTiltVar m σ '' Icc (-u₀) u₀)

theorem continuousOn_shellTiltVar (hm : 1 ≤ m) {u₀ : ℝ} (hu₀ : 1 < σ - u₀) :
    ContinuousOn (shellTiltVar m σ) (Icc (-u₀) u₀) := by
  have hreg : ∀ s ∈ Icc (-u₀) u₀, 1 < σ - s := fun s hs => by linarith [hs.2]
  have hc : ContinuousOn (fun s => eulerShellMoment m 2 (σ - s) / eulerShellMoment m 0 (σ - s) -
      (eulerShellMoment m 1 (σ - s) / eulerShellMoment m 0 (σ - s)) ^ 2) (Icc (-u₀) u₀) := fun s hs => by
    have h0 := (hasDerivAt_eulerShellMoment_sub m 0 (hreg s hs)).continuousAt
    have h1 := (hasDerivAt_eulerShellMoment_sub m 1 (hreg s hs)).continuousAt
    have h2 := (hasDerivAt_eulerShellMoment_sub m 2 (hreg s hs)).continuousAt
    have hne := (eulerShellMoment_zero_pos hm (hreg s hs)).ne'
    exact ((h2.div h0 hne).sub ((h1.div h0 hne).pow 2)).continuousWithinAt
  exact hc.congr fun s hs => shellTiltVar_eq hm (hreg s hs)

theorem shellTiltVar_le_shellVarSup (hm : 1 ≤ m) {u₀ : ℝ} (hu₀ : 1 < σ - u₀) {s : ℝ} (hs : s ∈ Icc (-u₀) u₀) :
    shellTiltVar m σ s ≤ shellVarSup m σ u₀ :=
  le_csSup (isCompact_Icc.bddAbove_image (continuousOn_shellTiltVar hm hu₀)) ⟨s, hs, rfl⟩

/-- **(CDW.21)** `M_{u₀}` is a finite positive number. -/
theorem shellVarSup_pos (hm : 1 ≤ m) {u₀ : ℝ} (hu₀ : 1 < σ - u₀) (hu₀' : 0 ≤ u₀) : 0 < shellVarSup m σ u₀ :=
  (shellTiltVar_pos hm (by linarith : 1 < σ - 0)).trans_le
    (shellTiltVar_le_shellVarSup hm hu₀ ⟨by linarith, hu₀'⟩)

theorem shellJeffreys_neg (hm : 1 ≤ m) {u : ℝ} (hu₁ : 1 < σ - u) (hu₂ : 1 < σ + u) :
    shellJeffreys m σ (-u) = shellJeffreys m σ u := by
  rw [shellJeffreys_eq (σ := σ) hm (u := -u) (by linarith) (by linarith), shellJeffreys_eq hm hu₁ hu₂, neg_neg]
  ring

theorem shellJeffreys_pos_le_of_pos (hm : 1 ≤ m) {u₀ : ℝ} (hu₀ : 1 < σ - u₀) {u : ℝ} (hu : 0 < u) (hle : u ≤ u₀) :
    0 < shellJeffreys m σ u ∧ shellJeffreys m σ u ≤ 4 * shellVarSup m σ u₀ * u ^ 2 := by
  have hreg : ∀ s ∈ Icc (-u) u, 1 < σ - s := fun s hs => by linarith [hs.2]
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (shellTiltMean m σ) (shellTiltVar m σ)
    (by linarith : -u < u)
    (fun s hs => (hasDerivAt_shellTiltMean hm (hreg s hs)).continuousAt.continuousWithinAt)
    (fun s hs => hasDerivAt_shellTiltMean hm (hreg s (Ioo_subset_Icc_self hs)))
  have hdiff : shellTiltMean m σ u - shellTiltMean m σ (-u) = 2 * u * shellTiltVar m σ c := by
    rw [hslope]
    field_simp
    ring
  have hJ : shellJeffreys m σ u = 4 * u ^ 2 * shellTiltVar m σ c := by
    rw [shellJeffreys_eq (σ := σ) hm (by linarith) (by linarith), hdiff]
    ring
  have hcI : c ∈ Icc (-u₀) u₀ := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hvar := shellTiltVar_pos hm (hreg c (Ioo_subset_Icc_self hc))
  refine ⟨by rw [hJ]; positivity, ?_⟩
  rw [hJ]
  have := shellTiltVar_le_shellVarSup hm hu₀ hcI
  nlinarith [sq_nonneg u]

/-- **(CDW.22)** `0 < J_m(u) ≤ 4 M_{u₀} u²` for `0 < |u| ≤ u₀`. -/
theorem shellJeffreys_pos_le (hm : 1 ≤ m) {u₀ : ℝ} (hu₀ : 1 < σ - u₀) {u : ℝ} (hu : u ≠ 0) (hle : |u| ≤ u₀) :
    0 < shellJeffreys m σ u ∧ shellJeffreys m σ u ≤ 4 * shellVarSup m σ u₀ * u ^ 2 := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have h := shellJeffreys_pos_le_of_pos hm hu₀ (neg_pos.2 hneg) (by rw [abs_of_neg hneg] at hle; exact hle)
    rw [shellJeffreys_neg (σ := σ) hm (by rw [abs_of_neg hneg] at hle; linarith)
      (by rw [abs_of_neg hneg] at hle; linarith), neg_sq] at h
    exact h
  · exact shellJeffreys_pos_le_of_pos hm hu₀ hpos (by rwa [abs_of_pos hpos] at hle)

/-! ## Work cusp versus information -/

/-- **(CDW.23)** `𝔠_pair(u,T) = 4|u|/T²` for `|u| ≤ T`. -/
theorem pairWork_of_le {u T : ℝ} (h : |u| ≤ T) : pairWork u T = 4 * |u| / T ^ 2 := by
  rw [pairWork, min_eq_left h]

/-- **(CDW.24)** `𝔠_pair(u,T)/J_m(u) ≥ 1/(M_{u₀} T² |u|)` for `0 < |u| ≤ min(u₀, T)`. -/
theorem pairWork_div_shellJeffreys_ge (hm : 1 ≤ m) {u₀ T : ℝ} (hu₀ : 1 < σ - u₀) (hT : 0 < T) {u : ℝ} (hu : u ≠ 0)
    (hle : |u| ≤ u₀) (hleT : |u| ≤ T) :
    1 / (shellVarSup m σ u₀ * T ^ 2 * |u|) ≤ pairWork u T / shellJeffreys m σ u := by
  obtain ⟨hJ, hJle⟩ := shellJeffreys_pos_le hm hu₀ hu hle
  have hM := shellVarSup_pos hm hu₀ ((abs_nonneg u).trans hle)
  have habs : 0 < |u| := abs_pos.2 hu
  rw [pairWork_of_le hleT]
  calc 1 / (shellVarSup m σ u₀ * T ^ 2 * |u|) = (4 * |u| / T ^ 2) / (4 * shellVarSup m σ u₀ * u ^ 2) := by
        rw [← sq_abs u]
        field_simp
    _ ≤ (4 * |u| / T ^ 2) / shellJeffreys m σ u :=
        div_le_div_of_nonneg_left (by positivity) hJ hJle

/-- **(CDW.24)** `𝔠_pair(u,T)/J_m(u) → ∞` as `u → 0`, `u ≠ 0`: information underprices causal work. -/
theorem tendsto_pairWork_div_shellJeffreys (hm : 1 ≤ m) {u₀ T : ℝ} (hu₀ : 1 < σ - u₀) (hu₀' : 0 < u₀) (hT : 0 < T) :
    Tendsto (fun u => pairWork u T / shellJeffreys m σ u) (𝓝[≠] 0) atTop := by
  have hM := shellVarSup_pos hm hu₀ hu₀'.le
  have hlow : Tendsto (fun u : ℝ => (shellVarSup m σ u₀ * T ^ 2)⁻¹ * |u|⁻¹) (𝓝[≠] 0) atTop :=
    (tendsto_inv_nhdsGT_zero.comp tendsto_abs_nhdsNE_zero).const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' _ ?_ hlow
  have hball : ∀ᶠ u in 𝓝[≠] (0 : ℝ), |u| < min u₀ T := by
    have h : ∀ᶠ u in 𝓝 (0 : ℝ), u ∈ Metric.ball (0 : ℝ) (min u₀ T) :=
      Metric.ball_mem_nhds 0 (lt_min hu₀' hT)
    exact nhdsWithin_le_nhds (h.mono fun u hu => by simpa [Real.dist_eq] using hu)
  filter_upwards [hball, self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
  have h := pairWork_div_shellJeffreys_ge hm hu₀ hT hu0 (hu.le.trans (min_le_left _ _))
    (hu.le.trans (min_le_right _ _))
  rw [one_div, mul_inv] at h
  exact h

/-- **(CDW.25)** `J_m(u) = O(u²)` at `0`. -/
theorem shellJeffreys_isBigO (hm : 1 ≤ m) {u₀ : ℝ} (hu₀ : 1 < σ - u₀) (hu₀' : 0 < u₀) :
    shellJeffreys m σ =O[𝓝 0] fun u => u ^ 2 := by
  refine IsBigO.of_bound (4 * shellVarSup m σ u₀) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hu₀'] with u hu
  have hu' : |u| < u₀ := by simpa [Real.dist_eq] using hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg u)]
  by_cases h0 : u = 0
  · subst h0
    rw [shellJeffreys_eq (σ := σ) hm (by linarith) (by linarith)]
    simp
  · obtain ⟨hJ, hJle⟩ := shellJeffreys_pos_le hm hu₀ h0 hu'.le
    rw [abs_of_pos hJ]
    exact hJle

/-- **(CDW.25)** `𝔠_pair(u,T) = Θ(|u|)` at `0`. -/
theorem pairWork_isTheta {T : ℝ} (hT : 0 < T) : (fun u => pairWork u T) =Θ[𝓝 0] fun u => |u| := by
  have heq : (fun u => pairWork u T) =ᶠ[𝓝 0] fun u => (4 / T ^ 2) * |u| := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hT] with u hu
    have hu' : |u| ≤ T := by
      have h := Metric.mem_ball.1 hu
      rw [Real.dist_eq, sub_zero] at h
      exact h.le
    rw [pairWork_of_le hu']
    ring
  exact heq.trans_isTheta ((isTheta_const_mul_left (by positivity)).2 (isTheta_refl _ _))

end GaloisForLFunctions.HTGeometry
