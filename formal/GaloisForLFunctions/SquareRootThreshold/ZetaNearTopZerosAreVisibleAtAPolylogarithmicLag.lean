import GaloisForLFunctions.SquareRootThreshold.ZetaNearTopZerosAreVisibleBelowAnExplicitHeight

/-!
# Near-top zeros of `ζ` are visible at a polylogarithmic lag

`zeta_near_top_visible` holds under numeric conditions on a Fejér order `k`, a core scale `ρ`, a gap
`G` and a phase scale `H₀`. Here they are chosen explicitly (`κ₀ = 1`), through definitions that only
see a record bound `a`, a neighbour bound `D` and a noise constant `M`:

* `P = ⌈80 log(180Γ)⌉` companions (`explicitCount`), `Γ = recordHeightEnvelope w γ₀ ≍ γ₀`;
* `ρV = c = a/(10(P + 1)D + a)` (`explicitCoherence`), with `a = a_w²/(2e)` and `D ≍ log Γ`, so the
  kernels and phases move by `O(c)` over the core and the core mass is `≤ |D*|/2`;
* `G = 20(P + 1)²/c` (`explicitGap`): the eliminated factors move by at most `c`
  (`coreFactorPerturbation_le`);
* `k = P + ⌈log₂ Y⌉ + 1` (`explicitOrder`), `Y = 4(160π²/3)^P (2P)! M/q^P`, `q = c/(2(P + 1)G^P)`
  (`explicitRatio`), `M = A_w log(180(Γ + 6))`, so that the elimination noise is beaten
  (`collapse_form_lt`);
* `V ≥ V_w(γ₀, δ₀) = (8/δ₀)(13πk + 4 + |log(160 log(180Γ)(e^{w/2}B_w)²/a_w²)|) + w + 8we^{w/2}J_w/H₀`.

**Theorem** (`zeta_near_top_visible_at_polylog_lag`). A zero `½ + z₀`, `δ₀ = Re z₀ > 0`, at height
`γ₀ ≥ T_w` with `1280 log(180Γ)(e^{w/2}B_w)² ≤ a(1 + γ₀)⁴`, which is `1/V`-near the top for some
`V ≥ V_w(γ₀, δ₀)`, makes a difference test of the bump modulated to `γ₀` Weil negative at a lag in
`[0, V]`. Since `log Y ≍ P² log G ≍ (log γ₀)² log log γ₀`,
`V_w(γ₀, δ₀) ≍_w (log γ₀)² log log γ₀/δ₀`. The top need not be attained.

**Depth gap** (`zeta_depth_gap_of_lag_positivity`). If those tests are Weil nonnegative on `[0, V]`
with `V ≥ V_w(γ₀, δ₀)`, some zero lies more than `1/V` to the right of `½ + z₀`. An unattained
top is therefore approached only by zeros whose heights escape: a zero of depth `δ` at height `γ`
lies at least `1/V_w(γ, δ) ≍ δ/((log γ)² log log γ)` below the top.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Elementary bounds -/

/-- `(1 + t)^n − 1 ≤ 2nt` for `t ≥ 0` and `nt ≤ 1/2`. -/
theorem one_add_pow_sub_one_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (hnt : n * t ≤ 1 / 2) :
    (1 + t) ^ n - 1 ≤ 2 * (n * t) := by
  have h1 : (1 + t) ^ n ≤ Real.exp (n * t) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) n
  have hx0 : 0 ≤ (n : ℝ) * t := by positivity
  have h2 := Real.exp_bound_div_one_sub_of_interval hx0 (by linarith)
  have h3 : 1 / (1 - n * t) ≤ 1 + 2 * (n * t) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- `k^n ≤ n! e^k`. -/
theorem natCast_pow_le_factorial_mul_exp (k n : ℕ) :
    (k : ℝ) ^ n ≤ n.factorial * Real.exp 1 ^ k := by
  have h := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) n
  rw [div_le_iff₀ (by positivity)] at h
  have e : Real.exp (k : ℝ) = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul, mul_one]
  rw [e] at h
  linarith

/-- `Y < 2^{P + ⌈log₂ Y⌉ + 1}` for `Y > 0`. -/
theorem lt_two_pow_add_ceil_logb {Y : ℝ} (hY : 0 < Y) (P : ℕ) :
    Y < 2 ^ (P + ⌈Real.logb 2 Y⌉₊ + 1) := by
  have h1 : Y ≤ 2 ^ ⌈Real.logb 2 Y⌉₊ := by
    calc Y = (2 : ℝ) ^ Real.logb 2 Y := (Real.rpow_logb (by norm_num) (by norm_num) hY).symm
      _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 Y⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = 2 ^ ⌈Real.logb 2 Y⌉₊ := Real.rpow_natCast _ _
  have h2 : (1 : ℝ) ≤ 2 ^ P := one_le_pow₀ (by norm_num)
  have h3 : (0 : ℝ) ≤ 2 ^ ⌈Real.logb 2 Y⌉₊ := by positivity
  rw [pow_succ, pow_add]
  nlinarith

/-- **The collapse bound is beaten.** For `p ≤ P ≤ k`, `k ≥ 1`, `0 < q ≤ 1`, `X ≥ 13πk`, `M > 0` and
`4(160π²/3)^P (2P)! M < 2^k q^P`: `2(8/3)^p(4/3)^k · 2 · (4 + 4π²(k + p)²)^{k+p} M < q^p X^{2k+1}`.
The factor `(4 + 4π²(k + p)²)^{k+p} ≤ (20π²k²)^{k+P}` is paid by `X^{2k} ≥ (169π²k²)^k` up to
`k^{2P} ≤ (2P)! e^k` and `2 · (4/3) · 20π² e ≤ 169π²`. -/
theorem collapse_form_lt {p P k : ℕ} (hpP : p ≤ P) (hPk : P ≤ k) (hk : 1 ≤ k)
    {q X AL : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hX : 13 * π * k ≤ X) (hAL : 0 < AL)
    (hY : 4 * (160 * π ^ 2 / 3) ^ P * (2 * P).factorial * AL < 2 ^ k * q ^ P) :
    2 * ((8 / 3) ^ p * (4 / 3) ^ k * 2 * (4 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) * AL) <
      q ^ p * X ^ (2 * k + 1) := by
  have hπ : 3 < π := Real.pi_gt_three
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 20 * π ^ 2 * (k : ℝ) ^ 2 := ⟨_, rfl⟩
  have hπ2 : 9 ≤ π ^ 2 := by nlinarith
  have hk2 : 1 ≤ (k : ℝ) ^ 2 := by nlinarith
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith
  have hbase : 4 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 ≤ M := by
    have hpk : (p : ℝ) ≤ k := by exact_mod_cast hpP.trans hPk
    have hkp : ((k + p : ℕ) : ℝ) ≤ 2 * k := by push_cast; linarith
    have h0 : (0 : ℝ) ≤ ((k + p : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : ((k + p : ℕ) : ℝ) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
    have h3 : 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 ≤ 16 * π ^ 2 * (k : ℝ) ^ 2 := by nlinarith
    have h4 : 4 ≤ 4 * π ^ 2 * (k : ℝ) ^ 2 := by nlinarith
    rw [hM]; linarith
  have hpow1 : (4 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) ≤ M ^ (k + P) :=
    (pow_le_pow_left₀ (by positivity) hbase _).trans (pow_le_pow_right₀ hM1 (by omega))
  have h83 : ((8 : ℝ) / 3) ^ p ≤ (8 / 3) ^ P := pow_le_pow_right₀ (by norm_num) hpP
  have hfact := natCast_pow_le_factorial_mul_exp k (2 * P)
  have hMsplit : M ^ (k + P) = (20 * π ^ 2) ^ k * (20 * π ^ 2) ^ P * ((k : ℝ) ^ 2) ^ k *
      (k : ℝ) ^ (2 * P) := by
    rw [hM, pow_add]; simp only [mul_pow]; ring
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (4 / 3 * (20 * π ^ 2) * Real.exp 1) ^ k * ((k : ℝ) ^ 2) ^ k :=
    ⟨_, rfl⟩
  have hW0 : 0 < W := by rw [hW]; positivity
  have hAL0 := hAL.le
  -- the bound is at most `4(160π²/3)^P (2P)! AL · W`
  have hup : 2 * ((8 / 3) ^ p * (4 / 3) ^ k * 2 * (4 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) *
      AL) ≤ 4 * (160 * π ^ 2 / 3) ^ P * (2 * P).factorial * AL * W := by
    calc 2 * ((8 / 3) ^ p * (4 / 3) ^ k * 2 * (4 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) * AL)
        ≤ 2 * ((8 / 3) ^ P * (4 / 3) ^ k * 2 * M ^ (k + P) * AL) := by gcongr
      _ = 2 * ((8 / 3) ^ P * (4 / 3) ^ k * 2 * ((20 * π ^ 2) ^ k * (20 * π ^ 2) ^ P *
            ((k : ℝ) ^ 2) ^ k * (k : ℝ) ^ (2 * P)) * AL) := by rw [hMsplit]
      _ ≤ 2 * ((8 / 3) ^ P * (4 / 3) ^ k * 2 * ((20 * π ^ 2) ^ k * (20 * π ^ 2) ^ P *
            ((k : ℝ) ^ 2) ^ k * ((2 * P).factorial * Real.exp 1 ^ k)) * AL) := by gcongr
      _ = 4 * (160 * π ^ 2 / 3) ^ P * (2 * P).factorial * AL * W := by
          rw [hW, show (160 * π ^ 2 / 3 : ℝ) = 8 / 3 * (20 * π ^ 2) by ring]
          simp only [mul_pow]
          ring
  -- the right side is at least `2^k q^P W`
  have hX1 : 1 ≤ X := le_trans (by nlinarith) hX
  have hX2 : 169 * π ^ 2 * (k : ℝ) ^ 2 ≤ X ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hX 2
    nlinarith
  have he : 2 * (4 / 3 * (20 * π ^ 2) * Real.exp 1) ≤ 169 * π ^ 2 := by
    have := Real.exp_one_lt_d9
    nlinarith
  have hlow : 2 ^ k * q ^ P * W ≤ q ^ p * X ^ (2 * k + 1) := by
    have hqp : q ^ P ≤ q ^ p := pow_le_pow_of_le_one hq.le hq1 hpP
    calc 2 ^ k * q ^ P * W = q ^ P * ((2 * (4 / 3 * (20 * π ^ 2) * Real.exp 1)) ^ k *
          ((k : ℝ) ^ 2) ^ k) := by rw [hW]; simp only [mul_pow]; ring
      _ ≤ q ^ P * ((169 * π ^ 2) ^ k * ((k : ℝ) ^ 2) ^ k) := by gcongr
      _ = q ^ P * (169 * π ^ 2 * (k : ℝ) ^ 2) ^ k := by simp only [mul_pow]
      _ ≤ q ^ P * (X ^ 2) ^ k := by gcongr
      _ = q ^ P * X ^ (2 * k) := by rw [← pow_mul]
      _ ≤ q ^ p * X ^ (2 * k + 1) :=
          mul_le_mul hqp (pow_le_pow_right₀ hX1 (by omega)) (by positivity) (by positivity)
  have hmid : 4 * (160 * π ^ 2 / 3) ^ P * (2 * P).factorial * AL * W < 2 ^ k * q ^ P * W :=
    mul_lt_mul_of_pos_right hY hW0
  linarith

/-- At `κ₀ = 1` the collapse bound is `(8/3)^p(4/3)^k · 2 · (4 + 4π²(k + p)²)^{k+p} A_w log(180(Γ + 6))`. -/
theorem clusterCollapseBound_one (w γ₀ : ℝ) (k p : ℕ) :
    clusterCollapseBound w γ₀ 1 k p = (8 / 3) ^ p * (4 / 3) ^ k * 2 *
      (4 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) *
        (twinTightConstant w * Real.log (180 * (recordHeightEnvelope w γ₀ + 6))) := by
  rw [clusterCollapseBound]; ring

/-! ### The explicit parameters -/

/-- The companion count `P(Γ) = ⌈80 log(180Γ)⌉`. -/
def explicitCount (Γ : ℝ) : ℕ := ⌈80 * Real.log (180 * Γ)⌉₊

/-- The coherence product `c = ρV = a/(10(P + 1)D + a)` for a record coefficient `≥ a` and
neighbouring coefficients `≤ D`. -/
def explicitCoherence (a D : ℝ) (P : ℕ) : ℝ := a / (10 * (P + 1) * D + a)

/-- The annulus gap `G = 20(P + 1)²/c`. -/
def explicitGap (c : ℝ) (P : ℕ) : ℝ := 20 * (P + 1) ^ 2 / c

/-- The loose-factor ratio `q = c/(2(P + 1)G^P)`. -/
def explicitRatio (c : ℝ) (P : ℕ) : ℝ := c / (2 * (P + 1) * explicitGap c P ^ P)

/-- The Fejér order `k = P + ⌈log₂ Y⌉ + 1`, `Y = 4(160π²/3)^P (2P)! M/q^P`. -/
def explicitOrder (M c : ℝ) (P : ℕ) : ℕ :=
  P + ⌈Real.logb 2 (4 * (160 * π ^ 2 / 3) ^ P * (2 * P).factorial * M / explicitRatio c P ^ P)⌉₊ + 1

/-- The perturbation of the eliminated factors at `κ₀ = 1`, `ρ = c/V`, `G = 20(P + 1)²/c` is at most
`c`. -/
theorem coreFactorPerturbation_le {c V : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hV : 0 < V) (P : ℕ) :
    coreFactorPerturbation P 1 V (c / V) (explicitGap c P) ≤ c := by
  unfold coreFactorPerturbation explicitGap
  have hP1 : (0 : ℝ) < P + 1 := by positivity
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ,
      t₀ = (4 * 1 / V + c / V) * (2 * (P + 1) * V) / (20 * (P + 1) ^ 2 / c * 1) := ⟨_, rfl⟩
  rw [← ht₀]
  have e : t₀ = (4 + c) * c / (10 * (P + 1)) := by rw [ht₀]; field_simp; ring
  have ht0 : 0 ≤ t₀ := by rw [e]; positivity
  have hle : (P + 1) * t₀ ≤ c / 2 := by
    rw [e]
    have : (P + 1) * ((4 + c) * c / (10 * (P + 1))) = (4 + c) * c / 10 := by field_simp
    rw [this]; nlinarith
  have hPt : (P : ℝ) * t₀ ≤ (P + 1) * t₀ := by nlinarith
  have h := one_add_pow_sub_one_le ht0 P (by linarith)
  linarith

/-- The arithmetic facts behind the explicit parameters, for `a > 0`, `D ≥ 0`, `M > 0`. -/
theorem explicit_parameter_facts {a D M : ℝ} (ha : 0 < a) (hD : 0 ≤ D) (hM : 0 < M) (P : ℕ) :
    0 < explicitCoherence a D P ∧ explicitCoherence a D P ≤ 1 ∧
      explicitCoherence a D P * (10 * (P + 1) * D) ≤ a ∧
      1 ≤ explicitGap (explicitCoherence a D P) P ∧
      0 < explicitRatio (explicitCoherence a D P) P ∧ explicitRatio (explicitCoherence a D P) P ≤ 1 ∧
      P ≤ explicitOrder M (explicitCoherence a D P) P ∧
      1 ≤ explicitOrder M (explicitCoherence a D P) P ∧
      4 * (160 * π ^ 2 / 3) ^ P * (2 * P).factorial * M <
        2 ^ explicitOrder M (explicitCoherence a D P) P *
          explicitRatio (explicitCoherence a D P) P ^ P := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = explicitCoherence a D P := ⟨_, rfl⟩
  rw [← hc]
  have hden : 0 < 10 * (P + 1) * D + a := by positivity
  have hc0 : 0 < c := by rw [hc, explicitCoherence]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc, explicitCoherence, div_le_one hden]
    have : 0 ≤ 10 * ((P : ℝ) + 1) * D := by positivity
    linarith
  have hca : c * (10 * (P + 1) * D) ≤ a := by
    have e : c * (10 * (P + 1) * D + a) = a := by
      rw [hc, explicitCoherence]; exact div_mul_cancel₀ _ hden.ne'
    have : 0 ≤ c * a := by positivity
    nlinarith
  have hG1 : 1 ≤ explicitGap c P := by
    rw [explicitGap]
    have h1 : (1 : ℝ) ≤ 20 * (P + 1) ^ 2 := by
      have : (1 : ℝ) ≤ (P + 1) ^ 2 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) P])
      linarith
    exact h1.trans (le_div_self (by positivity) hc0 hc1)
  have hq0 : 0 < explicitRatio c P := by
    rw [explicitRatio]; have := pow_pos (lt_of_lt_of_le one_pos hG1) P; positivity
  have hq1 : explicitRatio c P ≤ 1 := by
    rw [explicitRatio]
    have h1 : 1 ≤ 2 * ((P : ℝ) + 1) * explicitGap c P ^ P := by
      have := one_le_pow₀ (n := P) hG1
      nlinarith [Nat.cast_nonneg (α := ℝ) P]
    exact (div_le_self hc0.le h1).trans hc1
  have hY0 : 0 < 4 * (160 * π ^ 2 / 3) ^ P * (2 * P).factorial * M / explicitRatio c P ^ P := by
    positivity
  have hk := lt_two_pow_add_ceil_logb hY0 P
  rw [div_lt_iff₀ (pow_pos hq0 P)] at hk
  refine ⟨hc0, hc1, hca, hG1, hq0, hq1, by rw [explicitOrder]; omega,
    by rw [explicitOrder]; omega, ?_⟩
  rw [explicitOrder]
  exact hk

/-- The coefficient bound `D_w(γ₀) = 80 log(180(Γ + 1))(e^{w/2}B_w)²` near the record. -/
def nearTopMass (w γ₀ : ℝ) : ℝ :=
  80 * Real.log (180 * (recordHeightEnvelope w γ₀ + 1)) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2

/-- The coherence product of the modulated family, with `a = a_w²/(2e)`. -/
def nearTopCoherence (w γ₀ : ℝ) : ℝ :=
  explicitCoherence (centerAmplitude w ^ 2 / (2 * Real.exp 1)) (nearTopMass w γ₀)
    (explicitCount (recordHeightEnvelope w γ₀))

/-- The Fejér order of the modulated family, with `M = A_w log(180(Γ + 6))`. -/
def nearTopOrder (w γ₀ : ℝ) : ℕ :=
  explicitOrder (twinTightConstant w * Real.log (180 * (recordHeightEnvelope w γ₀ + 6)))
    (nearTopCoherence w γ₀) (explicitCount (recordHeightEnvelope w γ₀))

/-- The phase-coherence scale `H₀ = (a/(80 log(180Γ)))^{1/2}`. -/
def nearTopScale (w γ₀ : ℝ) : ℝ :=
  Real.sqrt (centerAmplitude w ^ 2 / (2 * Real.exp 1) / (80 * Real.log (180 * recordHeightEnvelope w γ₀)))

/-- The lag `V_w(γ₀, δ₀) = (8/δ₀)(13πk + 4 + |log(160 log(180Γ)(e^{w/2}B_w)²/a_w²)|) + w +
8w e^{w/2} J_w/H₀`. -/
def nearTopLag (w γ₀ δ₀ : ℝ) : ℝ :=
  8 / δ₀ * (13 * π * nearTopOrder w γ₀ + 4 +
    |Real.log (160 * Real.log (180 * recordHeightEnvelope w γ₀) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)|) +
    w + 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScale w γ₀

/-! ### Visibility at an explicit lag -/

/-- **Near-top zeros of `ζ` are visible at an explicit polylogarithmic lag.** Let `½ + z₀` be a zero
right of the line, `δ₀ = Re z₀`, at height `γ₀ = Im z₀ ≥ T_w` with
`1280 log(180Γ)(e^{w/2}B_w)² ≤ (a_w²/(2e))(1 + γ₀)⁴`, let `V ≥ V_w(γ₀, δ₀)` (`nearTopLag`) and let
`½ + z₀` be `1/V`-near the top: `Re ρ − ½ ≤ δ₀ + 1/V` for every zero. Then some difference test of
the bump modulated to `γ₀` is Weil negative at a lag `v ∈ [0, V]`.

`V_w(γ₀, δ₀) ≍_w (log γ₀)² log log γ₀/δ₀`: `P ≍ log γ₀`, `G ≍ log⁴ γ₀`, and the Fejér order is
`k = P + ⌈log₂ Y⌉ + 1` with `log Y ≍ P² log G`. -/
theorem zeta_near_top_visible_at_polylog_lag {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (hγ : 1280 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) * (1 + z₀.im) ^ 4)
    {V : ℝ} (hV : nearTopLag w z₀.im z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re < 0 := by
  have hγ₀1 : 1 ≤ z₀.im := le_trans (by
    unfold nearTopHeight
    have : 0 ≤ 700000 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2 := by
      positivity
    linarith only [this]) hTw
  have hΓ0 : 2 * z₀.im ≤ recordHeightEnvelope w z₀.im := le_max_left _ _
  have ha0 : 0 < centerAmplitude w ^ 2 / (2 * Real.exp 1) := by
    have := centerAmplitude_pos hw; positivity
  have hDm0 : 0 ≤ nearTopMass w z₀.im := by
    unfold nearTopMass
    have : 0 ≤ Real.log (180 * (recordHeightEnvelope w z₀.im + 1)) :=
      Real.log_nonneg (by linarith only [hΓ0, hγ₀1])
    positivity
  have hAL : 0 < twinTightConstant w * Real.log (180 * (recordHeightEnvelope w z₀.im + 6)) := by
    have h1 : 0 < twinTightConstant w := by
      unfold twinTightConstant
      have hC := xiLineTwoLogDerivConstant_nonneg
      have : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
      have := centerAmplitude_pos hw
      positivity
    exact mul_pos h1 (Real.log_pos (by linarith only [hΓ0, hγ₀1]))
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = explicitCount (recordHeightEnvelope w z₀.im) := ⟨_, rfl⟩
  obtain ⟨hc0, hc1, hca, hG1, hq0, hq1, hPk, hk1, hY⟩ := explicit_parameter_facts ha0 hDm0 hAL P
  obtain ⟨c, hc⟩ : ∃ c : ℝ,
      c = explicitCoherence (centerAmplitude w ^ 2 / (2 * Real.exp 1)) (nearTopMass w z₀.im) P :=
    ⟨_, rfl⟩
  rw [← hc] at hc0 hc1 hca hG1 hq0 hq1 hPk hk1 hY
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = explicitOrder
      (twinTightConstant w * Real.log (180 * (recordHeightEnvelope w z₀.im + 6))) c P := ⟨_, rfl⟩
  rw [← hk] at hPk hk1 hY
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = explicitGap c P := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = explicitRatio c P := ⟨_, rfl⟩
  have hqe : q = c / (2 * (P + 1) * G ^ P) := by rw [hq, explicitRatio, ← hG]
  rw [← hG] at hG1
  rw [← hq] at hq0 hq1 hY
  have hkk : nearTopOrder w z₀.im = k := by rw [hk, hc, hP]; rfl
  obtain ⟨H₀, hH₀⟩ : ∃ H₀ : ℝ, H₀ = nearTopScale w z₀.im := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) := ⟨_, rfl⟩
  rw [nearTopLag, hkk, ← hH₀, ← hℓ] at hV
  -- basic facts
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1 : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hℓ₁ : 0 < Real.log (180 * recordHeightEnvelope w z₀.im) := Real.log_pos (by linarith)
  have hH₀0 : 0 < H₀ := by rw [hH₀, nearTopScale]; exact Real.sqrt_pos.mpr (by positivity)
  have hH₀sq : H₀ ^ 2 = centerAmplitude w ^ 2 / (2 * Real.exp 1) /
      (80 * Real.log (180 * recordHeightEnvelope w z₀.im)) := by
    rw [hH₀, nearTopScale]; exact Real.sq_sqrt (by positivity)
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hJ'0 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w := mul_nonneg (by positivity) hJ0
  have hπk : 0 ≤ 13 * π * k := by positivity
  have hℓa := abs_nonneg ℓ
  have hT2 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / H₀ := div_nonneg hJ'0 hH₀0.le
  have h8 : 0 ≤ 8 / z₀.re * (13 * π * k + 4 + |ℓ|) := by positivity
  have hVw : w ≤ V := by linarith only [hV, h8, hT2]
  have hV0 : 0 < V := lt_of_lt_of_le hw hVw
  have hVJ : 8 * w * Real.exp (w / 2) * bumpMass w / H₀ ≤ V := by linarith only [hV, h8, hw]
  have hδV : 8 * (13 * π * k + 4 + |ℓ|) ≤ z₀.re * V := by
    have h1 : 8 / z₀.re * (13 * π * k + 4 + |ℓ|) ≤ V := by linarith only [hV, hT2, hw]
    have h2 := mul_le_mul_of_nonneg_left h1 hre₀.le
    have e : z₀.re * (8 / z₀.re * (13 * π * k + 4 + |ℓ|)) = 8 * (13 * π * k + 4 + |ℓ|) := by
      field_simp
    linarith only [h2, e]
  have hδV2 : z₀.re * V ≤ V / 2 := by nlinarith
  have hkP : ((k + P : ℕ) : ℝ) ≤ 2 * k := by
    push_cast; have : (P : ℝ) ≤ k := by exact_mod_cast hPk
    linarith
  have hπkP := mul_le_mul_of_nonneg_left hkP Real.pi_pos.le
  -- the height conditions
  have hB4 : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4 ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) / (80 * Real.log (180 * recordHeightEnvelope w z₀.im)) / 16 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith only [hγ]
  have e1 : centerAmplitude w ^ 2 / (2 * Real.exp 1) / (40 * Real.log (180 * recordHeightEnvelope w z₀.im)) =
      2 * (centerAmplitude w ^ 2 / (2 * Real.exp 1) /
        (80 * Real.log (180 * recordHeightEnvelope w z₀.im))) := by
    field_simp; ring
  have hpos80 : 0 < centerAmplitude w ^ 2 / (2 * Real.exp 1) /
      (80 * Real.log (180 * recordHeightEnvelope w z₀.im)) := by positivity
  have hH : H₀ ^ 2 ≤ centerAmplitude w ^ 2 / (2 * Real.exp 1) /
      (40 * Real.log (180 * recordHeightEnvelope w z₀.im)) -
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4 := by
    rw [hH₀sq, e1]; linarith only [hB4, hpos80]
  have hK : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4 ≤ H₀ ^ 2 / 16 := by
    rw [hH₀sq]; exact hB4
  -- the lag conditions
  have hPceil : 80 * Real.log (180 * recordHeightEnvelope w z₀.im) ≤ P := by
    rw [hP, explicitCount]; exact Nat.le_ceil _
  have hV2 : 2 * ℓ ≤ z₀.re * V := by linarith only [hδV, le_abs_self ℓ, hπk, hℓa]
  have hκV : 2 * 1 / V ≤ z₀.re / 16 := by
    rw [div_le_div_iff₀ hV0 (by norm_num)]; linarith only [hδV, hπk, hℓa]
  have hVk : π * (k + P : ℕ) ≤ V := by linarith only [hπkP, hδV, hδV2, hℓa, hπk]
  have hVr : 4 * π * (k + P : ℕ) ≤ V * (z₀.re / 8) := by
    linarith only [hπkP, hδV, hℓa, hπk]
  -- the core conditions
  have hρ : 0 < c / V := div_pos hc0 hV0
  have hρV : c / V * V ≤ 1 := by rw [div_mul_cancel₀ c hV0.ne']; exact hc1
  have hρw : w * (c / V) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hV0]
    have := mul_le_mul_of_nonneg_left hc1 hw.le
    linarith only [this, hVw]
  have hρL : 8 * w * Real.exp (w / 2) * bumpMass w * (c / V) ≤ H₀ := by
    rw [mul_div_assoc', div_le_iff₀ hV0]
    have h1 : 8 * w * Real.exp (w / 2) * bumpMass w ≤ V * H₀ := by
      have := mul_le_mul_of_nonneg_right hVJ hH₀0.le
      rwa [div_mul_cancel₀ _ hH₀0.ne'] at this
    have h2 := mul_le_mul_of_nonneg_left hc1 hJ'0
    linarith only [h1, h2]
  have hρr : c / V ≤ z₀.re / 16 := by
    rw [div_le_div_iff₀ hV0 (by norm_num)]; linarith only [hδV, hπk, hℓa, hc1]
  have hDm : nearTopMass w z₀.im = 80 * Real.log (180 * (recordHeightEnvelope w z₀.im + 1)) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := rfl
  have hη : ((1 + coreFactorPerturbation P 1 V (c / V) G) * (2 * (c / V * V)) +
      coreFactorPerturbation P 1 V (c / V) G) * ((P + 1) * (80 * Real.log (180 *
        (recordHeightEnvelope w z₀.im + 1)) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2)) ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) / 2 := by
    rw [div_mul_cancel₀ c hV0.ne', ← hDm, hG]
    have hτ := coreFactorPerturbation_le hc0 hc1 hV0 P
    have h1 : coreFactorPerturbation P 1 V (c / V) (explicitGap c P) * (2 * c) ≤ 1 * (2 * c) :=
      mul_le_mul_of_nonneg_right (hτ.trans hc1) (by positivity)
    have hτ' : (1 + coreFactorPerturbation P 1 V (c / V) (explicitGap c P)) * (2 * c) +
        coreFactorPerturbation P 1 V (c / V) (explicitGap c P) ≤ 5 * c := by
      linarith only [h1, hτ]
    have hm : 0 ≤ ((P : ℝ) + 1) * nearTopMass w z₀.im := by positivity
    have h2 := mul_le_mul_of_nonneg_right hτ' hm
    linarith only [h2, hca]
  have hmain : ∀ p : ℕ, p ≤ P → 2 * clusterCollapseBound w z₀.im 1 k p <
      (c / V * 1 / (2 * (P + 1) * G ^ P)) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1) := by
    intro p hp
    have hG0 : 0 < G := lt_of_lt_of_le one_pos hG1
    have hD0 : (2 * ((P : ℝ) + 1) * G ^ P) ≠ 0 := by positivity
    have e : (c / V * 1 / (2 * (P + 1) * G ^ P)) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1) =
        q ^ p * (V * (z₀.re / 8)) ^ (2 * k + 1) := by
      have e0 : c / V * 1 / (2 * (P + 1) * G ^ P) = c / (2 * (P + 1) * G ^ P) / V := by ring
      have hVp : V ^ p ≠ 0 := pow_ne_zero _ hV0.ne'
      rw [hqe, e0, div_pow, show 2 * k + p + 1 = (2 * k + 1) + p by ring, pow_add, mul_pow]
      field_simp
    rw [e]
    have hX : 13 * π * k ≤ V * (z₀.re / 8) := by linarith only [hδV, hℓa]
    rw [clusterCollapseBound_one]
    exact collapse_form_lt hp hPk hk1 hq0 hq1 hX hAL hY
  exact zeta_near_top_visible hw hz₀ hre₀ hTw hV0 htop hPceil hk1 le_rfl (by rw [← hℓ]; exact hV2)
    hκV hVk hVr hH₀0 hH hK
    hρ hG1 hρV hρw hρL hρr hη hmain

/-- **Depth gap below the explicit lag.** Under the height condition of
`zeta_near_top_visible_at_polylog_lag`, if the difference tests of the bump modulated to `γ₀ = Im z₀`
are Weil nonnegative on `[0, V]` and `V ≥ V_w(γ₀, Re z₀)`, then some zero `ρ` has
`Re ρ − ½ > Re z₀ + 1/V`. -/
theorem zeta_depth_gap_of_lag_positivity {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (hγ : 1280 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) * (1 + z₀.im) ^ 4)
    {V : ℝ} (hV : nearTopLag w z₀.im z₀.re ≤ V)
    (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re) :
    ∃ ρ ∈ zetaZeroConfig.carrier, z₀.re + 1 / V < ρ.re - 1 / 2 := by
  by_contra h
  push Not at h
  obtain ⟨v, hv, hneg⟩ := zeta_near_top_visible_at_polylog_lag hw hz₀ hre₀ hTw hγ hV h
  exact absurd (hpos v hv) (not_le.mpr hneg)

end GaloisForLFunctions.SquareRootThreshold
