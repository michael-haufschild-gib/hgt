import GaloisForLFunctions.TransHorizonIncidenceMechanics.FiniteKernelsRepairAPositiveDriftOnlyAtItsPole
import GaloisForLFunctions.RHTower.ZetaDerivResidue

/-!
# The damped Möbius first moment, Leibniz inversion, and the Chebyshev tangent bridge

This module connects the logarithmic-moment and Mellin-cell machinery of
`TransHorizonIncidenceMechanics` (`THIM`) with the Báez–Duarte readout-variance decomposition of
`BezoutValuationIncidence` (`BVI`) and the zeta-residue calculus of `RHTower`:

1. **Mellin-cell pairing at `σ = 1`, log-power mean recursion, and Leibniz derivation law**:
   * At `σ = 1`, the Mellin cell is the pronic weight `Δ_n(1) = 1/(n(n+1))`, so the Mellin-cell
     pairing `Σ_n A_c(n) Δ_n(1)` is identically `firstPronicMoment c`.
   * The mean of the `(k+1)`-st log-power weight is the negative of the `k`-th logarithmic
     pronic moment: `Σ_d (c · log^{k+1})(d)/d = -firstPronicMoment (logPowWeight c k)`.
   * Under Dirichlet convolution on the damped class, `firstPronicMoment` obeys the Leibniz
     derivation law `M(a ⋆ b) = m_b M(a) + m_a M(b)`. For a Dirichlet-invertible pair
     `a ⋆ b = δ₁`, `m_a m_b = 1` and `M(a) = -m_a² M(b)`.

2. **Unit-constant Cauchy–Schwarz bound and readout–variance decomposition**:
   * Because `Σ_{1 ≤ n ≤ T} 1/(n(n+1)) = 1 - 1/(T+1) ≤ 1`, at every horizon `T` the pronic energy
     dominates the squared partial first moment `(Σ_{n≤T} A_c(n)/(n(n+1)))² ≤ E_T(c)`, and the
     dual residual dominates `(1 - 1/(T+1) - Σ_{n≤T} A_c(n)/(n(n+1)))² ≤ Σ_{n≤T} (1 - A_c(n))²/(n(n+1))`,
     whose left-hand sides converge unconditionally as `T → ∞` to `firstPronicMoment c ^ 2` and
     `(1 - firstPronicMoment c) ^ 2`.
   * For every bounded receiver (in particular for `pmPowerDampedRealWeight ε` and
     `negatedMoebiusWeight ε` at every `ε ≥ 1/2`), the infinite-horizon pronic energy and dual
     residual split orthogonally into `firstPronicMoment c ^ 2` (resp. `(1 - firstPronicMoment c) ^ 2`)
     plus the pronic variance `Σ_n (A_c(n+1) - firstPronicMoment c)² / ((n+1)(n+2))`.

3. **Exact first pronic moments of the damped Möbius triplet (`c_ε`, `c'_ε`, `c_{b,ε}`)**:
   * Applying the Dirichlet-inverse Leibniz law to `c_ε ⋆ u_ε = δ₁` (`c_ε(d) = μ(d) d^{-ε}`,
     `u_ε(d) = d^{-ε}`) gives without Euler products:
     `firstPronicMoment (pmPowerDampedRealWeight ε) = dampedDensity ε * Σ_n Λ(n) n^{-(1+ε)} = Re(-ζ'(1+ε)/ζ(1+ε)²) > 0`,
     tending to `1` as `ε → 0+`, and matching the `Q → ∞` limit of the BVI energy mean
     `pmPowerDampedRamanujanEnergyMean ε Q`.
   * For both the parity twin `parityTwinWeight ε` and the first-moment-blind negated Möbius weight
     `negatedMoebiusWeight ε`, the first pronic moment is `-firstPronicMoment (pmPowerDampedRealWeight ε) < 0`,
     tending to `-1` as `ε → 0+`.
   * At every `ε > 0`, the finite-horizon dual-residual gap between `negatedMoebiusWeight ε` and
     `pmPowerDampedRealWeight ε` is `4 Σ_{n≤T} A_{c_ε}(n)/(n(n+1))`, converging to
     `4 * moebiusDampedReadout ε > 0` as `T → ∞`.

4. **Log-power receivers above half damping and the Chebyshev tangent law**:
   * Absorbing `log^k d` into an arbitrary fraction `d^δ` of the damping shows that for every
     `ε > 1/2`, every `c ∈ DampedClass K ε`, and every `k : ℕ`, `ReceiverBounded (logPowWeight c k)`
     holds unconditionally.
   * For `logWeight (pmPowerDampedRealWeight η)`, the centered prefix `A_{c_η · log}(n)` is the
     negated damping derivative `-∂_η A_{c_η}(n)` of the Möbius centered prefix.
-/

open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ### §1. Mellin cell at `σ = 1`, log-power mean recursion, and Leibniz law -/

/-- At `σ = 1`, the Mellin cell `Δ_n(1) = n⁻¹ - (n+1)⁻¹` is the pronic weight `1/(n(n+1))`. -/
theorem mellinCell_one {n : ℕ} (hn : 1 ≤ n) :
    mellinCell 1 n = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [mellinCell, Real.rpow_neg_one, Real.rpow_neg_one]
  field_simp
  ring

/-- Pairing `weightCenteredPrefix` with `mellinCell 1` gives the pronic-weighted prefix at all `n`. -/
theorem weightCenteredPrefix_mul_mellinCell_one (c : ℕ → ℝ) (m : ℝ) (n : ℕ) :
    weightCenteredPrefix c m n * mellinCell 1 n =
      weightCenteredPrefix c m n / ((n : ℝ) * ((n : ℝ) + 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [weightCenteredPrefix_zero]
  · rw [mellinCell_one hn, mul_one_div]

/-- The Mellin-cell pairing `Φ_c(1) = Σ_n A_c(n) Δ_n(1)` is identically `firstPronicMoment c`. -/
theorem tsum_weightCenteredPrefix_mul_mellinCell_one (c : ℕ → ℝ) :
    ∑' n : ℕ, weightCenteredPrefix c (∑' d : ℕ, c d / d) n * mellinCell 1 n =
      firstPronicMoment c :=
  tsum_congr (weightCenteredPrefix_mul_mellinCell_one c _)

@[simp] theorem logPowWeight_zero (c : ℕ → ℝ) : logPowWeight c 0 = c := by
  funext d; simp [logPowWeight]

@[simp] theorem logPowWeight_one (c : ℕ → ℝ) : logPowWeight c 1 = logWeight c := by
  funext d; simp [logPowWeight, logWeight]

/-- **Log-power mean recursion.** The mean of `logPowWeight c (k + 1)` is
`-firstPronicMoment (logPowWeight c k)`. -/
theorem tsum_logPowWeight_succ_div {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (k : ℕ) :
    ∑' d : ℕ, logPowWeight c (k + 1) d / d = -firstPronicMoment (logPowWeight c k) := by
  rw [firstPronicMoment_logPowWeight_eq_tsum hε hc k, neg_neg]
  rfl

/-- The mean of `logWeight c` is `-firstPronicMoment c`. -/
theorem tsum_logWeight_div {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c) :
    ∑' d : ℕ, logWeight c d / d = -firstPronicMoment c := by
  have h := tsum_logPowWeight_succ_div hε hc 0
  simpa using h

/-- Pointwise Leibniz rule for `logWeight` under Dirichlet convolution. -/
theorem logWeight_dirichletConv (a b : ℕ → ℝ) (n : ℕ) :
    logWeight (RHTower.dirichletConv a b) n =
      RHTower.dirichletConv (logWeight a) b n + RHTower.dirichletConv a (logWeight b) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [logWeight, RHTower.dirichletConv]
  · unfold logWeight RHTower.dirichletConv
    rw [sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hq0 : n / d ≠ 0 := fun h => hn (by
      rw [← Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), h, mul_zero])
    have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    rw [← hmul, Real.log_mul (by exact_mod_cast hd0) (by exact_mod_cast hq0)]
    ring

theorem summable_abs_div_of_dampedClass {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) : Summable (fun d : ℕ => |c d / d|) := by
  have hc' : DampedClass K ε (fun d => |c d|) := fun d => by rw [abs_abs]; exact hc d
  exact (summable_div_of_dampedClass hε hc').congr fun d => by rw [abs_div, Nat.abs_cast]

/-- **Leibniz derivation law of `firstPronicMoment` under Dirichlet convolution.** -/
theorem firstPronicMoment_dirichletConv {Ka Kb ε : ℝ} (hε : 0 < ε) {a b : ℕ → ℝ}
    (ha : DampedClass Ka ε a) (hb : DampedClass Kb ε b) :
    firstPronicMoment (RHTower.dirichletConv a b) =
      (∑' q : ℕ, b q / q) * firstPronicMoment a +
        (∑' d : ℕ, a d / d) * firstPronicMoment b := by
  have hε2 : 0 < ε / 2 := by linarith
  have hla := logWeight_mem_dampedClass hε ha
  have hlb := logWeight_mem_dampedClass hε hb
  have ha2 := dampedClass_mono hε2 (by linarith) ha
  have hb2 := dampedClass_mono hε2 (by linarith) hb
  have hsa := summable_div_of_dampedClass hε ha
  have hsb := summable_div_of_dampedClass hε hb
  have hsla := summable_div_of_dampedClass hε2 hla
  have hslb := summable_div_of_dampedClass hε2 hlb
  have hab : HasSum (fun n : ℕ => RHTower.dirichletConv a b n / n)
      ((∑' d : ℕ, a d / d) * (∑' q : ℕ, b q / q)) :=
    hasSum_dirichletConv_div hsa.hasSum hsb.hasSum
      (summable_abs_div_of_dampedClass hε ha) (summable_abs_div_of_dampedClass hε hb)
  have h1 : HasSum (fun n : ℕ => RHTower.dirichletConv (logWeight a) b n / n)
      ((∑' d : ℕ, logWeight a d / d) * (∑' q : ℕ, b q / q)) :=
    hasSum_dirichletConv_div hsla.hasSum hsb.hasSum
      (summable_abs_div_of_dampedClass hε2 hla) (summable_abs_div_of_dampedClass hε2 hb2)
  have h2 : HasSum (fun n : ℕ => RHTower.dirichletConv a (logWeight b) n / n)
      ((∑' d : ℕ, a d / d) * (∑' q : ℕ, logWeight b q / q)) :=
    hasSum_dirichletConv_div hsa.hasSum hslb.hasSum
      (summable_abs_div_of_dampedClass hε2 ha2) (summable_abs_div_of_dampedClass hε2 hlb)
  have ha_abs : DampedClass Ka ε (fun d => |a d|) := fun d => by rw [abs_abs]; exact ha d
  have hb_abs : DampedClass Kb ε (fun d => |b d|) := fun d => by rw [abs_abs]; exact hb d
  have hla_abs := logWeight_mem_dampedClass hε ha_abs
  have hlb_abs := logWeight_mem_dampedClass hε hb_abs
  have h1_abs := (hasSum_dirichletConv_div
    (summable_div_of_dampedClass hε2 hla_abs).hasSum (summable_div_of_dampedClass hε hb_abs).hasSum
    (summable_abs_div_of_dampedClass hε2 hla_abs) (summable_abs_div_of_dampedClass hε hb_abs)).summable
  have h2_abs := (hasSum_dirichletConv_div
    (summable_div_of_dampedClass hε ha_abs).hasSum (summable_div_of_dampedClass hε2 hlb_abs).hasSum
    (summable_abs_div_of_dampedClass hε ha_abs) (summable_abs_div_of_dampedClass hε2 hlb_abs)).summable
  have hlog_ab : Summable (fun n : ℕ => |RHTower.dirichletConv a b n| * Real.log n / n) := by
    refine (h1_abs.add h2_abs).of_nonneg_of_le
      (fun n => by have := Real.log_natCast_nonneg n; positivity) fun n => ?_
    have hle : |RHTower.dirichletConv a b n| ≤
        RHTower.dirichletConv (fun d => |a d|) (fun q => |b q|) n := by
      unfold RHTower.dirichletConv
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => by rw [abs_mul])
    have hmul := mul_le_mul_of_nonneg_right hle (Real.log_natCast_nonneg n)
    have hdiv := div_le_div_of_nonneg_right hmul (Nat.cast_nonneg n)
    refine hdiv.trans_eq ?_
    change logWeight (RHTower.dirichletConv (fun d => |a d|) (fun q => |b q|)) n / n = _
    rw [logWeight_dirichletConv, add_div]
  have htot : HasSum (fun d : ℕ => RHTower.dirichletConv a b d * Real.log d / d)
      ((∑' d : ℕ, logWeight a d / d) * (∑' q : ℕ, b q / q) +
        (∑' d : ℕ, a d / d) * (∑' q : ℕ, logWeight b q / q)) :=
    (h1.add h2).congr_fun fun n => by
      rw [← add_div, ← logWeight_dirichletConv]; rfl
  calc firstPronicMoment (RHTower.dirichletConv a b)
      = -∑' d : ℕ, RHTower.dirichletConv a b d * Real.log d / d :=
        (hasSum_weightCenteredPrefix_div_pronic hab.summable hlog_ab).tsum_eq
    _ = -((∑' d : ℕ, logWeight a d / d) * (∑' q : ℕ, b q / q) +
          (∑' d : ℕ, a d / d) * (∑' q : ℕ, logWeight b q / q)) := by
        rw [htot.tsum_eq]
    _ = (∑' q : ℕ, b q / q) * firstPronicMoment a +
          (∑' d : ℕ, a d / d) * firstPronicMoment b := by
        rw [tsum_logWeight_div hε ha, tsum_logWeight_div hε hb]; ring

theorem unitMass_mem_dampedClass (ε : ℝ) : DampedClass 1 ε unitMass := fun d => by
  unfold unitMass
  split_ifs with hd
  · subst hd; simp
  · simp [Real.rpow_nonneg (Nat.cast_nonneg d)]

@[simp] theorem firstPronicMoment_unitMass : firstPronicMoment unitMass = 0 := by
  have h1 : (0 : ℝ) < 1 := by norm_num
  have h := tsum_logWeight_div h1 (unitMass_mem_dampedClass 1)
  have hzero : ∀ d : ℕ, logWeight unitMass d / d = 0 := fun d => by
    unfold logWeight unitMass
    split_ifs with hd
    · subst hd; simp
    · simp
  simp only [hzero, tsum_zero] at h
  linarith

/-- **Dirichlet-inverse Leibniz law.** If `a ⋆ b = δ₁` in `DampedClass`, then `m_a m_b = 1` and
`M(a) = -m_a² M(b)`. -/
theorem firstPronicMoment_eq_of_dirichletConv_eq_unitMass {Ka Kb ε : ℝ} (hε : 0 < ε)
    {a b : ℕ → ℝ} (ha : DampedClass Ka ε a) (hb : DampedClass Kb ε b)
    (hab : RHTower.dirichletConv a b = unitMass) :
    (∑' d : ℕ, a d / d) * (∑' q : ℕ, b q / q) = 1 ∧
      firstPronicMoment a = -(∑' d : ℕ, a d / d) ^ 2 * firstPronicMoment b := by
  have hm : HasSum (fun n : ℕ => RHTower.dirichletConv a b n / n)
      ((∑' d : ℕ, a d / d) * (∑' q : ℕ, b q / q)) :=
    hasSum_dirichletConv_div (summable_div_of_dampedClass hε ha).hasSum
      (summable_div_of_dampedClass hε hb).hasSum
      (summable_abs_div_of_dampedClass hε ha) (summable_abs_div_of_dampedClass hε hb)
  have hu : HasSum (fun d : ℕ => unitMass d / d) 1 := by
    refine (hasSum_ite_eq (1 : ℕ) (1 : ℝ)).congr_fun fun d => ?_
    by_cases hd : d = 1 <;> simp [unitMass, hd]
  rw [hab] at hm
  have hprod : (∑' d : ℕ, a d / d) * (∑' q : ℕ, b q / q) = 1 := hm.unique hu
  have hleib := firstPronicMoment_dirichletConv hε ha hb
  rw [hab, firstPronicMoment_unitMass] at hleib
  refine ⟨hprod, ?_⟩
  calc firstPronicMoment a
      = ((∑' d : ℕ, a d / d) * (∑' q : ℕ, b q / q)) * firstPronicMoment a := by
        rw [hprod, one_mul]
    _ = (∑' d : ℕ, a d / d) * ((∑' q : ℕ, b q / q) * firstPronicMoment a +
          (∑' d : ℕ, a d / d) * firstPronicMoment b) -
        (∑' d : ℕ, a d / d) ^ 2 * firstPronicMoment b := by ring
    _ = -(∑' d : ℕ, a d / d) ^ 2 * firstPronicMoment b := by
        rw [← hleib]; ring

/-! ### §2. Unit-constant Cauchy–Schwarz bound and readout–variance decomposition -/

/-- Exact telescoping sum of the pronic weights on `[1, T]`. -/
theorem sum_Icc_pronic_mass (T : ℕ) :
    ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) = 1 - 1 / ((T : ℝ) + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    field_simp
    ring

/-- **Finite-horizon Cauchy–Schwarz bound.** For any sequence `f`, the squared pronic pairing on
`[1, T]` is bounded by `(1 - 1/(T+1))` times the pronic energy on `[1, T]`. -/
theorem sq_sum_div_pronic_le (f : ℕ → ℝ) (T : ℕ) :
    (∑ n ∈ Icc 1 T, f n / ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 ≤
      (1 - 1 / ((T : ℝ) + 1)) * ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  set w : ℕ → ℝ := fun n => (n : ℝ) * ((n : ℝ) + 1)
  have hw : ∀ n ∈ Icc 1 T, 0 < w n := fun n hn => by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [w]; positivity
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 T)
    (fun n => 1 / Real.sqrt (w n)) (fun n => f n / Real.sqrt (w n))
  have e1 : ∑ n ∈ Icc 1 T, 1 / Real.sqrt (w n) * (f n / Real.sqrt (w n)) =
      ∑ n ∈ Icc 1 T, f n / w n := sum_congr rfl fun n hn => by
    rw [one_div_mul_eq_div, div_div, Real.mul_self_sqrt (hw n hn).le]
  have e2 : ∑ n ∈ Icc 1 T, (1 / Real.sqrt (w n)) ^ 2 = 1 - 1 / ((T : ℝ) + 1) := by
    rw [← sum_Icc_pronic_mass T]
    exact sum_congr rfl fun n hn => by rw [div_pow, one_pow, Real.sq_sqrt (hw n hn).le]
  have e3 : ∑ n ∈ Icc 1 T, (f n / Real.sqrt (w n)) ^ 2 =
      ∑ n ∈ Icc 1 T, f n ^ 2 / w n := sum_congr rfl fun n hn => by
    rw [div_pow, Real.sq_sqrt (hw n hn).le]
  rw [e1, e2, e3] at hcs
  exact hcs

theorem sq_sum_div_pronic_le_weightPronicEnergy (c : ℕ → ℝ) (m : ℝ) (T : ℕ) :
    (∑ n ∈ Icc 1 T, weightCenteredPrefix c m n / ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 ≤
      weightPronicEnergy c m T := by
  refine (sq_sum_div_pronic_le (weightCenteredPrefix c m) T).trans ?_
  rw [← weightPronicEnergy]
  have hE : 0 ≤ weightPronicEnergy c m T := sum_nonneg fun n _ => by positivity
  have h1 : 1 - 1 / ((T : ℝ) + 1) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
    linarith
  nlinarith

/-- Finite-horizon expansion of the dual residual `Σ_{n≤T} (1 - f(n))²/(n(n+1))`. -/
theorem sum_one_sub_sq_div_pronic (f : ℕ → ℝ) (T : ℕ) :
    ∑ n ∈ Icc 1 T, (1 - f n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      (1 - 1 / ((T : ℝ) + 1)) - 2 * (∑ n ∈ Icc 1 T, f n / ((n : ℝ) * ((n : ℝ) + 1))) +
        ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  rw [← sum_Icc_pronic_mass T, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- Finite-horizon Cauchy–Schwarz lower bound on the dual residual: at every horizon `T`,
`(1 - 1/(T+1) - Σ_{n≤T} f(n)/(n(n+1)))² ≤ Σ_{n≤T} (1 - f(n))²/(n(n+1))`. -/
theorem sq_one_sub_sum_div_pronic_le_dual_residual (f : ℕ → ℝ) (T : ℕ) :
    (1 - 1 / ((T : ℝ) + 1) - ∑ n ∈ Icc 1 T, f n / ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 ≤
      ∑ n ∈ Icc 1 T, (1 - f n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have heq : 1 - 1 / ((T : ℝ) + 1) - ∑ n ∈ Icc 1 T, f n / ((n : ℝ) * ((n : ℝ) + 1)) =
      ∑ n ∈ Icc 1 T, (1 - f n) / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [← sum_Icc_pronic_mass T, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [heq]
  have hcs := sq_sum_div_pronic_le (fun n => 1 - f n) T
  have h1 : 1 - 1 / ((T : ℝ) + 1) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
    linarith
  have hnn : 0 ≤ ∑ n ∈ Icc 1 T, (1 - f n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
    sum_nonneg fun n _ => by positivity
  exact hcs.trans (mul_le_of_le_one_left hnn h1)

/-- For every weight in `DampedClass`, the finite-horizon energy lower bound
`(Σ_{n≤T} A_c(n)/(n(n+1)))²` converges to `firstPronicMoment c ^ 2` and the dual-residual
lower bound `(1 - 1/(T+1) - Σ_{n≤T} A_c(n)/(n(n+1)))²` converges to `(1 - firstPronicMoment c) ^ 2`. -/
theorem tendsto_sq_partial_firstPronicMoment {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) :
    Tendsto (fun T : ℕ =>
        (∑ n ∈ Icc 1 T, weightCenteredPrefix c (∑' d : ℕ, c d / d) n /
          ((n : ℝ) * ((n : ℝ) + 1))) ^ 2)
      atTop (𝓝 (firstPronicMoment c ^ 2)) ∧
    Tendsto (fun T : ℕ =>
        (1 - 1 / ((T : ℝ) + 1) - ∑ n ∈ Icc 1 T, weightCenteredPrefix c (∑' d : ℕ, c d / d) n /
          ((n : ℝ) * ((n : ℝ) + 1))) ^ 2)
      atTop (𝓝 ((1 - firstPronicMoment c) ^ 2)) := by
  set m := ∑' d : ℕ, c d / d
  set A := weightCenteredPrefix c m
  have hhas : HasSum (fun n : ℕ => A n / ((n : ℝ) * ((n : ℝ) + 1))) (firstPronicMoment c) :=
    (hasSum_firstPronicMoment hε hc).summable.hasSum
  have hAlim : Tendsto (fun T : ℕ => ∑ n ∈ Icc 1 T, A n / ((n : ℝ) * ((n : ℝ) + 1)))
      atTop (𝓝 (firstPronicMoment c)) := by
    refine (hhas.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun T => ?_
    simp only [Function.comp_apply]
    rw [dampedSign_sum_range_succ_eq_add_Icc]
    simp [A, weightCenteredPrefix_zero]
  have h1lim : Tendsto (fun T : ℕ => 1 - 1 / ((T : ℝ) + 1)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h
  exact ⟨hAlim.pow 2, (h1lim.sub hAlim).pow 2⟩

/-- **Orthogonal readout–variance decomposition of a bounded receiver.** When `ReceiverBounded c`
holds, the infinite-horizon pronic energy and dual residual decompose orthogonally around
`firstPronicMoment c`. -/
theorem tsum_pronic_energy_and_dual_residual_eq_add_variance {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (hB : ReceiverBounded c) :
    Summable (fun n : ℕ => (weightCenteredPrefix c (∑' d : ℕ, c d / d) (n + 1) -
        firstPronicMoment c) ^ 2 / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) ∧
      (∑' n : ℕ, weightCenteredPrefix c (∑' d : ℕ, c d / d) (n + 1) ^ 2 /
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) =
        firstPronicMoment c ^ 2 +
          ∑' n : ℕ, (weightCenteredPrefix c (∑' d : ℕ, c d / d) (n + 1) -
            firstPronicMoment c) ^ 2 / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) ∧
      (∑' n : ℕ, (1 - weightCenteredPrefix c (∑' d : ℕ, c d / d) (n + 1)) ^ 2 /
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) =
        (1 - firstPronicMoment c) ^ 2 +
          ∑' n : ℕ, (weightCenteredPrefix c (∑' d : ℕ, c d / d) (n + 1) -
            firstPronicMoment c) ^ 2 / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) := by
  obtain ⟨E, hE⟩ := hB
  set m := ∑' d : ℕ, c d / d
  set A := weightCenteredPrefix c m
  set M := firstPronicMoment c
  set w : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)
  have h1 : HasSum (fun n : ℕ => 1 / w n) 1 := by
    have h := RHTower.hasSum_pm_reciprocal_weight
    rw [← hasSum_nat_add_iff' 1] at h
    simpa [w] using h
  have hA1 : HasSum (fun n : ℕ => A (n + 1) / w n) M := by
    have h : HasSum (fun n : ℕ => A n / ((n : ℝ) * ((n : ℝ) + 1))) M :=
      (hasSum_firstPronicMoment hε hc).summable.hasSum
    rw [← hasSum_nat_add_iff' 1] at h
    simpa [A, weightCenteredPrefix_zero, w] using h
  have hsA2 : Summable (fun n : ℕ => A (n + 1) ^ 2 / w n) := by
    refine summable_of_sum_range_le (c := E) (fun n => by positivity) fun T => ?_
    have hrange : ∑ n ∈ range T, A (n + 1) ^ 2 / w n = weightPronicEnergy c m T := by
      induction T with
      | zero => simp [weightPronicEnergy]
      | succ T ih =>
        rw [Finset.sum_range_succ, ih]
        unfold weightPronicEnergy
        rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 T)]
    rw [hrange]
    exact hE T
  set E_inf := ∑' n : ℕ, A (n + 1) ^ 2 / w n
  have hvar : HasSum (fun n : ℕ => (A (n + 1) - M) ^ 2 / w n) (E_inf - M ^ 2) := by
    have h := (hsA2.hasSum.sub (hA1.mul_left (2 * M))).add (h1.mul_left (M ^ 2))
    rw [show E_inf - 2 * M * M + M ^ 2 * 1 = E_inf - M ^ 2 by ring] at h
    exact h.congr_fun fun n => by ring
  have hdual : HasSum (fun n : ℕ => (1 - A (n + 1)) ^ 2 / w n)
      ((1 - M) ^ 2 + (E_inf - M ^ 2)) := by
    have h := (h1.sub (hA1.mul_left 2)).add hsA2.hasSum
    rw [show 1 - 2 * M + E_inf = (1 - M) ^ 2 + (E_inf - M ^ 2) by ring] at h
    exact h.congr_fun fun n => by ring
  refine ⟨hvar.summable, ?_, ?_⟩
  · rw [hvar.tsum_eq]; ring
  · rw [hdual.tsum_eq, hvar.tsum_eq]

/-! ### §3. Exact first pronic moments of the damped Möbius triplet via Leibniz inversion -/

theorem pmPowerDampedRealWeight_mem_dampedClass (ε : ℝ) :
    DampedClass 1 ε (pmPowerDampedRealWeight ε) := fun d => by
  rw [pmPowerDampedRealWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
    one_mul]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (by
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h])

theorem unitSign_mem_dampedClass (ε : ℝ) :
    DampedClass 1 ε (dampedSignWeight unitSign ε) := fun d => by
  rw [dampedSignWeight, unitSign, one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]

/-- `c_ε ⋆ u_ε = δ₁`: the damped Möbius weight and the smooth power `d^{-ε}` are Dirichlet inverses. -/
theorem dirichletConv_pmPowerDamped_unitSign (ε : ℝ) :
    RHTower.dirichletConv (pmPowerDampedRealWeight ε) (dampedSignWeight unitSign ε) = unitMass := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [RHTower.dirichletConv, unitMass]
  · unfold RHTower.dirichletConv pmPowerDampedRealWeight dampedSignWeight unitSign
    have hterm : ∀ d ∈ n.divisors, moebiusReal d * (d : ℝ) ^ (-ε) * (1 * ((n / d : ℕ) : ℝ) ^ (-ε)) =
        moebiusReal d * (n : ℝ) ^ (-ε) := fun d hd => by
      have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by
        exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      rw [one_mul, mul_assoc, ← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), hmul]
    rw [sum_congr rfl hterm, ← sum_mul, sum_divisors_moebiusReal]
    unfold unitMass
    split_ifs with h1
    · subst h1; simp
    · simp

/-- First pronic moment of the smooth power `u_ε(d) = d^{-ε}`:
`M(u_ε) = -m_{u_ε} Σ_e Λ(e) e^{-(1+ε)}`. -/
theorem firstPronicMoment_unitSign {ε : ℝ} (hε : 0 < ε) :
    firstPronicMoment (dampedSignWeight unitSign ε) =
      -(∑' k : ℕ, dampedSignWeight unitSign ε k / k) *
        ∑' e : ℕ, Λ e * (e : ℝ) ^ (-(1 + ε)) := by
  have hu := unitSign_mem_dampedClass ε
  have hmul : ∀ a b : ℕ, unitSign (a * b) = unitSign a * unitSign b := fun _ _ => by
    simp [unitSign]
  unfold firstPronicMoment
  rw [(hasSum_firstPronicMoment hε hu).tsum_eq, neg_mul, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun e => ?_
  unfold weightRamanujanCoeff
  simp_rw [dampedSignWeight_mul_div hmul e]
  rw [tsum_mul_left, dampedSignWeight_div hε, unitSign, mul_one]
  ring

/-- `Σ_n Λ(n) n^{-s} = Re(-ζ'(s)/ζ(s))` for real `s > 1`. -/
theorem hasSum_vonMangoldt_rpow' {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => Λ n * (n : ℝ) ^ (-s))
      (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have hsum := (ArithmeticFunction.LSeriesSummable_vonMangoldt hsC).hasSum
  rw [show ∑' n, LSeries.term (fun n => (Λ n : ℂ)) (s : ℂ) n =
    LSeries (fun n => (Λ n : ℂ)) (s : ℂ) from rfl,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hsC] at hsum
  have hre := Complex.reCLM.hasSum hsum
  refine hre.congr_fun fun n => ?_
  simp only [Complex.reCLM_apply, LSeries.term_def]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg hn.ne', Real.rpow_neg (Nat.cast_nonneg n),
      show ((n : ℂ) ^ (s : ℂ)) = (((n : ℝ) ^ s : ℝ) : ℂ) by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; rfl,
      ← Complex.ofReal_div, Complex.ofReal_re, div_eq_mul_inv]

/-- The damped readout `m(ε) = Re(-ζ'(1+ε)/ζ(1+ε)²)`, the damping derivative of `1/ζ(1+ε)`. -/
def moebiusDampedReadout (ε : ℝ) : ℝ :=
  (-deriv riemannZeta (1 + (ε : ℂ)) / riemannZeta (1 + (ε : ℂ)) ^ 2).re

theorem moebiusDampedReadout_eq_density_mul {ε : ℝ} (hε : 0 < ε) :
    moebiusDampedReadout ε =
      dampedDensity ε * ∑' e : ℕ, Λ e * (e : ℝ) ^ (-(1 + ε)) := by
  set z : ℂ := ((1 + ε : ℝ) : ℂ) with hzdef
  have hzε : z = 1 + (ε : ℂ) := by rw [hzdef]; push_cast; ring
  have hDz : RHTower.pmPowerDampedDivisorDensity ε = 1 / riemannZeta z := by
    rw [RHTower.pmPowerDampedDivisorDensity, hzε]
  have hDim : (1 / riemannZeta z).im = 0 := by
    rw [← hDz, RHTower.pmPowerDampedDivisorDensity_eq_ofReal_re hε, Complex.ofReal_im]
  have hvon := hasSum_vonMangoldt_rpow' (s := 1 + ε) (by linarith)
  have hLim : (-deriv riemannZeta z / riemannZeta z).im = 0 := by
    have hsC : 1 < z.re := by rw [hzdef, Complex.ofReal_re]; linarith
    have hc := (ArithmeticFunction.LSeriesSummable_vonMangoldt hsC).hasSum
    rw [show ∑' n, LSeries.term (fun n => (Λ n : ℂ)) z n =
      LSeries (fun n => (Λ n : ℂ)) z from rfl,
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hsC] at hc
    have hreal := Complex.ofRealCLM.hasSum hvon
    have heq := hc.unique (hreal.congr_fun fun n => ?_)
    · rw [heq]; simp
    · simp only [Complex.ofRealCLM_apply, LSeries.term_def]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [if_neg hn.ne', Real.rpow_neg (Nat.cast_nonneg n), hzdef,
          show ((n : ℂ) ^ ((1 + ε : ℝ) : ℂ)) = (((n : ℝ) ^ (1 + ε) : ℝ) : ℂ) by
            rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; rfl]
        push_cast; ring
  unfold moebiusDampedReadout dampedDensity
  rw [hvon.tsum_eq, ← hzε, show -deriv riemannZeta z / riemannZeta z ^ 2 =
      (1 / riemannZeta z) * (-deriv riemannZeta z / riemannZeta z) by ring,
    Complex.mul_re, hDim, zero_mul, sub_zero, hDz]

/-- **Exact evaluation of the first pronic moment of the damped Möbius weight via Leibniz inversion.**
For every `ε > 0`, `firstPronicMoment (pmPowerDampedRealWeight ε) = moebiusDampedReadout ε > 0`. -/
theorem firstPronicMoment_pmPowerDamped {ε : ℝ} (hε : 0 < ε) :
    firstPronicMoment (pmPowerDampedRealWeight ε) =
      dampedDensity ε * ∑' e : ℕ, Λ e * (e : ℝ) ^ (-(1 + ε)) ∧
    firstPronicMoment (pmPowerDampedRealWeight ε) = moebiusDampedReadout ε := by
  obtain ⟨hprod, hinv⟩ := firstPronicMoment_eq_of_dirichletConv_eq_unitMass hε
    (pmPowerDampedRealWeight_mem_dampedClass ε) (unitSign_mem_dampedClass ε)
    (dirichletConv_pmPowerDamped_unitSign ε)
  set L := ∑' e : ℕ, Λ e * (e : ℝ) ^ (-(1 + ε))
  have hm : (∑' d : ℕ, pmPowerDampedRealWeight ε d / d) = dampedDensity ε :=
    (hasSum_pmPowerDampedRealWeight_div hε).tsum_eq
  rw [hm] at hprod hinv
  rw [firstPronicMoment_unitSign hε] at hinv
  have h1 : firstPronicMoment (pmPowerDampedRealWeight ε) = dampedDensity ε * L := by
    calc firstPronicMoment (pmPowerDampedRealWeight ε)
        = -(dampedDensity ε) ^ 2 * (-(∑' k : ℕ, dampedSignWeight unitSign ε k / k) * L) := hinv
      _ = dampedDensity ε * (dampedDensity ε * ∑' k : ℕ, dampedSignWeight unitSign ε k / k) * L := by
          ring
      _ = dampedDensity ε * L := by rw [hprod, mul_one]
  exact ⟨h1, h1.trans (moebiusDampedReadout_eq_density_mul hε).symm⟩

theorem firstPronicMoment_pmPowerDamped_pos {ε : ℝ} (hε : 0 < ε) :
    0 < firstPronicMoment (pmPowerDampedRealWeight ε) := by
  rw [(firstPronicMoment_pmPowerDamped hε).1]
  refine mul_pos (RHTower.pmPowerDampedDivisorDensity_re_pos hε) ?_
  have h := hasSum_vonMangoldt_rpow' (s := 1 + ε) (by linarith)
  refine h.summable.tsum_pos (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)) 2 ?_
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- **The BVI energy mean `pmPowerDampedRamanujanEnergyMean ε Q` converges to
`firstPronicMoment (pmPowerDampedRealWeight ε)` as `Q → ∞`.** -/
theorem tendsto_pmPowerDampedRamanujanEnergyMean_firstPronicMoment {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun Q : ℕ => RHTower.pmPowerDampedRamanujanEnergyMean ε Q) atTop
      (𝓝 (firstPronicMoment (pmPowerDampedRealWeight ε))) := by
  have hs : Summable (fun e : ℕ => Λ e * weightRamanujanCoeff (pmPowerDampedRealWeight ε) e) := by
    refine (hasSum_vonMangoldt_rpow' (s := 1 + ε) (by linarith)).summable.of_norm_bounded fun e => ?_
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        weightRamanujanCoeff_pmPowerDamped hε he, Real.rpow_neg (Nat.cast_nonneg e), ← one_div]
      refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
      exact (Complex.abs_re_le_norm _).trans (RHTower.norm_pmPowerDampedRamanujanWeight_le hε he)
  have hM : HasSum (fun e : ℕ => -(Λ e * weightRamanujanCoeff (pmPowerDampedRealWeight ε) e))
      (firstPronicMoment (pmPowerDampedRealWeight ε)) := by
    rw [firstPronicMoment,
      (hasSum_firstPronicMoment hε (pmPowerDampedRealWeight_mem_dampedClass ε)).tsum_eq,
      ← tsum_neg]
    exact hs.neg.hasSum
  refine (hM.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)).congr fun Q => ?_
  simp only [Function.comp_apply]
  rw [RHTower.pmPowerDampedRamanujanEnergyMean, Finset.sum_range_succ' _ (Q + 1),
    Finset.sum_range_succ' _ Q, ArithmeticFunction.vonMangoldt_apply_one, zero_mul, neg_zero,
    add_zero, ArithmeticFunction.map_zero, zero_mul, neg_zero, add_zero, ← sum_neg_distrib]
  refine sum_congr rfl fun q _ => ?_
  rw [show q + 1 + 1 = q + 2 from rfl, weightRamanujanCoeff_pmPowerDamped hε (by omega),
    dampedRamanujanCoeff]
  ring

/-- **Small-damping limit of the Möbius first pronic moment**:
`firstPronicMoment (pmPowerDampedRealWeight ε) → 1` as `ε → 0+`. -/
theorem tendsto_firstPronicMoment_pmPowerDamped_zero :
    Tendsto (fun ε => firstPronicMoment (pmPowerDampedRealWeight ε)) (𝓝[>] 0) (𝓝 1) := by
  have h1 := riemannZeta_residue_one
  have h2 := RHTower.tendsto_sub_one_sq_mul_deriv_riemannZeta
  have hq : Tendsto (fun s : ℂ => -deriv riemannZeta s / riemannZeta s ^ 2)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (𝓝 1) := by
    have h := (h2.neg).div (h1.pow 2) (by norm_num)
    simp only [neg_neg, one_pow, div_one] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (s - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hs)
    simp only [Pi.div_apply]
    rw [mul_pow, neg_mul_eq_mul_neg, mul_div_mul_left _ _ hs1, neg_div]
  have hmap : Tendsto (fun ε : ℝ => 1 + (ε : ℂ)) (𝓝[>] 0) (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => 1 + (ε : ℂ)) (𝓝 0) (𝓝 (1 + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [Set.mem_Ioi.mp hε]
  have hc := (Complex.continuous_re.tendsto 1).comp (hq.comp hmap)
  simp only [Complex.one_re] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (firstPronicMoment_pmPowerDamped hε).2.symm

/-- At every modulus `e`, the von Mangoldt pairing of the parity twin is the negative of the
von Mangoldt pairing of the damped Möbius weight. -/
theorem vonMangoldt_mul_weightRamanujanCoeff_parityTwin {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    Λ e * weightRamanujanCoeff (parityTwinWeight ε) e =
      -(Λ e * weightRamanujanCoeff (pmPowerDampedRealWeight ε) e) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  rw [weightRamanujanCoeff_parityTwin hε e, weightRamanujanCoeff_pmPowerDamped hε he]
  by_cases hp : e.Prime
  · rw [ArithmeticFunction.moebius_apply_prime hp]; push_cast; ring
  · by_cases hpow : IsPrimePow e
    · have hns : ¬ Squarefree e := by
        intro hsq
        obtain ⟨r, k, hr, hk, hrk⟩ := hpow
        rw [← hrk, Nat.squarefree_pow_iff hr.nat_prime.ne_one hk.ne'] at hsq
        rw [← hrk, hsq.2, pow_one] at hp
        exact hp hr.nat_prime
      rw [dampedRamanujanCoeff_eq_closed hε,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
      simp
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]
      ring

/-- **Exact evaluation of the first pronic moment of the parity twin**:
`firstPronicMoment (parityTwinWeight ε) = -moebiusDampedReadout ε < 0`. -/
theorem firstPronicMoment_parityTwin {ε : ℝ} (hε : 0 < ε) :
    firstPronicMoment (parityTwinWeight ε) = -firstPronicMoment (pmPowerDampedRealWeight ε) ∧
      firstPronicMoment (parityTwinWeight ε) = -moebiusDampedReadout ε := by
  obtain ⟨K, hK⟩ := parityTwinWeight_mem_dampedClass hε
  have h1 : firstPronicMoment (parityTwinWeight ε) =
      -firstPronicMoment (pmPowerDampedRealWeight ε) := by
    unfold firstPronicMoment
    rw [(hasSum_firstPronicMoment (by linarith : 0 < ε / 2) hK).tsum_eq,
      (hasSum_firstPronicMoment hε (pmPowerDampedRealWeight_mem_dampedClass ε)).tsum_eq,
      tsum_congr (vonMangoldt_mul_weightRamanujanCoeff_parityTwin hε), tsum_neg, neg_neg]
  exact ⟨h1, by rw [h1, (firstPronicMoment_pmPowerDamped hε).2]⟩

theorem firstPronicMoment_parityTwin_neg {ε : ℝ} (hε : 0 < ε) :
    firstPronicMoment (parityTwinWeight ε) < 0 := by
  rw [(firstPronicMoment_parityTwin hε).1]
  linarith [firstPronicMoment_pmPowerDamped_pos hε]

/-- **Small-damping limit of the parity twin's first pronic moment**:
`firstPronicMoment (parityTwinWeight ε) → -1` as `ε → 0+`. -/
theorem tendsto_firstPronicMoment_parityTwin_zero :
    Tendsto (fun ε => firstPronicMoment (parityTwinWeight ε)) (𝓝[>] 0) (𝓝 (-1)) := by
  refine tendsto_firstPronicMoment_pmPowerDamped_zero.neg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (firstPronicMoment_parityTwin hε).1.symm

/-- **Exact evaluation of the first pronic moment of the negated Möbius weight**:
`firstPronicMoment (negatedMoebiusWeight ε) = -moebiusDampedReadout ε < 0`. -/
theorem firstPronicMoment_negatedMoebius {ε : ℝ} (hε : 0 < ε) :
    firstPronicMoment (negatedMoebiusWeight ε) = -firstPronicMoment (pmPowerDampedRealWeight ε) ∧
      firstPronicMoment (negatedMoebiusWeight ε) = -moebiusDampedReadout ε := by
  obtain ⟨K, hK⟩ := parityTwinWeight_mem_dampedClass hε
  have heq : firstPronicMoment (negatedMoebiusWeight ε) = firstPronicMoment (parityTwinWeight ε) := by
    unfold firstPronicMoment
    rw [(hasSum_firstPronicMoment hε (negatedMoebiusWeight_mem_dampedClass hε)).tsum_eq,
      (hasSum_firstPronicMoment (by linarith : 0 < ε / 2) hK).tsum_eq]
    congr 1
    refine tsum_congr fun e => ?_
    by_cases he : IsPrimePow e
    · rw [weightRamanujanCoeff_negatedMoebius_eq_twin hε he]
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr he, zero_mul, zero_mul]
  rw [heq]
  exact firstPronicMoment_parityTwin hε

/-- **The first-moment gap of the damped Möbius parity pair** is `2 * moebiusDampedReadout ε > 0`. -/
theorem firstPronicMoment_pmPowerDamped_sub_parityTwin {ε : ℝ} (hε : 0 < ε) :
    firstPronicMoment (pmPowerDampedRealWeight ε) - firstPronicMoment (parityTwinWeight ε) =
      2 * moebiusDampedReadout ε := by
  rw [(firstPronicMoment_pmPowerDamped hε).2, (firstPronicMoment_parityTwin hε).2]
  ring

/-- **Unconditional finite-horizon and asymptotic separation of the dual residuals of
`negatedMoebiusWeight ε` and `pmPowerDampedRealWeight ε` at every damping `ε > 0`.** -/
theorem dual_residual_negatedMoebius_sub_pmPowerDamped {ε : ℝ} (hε : 0 < ε) :
    (∀ T : ℕ,
      (∑ n ∈ Icc 1 T, (1 - weightCenteredPrefix (negatedMoebiusWeight ε) (dampedDensity ε) n) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1))) -
        (∑ n ∈ Icc 1 T,
          (1 - weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1))) =
        4 * ∑ n ∈ Icc 1 T,
          weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n /
            ((n : ℝ) * ((n : ℝ) + 1))) ∧
    Tendsto (fun T : ℕ =>
      (∑ n ∈ Icc 1 T, (1 - weightCenteredPrefix (negatedMoebiusWeight ε) (dampedDensity ε) n) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1))) -
        (∑ n ∈ Icc 1 T,
          (1 - weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1))))
      atTop (𝓝 (4 * moebiusDampedReadout ε)) := by
  have hdiff : ∀ T : ℕ,
      (∑ n ∈ Icc 1 T, (1 - weightCenteredPrefix (negatedMoebiusWeight ε) (dampedDensity ε) n) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1))) -
        (∑ n ∈ Icc 1 T,
          (1 - weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1))) =
        4 * ∑ n ∈ Icc 1 T,
          weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n /
            ((n : ℝ) * ((n : ℝ) + 1)) := fun T => by
    rw [← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [weightCenteredPrefix_negatedMoebius]
    ring
  refine ⟨hdiff, ?_⟩
  simp_rw [hdiff]
  have hm : (∑' d : ℕ, pmPowerDampedRealWeight ε d / d) = dampedDensity ε :=
    (hasSum_pmPowerDampedRealWeight_div hε).tsum_eq
  have hhas : HasSum (fun n : ℕ =>
      weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n /
        ((n : ℝ) * ((n : ℝ) + 1))) (moebiusDampedReadout ε) := by
    have h : HasSum (fun n : ℕ =>
        weightCenteredPrefix (pmPowerDampedRealWeight ε)
          (∑' d : ℕ, pmPowerDampedRealWeight ε d / d) n /
          ((n : ℝ) * ((n : ℝ) + 1))) (firstPronicMoment (pmPowerDampedRealWeight ε)) :=
      (hasSum_firstPronicMoment hε (pmPowerDampedRealWeight_mem_dampedClass ε)).summable.hasSum
    rwa [hm, (firstPronicMoment_pmPowerDamped hε).2] at h
  have hlim : Tendsto (fun T : ℕ => ∑ n ∈ Icc 1 T,
      weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n /
        ((n : ℝ) * ((n : ℝ) + 1))) atTop (𝓝 (moebiusDampedReadout ε)) := by
    refine (hhas.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun T => ?_
    simp only [Function.comp_apply]
    rw [dampedSign_sum_range_succ_eq_add_Icc, weightCenteredPrefix_zero, zero_div, zero_add]
  exact hlim.const_mul 4

/-- **Unconditional orthogonal readout–variance decomposition of the damped Möbius receiver
for all `ε ≥ 1/2`.** -/
theorem tsum_pmPowerDamped_energy_and_dual_residual_of_half_le {ε : ℝ} (hε : 1 / 2 ≤ ε) :
    ReceiverBounded (pmPowerDampedRealWeight ε) ∧
      (∑' n : ℕ, weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) (n + 1) ^ 2 /
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) =
        moebiusDampedReadout ε ^ 2 +
          ∑' n : ℕ, (weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) (n + 1) -
            moebiusDampedReadout ε) ^ 2 / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) ∧
      (∑' n : ℕ, (1 - weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) (n + 1)) ^ 2 /
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) =
        (1 - moebiusDampedReadout ε) ^ 2 +
          ∑' n : ℕ, (weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) (n + 1) -
            moebiusDampedReadout ε) ^ 2 / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) := by
  have hε0 : 0 < ε := by linarith
  have hm : (∑' d : ℕ, pmPowerDampedRealWeight ε d / d) = dampedDensity ε :=
    (hasSum_pmPowerDampedRealWeight_div hε0).tsum_eq
  obtain ⟨B, hB⟩ := RHTower.exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le hε
  have hrec : ReceiverBounded (pmPowerDampedRealWeight ε) := ⟨B, fun T => by
    rw [hm, weightPronicEnergy_pmPowerDamped]
    exact hB T⟩
  obtain ⟨_, hE, hD⟩ := tsum_pronic_energy_and_dual_residual_eq_add_variance hε0
    (pmPowerDampedRealWeight_mem_dampedClass ε) hrec
  rw [hm, (firstPronicMoment_pmPowerDamped hε0).2] at hE hD
  exact ⟨hrec, hE, hD⟩

/-! ### §4. Log-power receivers above half damping and the Chebyshev tangent law -/

/-- Arbitrary-loss damping class bound for `logPowWeight`: absorbing `log^k d` into `d^δ` (`0 < δ < ε`)
places `logPowWeight c k` into `DampedClass (K * ((k + 1) / δ) ^ k) (ε - δ)`. -/
theorem logPowWeight_mem_dampedClass_sub {K ε δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (k : ℕ) :
    DampedClass (K * ((k + 1 : ℝ) / δ) ^ k) (ε - δ) (logPowWeight c k) := fun d => by
  have hK := nonneg_of_dampedClass hc
  set η : ℝ := δ / (k + 1)
  have hη : 0 < η := by positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : c 0 = 0 := by
      have hc0 := hc 0
      rw [Nat.cast_zero, Real.zero_rpow (by linarith : -ε ≠ 0), mul_zero] at hc0
      exact abs_nonpos_iff.mp hc0
    rw [logPowWeight, h0, zero_mul, abs_zero]
    positivity
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hlog0 := Real.log_natCast_nonneg d
    have hlog := Real.log_le_rpow_div (x := d) hd0.le hη
    have hpowlog : Real.log d ^ k ≤ ((d : ℝ) ^ η / η) ^ k := pow_le_pow_left₀ hlog0 hlog k
    have hpowd : ((d : ℝ) ^ η / η) ^ k = (d : ℝ) ^ (η * k) * (1 / η) ^ k := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hd0.le]; ring
    have hexp : (d : ℝ) ^ (η * k) ≤ (d : ℝ) ^ δ :=
      Real.rpow_le_rpow_of_exponent_le hd1 (by
        simp only [η]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    rw [logPowWeight, abs_mul, abs_of_nonneg (pow_nonneg hlog0 k)]
    have h1η : (1 / η) ^ k = ((k + 1 : ℝ) / δ) ^ k := by simp only [η]; rw [one_div_div]
    calc |c d| * Real.log d ^ k ≤ K * (d : ℝ) ^ (-ε) * ((d : ℝ) ^ δ * (1 / η) ^ k) := by
          refine mul_le_mul (hc d) (hpowlog.trans ?_) (pow_nonneg hlog0 k) (by positivity)
          rw [hpowd]
          exact mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = K * ((k + 1 : ℝ) / δ) ^ k * (d : ℝ) ^ (-(ε - δ)) := by
          rw [h1η, show -(ε - δ) = -ε + δ by ring, Real.rpow_add hd0]; ring

/-- **Every log-power weight has bounded receiver above half damping.** -/
theorem receiverBounded_logPowWeight_of_half_lt {K ε : ℝ} (hε : 1 / 2 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (k : ℕ) :
    ReceiverBounded (logPowWeight c k) := by
  set δ := (ε - 1 / 2) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hδε : δ < ε := by simp only [δ]; linarith
  have hsub : 1 / 2 < ε - δ := by simp only [δ]; linarith
  obtain ⟨E, hE⟩ := exists_uniform_weightPronicEnergy_bound
    (K := K * ((k + 1 : ℝ) / δ) ^ k) hsub
  exact ⟨E, hE _ (logPowWeight_mem_dampedClass_sub hδ hδε hc k)⟩

/-- In particular, every log-power weight of the damped Möbius weight has bounded receiver
for all `ε > 1/2`. -/
theorem receiverBounded_logPowWeight_pmPowerDamped_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε) (k : ℕ) :
    ReceiverBounded (logPowWeight (pmPowerDampedRealWeight ε) k) :=
  receiverBounded_logPowWeight_of_half_lt hε (pmPowerDampedRealWeight_mem_dampedClass ε) k

/-- **The tangent law of the Möbius receiver.** The damping derivative of the centered Möbius
prefix `weightCenteredPrefix (pmPowerDampedRealWeight η) (dampedDensity η) n` at `η > 0` is the
negated centered prefix of `logWeight (pmPowerDampedRealWeight η)`. -/
theorem hasDerivAt_weightCenteredPrefix_pmPowerDamped {η : ℝ} (hη : 0 < η) (n : ℕ) :
    HasDerivAt (fun x => weightCenteredPrefix (pmPowerDampedRealWeight x) (dampedDensity x) n)
      (-weightCenteredPrefix (logWeight (pmPowerDampedRealWeight η))
        (∑' d : ℕ, logWeight (pmPowerDampedRealWeight η) d / d) n) η := by
  have hrpow : ∀ d : ℕ, 0 < d →
      HasDerivAt (fun x : ℝ => (d : ℝ) ^ (-x)) (-(Real.log d * (d : ℝ) ^ (-η))) η := fun d hd => by
    have h := (hasDerivAt_neg η).const_rpow (a := (d : ℝ)) (by exact_mod_cast hd)
    exact h.congr_deriv (by ring)
  have hdiv : ∀ k : ℕ, HasDerivAt (fun x => ∑ d ∈ k.divisors, pmPowerDampedRealWeight x d)
      (-∑ d ∈ k.divisors, logWeight (pmPowerDampedRealWeight η) d) η := fun k => by
    unfold pmPowerDampedRealWeight logWeight
    have h := HasDerivAt.fun_sum (u := k.divisors)
      (A := fun d x => moebiusReal d * (d : ℝ) ^ (-x))
      (A' := fun d => moebiusReal d * -(Real.log d * (d : ℝ) ^ (-η)))
      (fun d hd => (hrpow d (Nat.pos_of_mem_divisors hd)).const_mul _)
    refine h.congr_deriv ?_
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun d _ => by ring
  have h1ne : (1 + (η : ℂ)) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1re : 1 < (1 + (η : ℂ)).re := by simp; linarith
  have hζ : HasDerivAt (fun z : ℂ => riemannZeta (1 + z)) (deriv riemannZeta (1 + (η : ℂ)))
      (η : ℂ) := by
    have h1 := (differentiableAt_riemannZeta h1ne).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => 1 + z) 1 (η : ℂ) := (hasDerivAt_id _).const_add 1
    have h3 := h1.comp (η : ℂ) h2
    rw [mul_one] at h3; exact h3
  have hρ : HasDerivAt dampedDensity (moebiusDampedReadout η) η := by
    have h := (hζ.inv (riemannZeta_ne_zero_of_one_lt_re h1re)).real_of_complex
    unfold moebiusDampedReadout dampedDensity
    convert h using 1
    funext x
    simp [RHTower.pmPowerDampedDivisorDensity, one_div]
  have hmean : ∑' d : ℕ, logWeight (pmPowerDampedRealWeight η) d / d = -moebiusDampedReadout η := by
    rw [tsum_logWeight_div hη (pmPowerDampedRealWeight_mem_dampedClass η),
      (firstPronicMoment_pmPowerDamped hη).2]
  unfold weightCenteredPrefix
  rw [hmean]
  have hsum : HasDerivAt
      (fun x => ∑ j ∈ Icc 1 n, ∑ d ∈ j.divisors, pmPowerDampedRealWeight x d)
      (∑ j ∈ Icc 1 n, -∑ d ∈ j.divisors, logWeight (pmPowerDampedRealWeight η) d) η :=
    HasDerivAt.fun_sum fun j _ => hdiv j
  have h := hsum.sub (hρ.mul_const (n : ℝ))
  refine h.congr_deriv ?_
  rw [sum_neg_distrib]
  ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
