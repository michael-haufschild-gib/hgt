import GaloisForLFunctions.RHTower.BakerGeneralProof.BakerGeneralIteration
import GaloisForLFunctions.RHTower.BakerGeneralProof.TerminalZeroEstimate

/-!
# Terminal contradiction and the general Baker capstone

At the last stage the base auxiliary function vanishes to order `M_J` at each of `S_J` consecutive
natural samples, so the gap-free terminal zero estimate applies with `M_J S_J` prescribed zeros.
Its right-hand side is an exponential on the scale `q^{2n²+2n+3}` while the zero count is
`q^{2n²+2n+4}/2^J`, one power of the parameter larger.  The estimate therefore fails for every
large structured parameter, so no solved algebraic relation among the chosen logarithms exists.
-/

open scoped Classical
open BigOperators NumberField
open Filter Topology

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

namespace GeneralParameters

/-- The right-hand side of the terminal gap-free zero estimate. -/
noncomputable def terminalMajorant (Omega Rr : ℝ) (N : ℕ) : ℝ :=
  frequencyContourRadius Omega *
    (Real.exp ((4 * Rr) * frequencyContourRadius Omega) *
      (frequencyContourRadius Omega ^ N * (1 + Omega) ^ N) /
      (frequencyContourRadius Omega - Omega) ^ N) *
    ∑ m ∈ Finset.range (N + 1), (Nat.factorial m : ℝ) / Rr ^ m

theorem sum_factorial_div_le {Rr : ℝ} (hRr : 1 ≤ Rr) (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), (Nat.factorial m : ℝ) / Rr ^ m ≤
      ((N + 1 : ℕ) : ℝ) * ((N : ℝ) ^ N) := by
  have hRr0 : (0 : ℝ) < Rr := lt_of_lt_of_le zero_lt_one hRr
  have hterm : ∀ m ∈ Finset.range (N + 1),
      (Nat.factorial m : ℝ) / Rr ^ m ≤ (N : ℝ) ^ N := by
    intro m hm
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hpow : (1 : ℝ) ≤ Rr ^ m := one_le_pow₀ hRr
    have h1 : (Nat.factorial m : ℝ) / Rr ^ m ≤ (Nat.factorial m : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.factorial m)]
    refine h1.trans ?_
    have h2 : (Nat.factorial m : ℝ) ≤ (Nat.factorial N : ℝ) := by
      exact_mod_cast Nat.factorial_le hmN
    refine h2.trans ?_
    have h3 : (Nat.factorial N : ℝ) ≤ ((N ^ N : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_le_pow N
    simpa using h3
  calc
    ∑ m ∈ Finset.range (N + 1), (Nat.factorial m : ℝ) / Rr ^ m ≤
        ∑ _m ∈ Finset.range (N + 1), (N : ℝ) ^ N := Finset.sum_le_sum hterm
    _ = ((N + 1 : ℕ) : ℝ) * ((N : ℝ) ^ N) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem terminalMajorant_le {Omega Rr w : ℝ} (hOmega : 0 ≤ Omega) (hRr : 1 ≤ Rr) (N : ℕ)
    (h2 : (2 : ℝ) ≤ Real.exp w) (hrho : frequencyContourRadius Omega ≤ Real.exp w)
    (hOm : 1 + Omega ≤ Real.exp w) (hN : (N : ℝ) ≤ Real.exp w)
    (hN1 : ((N + 1 : ℕ) : ℝ) ≤ Real.exp w) :
    terminalMajorant Omega Rr N ≤
      Real.exp (2 * w + (4 * Rr) * frequencyContourRadius Omega + 3 * (w * N)) := by
  have hrho1 : 1 ≤ frequencyContourRadius Omega := one_le_frequencyContourRadius hOmega
  have hsub : 0 < frequencyContourRadius Omega - Omega := frequencyContourRadius_sub_pos hOmega
  have hOm0 : (0 : ℝ) ≤ 1 + Omega := by linarith
  have hratio : frequencyContourRadius Omega / (frequencyContourRadius Omega - Omega) ≤ 2 := by
    rw [div_le_iff₀ hsub]
    unfold frequencyContourRadius
    linarith
  have hratio0 : 0 ≤ frequencyContourRadius Omega / (frequencyContourRadius Omega - Omega) :=
    div_nonneg (by linarith) hsub.le
  have hsplit : frequencyContourRadius Omega ^ N * (1 + Omega) ^ N /
      (frequencyContourRadius Omega - Omega) ^ N =
      (frequencyContourRadius Omega / (frequencyContourRadius Omega - Omega)) ^ N *
        (1 + Omega) ^ N := by
    rw [div_pow]
    field_simp
  have hpow1 : (frequencyContourRadius Omega /
      (frequencyContourRadius Omega - Omega)) ^ N ≤ Real.exp (w * N) := by
    refine le_trans (pow_le_pow_left₀ hratio0 hratio N) ?_
    exact pow_le_exp_mul (by norm_num) h2 N
  have hpow2 : (1 + Omega) ^ N ≤ Real.exp (w * N) := pow_le_exp_mul hOm0 hOm N
  have hpowN : (N : ℝ) ^ N ≤ Real.exp (w * N) :=
    pow_le_exp_mul (Nat.cast_nonneg _) hN N
  have hsum : ∑ m ∈ Finset.range (N + 1), (Nat.factorial m : ℝ) / Rr ^ m ≤
      Real.exp w * Real.exp (w * N) := by
    refine le_trans (sum_factorial_div_le hRr N) ?_
    exact mul_le_mul hN1 hpowN (by positivity) (Real.exp_nonneg _)
  unfold terminalMajorant
  calc
    frequencyContourRadius Omega *
        (Real.exp ((4 * Rr) * frequencyContourRadius Omega) *
          (frequencyContourRadius Omega ^ N * (1 + Omega) ^ N) /
          (frequencyContourRadius Omega - Omega) ^ N) *
        ∑ m ∈ Finset.range (N + 1), (Nat.factorial m : ℝ) / Rr ^ m =
        frequencyContourRadius Omega *
          (Real.exp ((4 * Rr) * frequencyContourRadius Omega) *
            ((frequencyContourRadius Omega /
              (frequencyContourRadius Omega - Omega)) ^ N * (1 + Omega) ^ N)) *
          ∑ m ∈ Finset.range (N + 1), (Nat.factorial m : ℝ) / Rr ^ m := by
      rw [← hsplit]
      ring
    _ ≤ Real.exp w *
          (Real.exp ((4 * Rr) * frequencyContourRadius Omega) *
            (Real.exp (w * N) * Real.exp (w * N))) *
          (Real.exp w * Real.exp (w * N)) := by
      gcongr
    _ = Real.exp (2 * w + (4 * Rr) * frequencyContourRadius Omega + 3 * (w * N)) := by
      simp only [← Real.exp_add]
      congr 1
      ring

theorem structuredBase_dvd_pow (n u k : ℕ) (hk : k ≤ iterationLength n + 1) :
    2 ^ k ∣ (structuredBase n u) ^ (2 * n + 2) := by
  unfold structuredBase
  rw [mul_pow, ← pow_mul]
  refine Dvd.dvd.mul_right (pow_dvd_pow 2 ?_) _
  have h2 : iterationLength n + 1 ≤ (iterationLength n + 1) * (2 * n + 2) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem terminalExponent_mul (n q : ℕ) (hdvd : 2 ^ (iterationLength n) ∣ q ^ (2 * n + 2)) :
    (stageOrder n q (iterationLength n) * stageSampleCount q (iterationLength n)) *
      2 ^ (iterationLength n) = q ^ (2 * n + iterationLength n + 4) := by
  unfold stageSampleCount stageOrder
  calc
    q ^ (2 * n + 2) / 2 ^ iterationLength n * q ^ (iterationLength n + 2) *
        2 ^ iterationLength n =
        (q ^ (2 * n + 2) / 2 ^ iterationLength n * 2 ^ iterationLength n) *
          q ^ (iterationLength n + 2) := by ring
    _ = q ^ (2 * n + 2) * q ^ (iterationLength n + 2) := by rw [Nat.div_mul_cancel hdvd]
    _ = q ^ (2 * n + iterationLength n + 4) := by
      rw [← pow_add]
      congr 1
      omega

theorem terminalColumnCount_cast (n q : ℕ) :
    ((exponentWidth n q ^ n * additiveWidth n q : ℕ) : ℝ) =
      2 * (q : ℝ) ^ (2 * n * n + 2 * n + 2) := by
  push_cast [exponentWidth, additiveWidth]
  rw [← pow_mul, mul_comm (((q : ℝ)) ^ (2 * n * n)) _, mul_assoc, ← pow_add]
  ring_nf

/-- The terminal zero estimate is violated for every large structured parameter. -/
theorem eventually_terminalSmallness (R : SolvedRelation) :
    ∀ᶠ u : ℕ in atTop,
      terminalMajorant
          (((exponentWidth R.n (structuredBase R.n u) : ℕ) : ℝ) * R.lambdaNormSum)
          ((stageSampleCount (structuredBase R.n u) (iterationLength R.n) : ℕ) : ℝ)
          (exponentWidth R.n (structuredBase R.n u) ^ R.n *
            additiveWidth R.n (structuredBase R.n u)) *
        ((2 : ℝ) / 3) ^ (stageOrder R.n (structuredBase R.n u) (iterationLength R.n) *
          stageSampleCount (structuredBase R.n u) (iterationLength R.n)) < 1 := by
  have hL0 : 0 ≤ R.lambdaNormSum := R.lambdaNormSum_nonneg
  have hkappa : 0 < Real.log (3 / 2) / 2 ^ (iterationLength R.n) := by
    have : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    positivity
  have hrho := eventually_const_pow_le_exp (2 * R.lambdaNormSum + 2) (2 * R.n)
  have hOm := eventually_const_pow_le_exp (1 + R.lambdaNormSum) (2 * R.n)
  have hN := eventually_const_pow_le_exp (4 : ℝ) (2 * R.n * R.n + 2 * R.n + 2)
  have hcmp := eventually_lt_succ_pow
    (2 + 4 * (2 * R.lambdaNormSum + 2) + 6) (Real.log (3 / 2) / 2 ^ (iterationLength R.n))
    hkappa (2 * R.n * R.n + 2 * R.n + 3)
  have hmain : ∀ᶠ q : ℕ in atTop,
      ((2 * R.lambdaNormSum + 2) * (q : ℝ) ^ (2 * R.n) ≤ Real.exp q) ∧
      ((1 + R.lambdaNormSum) * (q : ℝ) ^ (2 * R.n) ≤ Real.exp q) ∧
      ((4 : ℝ) * (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 2) ≤ Real.exp q) ∧
      ((2 + 4 * (2 * R.lambdaNormSum + 2) + 6) *
        (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 3) <
        (Real.log (3 / 2) / 2 ^ (iterationLength R.n)) *
          (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 3 + 1)) ∧ 1 ≤ q := by
    filter_upwards [hrho, hOm, hN, hcmp, eventually_ge_atTop 1] with q h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  filter_upwards [(structuredBase_tendsto_atTop R.n).eventually hmain] with u hu
  obtain ⟨hrhoq, hOmq, hNq, hcmpq, hq1⟩ := hu
  set q := structuredBase R.n u with hqdef
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpow : ∀ j : ℕ, (1 : ℝ) ≤ (q : ℝ) ^ j := fun j => one_le_pow₀ hq1R
  set Omega : ℝ := ((exponentWidth R.n q : ℕ) : ℝ) * R.lambdaNormSum with hOmega
  set Rr : ℝ := ((stageSampleCount q (iterationLength R.n) : ℕ) : ℝ) with hRr
  set N : ℕ := exponentWidth R.n q ^ R.n * additiveWidth R.n q with hN2
  have hOmega0 : 0 ≤ Omega := by
    rw [hOmega]
    exact mul_nonneg (Nat.cast_nonneg _) hL0
  have hOmegaVal : Omega = (q : ℝ) ^ (2 * R.n) * R.lambdaNormSum := by
    rw [hOmega, exponentWidth_cast]
  have hRr1 : (1 : ℝ) ≤ Rr := by
    rw [hRr, stageSampleCount_cast]
    exact hqpow _
  have h2exp : (2 : ℝ) ≤ Real.exp q := by
    have := Real.add_one_le_exp ((q : ℝ))
    linarith
  have hrhole : frequencyContourRadius Omega ≤ Real.exp q := by
    unfold frequencyContourRadius
    refine le_trans ?_ hrhoq
    rw [hOmegaVal]
    nlinarith [hqpow (2 * R.n), hL0]
  have hOmle : 1 + Omega ≤ Real.exp q := by
    refine le_trans ?_ hOmq
    rw [hOmegaVal]
    nlinarith [hqpow (2 * R.n), hL0]
  have hNcast : ((N : ℕ) : ℝ) = 2 * (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 2) := by
    rw [hN2]
    exact terminalColumnCount_cast R.n q
  have hNle : ((N : ℕ) : ℝ) ≤ Real.exp q := by
    rw [hNcast]
    refine le_trans ?_ hNq
    nlinarith [hqpow (2 * R.n * R.n + 2 * R.n + 2)]
  have hN1le : ((N + 1 : ℕ) : ℝ) ≤ Real.exp q := by
    refine le_trans ?_ hNq
    push_cast
    rw [hNcast]
    nlinarith [hqpow (2 * R.n * R.n + 2 * R.n + 2)]
  have hmaj := terminalMajorant_le hOmega0 hRr1 N h2exp hrhole hOmle hNle hN1le
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hmaj (pow_nonneg (by norm_num) _)) ?_
  rw [mul_comm]
  refine decay_mul_exp_lt_one ?_
  have hdvd : 2 ^ (iterationLength R.n) ∣ q ^ (2 * R.n + 2) :=
    structuredBase_dvd_pow R.n u _ (by omega)
  have hPcast : ((stageOrder R.n q (iterationLength R.n) *
      stageSampleCount q (iterationLength R.n) : ℕ) : ℝ) * 2 ^ (iterationLength R.n) =
      (q : ℝ) ^ (2 * R.n + iterationLength R.n + 4) := by
    have := terminalExponent_mul R.n q hdvd
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
  have hexpeq : 2 * R.n + iterationLength R.n + 4 = 2 * R.n * R.n + 2 * R.n + 4 := by
    unfold iterationLength
    omega
  rw [hexpeq] at hPcast
  have h2pos : (0 : ℝ) < 2 ^ (iterationLength R.n) := by positivity
  have hPval : ((stageOrder R.n q (iterationLength R.n) *
      stageSampleCount q (iterationLength R.n) : ℕ) : ℝ) =
      (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 4) / 2 ^ (iterationLength R.n) := by
    field_simp at hPcast ⊢
    linarith [hPcast]
  rw [hPval]
  have hsucc : 2 * R.n * R.n + 2 * R.n + 3 + 1 = 2 * R.n * R.n + 2 * R.n + 4 := by omega
  rw [hsucc] at hcmpq
  have hRrval : Rr = (q : ℝ) ^ (iterationLength R.n + 2) := by
    rw [hRr, stageSampleCount_cast]
  have hbudget : 2 * (q : ℝ) + (4 * Rr) * frequencyContourRadius Omega +
      3 * ((q : ℝ) * (N : ℕ)) ≤
      (2 + 4 * (2 * R.lambdaNormSum + 2) + 6) *
        (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 3) := by
    have hA : (2 : ℝ) * (q : ℝ) ≤ 2 * (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 3) := by
      have : (q : ℝ) ≤ (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 3) := by
        simpa using pow_le_pow_right₀ hq1R (show 1 ≤ 2 * R.n * R.n + 2 * R.n + 3 by omega)
      linarith
    have hrhoval : frequencyContourRadius Omega ≤
        (2 * R.lambdaNormSum + 2) * (q : ℝ) ^ (2 * R.n) := by
      unfold frequencyContourRadius
      rw [hOmegaVal]
      nlinarith [hqpow (2 * R.n), hL0]
    have hrho0 : (0 : ℝ) ≤ frequencyContourRadius Omega :=
      le_trans zero_le_one (one_le_frequencyContourRadius hOmega0)
    have hB : (4 * Rr) * frequencyContourRadius Omega ≤
        4 * (2 * R.lambdaNormSum + 2) * (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 3) := by
      have hRr0 : (0 : ℝ) ≤ Rr := le_trans zero_le_one hRr1
      have hstep : (4 * Rr) * frequencyContourRadius Omega ≤
          (4 * Rr) * ((2 * R.lambdaNormSum + 2) * (q : ℝ) ^ (2 * R.n)) :=
        mul_le_mul_of_nonneg_left hrhoval (by linarith)
      refine hstep.trans ?_
      rw [hRrval]
      have hpowmul : (q : ℝ) ^ (iterationLength R.n + 2) * (q : ℝ) ^ (2 * R.n) =
          (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 2) := by
        rw [← pow_add]
        congr 1
        unfold iterationLength
        omega
      have hle : (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 2) ≤
          (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 3) :=
        pow_le_pow_right₀ hq1R (by omega)
      nlinarith [hL0, hqpow (2 * R.n * R.n + 2 * R.n + 2)]
    have hC : 3 * ((q : ℝ) * (N : ℕ)) ≤ 6 * (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 3) := by
      rw [hNcast]
      have hpowmul : (q : ℝ) * (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 2) =
          (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 3) := by
        rw [← pow_succ']
      nlinarith [hpowmul]
    linarith
  calc
    2 * (q : ℝ) + (4 * Rr) * frequencyContourRadius Omega + 3 * ((q : ℝ) * (N : ℕ)) ≤
        (2 + 4 * (2 * R.lambdaNormSum + 2) + 6) *
          (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 3) := hbudget
    _ < (Real.log (3 / 2) / 2 ^ (iterationLength R.n)) *
          (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 4) := hcmpq
    _ = (q : ℝ) ^ (2 * R.n * R.n + 2 * R.n + 4) / 2 ^ (iterationLength R.n) *
          Real.log (3 / 2) := by ring

/-- A solved algebraic relation among chosen logarithms is impossible: the long extrapolation
supplies more zeros than the gap-free terminal estimate allows. -/
theorem _root_.GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelation.false_of_long_extrapolation
    (R : SolvedRelation) : False := by
  classical
  obtain ⟨c, hc, hcomp0⟩ := R.exists_component_common_integer_scale
  obtain ⟨d, hd, hbase0⟩ := R.exists_base_common_integer_scale
  have hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir) := by
    simpa [SolvedRelation.scaledComponentCoeff] using hcomp0
  have hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i) := by
    simpa [SolvedRelation.scaledBase] using hbase0
  obtain ⟨CH, hCH0, hCHev⟩ := exists_eventually_coefficientBudget_le_exp R c d hcomp hbase
  have hstages : ∀ᶠ u : ℕ in atTop,
      ∀ k ∈ Finset.range (iterationLength R.n),
        ∀ (nu : R.Direction → ℕ) (Heta : ℝ) (s : ℕ),
          (∀ dir, nu dir ≤ stageOrder R.n (structuredBase R.n u) (k + 1)) → 0 ≤ Heta →
          Heta ≤ Real.exp (CH * ((structuredBase R.n u : ℕ) : ℝ) ^ (2 * R.n + 3)) →
          s ≤ stageSampleCount (structuredBase R.n u) (k + 1) →
          (|(d : ℝ)| ^ (s * (R.n * exponentWidth R.n (structuredBase R.n u))) *
            (((s + stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ) ^
                (stageOrder R.n (structuredBase R.n u) (k + 1) *
                  stageSampleCount (structuredBase R.n u) k) *
              (R.jetScalarBound c (additiveWidth R.n (structuredBase R.n u))
                  (exponentWidth R.n (structuredBase R.n u)) nu Heta
                  ((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) /
                (((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) -
                  ((stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ)) ^
                  (stageOrder R.n (structuredBase R.n u) (k + 1) *
                    stageSampleCount (structuredBase R.n u) k)))) *
            R.jetHouseScalarBound c d (additiveWidth R.n (structuredBase R.n u))
              (exponentWidth R.n (structuredBase R.n u)) nu Heta s ^
              (Module.finrank ℚ R.CoefficientField - 1) < 1 := by
    rw [Filter.eventually_all_finset]
    intro k hk
    exact eventually_stageSmallness R c d k (le_of_lt (Finset.mem_range.mp hk)) CH hCH0
  obtain ⟨u, hstage, hterm, hCHq, hq1⟩ :=
    (hstages.and ((eventually_terminalSmallness R).and
      (((structuredBase_tendsto_atTop R.n).eventually hCHev).and
        (eventually_ge_atTop 1)))).exists
  have hqpos : 0 < structuredBase R.n u := structuredBase_pos hq1
  have hq1' : 1 ≤ structuredBase R.n u := hqpos
  have hU0 : 0 < additiveWidth R.n (structuredBase R.n u) := additiveWidth_pos hqpos
  have hV0 : 0 < exponentWidth R.n (structuredBase R.n u) := exponentWidth_pos hqpos
  have hS0 : 0 < stageSampleCount (structuredBase R.n u) 0 := stageSampleCount_pos hqpos
  have hT0 : 0 < stageOrder R.n (structuredBase R.n u) 0 := by
    rw [stageOrder_zero]
    exact pow_pos hqpos _
  obtain ⟨eta, heta, hker0, hEta⟩ :=
    R.exists_polynomial_auxiliary_coefficients_budget c d hcomp hbase
      (additiveWidth R.n (structuredBase R.n u)) (exponentWidth R.n (structuredBase R.n u))
      (stageSampleCount (structuredBase R.n u) 0) (stageOrder R.n (structuredBase R.n u) 0)
      hU0 hV0 hS0 hT0 hd (dimension_double R.n (structuredBase R.n u))
  have hHeta0 := R.coefficientBudget_nonneg c d hcomp hbase
    (additiveWidth R.n (structuredBase R.n u)) (exponentWidth R.n (structuredBase R.n u))
    (stageSampleCount (structuredBase R.n u) 0) (stageOrder R.n (structuredBase R.n u) 0)
  have hkerJ := polynomialAuxiliaryMatrix_kernel_iterate R c d hc hcomp hbase hd u hq1' eta
    (R.coefficientBudget c d hcomp hbase (additiveWidth R.n (structuredBase R.n u))
      (exponentWidth R.n (structuredBase R.n u)) (stageSampleCount (structuredBase R.n u) 0)
      (stageOrder R.n (structuredBase R.n u) 0))
    hHeta0 hEta hker0 (iterationLength R.n) le_rfl
    (fun k hk nu s hnu hs => hstage k (Finset.mem_range.mpr hk) nu _ s hnu hHeta0 hCHq hs)
    (iterationLength R.n) le_rfl
  have hFne : exponentialPolynomial (R.polynomialAuxiliaryCoefficient eta)
      R.exponentialFrequency ≠ 0 := by
    rw [← R.polynomialComponentJetAuxiliaryFunction_zero_eq_exponentialPolynomial c]
    exact R.polynomialComponentJetAuxiliaryFunction_zero_ne_zero_of_eta_ne_zero c eta heta
  have horder : ∀ z ∈ BakerProof.initialSamplePoints
      (stageSampleCount (structuredBase R.n u) (iterationLength R.n)),
      stageOrder R.n (structuredBase R.n u) (iterationLength R.n) ≤
        analyticOrderAt (exponentialPolynomial (R.polynomialAuxiliaryCoefficient eta)
          R.exponentialFrequency) z := by
    intro z hz
    obtain ⟨sample, rfl⟩ := BakerProof.mem_initialSamplePoints.mp hz
    rw [← R.polynomialComponentJetAuxiliaryFunction_zero_eq_exponentialPolynomial c]
    exact R.polynomialAuxiliaryFunction_analyticOrderAt_ge c d hc hcomp hbase eta hkerJ hd sample
  have hOmega0 : (0 : ℝ) ≤
      ((exponentWidth R.n (structuredBase R.n u) : ℕ) : ℝ) * R.lambdaNormSum :=
    mul_nonneg (Nat.cast_nonneg _) R.lambdaNormSum_nonneg
  have hRpos : (0 : ℝ) <
      ((stageSampleCount (structuredBase R.n u) (iterationLength R.n) : ℕ) : ℝ) := by
    exact_mod_cast stageSampleCount_pos (q := structuredBase R.n u)
      (k := iterationLength R.n) hqpos
  have hest := repeatedFrequency_terminal_zero_inequality
    (R.polynomialAuxiliaryCoefficient eta) R.exponentialFrequency
    (additiveWidth R.n (structuredBase R.n u))
    (fun m => R.polynomialAuxiliaryCoefficient_natDegree_lt hU0 eta m)
    hFne hOmega0 (fun m => R.norm_exponentialFrequency_le m) hRpos
    (BakerProof.initialSamplePoints
      (stageSampleCount (structuredBase R.n u) (iterationLength R.n)))
    (stageOrder R.n (structuredBase R.n u) (iterationLength R.n))
    (fun z hz => BakerProof.norm_le_card_of_mem_initialSamplePoints hz) horder
  rw [BakerProof.card_initialSamplePoints, R.card_exponentialColumn] at hest
  set h : ℕ := stageOrder R.n (structuredBase R.n u) (iterationLength R.n) *
    stageSampleCount (structuredBase R.n u) (iterationLength R.n) with hh
  set Rr : ℝ := ((stageSampleCount (structuredBase R.n u) (iterationLength R.n) : ℕ) : ℝ) with hRr
  set TM : ℝ := terminalMajorant
    (((exponentWidth R.n (structuredBase R.n u) : ℕ) : ℝ) * R.lambdaNormSum) Rr
    (exponentWidth R.n (structuredBase R.n u) ^ R.n *
      additiveWidth R.n (structuredBase R.n u)) with hTM
  have hestTM : (3 * Rr) ^ h ≤ (2 * Rr) ^ h * TM := by
    rw [hTM]
    unfold terminalMajorant
    rw [← mul_assoc]
    exact hest
  have hposbase : (0 : ℝ) < (2 * Rr) ^ h := by positivity
  have hsplit : (3 * Rr) ^ h = ((3 : ℝ) / 2) ^ h * (2 * Rr) ^ h := by
    rw [← mul_pow]
    congr 1
    ring
  have hle : ((3 : ℝ) / 2) ^ h ≤ TM := by
    rw [hsplit, mul_comm ((2 * Rr) ^ h) TM] at hestTM
    exact le_of_mul_le_mul_right hestTM hposbase
  have hone : ((3 : ℝ) / 2) ^ h * ((2 : ℝ) / 3) ^ h = 1 := by
    rw [← mul_pow]
    norm_num
  have hfinal : (1 : ℝ) ≤ TM * ((2 : ℝ) / 3) ^ h := by
    calc
      (1 : ℝ) = ((3 : ℝ) / 2) ^ h * ((2 : ℝ) / 3) ^ h := hone.symm
      _ ≤ TM * ((2 : ℝ) / 3) ^ h :=
        mul_le_mul_of_nonneg_right hle (by positivity)
  linarith [hterm]

end GeneralParameters

end GaloisForLFunctions.RHTower.BakerGeneralProof

namespace GaloisForLFunctions.RHTower

/-- **Baker's theorem for arbitrary chosen logarithms of algebraic numbers, including the
inhomogeneous extension.**  If the logarithms are `ℚ`-linearly independent, then `1` together with
them is linearly independent over the field of algebraic numbers. -/
theorem bakerTheorem_holds : BakerTheorem := by
  intro n lambda halg hind
  by_contra hnot
  obtain ⟨R, -⟩ :=
    BakerGeneralProof.exists_solvedRelation_of_not_full_linearIndependent lambda halg hind hnot
  exact R.false_of_long_extrapolation

end GaloisForLFunctions.RHTower
