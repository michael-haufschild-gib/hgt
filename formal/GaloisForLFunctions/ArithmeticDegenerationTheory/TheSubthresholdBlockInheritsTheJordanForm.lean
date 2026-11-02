import GaloisForLFunctions.ArithmeticDegenerationTheory.TheSubthresholdBlockIsUniformlyJordan
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheWeilEnergiesOfTheArithmeticModes
import GaloisForLFunctions.BiScaleUncertainty.SieveCoordinateSupNorm
import GaloisForLFunctions.SuccessorShellArithmetic.TheShellsAloneCostTheSquareOfTheOverlap

/-!
# The subthreshold block inherits the Jordan form

The limiting mixed structure (`TheLimitingMixedStructure`) holds on every fixed finite packet of
conductors. This file proves it on the whole **growing** subthreshold block: along every schedule
`c_N → ∞`, `c_N ≤ (log N)^α`, `α < 1/8`, and for every `ε > 0` there is `X` such that eventually, for
all coefficients `b` on the block `{e ≤ c_N/X}`,

`|c_N⁷ ⟨W x, x⟩ − Σ_e J(e) b_e²| ≤ ε Σ_e J(e) b_e²`,   `x = Σ_e b_e r_e`

(`eventually_subthreshold_block_jordan`). The polarization of the rescaled limit is inherited, with
arbitrarily small loss, on the whole degenerating part of the conductor spectrum, past the
universal regime `1/9` of the whole space.

Three errors are controlled, each relative to the Jordan form:
* the **diagonal**: `c⁷E_e − J(e)`, by the uniform Jordan law on the subthreshold block;
* the **non-orthogonality** of the packets: `|⟨r_e, r_{e'}⟩ − δ| ≤ (2ee'(√(φ(e)φ(e')) + 1) + 1)/log N`
  (`abs_inner_normalizedRamanujanHorizonVector_sub_le`), from the periodicity of Ramanujan sums and
  their orthogonality over a period; weighted by the spread `√(J_max/J_min) ≤ √ζ(8) Q⁴` of the
  Jordan coefficients it costs `O(Q⁸/log N)`;
* the **extension data**: their Hilbert–Schmidt norm relative to the margins (HWV), which vanishes
  below `1/8`.
-/

noncomputable section

open Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis HodgeTheoryWithoutVarieties BezoutValuationIncidence

/-! ## Non-orthogonality of the packets -/

theorem abs_normalizedRamanujanMode_le {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |normalizedRamanujanMode m n| ≤ Real.sqrt m.totient := by
  have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  rw [normalizedRamanujanMode, TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hm,
    abs_div, abs_of_pos (Real.sqrt_pos.mpr ht), div_le_iff₀ (Real.sqrt_pos.mpr ht),
    Real.mul_self_sqrt ht.le]
  exact BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m n

/-- **Uniform non-orthogonality of the conductor packets.** -/
theorem abs_inner_normalizedRamanujanHorizonVector_sub_le {m l N : ℕ} (hm : 0 < m) (hl : 0 < l)
    (hN : 2 ≤ N) :
    |⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        (if m = l then 1 else 0)| ≤
      (2 * ((m * l : ℕ) : ℝ) * (Real.sqrt m.totient * Real.sqrt l.totient + 1) + 1) / Real.log N := by
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  set δ : ℝ := if m = l then 1 else 0
  set ψ : ℕ → ℝ := fun n => normalizedRamanujanMode m n * normalizedRamanujanMode l n - δ
  have hq : 1 ≤ m * l := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm.ne' hl.ne')
  have hper : ∀ n, ψ (n + m * l) = ψ n := by
    intro n
    have h1 : normalizedRamanujanMode m (n + m * l) = normalizedRamanujanMode m n := by
      simpa [Nat.cast_id, Nat.mul_comm] using ((normalizedRamanujanMode_periodic hm).nat_mul l) n
    have h2 : normalizedRamanujanMode l (n + m * l) = normalizedRamanujanMode l n := by
      simpa [Nat.cast_id] using ((normalizedRamanujanMode_periodic hl).nat_mul m) n
    simp only [ψ, h1, h2]
  have hmean : ∑ r ∈ range (m * l), ψ r = 0 := by
    have h := periodMean_normalizedRamanujanMode_mul hm hl (dvd_mul_right m l) (dvd_mul_left l m)
      (by omega)
    have hq0 : ((m * l : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m * l ≠ 0 by omega)
    simp only [RenormalizedBiarithmeticGeometry.periodMean] at h
    simp only [ψ, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [div_eq_iff hq0] at h
    rw [h]
    simp only [δ]
    ring
  have hB : ∀ n, |ψ n| ≤ Real.sqrt m.totient * Real.sqrt l.totient + 1 := by
    intro n
    calc |ψ n| ≤ |normalizedRamanujanMode m n * normalizedRamanujanMode l n| + |δ| := abs_sub _ _
      _ ≤ Real.sqrt m.totient * Real.sqrt l.totient + 1 := by
          rw [abs_mul]
          gcongr
          · exact abs_normalizedRamanujanMode_le hm n
          · exact abs_normalizedRamanujanMode_le hl n
          · simp only [δ]; split_ifs <;> simp
  have hsum := abs_sum_Icc_periodic_div_le (N := N) hq ψ hper hmean hB
  have hharm := SuccessorShellArithmetic.harmonic_sum_bounds N
  have hsplit : ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n =
      ∑ n ∈ Icc 1 N, ψ n / n + δ * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    simp only [ramanujanPoleProfile, ψ]
    field_simp
    rw [Real.sq_sqrt hn0.le]
    ring
  rw [normalizedRamanujanHorizonVector_inner, hsplit]
  rw [show (∑ n ∈ Icc 1 N, ψ n / n + δ * ∑ n ∈ Icc 1 N, 1 / (n : ℝ)) / Real.log N - δ =
      (∑ n ∈ Icc 1 N, ψ n / n + δ * (∑ n ∈ Icc 1 N, 1 / (n : ℝ) - Real.log N)) / Real.log N by
    field_simp; ring, abs_div, abs_of_pos hL]
  refine div_le_div_of_nonneg_right ?_ hL.le
  have hδ : |δ * (∑ n ∈ Icc 1 N, 1 / (n : ℝ) - Real.log N)| ≤ 1 := by
    rw [abs_mul]
    have h1 : |δ| ≤ 1 := by simp only [δ]; split_ifs <;> simp
    have h2 : |∑ n ∈ Icc 1 N, 1 / (n : ℝ) - Real.log N| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hharm.1, hharm.2]
    nlinarith [abs_nonneg δ, abs_nonneg (∑ n ∈ Icc 1 N, 1 / (n : ℝ) - Real.log N)]
  calc |∑ n ∈ Icc 1 N, ψ n / n + δ * (∑ n ∈ Icc 1 N, 1 / (n : ℝ) - Real.log N)|
      ≤ |∑ n ∈ Icc 1 N, ψ n / n| + |δ * (∑ n ∈ Icc 1 N, 1 / (n : ℝ) - Real.log N)| := abs_add_le _ _
    _ ≤ 2 * ((m * l : ℕ) : ℝ) * (Real.sqrt m.totient * Real.sqrt l.totient + 1) + 1 := by
        push_cast at hsum ⊢
        linarith

/-! ## The spread of the Jordan coefficients -/

theorem coprimeZetaSum_le_zetaSum (m : ℕ) : coprimeZetaSum 8 m ≤ zetaSum 8 := by
  have hs := summable_shift_rpow_neg (k := 8) (by norm_num)
  exact (summable_coprime_shift_rpow_neg (k := 8) (by norm_num) m).tsum_le_tsum
    (fun n => by split_ifs <;> [exact le_rfl; positivity]) hs

/-- The Jordan constant `K = 2A_φ/M`. -/
def jordanConstant : ℝ := 2 / (∫ u, tiltedUnitSpline u ^ 2) * tiltedTailConstant

theorem jordanConstant_pos : 0 < jordanConstant := by
  have := tiltedTailConstant_pos
  have := integral_tiltedUnitSpline_sq_pos
  unfold jordanConstant
  positivity

/-- `K ≤ J(m) ≤ K ζ(8) m⁸`. -/
theorem jordanCoefficient_bounds {m : ℕ} (hm : 0 < m) :
    jordanConstant ≤ jordanCoefficient m ∧
      jordanCoefficient m ≤ jordanConstant * zetaSum 8 * (m : ℝ) ^ 8 := by
  have hφ1 : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hφm : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hS1 := one_le_coprimeZetaSum (k := 8) (by norm_num) m
  have hSZ := coprimeZetaSum_le_zetaSum m
  have hK := jordanConstant_pos
  have hrw : jordanCoefficient m = jordanConstant * ((m : ℝ) ^ 8 / m.totient) * coprimeZetaSum 8 m := by
    rw [jordanCoefficient_eq_coprime hm, jordanConstant,
      show ((m : ℝ) ^ (8 : ℝ)) = (m : ℝ) ^ 8 by norm_cast]
    field_simp
  rw [hrw]
  have hratio : 1 ≤ (m : ℝ) ^ 8 / m.totient := by
    rw [le_div_iff₀ (by linarith)]
    calc 1 * (m.totient : ℝ) ≤ m := by linarith
      _ ≤ (m : ℝ) ^ 8 := by
          calc (m : ℝ) = (m : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (m : ℝ) ^ 8 := pow_le_pow_right₀ hm1 (by norm_num)
  have hratio' : (m : ℝ) ^ 8 / m.totient ≤ (m : ℝ) ^ 8 := div_le_self (by positivity) hφ1
  constructor
  · calc jordanConstant = jordanConstant * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc jordanConstant * ((m : ℝ) ^ 8 / m.totient) * coprimeZetaSum 8 m
        ≤ jordanConstant * ((m : ℝ) ^ 8) * zetaSum 8 := by gcongr
      _ = jordanConstant * zetaSum 8 * (m : ℝ) ^ 8 := by ring

/-! ## A bilinear Cauchy–Schwarz -/

/-- `|Σ u_e u_{e'} M_{ee'}| ≤ (Σ u_e²) ‖M‖_HS`. -/
theorem abs_bilinear_le_hs (S : Finset ℕ) (u : ℕ → ℝ) (M : ℕ → ℕ → ℝ) :
    |∑ e ∈ S, ∑ e' ∈ S, u e * u e' * M e e'| ≤
      (∑ e ∈ S, u e ^ 2) * Real.sqrt (∑ e ∈ S, ∑ e' ∈ S, M e e' ^ 2) := by
  rw [← sum_product' (f := fun e e' => u e * u e' * M e e'),
    ← sum_product' (f := fun e e' => M e e' ^ 2)]
  have hcs := sum_mul_sq_le_sq_mul_sq (S ×ˢ S) (fun p => u p.1 * u p.2) (fun p => M p.1 p.2)
  have huu : ∑ p ∈ S ×ˢ S, (u p.1 * u p.2) ^ 2 = (∑ e ∈ S, u e ^ 2) ^ 2 := by
    rw [sq (∑ e ∈ S, u e ^ 2), sum_mul_sum, ← sum_product']
    exact sum_congr rfl fun p _ => by ring
  rw [huu] at hcs
  have h0 : 0 ≤ ∑ e ∈ S, u e ^ 2 := sum_nonneg fun e _ => sq_nonneg _
  rw [← Real.sqrt_sq (abs_nonneg _), ← Real.sqrt_sq h0, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (by rw [sq_abs]; exact hcs)

/-! ## The main theorem -/

/-- `Σ_{e,e'} |b_e||b_{e'}| J(e) ≤ √ζ(8) Q⁵ Σ J(e) b_e²` on a block of conductors `≤ Q`. -/
theorem sum_abs_mul_jordan_le {Q : ℕ} (b : ℕ → ℝ) :
    ∑ e ∈ Icc 1 Q, ∑ e' ∈ Icc 1 Q, |b e| * |b e'| * jordanCoefficient e ≤
      Real.sqrt (zetaSum 8) * (Q : ℝ) ^ 5 * ∑ e ∈ Icc 1 Q, jordanCoefficient e * b e ^ 2 := by
  set S := Icc 1 Q
  set K := jordanConstant
  set Z := zetaSum 8
  have hK := jordanConstant_pos
  have hmem : ∀ e ∈ S, 0 < e := fun e he => (mem_Icc.mp he).1
  have hJpos : ∀ e ∈ S, 0 < jordanCoefficient e := fun e he => jordanCoefficient_pos (hmem e he)
  have hJlo : ∀ e ∈ S, K ≤ jordanCoefficient e := fun e he => (jordanCoefficient_bounds (hmem e he)).1
  have hJhi : ∀ e ∈ S, jordanCoefficient e ≤ K * Z * (Q : ℝ) ^ 8 := fun e he => by
    refine (jordanCoefficient_bounds (hmem e he)).2.trans ?_
    have : (e : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp he).2
    have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
    gcongr
  set u : ℕ → ℝ := fun e => Real.sqrt (jordanCoefficient e) * |b e|
  have hu2 : ∀ e ∈ S, u e ^ 2 = jordanCoefficient e * b e ^ 2 := fun e he => by
    simp only [u, mul_pow, Real.sq_sqrt (hJpos e he).le, sq_abs]
  -- factor the double sum
  have hfac : ∑ e ∈ S, ∑ e' ∈ S, |b e| * |b e'| * jordanCoefficient e =
      (∑ e ∈ S, Real.sqrt (jordanCoefficient e) * u e) *
        (∑ e' ∈ S, u e' / Real.sqrt (jordanCoefficient e')) := by
    rw [sum_mul_sum]
    refine sum_congr rfl fun e he => sum_congr rfl fun e' he' => ?_
    have h1 := Real.sqrt_pos.mpr (hJpos e he)
    have h2 := Real.sqrt_pos.mpr (hJpos e' he')
    have h3 : Real.sqrt (jordanCoefficient e) * Real.sqrt (jordanCoefficient e) = jordanCoefficient e :=
      Real.mul_self_sqrt (hJpos e he).le
    simp only [u]
    rw [mul_div_cancel_left₀ _ h2.ne',
      show Real.sqrt (jordanCoefficient e) * (Real.sqrt (jordanCoefficient e) * |b e|) * |b e'| =
        (Real.sqrt (jordanCoefficient e) * Real.sqrt (jordanCoefficient e)) * (|b e| * |b e'|) by ring,
      h3]
    ring
  have hcs1 := sum_mul_sq_le_sq_mul_sq S (fun e => Real.sqrt (jordanCoefficient e)) u
  have hcs2 := sum_mul_sq_le_sq_mul_sq S (fun e => 1 / Real.sqrt (jordanCoefficient e)) u
  have hsumJ : ∑ e ∈ S, Real.sqrt (jordanCoefficient e) ^ 2 ≤ Q * (K * Z * (Q : ℝ) ^ 8) := by
    calc ∑ e ∈ S, Real.sqrt (jordanCoefficient e) ^ 2 = ∑ e ∈ S, jordanCoefficient e :=
          sum_congr rfl fun e he => Real.sq_sqrt (hJpos e he).le
      _ ≤ ∑ e ∈ S, K * Z * (Q : ℝ) ^ 8 := sum_le_sum hJhi
      _ = Q * (K * Z * (Q : ℝ) ^ 8) := by simp [S]
  have hsuminv : ∑ e ∈ S, (1 / Real.sqrt (jordanCoefficient e)) ^ 2 ≤ Q * (1 / K) := by
    calc ∑ e ∈ S, (1 / Real.sqrt (jordanCoefficient e)) ^ 2 = ∑ e ∈ S, 1 / jordanCoefficient e :=
          sum_congr rfl fun e he => by rw [div_pow, one_pow, Real.sq_sqrt (hJpos e he).le]
      _ ≤ ∑ e ∈ S, 1 / K := sum_le_sum fun e he =>
          one_div_le_one_div_of_le hK (hJlo e he)
      _ = Q * (1 / K) := by simp [S]
  have hU : 0 ≤ ∑ e ∈ S, u e ^ 2 := sum_nonneg fun e _ => sq_nonneg _
  have hA := Real.sqrt_le_sqrt (hcs1.trans (mul_le_mul_of_nonneg_right hsumJ hU))
  have hB := Real.sqrt_le_sqrt (hcs2.trans (mul_le_mul_of_nonneg_right hsuminv hU))
  rw [Real.sqrt_sq_eq_abs] at hA hB
  have hu_eq : ∑ e ∈ S, u e ^ 2 = ∑ e ∈ S, jordanCoefficient e * b e ^ 2 := sum_congr rfl hu2
  rw [hfac]
  calc (∑ e ∈ S, Real.sqrt (jordanCoefficient e) * u e) * (∑ e' ∈ S, u e' / Real.sqrt (jordanCoefficient e'))
      ≤ |∑ e ∈ S, Real.sqrt (jordanCoefficient e) * u e| *
          |∑ e ∈ S, 1 / Real.sqrt (jordanCoefficient e) * u e| := by
        rw [← abs_mul]
        refine le_trans (le_abs_self _) (le_of_eq ?_)
        congr 2
        exact sum_congr rfl fun e _ => by ring
    _ ≤ Real.sqrt (Q * (K * Z * (Q : ℝ) ^ 8) * ∑ e ∈ S, u e ^ 2) *
          Real.sqrt (Q * (1 / K) * ∑ e ∈ S, u e ^ 2) := mul_le_mul hA hB (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt Z * (Q : ℝ) ^ 5 * ∑ e ∈ S, jordanCoefficient e * b e ^ 2 := by
        have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
        set U := ∑ e ∈ S, u e ^ 2
        have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
        have hp1 : 0 ≤ Q * (K * Z * (Q : ℝ) ^ 8) * U :=
          mul_nonneg (mul_nonneg hQ0 (mul_nonneg (mul_nonneg hK.le hZ0) (by positivity))) hU
        rw [← Real.sqrt_mul hp1, ← hu_eq]
        have hKne : K ≠ 0 := ne_of_gt hK
        have e1 : Q * (K * Z * (Q : ℝ) ^ 8) * U * (Q * (1 / K) * U) =
            (Real.sqrt Z * (Q : ℝ) ^ 5 * U) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hZ0]
          field_simp
        rw [e1, Real.sqrt_sq (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) hU)]

/-- `Σ_{e,e'} (s D_{ee'}/(√J_e √J_{e'}))² ≤ 4 Σ D_{ee'}²/(E_e E_{e'})` when `0 < sE_e ≤ 2J_e`. -/
theorem sum_sq_normalized_le (S : Finset ℕ) (J E : ℕ → ℝ) (D : ℕ → ℕ → ℝ) {s : ℝ} (hs : 0 < s)
    (hJ : ∀ e ∈ S, 0 < J e) (hE : ∀ e ∈ S, 0 < E e) (hsE : ∀ e ∈ S, s * E e ≤ 2 * J e) :
    ∑ e ∈ S, ∑ e' ∈ S, (s * D e e' / (Real.sqrt (J e) * Real.sqrt (J e'))) ^ 2 ≤
      4 * ∑ e ∈ S, ∑ e' ∈ S, D e e' ^ 2 / (E e * E e') := by
  rw [mul_sum]
  refine sum_le_sum fun e he => ?_
  rw [mul_sum]
  refine sum_le_sum fun e' he' => ?_
  have hJe := hJ e he
  have hJe' := hJ e' he'
  have hEe := hE e he
  have hEe' := hE e' he'
  have hratio : (s * E e) * (s * E e') ≤ 4 * (J e * J e') := by
    have h1 := hsE e he
    have h2 := hsE e' he'
    have h3 : 0 ≤ s * E e := (mul_pos hs hEe).le
    have h4 : 0 ≤ s * E e' := (mul_pos hs hEe').le
    calc (s * E e) * (s * E e') ≤ (2 * J e) * (2 * J e') := mul_le_mul h1 h2 h4 (by linarith)
      _ = 4 * (J e * J e') := by ring
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hJe.le, Real.sq_sqrt hJe'.le,
    div_le_iff₀ (mul_pos hJe hJe'),
    show 4 * (D e e' ^ 2 / (E e * E e')) * (J e * J e') = (4 * D e e' ^ 2 * (J e * J e')) / (E e * E e') by
      ring, le_div_iff₀ (mul_pos hEe hEe')]
  have hD2 : 0 ≤ D e e' ^ 2 := sq_nonneg _
  have key := mul_le_mul_of_nonneg_left hratio hD2
  calc s ^ 2 * D e e' ^ 2 * (E e * E e') = D e e' ^ 2 * ((s * E e) * (s * E e')) := by ring
    _ ≤ D e e' ^ 2 * (4 * (J e * J e')) := key
    _ = 4 * D e e' ^ 2 * (J e * J e') := by ring

/-- **The block bound, deterministic form.** If the rescaled diagonal is within `η` of the Jordan
coefficients, the Gram defect is at most `g`, `Σ|b||b'|J ≤ C W` and the normalized extension data
have Hilbert–Schmidt norm at most `h`, then the rescaled block form is within `(η + 2gC + h) W` of
the Jordan form `W = Σ J b²`. -/
theorem block_bound (S : Finset ℕ) (b J A : ℕ → ℝ) (G D : ℕ → ℕ → ℝ) {s η g C h : ℝ}
    (hJ : ∀ e ∈ S, 0 < J e) (hA : ∀ e ∈ S, |A e - J e| ≤ η * J e) (hη : η ≤ 1)
    (hG : ∀ e ∈ S, ∀ e' ∈ S, |G e e' - (if e = e' then 1 else 0)| ≤ g) (hg : 0 ≤ g)
    (hC : ∑ e ∈ S, ∑ e' ∈ S, |b e| * |b e'| * J e ≤ C * ∑ e ∈ S, J e * b e ^ 2)
    (hM : Real.sqrt (∑ e ∈ S, ∑ e' ∈ S, (s * D e e' / (Real.sqrt (J e) * Real.sqrt (J e'))) ^ 2) ≤ h) :
    |∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (A e * G e e' + s * D e e') - ∑ e ∈ S, J e * b e ^ 2| ≤
      (η + 2 * g * C + h) * ∑ e ∈ S, J e * b e ^ 2 := by
  set W := ∑ e ∈ S, J e * b e ^ 2
  have hW0 : 0 ≤ W := sum_nonneg fun e he => mul_nonneg (hJ e he).le (sq_nonneg _)
  have hAle : ∀ e ∈ S, |A e| ≤ 2 * J e := fun e he => by
    have h1 := hA e he
    have h2 := hJ e he
    calc |A e| = |(A e - J e) + J e| := by ring_nf
      _ ≤ |A e - J e| + |J e| := abs_add_le _ _
      _ ≤ η * J e + J e := by rw [abs_of_pos h2]; linarith
      _ ≤ 2 * J e := by nlinarith
  -- the decomposition
  have hdiag : ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (A e * (if e = e' then 1 else 0)) =
      ∑ e ∈ S, b e ^ 2 * A e := by
    refine sum_congr rfl fun e he => ?_
    rw [sum_eq_single_of_mem e he (fun e' _ hne => by simp [Ne.symm hne])]
    simp only [if_true]
    ring
  have hsplit : ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (A e * G e e' + s * D e e') - W =
      ∑ e ∈ S, b e ^ 2 * (A e - J e) +
        ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (A e * (G e e' - if e = e' then 1 else 0)) +
        ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (s * D e e') := by
    have hexp : ∀ e e', b e * b e' * (A e * G e e' + s * D e e') =
        b e * b e' * (A e * (if e = e' then 1 else 0)) +
          b e * b e' * (A e * (G e e' - if e = e' then 1 else 0)) + b e * b e' * (s * D e e') :=
      fun e e' => by ring
    have e1 : ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (A e * G e e' + s * D e e') =
        ∑ e ∈ S, b e ^ 2 * A e +
          ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (A e * (G e e' - if e = e' then 1 else 0)) +
          ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (s * D e e') := by
      simp only [hexp, sum_add_distrib, hdiag]
    have e2 : ∑ e ∈ S, b e ^ 2 * A e - W = ∑ e ∈ S, b e ^ 2 * (A e - J e) := by
      simp only [W]
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun e _ => by ring
    rw [e1, ← e2]
    ring
  rw [hsplit]
  have h1 : |∑ e ∈ S, b e ^ 2 * (A e - J e)| ≤ η * W := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simp only [W, mul_sum]
    refine sum_le_sum fun e he => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hA e he, sq_nonneg (b e)]
  have h2 : |∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (A e * (G e e' - if e = e' then 1 else 0))| ≤
      2 * g * C * W := by
    calc |∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (A e * (G e e' - if e = e' then 1 else 0))|
        ≤ ∑ e ∈ S, ∑ e' ∈ S, (2 * g) * (|b e| * |b e'| * J e) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e he => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e' he' => ?_)
          rw [abs_mul, abs_mul, abs_mul]
          have hq := hG e he e' he'
          have ha := hAle e he
          have hJ0 := (hJ e he).le
          calc |b e| * |b e'| * (|A e| * |G e e' - if e = e' then 1 else 0|)
              ≤ |b e| * |b e'| * (2 * J e * g) := by gcongr
            _ = (2 * g) * (|b e| * |b e'| * J e) := by ring
      _ = (2 * g) * ∑ e ∈ S, ∑ e' ∈ S, |b e| * |b e'| * J e := by
          rw [mul_sum]; exact sum_congr rfl fun e _ => by rw [mul_sum]
      _ ≤ (2 * g) * (C * W) := mul_le_mul_of_nonneg_left hC (by positivity)
      _ = 2 * g * C * W := by ring
  have h3 : |∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (s * D e e')| ≤ h * W := by
    set u : ℕ → ℝ := fun e => Real.sqrt (J e) * b e
    set M : ℕ → ℕ → ℝ := fun e e' => s * D e e' / (Real.sqrt (J e) * Real.sqrt (J e'))
    have hrw : ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (s * D e e') =
        ∑ e ∈ S, ∑ e' ∈ S, u e * u e' * M e e' := by
      refine sum_congr rfl fun e he => sum_congr rfl fun e' he' => ?_
      have h1' := Real.sqrt_pos.mpr (hJ e he)
      have h2' := Real.sqrt_pos.mpr (hJ e' he')
      simp only [u, M]
      field_simp
    have hu2 : ∑ e ∈ S, u e ^ 2 = W := sum_congr rfl fun e he => by
      simp only [u, mul_pow, Real.sq_sqrt (hJ e he).le]
    have hcs := abs_bilinear_le_hs S u M
    rw [← hrw, hu2] at hcs
    refine hcs.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hM hW0
  calc |∑ e ∈ S, b e ^ 2 * (A e - J e) +
        ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (A e * (G e e' - if e = e' then 1 else 0)) +
        ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * (s * D e e')|
      ≤ η * W + 2 * g * C * W + h * W :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)
    _ = (η + 2 * g * C + h) * W := by ring

/-- **The block estimate at one resolution.** All analytic inputs at a single `(c, N)` are passed as
hypotheses; the conclusion is the Jordan bound on the block `[1, Q]`. -/
theorem block_estimate_at {cc ε₀ Kd : ℝ} {N Q k : ℕ} (b : ℕ → ℝ) (hε₀1 : ε₀ ≤ 1)
    (hc7 : 7 ≤ cc) (hQc : (Q : ℝ) ≤ cc) (hN2 : 2 ≤ N) (hKd : 0 < Kd)
    (hdiag : ∀ e ∈ Icc 1 Q, |cc ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline cc e -
      jordanCoefficient e| ≤ ε₀ / 3 * jordanCoefficient e)
    (hgN : 10 * Real.sqrt (zetaSum 8) * (cc ^ 8 / Real.log N) < ε₀ / 3)
    (hdN : 4 * Real.sqrt Kd * (cc ^ 7 * (cc * (1 + Real.log cc) ^ 2 * Real.log N ^ (1 / (k : ℝ)) /
      Real.log N + cc ^ 5 * Real.log N / (N : ℝ))) < ε₀ / 3)
    (hsum : ∑ e ∈ Icc 1 Q, ∑ e' ∈ Icc 1 Q, conductorDeviation cc N e e' ^ 2 /
        (completedConductorEnergy tiltedUnitSpline cc e * completedConductorEnergy tiltedUnitSpline cc e') ≤
      Kd * (cc ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) ^ 2 *
        (cc * (1 + Real.log cc) ^ 2 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
          cc ^ 5 * Real.log N / (N : ℝ)) ^ 2) :
    |∑ e ∈ Icc 1 Q, ∑ e' ∈ Icc 1 Q, b e * b e' * rescaledConductorGram cc N e e' -
        ∑ e ∈ Icc 1 Q, jordanCoefficient e * b e ^ 2| ≤
      ε₀ * ∑ e ∈ Icc 1 Q, jordanCoefficient e * b e ^ 2 := by
  have hc0 : 0 < cc := by linarith only [hc7]
  have hL0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hmemS : ∀ e ∈ Icc 1 Q, 0 < e ∧ (e : ℝ) ≤ Q := fun e he =>
    ⟨(mem_Icc.mp he).1, by exact_mod_cast (mem_Icc.mp he).2⟩
  have hJpos : ∀ e ∈ Icc 1 Q, 0 < jordanCoefficient e := fun e he =>
    jordanCoefficient_pos (hmemS e he).1
  have hc7pos : 0 < cc ^ (7 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hcE_up : ∀ e ∈ Icc 1 Q, cc ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline cc e ≤
      2 * jordanCoefficient e := fun e he => by
    have h := (abs_le.mp (hdiag e he)).2
    have hJ := hJpos e he
    nlinarith only [h, hJ, hε₀1]
  have hEpos : ∀ e ∈ Icc 1 Q, 0 < completedConductorEnergy tiltedUnitSpline cc e := fun e he => by
    have h := (abs_le.mp (hdiag e he)).1
    have hJ := hJpos e he
    have h2 : 0 < cc ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline cc e := by
      nlinarith only [h, hJ, hε₀1]
    exact pos_of_mul_pos_right h2 hc7pos.le
  have hW0 : 0 ≤ ∑ e ∈ Icc 1 Q, jordanCoefficient e * b e ^ 2 :=
    sum_nonneg fun e he => mul_nonneg (hJpos e he).le (sq_nonneg _)
  have hrw : ∑ e ∈ Icc 1 Q, ∑ e' ∈ Icc 1 Q, b e * b e' * rescaledConductorGram cc N e e' =
      ∑ e ∈ Icc 1 Q, ∑ e' ∈ Icc 1 Q, b e * b e' *
        (cc ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline cc e *
            ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫ +
          cc ^ (7 : ℝ) * conductorDeviation cc N e e') := by
    refine sum_congr rfl fun e _ => sum_congr rfl fun e' _ => ?_
    simp only [rescaledConductorGram, conductorDeviation]
    ring
  -- the Gram defect on the block
  have hQ1 : ∀ e ∈ Icc 1 Q, ∀ e' ∈ Icc 1 Q,
      |⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫ -
        (if e = e' then 1 else 0)| ≤ 5 * (Q : ℝ) ^ 3 / Real.log N := by
    intro e he e' he'
    have hg := abs_inner_normalizedRamanujanHorizonVector_sub_le (hmemS e he).1 (hmemS e' he').1 hN2
    refine hg.trans (div_le_div_of_nonneg_right ?_ hL0.le)
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast (hmemS e he).1
    have hQ1' : (1 : ℝ) ≤ Q := he1.trans (hmemS e he).2
    have hφe : Real.sqrt (e.totient : ℝ) ≤ Real.sqrt Q := Real.sqrt_le_sqrt
      ((show ((e.totient : ℕ) : ℝ) ≤ e by exact_mod_cast Nat.totient_le e).trans (hmemS e he).2)
    have hφe' : Real.sqrt (e'.totient : ℝ) ≤ Real.sqrt Q := Real.sqrt_le_sqrt
      ((show ((e'.totient : ℕ) : ℝ) ≤ e' by exact_mod_cast Nat.totient_le e').trans (hmemS e' he').2)
    have hsq : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt (by positivity)
    have hee : ((e * e' : ℕ) : ℝ) ≤ Q ^ 2 := by
      push_cast
      rw [sq]
      exact mul_le_mul (hmemS e he).2 (hmemS e' he').2 (by positivity) (by positivity)
    have hprod : Real.sqrt (e.totient : ℝ) * Real.sqrt (e'.totient : ℝ) ≤ Q :=
      (mul_le_mul hφe hφe' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans hsq.le
    calc 2 * ((e * e' : ℕ) : ℝ) * (Real.sqrt (e.totient : ℝ) * Real.sqrt (e'.totient : ℝ) + 1) + 1
        ≤ 2 * (Q : ℝ) ^ 2 * (Q + 1) + 1 := by gcongr
      _ ≤ 5 * (Q : ℝ) ^ 3 := by nlinarith only [hQ1']
  -- the extension data on the block
  set T' := cc * (1 + Real.log cc) ^ 2 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
    cc ^ 5 * Real.log N / (N : ℝ)
  have hlogQ : Real.log Q ≤ Real.log cc := by
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQ0
    · rw [hQ0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg (by linarith only [hc7])
    · exact Real.log_le_log (by exact_mod_cast hQ0) hQc
  have hB7 : (cc ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) ≤ 2 * cc ^ 7 := by
    have hlc : 1 + Real.log cc ≤ cc := by
      have := Real.log_le_sub_one_of_pos hc0
      linarith only [this]
    have h3' : (1 + Real.log Q) ^ 2 ≤ cc ^ 2 := by
      have hlogQ0 := Real.log_natCast_nonneg Q
      exact pow_le_pow_left₀ (by linarith only [hlogQ0]) (by linarith only [hlogQ, hlc]) 2
    have h4 : (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 ≤ cc ^ 2 * cc ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg Q) hQc 2) h3' (sq_nonneg _) (sq_nonneg _)
    have hc4 : cc ^ 2 * cc ^ 2 ≤ cc ^ 7 := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by linarith only [hc7]) (by norm_num)
    linarith only [h4, hc4]
  have hT'0 : 0 ≤ cc ^ 7 * T' := by
    have : 0 ≤ 1 + Real.log cc := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ cc by linarith only [hc7])
      linarith only [this]
    positivity
  have hrel : ∑ e ∈ Icc 1 Q, ∑ e' ∈ Icc 1 Q, conductorDeviation cc N e e' ^ 2 /
      (completedConductorEnergy tiltedUnitSpline cc e * completedConductorEnergy tiltedUnitSpline cc e') ≤
        4 * Kd * (cc ^ 7 * T') ^ 2 := by
    refine hsum.trans ?_
    have h0 : 0 ≤ cc ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 := by positivity
    calc Kd * (cc ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) ^ 2 * T' ^ 2
        ≤ Kd * (2 * cc ^ 7) ^ 2 * T' ^ 2 := by gcongr
      _ = 4 * Kd * (cc ^ 7 * T') ^ 2 := by ring
  have hM : Real.sqrt (∑ e ∈ Icc 1 Q, ∑ e' ∈ Icc 1 Q,
      (cc ^ (7 : ℝ) * conductorDeviation cc N e e' /
        (Real.sqrt (jordanCoefficient e) * Real.sqrt (jordanCoefficient e'))) ^ 2) ≤
        4 * Real.sqrt Kd * (cc ^ 7 * T') := by
    have hle := sum_sq_normalized_le (Icc 1 Q) jordanCoefficient
      (fun e => completedConductorEnergy tiltedUnitSpline cc e) (fun e e' => conductorDeviation cc N e e')
      hc7pos hJpos hEpos hcE_up
    calc _ ≤ Real.sqrt (4 * (4 * Kd * (cc ^ 7 * T') ^ 2)) :=
          Real.sqrt_le_sqrt (hle.trans (by linarith only [hrel]))
      _ = 4 * Real.sqrt Kd * (cc ^ 7 * T') := by
          have hsq : (4 * Real.sqrt Kd * (cc ^ 7 * T')) ^ 2 = 4 * (4 * Kd * (cc ^ 7 * T') ^ 2) := by
            rw [show (4 * Real.sqrt Kd * (cc ^ 7 * T')) ^ 2 =
              16 * (Real.sqrt Kd) ^ 2 * (cc ^ 7 * T') ^ 2 by ring, Real.sq_sqrt hKd.le]
            ring
          rw [← hsq]
          exact Real.sqrt_sq (by positivity)
  have hbound := block_bound (Icc 1 Q) b jordanCoefficient
    (fun e => cc ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline cc e)
    (fun e e' => ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫)
    (fun e e' => conductorDeviation cc N e e') (s := cc ^ (7 : ℝ)) (η := ε₀ / 3)
    (g := 5 * (Q : ℝ) ^ 3 / Real.log N) (C := Real.sqrt (zetaSum 8) * (Q : ℝ) ^ 5)
    (h := 4 * Real.sqrt Kd * (cc ^ 7 * T')) hJpos hdiag (by linarith only [hε₀1]) hQ1
    (by positivity) (sum_abs_mul_jordan_le b) hM
  rw [hrw]
  refine hbound.trans (mul_le_mul_of_nonneg_right ?_ hW0)
  have hQ8 : (Q : ℝ) ^ 8 ≤ cc ^ 8 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQc 8
  have hg2 : 2 * (5 * (Q : ℝ) ^ 3 / Real.log N) * (Real.sqrt (zetaSum 8) * (Q : ℝ) ^ 5) ≤ ε₀ / 3 := by
    calc 2 * (5 * (Q : ℝ) ^ 3 / Real.log N) * (Real.sqrt (zetaSum 8) * (Q : ℝ) ^ 5)
        = 10 * Real.sqrt (zetaSum 8) * ((Q : ℝ) ^ 8 / Real.log N) := by ring
      _ ≤ 10 * Real.sqrt (zetaSum 8) * (cc ^ 8 / Real.log N) := by gcongr
      _ ≤ ε₀ / 3 := hgN.le
  linarith only [hg2, hdN]

/-- **The subthreshold block inherits the Jordan form.** -/
theorem eventually_subthreshold_block_jordan {α : ℝ} (hα : α < 1 / 8) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (hcα : ∀ᶠ N : ℕ in atTop, c N ≤ Real.log N ^ α) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      |∑ e ∈ Icc 1 ⌊c N / X⌋₊, ∑ e' ∈ Icc 1 ⌊c N / X⌋₊, b e * b e' * rescaledConductorGram (c N) N e e' -
          ∑ e ∈ Icc 1 ⌊c N / X⌋₊, jordanCoefficient e * b e ^ 2| ≤
        ε * ∑ e ∈ Icc 1 ⌊c N / X⌋₊, jordanCoefficient e * b e ^ 2 := by
  have hε₀ : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨X, hX1, hX⟩ := uniform_jordan_law (ε := min ε 1 / 3) (by positivity)
  refine ⟨X, hX1, ?_⟩
  obtain ⟨Kd, hKd, hdev⟩ := exists_relative_conductorDeviation_sum_le
  obtain ⟨k, hk1, henv⟩ := exists_tendsto_envelope hα
  have hT0 := tendsto_schedule_envelope hα hc hcα henv
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hQ8 : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := 1 - 8 * α) (by linarith only [hα])
    refine squeeze_zero' ?_ ?_ (h.comp hL)
    · filter_upwards [hc.eventually_ge_atTop 0] with N hN
      exact div_nonneg (by positivity) (Real.log_natCast_nonneg N)
    · filter_upwards [hc.eventually_ge_atTop 0, hcα, hL.eventually_gt_atTop 0] with N hN hNα hLN
      simp only [Function.comp]
      have h8 : c N ^ 8 ≤ Real.log N ^ (8 * α) := by
        calc c N ^ 8 ≤ (Real.log N ^ α) ^ 8 := pow_le_pow_left₀ hN hNα 8
          _ = Real.log N ^ (8 * α) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hLN.le]; ring_nf
      rw [div_le_iff₀ hLN]
      calc c N ^ 8 ≤ Real.log N ^ (8 * α) := h8
        _ = Real.log N ^ (-(1 - 8 * α)) * Real.log N := by
            rw [← Real.rpow_add_one hLN.ne']; ring_nf
  have hgram : Tendsto (fun N : ℕ => 10 * Real.sqrt (zetaSum 8) * (c N ^ 8 / Real.log N)) atTop
      (𝓝 0) := by
    simpa using hQ8.const_mul (10 * Real.sqrt (zetaSum 8))
  have hdevT : Tendsto (fun N : ℕ => 4 * Real.sqrt Kd * (c N ^ 7 * (c N * (1 + Real.log (c N)) ^ 2 *
      Real.log N ^ (1 / (k : ℝ)) / Real.log N + c N ^ 5 * Real.log N / (N : ℝ)))) atTop (𝓝 0) := by
    simpa using hT0.const_mul (4 * Real.sqrt Kd)
  have hdevN := hdev 1 zero_le_one k hk1
  have hsize := eventually_size_schedule hα hc hcα
  filter_upwards [hgram.eventually (gt_mem_nhds (show (0 : ℝ) < min ε 1 / 3 by positivity)),
    hdevT.eventually (gt_mem_nhds (show (0 : ℝ) < min ε 1 / 3 by positivity)), hdevN, hsize,
    hc.eventually_ge_atTop (max X 7), hcα, hL.eventually_ge_atTop 1,
    eventually_ge_atTop 2] with N hgN hdN hdevN' hsN hcN hcαN hLN hN2 b
  have hcX : X ≤ c N := le_trans (le_max_left _ _) hcN
  have hc7 : (7 : ℝ) ≤ c N := le_trans (le_max_right _ _) hcN
  have hc0 : 0 < c N := by linarith only [hc7]
  have hX0 : 0 < X := by linarith only [hX1]
  have hQc : (⌊c N / X⌋₊ : ℝ) ≤ c N :=
    (Nat.floor_le (by positivity)).trans (div_le_self hc0.le hX1)
  have hQlog : (⌊c N / X⌋₊ : ℝ) ≤ Real.log N ^ (1 : ℝ) := by
    calc (⌊c N / X⌋₊ : ℝ) ≤ c N := hQc
      _ ≤ Real.log N ^ α := hcαN
      _ ≤ Real.log N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hLN (by linarith only [hα])
  have hdiag : ∀ e ∈ Icc 1 ⌊c N / X⌋₊, |c N ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline (c N) e -
      jordanCoefficient e| ≤ min ε 1 / 3 * jordanCoefficient e := fun e he => by
    have he := mem_Icc.mp he
    have h1 : (e : ℝ) ≤ c N / X :=
      (show (e : ℝ) ≤ ⌊c N / X⌋₊ by exact_mod_cast he.2).trans (Nat.floor_le (by positivity))
    rw [le_div_iff₀ hX0] at h1
    exact hX (c N) hc0 e he.1 (by linarith only [h1])
  have h := block_estimate_at (cc := c N) (N := N) (Q := ⌊c N / X⌋₊) (k := k) b (min_le_right _ _)
    hc7 hQc hN2 hKd hdiag hgN hdN (hdevN' (c N) (by linarith only [hc7]) hsN _ hQlog)
  exact h.trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
    (sum_nonneg fun e he => mul_nonneg (jordanCoefficient_pos (mem_Icc.mp he).1).le (sq_nonneg _)))

end GaloisForLFunctions.ArithmeticDegenerationTheory
