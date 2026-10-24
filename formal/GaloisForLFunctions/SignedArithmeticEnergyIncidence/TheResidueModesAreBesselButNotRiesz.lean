import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheRieszResidueExpansionConvergesAtHalfDamping
import GaloisForLFunctions.RHTower.MobiusDiscretePacketEdgeEstimates
import GaloisForLFunctions.RHTower.MobiusHilbertLogarithmicMertensBound

/-!
# The residue modes are Bessel but not Riesz

In the receiver norm the residue modes `v_d(n) = −{(n+1)/d}/(n+1)` form a **Bessel family**: for
every finitely supported `c`,
`‖Σ_d c_d v_d‖²_{ℓ²} ≤ 48 Σ_d c_d²` (`sum_sq_finiteResidueCombination_le`).  The Gram is
nonnegative with `⟨v_d, v_e⟩ ≤ 6 min(d,e)^{−1/4} max(d,e)^{−3/4}` (`gram_horizon_le`), and the weighted
Schur test with weights `d^{−½}` gives the bound.  So any square-summable coefficient sequence has a
residue series that converges in `ℓ²`.

They are **not a Riesz family**: no lower bound `β Σ c_d² ≤ ‖Σ c_d v_d‖²` holds on the modes
`d ≥ 2` (`not_riesz_residueModes`).  At half damping the residue series `Σ_d μ(d) d^{−½} v_d`
converges in `ℓ²` (`residuePartialSum_l2_tendsto_half`), while its coefficients have
`Σ μ(d)²/d ≥ Σ_p 1/p = ∞`.  The Gram therefore does not amplify, but it annihilates: the signed
receiver at the threshold exists through cancellation against the non-orthogonal residue Gram, not
through the size of its coefficients.
-/

open MeasureTheory Set Filter Topology
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The residue Gram -/

/-- `{N/d}/N ≤ min(1/N, 1/d)`. -/
theorem fract_div_div_le {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) :
    Int.fract ((N : ℝ) / d) / N ≤ 1 / N ∧ Int.fract ((N : ℝ) / d) / N ≤ 1 / d := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hf1 := Int.fract_lt_one ((N : ℝ) / d)
  have hfx : Int.fract ((N : ℝ) / d) ≤ (N : ℝ) / d := by
    have := Int.floor_nonneg.mpr (by positivity : (0 : ℝ) ≤ (N : ℝ) / d)
    rw [← Int.self_sub_floor]
    have : (0 : ℝ) ≤ ⌊(N : ℝ) / d⌋ := by exact_mod_cast this
    linarith
  constructor
  · exact div_le_div_of_nonneg_right hf1.le hN0.le
  · rw [div_le_iff₀ hN0]
    calc Int.fract ((N : ℝ) / d) ≤ (N : ℝ) / d := hfx
      _ = 1 / d * N := by ring

theorem residueProduct_eq {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (n : ℕ) :
    normalizedResidueProfile d n * normalizedResidueProfile e n =
      (Int.fract (((n : ℝ) + 1) / d) / ((n : ℝ) + 1)) *
        (Int.fract (((n : ℝ) + 1) / e) / ((n : ℝ) + 1)) := by
  rw [normalizedResidueProfile_eq_neg_fract hd, normalizedResidueProfile_eq_neg_fract he]
  ring

/-- The piecewise majorant `g(N) = 1/(de)` on `N ≤ d`, `1/(eN)` on `d < N ≤ e`, `1/N²` beyond. -/
def gramMajorant (d e N : ℕ) : ℝ :=
  if N ≤ d then 1 / ((d : ℝ) * e) else if N ≤ e then 1 / ((e : ℝ) * N) else 1 / (N : ℝ) ^ 2

theorem residueProduct_le_gramMajorant {d e : ℕ} (hd : 1 ≤ d) (hde : d ≤ e) (n : ℕ) :
    normalizedResidueProfile d n * normalizedResidueProfile e n ≤ gramMajorant d e (n + 1) := by
  have he : 1 ≤ e := hd.trans hde
  have hN : 1 ≤ n + 1 := Nat.succ_pos n
  rw [residueProduct_eq hd he]
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  obtain ⟨a1, a2⟩ := fract_div_div_le hN hd
  obtain ⟨b1, b2⟩ := fract_div_div_le hN he
  have a0 : 0 ≤ Int.fract (((n + 1 : ℕ) : ℝ) / d) / ((n + 1 : ℕ) : ℝ) :=
    div_nonneg (Int.fract_nonneg _) (by positivity)
  have b0 : 0 ≤ Int.fract (((n + 1 : ℕ) : ℝ) / e) / ((n + 1 : ℕ) : ℝ) :=
    div_nonneg (Int.fract_nonneg _) (by positivity)
  unfold gramMajorant
  split_ifs with h1 h2
  · refine (mul_le_mul a2 b2 b0 (by positivity)).trans (le_of_eq ?_)
    rw [one_div_mul_one_div]
  · refine (mul_le_mul a1 b2 b0 (by positivity)).trans (le_of_eq ?_)
    rw [one_div_mul_one_div, mul_comm]
  · refine (mul_le_mul a1 b1 b0 (by positivity)).trans (le_of_eq ?_)
    rw [one_div_mul_one_div, sq]

/-- `Σ_{N ≤ e} N^{−3/4} ≤ 4 e^{1/4}`. -/
theorem sum_Icc_rpow_neg_three_quarters_le (e : ℕ) :
    ∑ N ∈ Finset.Icc 1 e, (N : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 4 * (e : ℝ) ^ (1 / 4 : ℝ) := by
  rw [sum_Icc_one_eq_sum_range']
  have h := RHTower.sum_range_rpow_neg_le (3 / 4) (by norm_num) (by norm_num) e
  have e1 : (1 : ℝ) - 3 / 4 = 1 / 4 := by norm_num
  rw [e1] at h
  calc ∑ N ∈ Finset.range e, (((N + 1 : ℕ) : ℝ)) ^ (-(3 / 4 : ℝ))
      = ∑ N ∈ Finset.range e, ((N : ℝ) + 1) ^ (-(3 / 4 : ℝ)) :=
        Finset.sum_congr rfl fun N _ => by push_cast; ring_nf
    _ ≤ (e : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) := h
    _ = 4 * (e : ℝ) ^ (1 / 4 : ℝ) := by ring

/-- `Σ_{d < N ≤ e} 1/N ≤ 4 (e/d)^{1/4}`: the harmonic sum without logarithms. -/
theorem sum_inv_Ioc_le {d e : ℕ} (hd : 1 ≤ d) :
    ∑ N ∈ Finset.Ioc d e, 1 / (N : ℝ) ≤ 4 * ((e : ℝ) / d) ^ (1 / 4 : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hpt : ∀ N ∈ Finset.Ioc d e,
      1 / (N : ℝ) ≤ (d : ℝ) ^ (-(1 / 4 : ℝ)) * (N : ℝ) ^ (-(3 / 4 : ℝ)) := by
    intro N hN
    have hdN : (d : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Ioc.mp hN).1.le
    have hN0 : (0 : ℝ) < N := by linarith
    have h1 : (N : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (d : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hd0 hdN (by norm_num)
    have e1 : 1 / (N : ℝ) = (N : ℝ) ^ (-(1 / 4 : ℝ)) * (N : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_add hN0, show (-(1 / 4 : ℝ)) + -(3 / 4) = -1 by norm_num, Real.rpow_neg_one,
        one_div]
    rw [e1]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hsub : Finset.Ioc d e ⊆ Finset.Icc 1 e := fun N hN => by
    have := Finset.mem_Ioc.mp hN; exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have hsum : ∑ N ∈ Finset.Ioc d e, (N : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 4 * (e : ℝ) ^ (1 / 4 : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun N _ _ => by positivity).trans
      (sum_Icc_rpow_neg_three_quarters_le e)
  calc ∑ N ∈ Finset.Ioc d e, 1 / (N : ℝ)
      ≤ ∑ N ∈ Finset.Ioc d e, (d : ℝ) ^ (-(1 / 4 : ℝ)) * (N : ℝ) ^ (-(3 / 4 : ℝ)) :=
        Finset.sum_le_sum hpt
    _ = (d : ℝ) ^ (-(1 / 4 : ℝ)) * ∑ N ∈ Finset.Ioc d e, (N : ℝ) ^ (-(3 / 4 : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (d : ℝ) ^ (-(1 / 4 : ℝ)) * (4 * (e : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * ((e : ℝ) / d) ^ (1 / 4 : ℝ) := by
        rw [Real.div_rpow (Nat.cast_nonneg e) hd0.le, Real.rpow_neg hd0.le]
        field_simp

/-- **The residue Gram at a horizon**: for `1 ≤ d ≤ e`,
`Σ_{n<T} v_d(n) v_e(n) ≤ 6 d^{−1/4} e^{−3/4}`. -/
theorem gram_horizon_le {d e : ℕ} (hd : 1 ≤ d) (hde : d ≤ e) (T : ℕ) :
    ∑ n ∈ Finset.range T, normalizedResidueProfile d n * normalizedResidueProfile e n ≤
      6 * (d : ℝ) ^ (-(1 / 4 : ℝ)) * (e : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have he : 1 ≤ e := hd.trans hde
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hg0 : ∀ N, 0 ≤ gramMajorant d e N := fun N => by
    unfold gramMajorant; split_ifs <;> positivity
  -- compare with the full majorant up to `T + e`
  have h1 : ∑ n ∈ Finset.range T, normalizedResidueProfile d n * normalizedResidueProfile e n ≤
      ∑ N ∈ Finset.Ioc 0 (T + e), gramMajorant d e N := by
    calc _ ≤ ∑ n ∈ Finset.range T, gramMajorant d e (n + 1) :=
          Finset.sum_le_sum fun n _ => residueProduct_le_gramMajorant hd hde n
      _ = ∑ N ∈ Finset.Icc 1 T, gramMajorant d e N := (sum_Icc_one_eq_sum_range' _ T).symm
      _ ≤ ∑ N ∈ Finset.Ioc 0 (T + e), gramMajorant d e N := by
          rw [Icc_one_eq_Ioc_zero]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right (by omega))
            fun N _ _ => hg0 N
  -- split `(0, T+e] = (0, d] ∪ (d, e] ∪ (e, T+e]`
  have hsplit : ∑ N ∈ Finset.Ioc 0 (T + e), gramMajorant d e N =
      ∑ N ∈ Finset.Ioc 0 d, gramMajorant d e N + ∑ N ∈ Finset.Ioc d e, gramMajorant d e N +
        ∑ N ∈ Finset.Ioc e (T + e), gramMajorant d e N := by
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le d) hde,
      Finset.sum_Ioc_consecutive _ (Nat.zero_le e) (by omega)]
  have p1 : ∑ N ∈ Finset.Ioc 0 d, gramMajorant d e N = 1 / e := by
    rw [Finset.sum_congr rfl fun N hN => by
      unfold gramMajorant; rw [if_pos (Finset.mem_Ioc.mp hN).2]]
    rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
    field_simp
  have p2 : ∑ N ∈ Finset.Ioc d e, gramMajorant d e N ≤ 4 * ((e : ℝ) / d) ^ (1 / 4 : ℝ) / e := by
    rw [Finset.sum_congr rfl fun N hN => by
      have h := Finset.mem_Ioc.mp hN
      unfold gramMajorant; rw [if_neg (by omega), if_pos h.2]]
    have h := sum_inv_Ioc_le (e := e) hd
    calc ∑ N ∈ Finset.Ioc d e, 1 / ((e : ℝ) * N) = (1 / e) * ∑ N ∈ Finset.Ioc d e, 1 / (N : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun N _ => by rw [one_div_mul_one_div]
      _ ≤ (1 / e) * (4 * ((e : ℝ) / d) ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 4 * ((e : ℝ) / d) ^ (1 / 4 : ℝ) / e := by ring
  have p3 : ∑ N ∈ Finset.Ioc e (T + e), gramMajorant d e N ≤ 1 / e := by
    rw [Finset.sum_congr rfl fun N hN => by
      have h := Finset.mem_Ioc.mp hN
      unfold gramMajorant; rw [if_neg (by omega), if_neg (by omega)]]
    have h := RHTower.DiscretePacket.sum_Ioc_rpow_neg_le (s := 1) one_pos he (T + e)
    calc ∑ N ∈ Finset.Ioc e (T + e), 1 / (N : ℝ) ^ 2
        = ∑ N ∈ Finset.Ioc e (T + e), (N : ℝ) ^ (-(1 + 1 : ℝ)) := by
          refine Finset.sum_congr rfl fun N hN => ?_
          have hN0 : (0 : ℝ) < N := by
            have := (Finset.mem_Ioc.mp hN).1; exact_mod_cast (by omega : 0 < N)
          rw [show (-(1 + 1 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hN0.le,
            Real.rpow_natCast, one_div]
      _ ≤ (e : ℝ) ^ (-(1 : ℝ)) / 1 := h
      _ = 1 / e := by rw [Real.rpow_neg_one, div_one, one_div]
  have hq : 1 ≤ ((e : ℝ) / d) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by rw [le_div_iff₀ hd0]; simpa using (by exact_mod_cast hde : (d : ℝ) ≤ e))
      (by norm_num)
  have hfinal : 6 * ((e : ℝ) / d) ^ (1 / 4 : ℝ) / e =
      6 * (d : ℝ) ^ (-(1 / 4 : ℝ)) * (e : ℝ) ^ (-(3 / 4 : ℝ)) := by
    rw [Real.div_rpow he0.le hd0.le, Real.rpow_neg hd0.le,
      show (-(3 / 4 : ℝ)) = (1 / 4) - 1 by norm_num, Real.rpow_sub_one he0.ne']
    field_simp
  rw [← hfinal]
  calc _ ≤ ∑ N ∈ Finset.Ioc 0 (T + e), gramMajorant d e N := h1
    _ = _ := hsplit
    _ ≤ 1 / e + 4 * ((e : ℝ) / d) ^ (1 / 4 : ℝ) / e + 1 / e := by linarith
    _ ≤ 6 * ((e : ℝ) / d) ^ (1 / 4 : ℝ) / e := by
        have e1 : 1 / (e : ℝ) + 4 * ((e : ℝ) / d) ^ (1 / 4 : ℝ) / e + 1 / e =
            (2 + 4 * ((e : ℝ) / d) ^ (1 / 4 : ℝ)) / e := by ring
        rw [e1]
        exact div_le_div_of_nonneg_right (by linarith) he0.le

/-- The symmetric Gram kernel `K(d, e) = 6 min^{−1/4} max^{−3/4}`. -/
def gramKernel (d e : ℕ) : ℝ :=
  6 * ((min d e : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) * ((max d e : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))

theorem gramKernel_symm (d e : ℕ) : gramKernel d e = gramKernel e d := by
  unfold gramKernel; rw [min_comm, max_comm]

theorem gram_horizon_abs_le {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (T : ℕ) :
    0 ≤ ∑ n ∈ Finset.range T, normalizedResidueProfile d n * normalizedResidueProfile e n ∧
      ∑ n ∈ Finset.range T, normalizedResidueProfile d n * normalizedResidueProfile e n ≤
        gramKernel d e := by
  refine ⟨Finset.sum_nonneg fun n _ =>
    mul_nonneg_of_nonpos_of_nonpos (normalizedResidueProfile_nonpos d n)
      (normalizedResidueProfile_nonpos e n), ?_⟩
  rcases le_total d e with h | h
  · unfold gramKernel; rw [min_eq_left h, max_eq_right h]; exact gram_horizon_le hd h T
  · unfold gramKernel; rw [min_eq_right h, max_eq_left h]
    calc _ = ∑ n ∈ Finset.range T, normalizedResidueProfile e n * normalizedResidueProfile d n :=
          Finset.sum_congr rfl fun n _ => mul_comm _ _
      _ ≤ _ := gram_horizon_le he h T

/-- **Schur row bound**: `Σ_{e ≤ D} K(d, e) e^{−½} ≤ 48 d^{−½}`. -/
theorem sum_gramKernel_mul_le {d : ℕ} (hd : 1 ≤ d) (D : ℕ) :
    ∑ e ∈ Finset.Icc 1 D, gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 48 * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  -- split `e ≤ d` and `e > d`
  have hsplit : ∑ e ∈ Finset.Icc 1 D, gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ∑ e ∈ Finset.Icc 1 d, gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) +
        ∑ e ∈ Finset.Ioc d (D + d), gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hnn : ∀ e, 0 ≤ gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) := fun e => by
      unfold gramKernel; positivity
    rw [Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero,
      Finset.sum_Ioc_consecutive _ (Nat.zero_le d) (Nat.le_add_left d D)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right (by omega))
      fun e _ _ => hnn e
  have hlow : ∑ e ∈ Finset.Icc 1 d, gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      24 * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hterm : ∀ e ∈ Finset.Icc 1 d, gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) =
        6 * (d : ℝ) ^ (-(3 / 4 : ℝ)) * (e : ℝ) ^ (-(3 / 4 : ℝ)) := by
      intro e he
      have he' := Finset.mem_Icc.mp he
      have he0 : (0 : ℝ) < e := by exact_mod_cast he'.1
      unfold gramKernel
      rw [min_eq_right he'.2, max_eq_left he'.2,
        show (6 : ℝ) * (e : ℝ) ^ (-(1 / 4 : ℝ)) * (d : ℝ) ^ (-(3 / 4 : ℝ)) * (e : ℝ) ^ (-(1 / 2 : ℝ)) =
          6 * (d : ℝ) ^ (-(3 / 4 : ℝ)) * ((e : ℝ) ^ (-(1 / 4 : ℝ)) * (e : ℝ) ^ (-(1 / 2 : ℝ))) by ring,
        ← Real.rpow_add he0]
      norm_num
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have h := sum_Icc_rpow_neg_three_quarters_le d
    calc 6 * (d : ℝ) ^ (-(3 / 4 : ℝ)) * ∑ e ∈ Finset.Icc 1 d, (e : ℝ) ^ (-(3 / 4 : ℝ))
        ≤ 6 * (d : ℝ) ^ (-(3 / 4 : ℝ)) * (4 * (d : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 24 * ((d : ℝ) ^ (-(3 / 4 : ℝ)) * (d : ℝ) ^ (1 / 4 : ℝ)) := by ring
      _ = 24 * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hd0]; norm_num
  have hhigh : ∑ e ∈ Finset.Ioc d (D + d), gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      24 * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hterm : ∀ e ∈ Finset.Ioc d (D + d), gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) =
        6 * (d : ℝ) ^ (-(1 / 4 : ℝ)) * (e : ℝ) ^ (-(1 / 4 + 1 : ℝ)) := by
      intro e he
      have he' := Finset.mem_Ioc.mp he
      have he0 : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
      unfold gramKernel
      rw [min_eq_left he'.1.le, max_eq_right he'.1.le, mul_assoc, ← Real.rpow_add he0]
      norm_num
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have h := RHTower.DiscretePacket.sum_Ioc_rpow_neg_le (s := 1 / 4) (by norm_num) hd (D + d)
    calc 6 * (d : ℝ) ^ (-(1 / 4 : ℝ)) * ∑ e ∈ Finset.Ioc d (D + d), (e : ℝ) ^ (-(1 / 4 + 1 : ℝ))
        ≤ 6 * (d : ℝ) ^ (-(1 / 4 : ℝ)) * ((d : ℝ) ^ (-(1 / 4 : ℝ)) / (1 / 4)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 24 * ((d : ℝ) ^ (-(1 / 4 : ℝ)) * (d : ℝ) ^ (-(1 / 4 : ℝ))) := by ring
      _ = 24 * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hd0]; norm_num
  linarith

/-! ### Bessel -/

/-- **The residue modes are Bessel in the receiver norm**:
`Σ_{n<T} (Σ_{d ≤ D} c_d v_d(n))² ≤ 48 Σ_{d ≤ D} c_d²`. -/
theorem sum_sq_finiteResidueCombination_le (D : ℕ) (c : ℕ → ℝ) (T : ℕ) :
    ∑ n ∈ Finset.range T, (∑ d ∈ Finset.Icc 1 D, c d * normalizedResidueProfile d n) ^ 2 ≤
      48 * ∑ d ∈ Finset.Icc 1 D, c d ^ 2 := by
  -- expand the square into the Gram
  have hexp : ∑ n ∈ Finset.range T, (∑ d ∈ Finset.Icc 1 D, c d * normalizedResidueProfile d n) ^ 2 =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, c d * c e *
        ∑ n ∈ Finset.range T, normalizedResidueProfile d n * normalizedResidueProfile e n := by
    simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun n _ => by ring
  rw [hexp]
  -- weighted Schur with `w_d = d^{−½}`
  have hw : ∀ d ∈ Finset.Icc 1 D, (0 : ℝ) < (d : ℝ) ^ (-(1 / 2 : ℝ)) := fun d hd => by
    have : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    positivity
  have hterm : ∀ d ∈ Finset.Icc 1 D, ∀ e ∈ Finset.Icc 1 D,
      c d * c e * ∑ n ∈ Finset.range T, normalizedResidueProfile d n * normalizedResidueProfile e n ≤
        gramKernel d e / 2 * (c d ^ 2 * ((e : ℝ) ^ (-(1 / 2 : ℝ)) / (d : ℝ) ^ (-(1 / 2 : ℝ))) +
          c e ^ 2 * ((d : ℝ) ^ (-(1 / 2 : ℝ)) / (e : ℝ) ^ (-(1 / 2 : ℝ)))) := by
    intro d hd e he
    obtain ⟨g0, g1⟩ := gram_horizon_abs_le (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1 T
    set G := ∑ n ∈ Finset.range T, normalizedResidueProfile d n * normalizedResidueProfile e n
    set wd := (d : ℝ) ^ (-(1 / 2 : ℝ))
    set we := (e : ℝ) ^ (-(1 / 2 : ℝ))
    have hwd := hw d hd
    have hwe := hw e he
    -- `2|c_d c_e| ≤ c_d² w_e/w_d + c_e² w_d/w_e`
    have hAM : 2 * |c d * c e| ≤ c d ^ 2 * (we / wd) + c e ^ 2 * (wd / we) := by
      set r := we / wd with hr
      have hr0 : 0 < r := div_pos hwe hwd
      have hinv : wd / we = 1 / r := by rw [hr, one_div_div]
      rw [hinv]
      have key : 0 ≤ (|c d| * r - |c e|) ^ 2 / r := div_nonneg (sq_nonneg _) hr0.le
      have expand : (|c d| * r - |c e|) ^ 2 / r = c d ^ 2 * r - 2 * |c d * c e| + c e ^ 2 * (1 / r) := by
        rw [abs_mul]
        field_simp
        rw [← sq_abs (c d), ← sq_abs (c e)]
        ring
      linarith
    calc c d * c e * G ≤ |c d * c e| * G := mul_le_mul_of_nonneg_right (le_abs_self _) g0
      _ ≤ |c d * c e| * gramKernel d e := mul_le_mul_of_nonneg_left g1 (abs_nonneg _)
      _ ≤ gramKernel d e / 2 * (c d ^ 2 * (we / wd) + c e ^ 2 * (wd / we)) := by
          have hK : 0 ≤ gramKernel d e := by unfold gramKernel; positivity
          nlinarith
  have hrow : ∀ d ∈ Finset.Icc 1 D,
      ∑ e ∈ Finset.Icc 1 D, gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        48 * (d : ℝ) ^ (-(1 / 2 : ℝ)) := fun d hd => sum_gramKernel_mul_le (Finset.mem_Icc.mp hd).1 D
  calc ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, c d * c e *
        ∑ n ∈ Finset.range T, normalizedResidueProfile d n * normalizedResidueProfile e n
      ≤ ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, gramKernel d e / 2 *
          (c d ^ 2 * ((e : ℝ) ^ (-(1 / 2 : ℝ)) / (d : ℝ) ^ (-(1 / 2 : ℝ))) +
            c e ^ 2 * ((d : ℝ) ^ (-(1 / 2 : ℝ)) / (e : ℝ) ^ (-(1 / 2 : ℝ)))) :=
        Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun e he => hterm d hd e he
    _ = ∑ d ∈ Finset.Icc 1 D, c d ^ 2 / (d : ℝ) ^ (-(1 / 2 : ℝ)) *
          ∑ e ∈ Finset.Icc 1 D, gramKernel d e * (e : ℝ) ^ (-(1 / 2 : ℝ)) := by
        -- symmetrize the second half
        have hs : ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, gramKernel d e / 2 *
            (c e ^ 2 * ((d : ℝ) ^ (-(1 / 2 : ℝ)) / (e : ℝ) ^ (-(1 / 2 : ℝ)))) =
            ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, gramKernel d e / 2 *
            (c d ^ 2 * ((e : ℝ) ^ (-(1 / 2 : ℝ)) / (d : ℝ) ^ (-(1 / 2 : ℝ)))) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => by
            rw [gramKernel_symm]
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [hs, ← two_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ ≤ ∑ d ∈ Finset.Icc 1 D, c d ^ 2 / (d : ℝ) ^ (-(1 / 2 : ℝ)) * (48 * (d : ℝ) ^ (-(1 / 2 : ℝ))) :=
        Finset.sum_le_sum fun d hd =>
          mul_le_mul_of_nonneg_left (hrow d hd) (div_nonneg (sq_nonneg _) (hw d hd).le)
    _ = 48 * ∑ d ∈ Finset.Icc 1 D, c d ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have := (hw d hd).ne'
        field_simp

/-! ### Not Riesz -/

/-- `Σ_{d ≤ N} μ(d)²/d` is unbounded: it dominates `Σ_{p ≤ N} 1/p`. -/
theorem tendsto_sum_moebius_sq_div :
    Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / d)
      atTop atTop := by
  set ind : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) with hind
  have hind0 : ∀ n, 0 ≤ ind n := fun n => by
    simp only [hind, Set.indicator]; split_ifs <;> positivity
  have hp := (not_summable_iff_tendsto_nat_atTop_of_nonneg hind0).mp not_summable_one_div_on_primes
  refine tendsto_atTop_mono (fun N => ?_) (hp.comp (tendsto_add_atTop_nat 1))
  simp only [Function.comp]
  rw [Finset.sum_range_succ', sum_Icc_one_eq_sum_range']
  have h0 : ind 0 = 0 := by simp [hind, Nat.not_prime_zero]
  rw [h0, add_zero]
  refine Finset.sum_le_sum fun d _ => ?_
  simp only [hind, Set.indicator, Set.mem_setOf_eq]
  split_ifs with hpr
  · rw [ArithmeticFunction.moebius_apply_prime hpr]
    push_cast
    norm_num
  · positivity

theorem residuePartialSum_eq_Icc_two (N n : ℕ) :
    residuePartialSum N n = ∑ d ∈ Finset.Icc 2 N,
      (((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ))) *
        normalizedResidueProfile d n := by
  unfold residuePartialSum residueTerm
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [Icc_one_eq_Ioc_zero, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hN,
    show Finset.Icc 2 N = Finset.Ioc 1 N by simpa using Finset.Icc_add_one_left_eq_Ioc 1 N]
  simp [normalizedResidueProfile_one]

/-- **The residue modes are not a Riesz family**: there is no `β > 0` with
`β Σ_{2 ≤ d ≤ D} c_d² ≤ ‖Σ c_d v_d‖²` for all finitely supported `c`.  Otherwise the convergent
residue series at half damping would force `Σ μ(d)²/d < ∞`. -/
theorem not_riesz_residueModes :
    ¬ ∃ β : ℝ, 0 < β ∧ ∀ (D : ℕ) (c : ℕ → ℝ), ∃ T : ℕ,
      β * ∑ d ∈ Finset.Icc 2 D, c d ^ 2 ≤
        ∑ n ∈ Finset.range T, (∑ d ∈ Finset.Icc 2 D, c d * normalizedResidueProfile d n) ^ 2 := by
  rintro ⟨β, hβ, hR⟩
  have hsum : Summable fun n => orbitCoord (1 / 2) n ^ 2 := by
    have h := (admits_iff_summable_orbit (by norm_num : (0 : ℝ) < 1 / 2)).mp
      (admits_dampedMobiusEnergy_of_half_le le_rfl)
    simpa only [centeredOperator_reciprocal_eq_orbitCoord] using h
  set U := ∑' n, orbitCoord (1 / 2) n ^ 2 with hU
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (residuePartialSum_l2_tendsto_half 1 one_pos)
  have hbound : ∀ N, N₀ ≤ N → ∀ T : ℕ,
      ∑ n ∈ Finset.range T, residuePartialSum N n ^ 2 ≤ 2 + 2 * U := by
    intro N hN T
    have h1 := hN₀ N hN T
    have h2 : ∑ n ∈ Finset.range T, orbitCoord (1 / 2) n ^ 2 ≤ U :=
      hsum.sum_le_tsum _ fun n _ => sq_nonneg _
    calc ∑ n ∈ Finset.range T, residuePartialSum N n ^ 2
        ≤ ∑ n ∈ Finset.range T, (2 * (residuePartialSum N n - orbitCoord (1 / 2) n) ^ 2 +
            2 * orbitCoord (1 / 2) n ^ 2) :=
          Finset.sum_le_sum fun n _ => by
            nlinarith [sq_nonneg (residuePartialSum N n - 2 * orbitCoord (1 / 2) n)]
      _ = 2 * ∑ n ∈ Finset.range T, (residuePartialSum N n - orbitCoord (1 / 2) n) ^ 2 +
            2 * ∑ n ∈ Finset.range T, orbitCoord (1 / 2) n ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * 1 + 2 * U := by linarith
      _ = 2 + 2 * U := by ring
  -- the squarefree sum stays bounded, a contradiction
  have hle : ∀ N, N₀ ≤ N →
      ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / d ≤ 1 + (2 + 2 * U) / β := by
    intro N hN
    obtain ⟨T, hT⟩ := hR N fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ))
    have hc : ∀ d ∈ Finset.Icc 2 N, (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (d : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / d := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by have := (Finset.mem_Icc.mp hd).1; omega : 0 < d)
      rw [mul_pow, ← Real.rpow_natCast ((d : ℝ) ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul hd0.le]
      norm_num
      rw [Real.rpow_neg_one, div_eq_mul_inv]
    rw [Finset.sum_congr rfl hc] at hT
    simp only [← residuePartialSum_eq_Icc_two] at hT
    have h2 := (hT.trans (hbound N hN T))
    have h3 : ∑ d ∈ Finset.Icc 2 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / d ≤
        (2 + 2 * U) / β := by rw [le_div_iff₀ hβ]; linarith
    rcases Nat.eq_zero_or_pos N with rfl | hN1
    · simp; positivity
    rw [Icc_one_eq_Ioc_zero, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hN1,
      show Finset.Ioc 1 N = Finset.Icc 2 N by
        exact (by simpa using Finset.Icc_add_one_left_eq_Ioc 1 N : Finset.Icc 2 N = Finset.Ioc 1 N).symm]
    simp only [show Finset.Ioc 0 1 = {1} from rfl, Finset.sum_singleton,
      ArithmeticFunction.moebius_apply_one]
    norm_num
    linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (tendsto_sum_moebius_sq_div.eventually (eventually_gt_atTop (1 + (2 + 2 * U) / β)))
  have := hN₁ (max N₀ N₁) (le_max_right _ _)
  have := hle (max N₀ N₁) (le_max_left _ _)
  linarith

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
