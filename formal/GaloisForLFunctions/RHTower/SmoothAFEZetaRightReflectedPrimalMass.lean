import GaloisForLFunctions.RHTower.SmoothAFEZetaRightReflectedPrimal
import GaloisForLFunctions.RHTower.SteinhausLargestPrimePowerMass
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds

/-!
# Actual terminal mass for the reflected right-line primal block

The ordinary Gaussian cutoff is uniformly bounded below on a fixed
inner interval.  Multiplying the ideal right-line power profile by this
cutoff therefore preserves a fixed fraction of every largest-prime
channel and of the aggregate terminal channel mass.
-/

namespace RHTower

open Complex Finset Nat

noncomputable section

/-- Reflection of the left-line upper bound gives the matching lower
conductor envelope on the right line. -/
theorem exists_norm_zetaChi_rightDisplaced_ge_rpow
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ,
      c / (max 1 |τ|) ^ d ≤
        ‖zetaChi (rightDisplacedLinePt d τ)‖ := by
  obtain ⟨K, hK, hleft⟩ :=
    exists_norm_zetaChi_fixed_left_line_le_rpow hd hdhalf
  let c : ℝ := 1 / (K + 1)
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  refine ⟨c, hc, fun τ => ?_⟩
  let M : ℝ := max 1 |τ|
  have hM : 0 < M :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hleft' :
      ‖zetaChi (displacedLinePt d (-τ))‖ ≤
        (K + 1) * M ^ d := by
    have hbase :
        ‖zetaChi (displacedLinePt d (-τ))‖ ≤ K * M ^ d := by
      simpa [displacedLinePt, M, abs_neg] using hleft (-τ)
    exact hbase.trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg hM.le d))
  have hprod := zetaChi_right_mul_reflected_left hd hdhalf τ
  have hprodNorm :
      ‖zetaChi (rightDisplacedLinePt d τ)‖ *
          ‖zetaChi (displacedLinePt d (-τ))‖ = 1 := by
    calc
      ‖zetaChi (rightDisplacedLinePt d τ)‖ *
          ‖zetaChi (displacedLinePt d (-τ))‖ =
          ‖zetaChi (rightDisplacedLinePt d τ) *
            zetaChi (displacedLinePt d (-τ))‖ :=
        (norm_mul _ _).symm
      _ = 1 := by rw [hprod]; norm_num
  have hmul :
      1 ≤ ‖zetaChi (rightDisplacedLinePt d τ)‖ *
          ((K + 1) * M ^ d) := by
    calc
      1 = ‖zetaChi (rightDisplacedLinePt d τ)‖ *
          ‖zetaChi (displacedLinePt d (-τ))‖ := hprodNorm.symm
      _ ≤ ‖zetaChi (rightDisplacedLinePt d τ)‖ *
          ((K + 1) * M ^ d) :=
        mul_le_mul_of_nonneg_left hleft'
          (norm_nonneg (zetaChi (rightDisplacedLinePt d τ)))
  have hden : 0 < (K + 1) * M ^ d := by positivity
  have hinv :
      1 / ((K + 1) * M ^ d) ≤
        ‖zetaChi (rightDisplacedLinePt d τ)‖ := by
    apply (div_le_iff₀ hden).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    c / (max 1 |τ|) ^ d = 1 / ((K + 1) * M ^ d) := by
      dsimp only [c, M]
      have hK1 : K + 1 ≠ 0 := by linarith
      have hpow : (max 1 |τ|) ^ d ≠ 0 :=
        (Real.rpow_pos_of_pos hM d).ne'
      field_simp [hK1, hpow]
    _ ≤ ‖zetaChi (rightDisplacedLinePt d τ)‖ := hinv

/-- On every dyadic height window `[N,2N]`, the right chi factor has a
uniform lower bound at the natural conductor scale. -/
theorem exists_norm_zetaChi_rightDisplaced_ge_nat_window
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ}, 1 ≤ N → ∀ τ ∈ Set.Icc (N : ℝ) (2 * N : ℝ),
      c * (N : ℝ) ^ (-d) ≤
        ‖zetaChi (rightDisplacedLinePt d τ)‖ := by
  obtain ⟨a, ha, hchi⟩ :=
    exists_norm_zetaChi_rightDisplaced_ge_rpow hd hdhalf
  let c : ℝ := a / (2 : ℝ) ^ d
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  refine ⟨c, hc, fun {N} hN τ hτ => ?_⟩
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hτpos : 0 < τ := hNR.trans_le hτ.1
  have hmax : max 1 |τ| = τ := by
    rw [abs_of_pos hτpos, max_eq_right]
    exact (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ)).trans hτ.1
  have hraw := hchi τ
  rw [hmax] at hraw
  have hpow : τ ^ d ≤ (2 * (N : ℝ)) ^ d :=
    Real.rpow_le_rpow hτpos.le (by exact_mod_cast hτ.2) hd.le
  have hcompare : a / (2 * (N : ℝ)) ^ d ≤ a / τ ^ d :=
    div_le_div_of_nonneg_left ha.le
      (Real.rpow_pos_of_pos hτpos d) hpow
  calc
    c * (N : ℝ) ^ (-d) = a / (2 * (N : ℝ)) ^ d := by
      dsimp only [c]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hNR.le,
        Real.rpow_neg hNR.le]
      have h2 : (2 : ℝ) ^ d ≠ 0 :=
        (Real.rpow_pos_of_pos (by norm_num) d).ne'
      have hNd : (N : ℝ) ^ d ≠ 0 :=
        (Real.rpow_pos_of_pos hNR d).ne'
      field_simp [h2, hNd]
    _ ≤ a / τ ^ d := hcompare
    _ ≤ ‖zetaChi (rightDisplacedLinePt d τ)‖ := hraw

/-- The Gaussian cutoff has norm at least one half on some fixed
right-neighborhood of zero. -/
theorem exists_smoothAFECutoff_inner_norm_lower :
    ∃ r : ℝ, 0 < r ∧ ∀ {u : ℝ}, 0 < u → u ≤ r →
      (1 / 2 : ℝ) ≤ ‖smoothAFECutoff u‖ := by
  obtain ⟨K, hK, hcut⟩ :=
    exists_norm_smoothAFECutoff_sub_one_le_rpow
      (δ := (1 : ℝ)) (by norm_num)
  let r : ℝ := 1 / (2 * (K + 1))
  have hr : 0 < r := by
    dsimp only [r]
    positivity
  refine ⟨r, hr, fun {u} hu hur => ?_⟩
  have hraw := hcut hu
  have herror : ‖smoothAFECutoff u - 1‖ ≤ 1 / 2 := by
    calc
      ‖smoothAFECutoff u - 1‖ ≤ K * u ^ (1 : ℝ) := hraw
      _ = K * u := by rw [Real.rpow_one]
      _ ≤ K * r := mul_le_mul_of_nonneg_left hur hK
      _ = K / (2 * (K + 1)) := by
        dsimp only [r]
        ring
      _ ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * (K + 1))).2
        nlinarith
  have hreverse := norm_sub_norm_le (1 : ℂ) (smoothAFECutoff u)
  rw [norm_one] at hreverse
  have hsymmetric :
      ‖(1 : ℂ) - smoothAFECutoff u‖ =
        ‖smoothAFECutoff u - 1‖ := by
    rw [show (1 : ℂ) - smoothAFECutoff u =
        -(smoothAFECutoff u - 1) by ring, norm_neg]
  rw [hsymmetric] at hreverse
  linarith

/-- Ideal terminal power mass multiplied by the exact ordinary cutoff
appearing in the reflected-primal AFE at scale `x=N/r`. -/
def terminalReflectedCutoffSquareWeight
    (d r : ℝ) (N n : ℕ) : ℝ :=
  terminalPowerSquareWeight d N n *
    ‖smoothAFECutoff (r * (n : ℝ) / (N : ℝ))‖ ^ 2

/-- Literal squared magnitude profile of the reflected-primal AFE
coefficient, including its common right-line chi factor. -/
def terminalReflectedActualSquareWeight
    (d τ r : ℝ) (N n : ℕ) : ℝ :=
  ‖zetaChi (rightDisplacedLinePt d τ)‖ ^ 2 *
    (n : ℝ) ^ (-(1 - 2 * d)) *
    ‖smoothAFECutoff (r * (n : ℝ) / (N : ℝ))‖ ^ 2

/-- The literal profile is exactly the squared norm of the reflected-primal
AFE coefficient at scale `x=N/r`, with arithmetic index shifted from
positive integers to naturals. -/
theorem norm_sq_smoothAFEZetaRightReflectedPrimalCoefficient_eq_actual
    {d τ r : ℝ} (hr : 0 < r) {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) :
    ‖smoothAFEZetaRightReflectedPrimalCoefficient d τ
        ((N : ℝ) / r) (n - 1)‖ ^ 2 =
      terminalReflectedActualSquareWeight d τ r N n := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnsub : n - 1 + 1 = n := by omega
  have hnsubC : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
    exact_mod_cast hnsub
  have hnsubR : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hnsub
  have hncastC : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  have harg : (n : ℝ) / ((N : ℝ) / r) =
      r * (n : ℝ) / (N : ℝ) := by
    field_simp [hNR.ne', hr.ne']
  have hexp : (rightDisplacedLinePt d τ - 1).re =
      -1 / 2 + d := by
    rw [Complex.sub_re, rightDisplacedLinePt_re]
    norm_num
    ring
  have hpowSq : ((n : ℝ) ^ (-1 / 2 + d)) ^ 2 =
      (n : ℝ) ^ (-(1 - 2 * d)) := by
    calc
      ((n : ℝ) ^ (-1 / 2 + d)) ^ 2 =
          (n : ℝ) ^ (-1 / 2 + d) *
            (n : ℝ) ^ (-1 / 2 + d) := by ring
      _ = (n : ℝ) ^ ((-1 / 2 + d) + (-1 / 2 + d)) := by
        exact (Real.rpow_add hnR (-1 / 2 + d) (-1 / 2 + d)).symm
      _ = (n : ℝ) ^ (-(1 - 2 * d)) := by ring_nf
  unfold smoothAFEZetaRightReflectedPrimalCoefficient
    terminalReflectedActualSquareWeight
  rw [norm_mul, norm_mul]
  rw [hnsubC, hnsubR, hncastC]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hnR, hexp, harg]
  rw [mul_pow, mul_pow, hpowSq]

theorem chi_window_sq_mul_reflectedCutoff_le_actual
    {d c τ r : ℝ} {N n : ℕ} (hc : 0 ≤ c) (hN : 1 ≤ N)
    (hchi : c * (N : ℝ) ^ (-d) ≤
      ‖zetaChi (rightDisplacedLinePt d τ)‖) :
    c ^ 2 * terminalReflectedCutoffSquareWeight d r N n ≤
      terminalReflectedActualSquareWeight d τ r N n := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hleft0 : 0 ≤ c * (N : ℝ) ^ (-d) := by positivity
  have hsq :
      (c * (N : ℝ) ^ (-d)) ^ 2 ≤
        ‖zetaChi (rightDisplacedLinePt d τ)‖ ^ 2 := by
    nlinarith [norm_nonneg (zetaChi (rightDisplacedLinePt d τ))]
  have hrpowSq : ((N : ℝ) ^ (-d)) ^ 2 =
      (N : ℝ) ^ (-2 * d) := by
    calc
      ((N : ℝ) ^ (-d)) ^ 2 =
          (N : ℝ) ^ (-d) * (N : ℝ) ^ (-d) := by ring
      _ = (N : ℝ) ^ (-d + -d) := by
        rw [Real.rpow_add hNR]
      _ = (N : ℝ) ^ (-2 * d) := by ring_nf
  rw [mul_pow, hrpowSq] at hsq
  unfold terminalReflectedCutoffSquareWeight terminalPowerSquareWeight
    terminalReflectedActualSquareWeight
  have hbase : 0 ≤
      (n : ℝ) ^ (-(1 - 2 * d)) *
        ‖smoothAFECutoff (r * (n : ℝ) / (N : ℝ))‖ ^ 2 := by
    positivity
  calc
    c ^ 2 *
          ((N : ℝ) ^ (-2 * d) * (n : ℝ) ^ (-(1 - 2 * d)) *
            ‖smoothAFECutoff (r * (n : ℝ) / (N : ℝ))‖ ^ 2) =
        (c ^ 2 * (N : ℝ) ^ (-2 * d)) *
          ((n : ℝ) ^ (-(1 - 2 * d)) *
            ‖smoothAFECutoff (r * (n : ℝ) / (N : ℝ))‖ ^ 2) := by ring
    _ ≤ ‖zetaChi (rightDisplacedLinePt d τ)‖ ^ 2 *
          ((n : ℝ) ^ (-(1 - 2 * d)) *
            ‖smoothAFECutoff (r * (n : ℝ) / (N : ℝ))‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hsq hbase
    _ = ‖zetaChi (rightDisplacedLinePt d τ)‖ ^ 2 *
          (n : ℝ) ^ (-(1 - 2 * d)) *
          ‖smoothAFECutoff (r * (n : ℝ) / (N : ℝ))‖ ^ 2 := by ring

theorem quarter_terminalPowerSquareWeight_le_reflectedCutoff
    {d r : ℝ} (hr : 0 < r)
    (hcut : ∀ {u : ℝ}, 0 < u → u ≤ r →
      (1 / 2 : ℝ) ≤ ‖smoothAFECutoff u‖)
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n) (hnN : n ≤ N) :
    (1 / 4 : ℝ) * terminalPowerSquareWeight d N n ≤
      terminalReflectedCutoffSquareWeight d r N n := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hratio : (n : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNR]
    exact_mod_cast hnN
  have hu : 0 < r * (n : ℝ) / (N : ℝ) := by positivity
  have hur : r * (n : ℝ) / (N : ℝ) ≤ r := by
    calc
      r * (n : ℝ) / (N : ℝ) = r * ((n : ℝ) / (N : ℝ)) := by ring
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hratio hr.le
      _ = r := mul_one r
  have hnorm := hcut hu hur
  have hsq : (1 / 4 : ℝ) ≤
      ‖smoothAFECutoff (r * (n : ℝ) / (N : ℝ))‖ ^ 2 := by
    nlinarith [norm_nonneg
      (smoothAFECutoff (r * (n : ℝ) / (N : ℝ)))]
  have hweight : 0 ≤ terminalPowerSquareWeight d N n := by
    unfold terminalPowerSquareWeight
    positivity
  unfold terminalReflectedCutoffSquareWeight
  calc
    (1 / 4 : ℝ) * terminalPowerSquareWeight d N n =
        terminalPowerSquareWeight d N n * (1 / 4 : ℝ) := by ring
    _ ≤ terminalPowerSquareWeight d N n *
        ‖smoothAFECutoff (r * (n : ℝ) / (N : ℝ))‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hweight

/-- Every variable-cofactor channel retains one quarter of its ideal
reciprocal-prime lower bound after inserting the actual cutoff. -/
theorem normalized_reflected_cutoff_channel_lower_recip
    {d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2)
    {r : ℝ} (hr : 0 < r)
    (hcut : ∀ {u : ℝ}, 0 < u → u ≤ r →
      (1 / 2 : ℝ) ≤ ‖smoothAFECutoff u‖)
    {N p : ℕ} (hp : 0 < p) (h2p : 2 * p ≤ N) :
    (1 / 4 : ℝ) *
        (((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) * ((p : ℝ)⁻¹)) ≤
      ∑ m ∈ dyadicCofactorBlock N p,
        terminalReflectedCutoffSquareWeight d r N (p * m) := by
  have hN : 0 < N := by omega
  have hideal := normalized_power_channel_lower_recip
    hd0 hdhalf hp h2p
  calc
    (1 / 4 : ℝ) *
        (((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) * ((p : ℝ)⁻¹))
      ≤ (1 / 4 : ℝ) *
          (∑ m ∈ dyadicCofactorBlock N p,
            terminalPowerSquareWeight d N (p * m)) :=
        mul_le_mul_of_nonneg_left hideal (by norm_num)
    _ = ∑ m ∈ dyadicCofactorBlock N p,
          (1 / 4 : ℝ) * terminalPowerSquareWeight d N (p * m) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ dyadicCofactorBlock N p,
          terminalReflectedCutoffSquareWeight d r N (p * m) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmle : m ≤ N / p := (Finset.mem_Icc.1 hm).2
        have hmpos : 0 < m := by
          have hmlo := (Finset.mem_Icc.1 hm).1
          omega
        have hpmN : p * m ≤ N := by
          calc
            p * m ≤ p * (N / p) := Nat.mul_le_mul_left p hmle
            _ ≤ N := Nat.mul_div_le N p
        exact quarter_terminalPowerSquareWeight_le_reflectedCutoff
          hr hcut hN (Nat.mul_pos hp hmpos) hpmN

/-- **Actual reflected-primal terminal mass floor.** A fixed inner
fraction of the ordinary cutoff preserves positive aggregate normalized
mass in the half-to-two-thirds largest-prime window. -/
theorem exists_eventually_reflected_cutoff_terminal_channels_lower
    {d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 4 : ℝ) *
          (((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) *
            ((-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ))) / 2)) ≤
        ∑ p ∈ terminalPrimePowerWindow N,
          ∑ m ∈ dyadicCofactorBlock N p,
            terminalReflectedCutoffSquareWeight d r N (p * m) := by
  obtain ⟨r, hr, hcut⟩ := exists_smoothAFECutoff_inner_norm_lower
  refine ⟨r, hr, ?_⟩
  have hideal := eventually_normalized_power_terminal_channels_lower
    hd0 hdhalf
  filter_upwards [hideal, eventually_two_mul_twoThirdsPowerWindowIndex_le]
    with N hidealN htwo
  calc
    (1 / 4 : ℝ) *
        (((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) *
          ((-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ))) / 2))
      ≤ (1 / 4 : ℝ) *
          (∑ p ∈ terminalPrimePowerWindow N,
            ∑ m ∈ dyadicCofactorBlock N p,
              terminalPowerSquareWeight d N (p * m)) :=
        mul_le_mul_of_nonneg_left hidealN (by norm_num)
    _ = ∑ p ∈ terminalPrimePowerWindow N,
          ∑ m ∈ dyadicCofactorBlock N p,
            (1 / 4 : ℝ) * terminalPowerSquareWeight d N (p * m) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _hp
        rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ terminalPrimePowerWindow N,
          ∑ m ∈ dyadicCofactorBlock N p,
            terminalReflectedCutoffSquareWeight d r N (p * m) := by
        apply Finset.sum_le_sum
        intro p hpwindow
        apply Finset.sum_le_sum
        intro m hm
        have hpdata := (mem_terminalPrimePowerWindow.mp hpwindow)
        have hp : 0 < p := hpdata.1.pos
        have hpupper : p < powerWindowIndex (2 / 3 : ℝ) N := hpdata.2.2
        have h2p : 2 * p ≤ N := by omega
        have hN : 0 < N := by omega
        have hmle : m ≤ N / p := (Finset.mem_Icc.1 hm).2
        have hmpos : 0 < m := by
          have hmlo := (Finset.mem_Icc.1 hm).1
          omega
        have hpmN : p * m ≤ N := by
          calc
            p * m ≤ p * (N / p) := Nat.mul_le_mul_left p hmle
            _ ≤ N := Nat.mul_div_le N p
        exact quarter_terminalPowerSquareWeight_le_reflectedCutoff
          hr hcut hN (Nat.mul_pos hp hmpos) hpmN

/-- **Literal actual-coefficient terminal mass floor.** Uniformly for
`τ∈[N,2N]`, the reflected-primal coefficients retain positive aggregate
largest-prime channel mass. -/
theorem exists_eventually_reflected_actual_terminal_channels_lower
    {d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ τ ∈ Set.Icc (N : ℝ) (2 * N : ℝ),
        c ^ 2 *
            ((1 / 4 : ℝ) *
              (((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) *
                ((-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ))) / 2))) ≤
          ∑ p ∈ terminalPrimePowerWindow N,
            ∑ m ∈ dyadicCofactorBlock N p,
              terminalReflectedActualSquareWeight d τ r N (p * m) := by
  obtain ⟨c, hc, hchi⟩ :=
    exists_norm_zetaChi_rightDisplaced_ge_nat_window hd0 hdhalf
  obtain ⟨r, hr, hmass⟩ :=
    exists_eventually_reflected_cutoff_terminal_channels_lower hd0 hdhalf
  refine ⟨c, r, hc, hr, ?_⟩
  filter_upwards [hmass, Filter.eventually_ge_atTop 1] with N hmassN hN
  intro τ hτ
  have hchiN := hchi hN τ hτ
  calc
    c ^ 2 *
        ((1 / 4 : ℝ) *
          (((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) *
            ((-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ))) / 2)))
      ≤ c ^ 2 *
          (∑ p ∈ terminalPrimePowerWindow N,
            ∑ m ∈ dyadicCofactorBlock N p,
              terminalReflectedCutoffSquareWeight d r N (p * m)) :=
        mul_le_mul_of_nonneg_left hmassN (sq_nonneg c)
    _ = ∑ p ∈ terminalPrimePowerWindow N,
          ∑ m ∈ dyadicCofactorBlock N p,
            c ^ 2 * terminalReflectedCutoffSquareWeight d r N (p * m) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _hp
        rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ terminalPrimePowerWindow N,
          ∑ m ∈ dyadicCofactorBlock N p,
            terminalReflectedActualSquareWeight d τ r N (p * m) := by
        apply Finset.sum_le_sum
        intro p _hp
        apply Finset.sum_le_sum
        intro m _hm
        exact chi_window_sq_mul_reflectedCutoff_le_actual hc.le hN hchiN

end

end RHTower
