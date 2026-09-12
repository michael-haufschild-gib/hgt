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

end

end RHTower
