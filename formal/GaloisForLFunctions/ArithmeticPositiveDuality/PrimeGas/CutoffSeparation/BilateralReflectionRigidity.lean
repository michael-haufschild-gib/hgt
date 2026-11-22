import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.PoleFreeAdjacentExpansion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.CutoffObstructions
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.JointPrimeReading
import GaloisForLFunctions.RHTower.ZetaReflectionMultiplierExplicit

/-!
# Bilateral functional-reflection coupling and sharp rigidity against positive surgeries

Exploiting the simultaneous pole cancellation in `PoleFreeAdjacentExpansion`, this module couples
two-prime `{2, 3}` aligned shell contrasts at `(4^K, 9^K)` directly across functional reflection
`w ↔ 1 - w` and establishes the exact sharp boundary that defeats all finite positive surgeries:

1. **Pole-free, `|ζ|`-free two-prime aligned reconstruction (`norm_alignedReconstructedCutoff_sub_le`)**:
   evaluating `halfTurnClock` at `4^K` and `primeThreeClock` at `9^K` (`K ≥ 1`) reconstructs the
   entire function `zetaPoleUnit w = (w - 1) ζ(w)` across **all** `Re w > 0` — including the pole
   `w = 1` — with an explicit `|ζ(w)|`-free, pole-free error bound `alignedReconstructionError K w`,
   certifying an unconditional finite-shell margin right at `w = 1`.
2. **Unconditional `|ζ|`-free decay of the bilateral reflection defect
   (`norm_bilateralReflectionDefect_one_le`)**: pairing `w` and `1 - w` through the archimedean
   multiplier `poleReflectionMultiplier w` cancels `ζ(w)` identically in the limit and bounds
   `‖bilateralReflectionDefect (fun _ => 1) K w‖` across `0 < Re w < 1` with no `ζ` factor and no
   pole singularity.
3. **Single-point bypass vs. `{5, 7}` positive quartet obstruction
   (`exists_coprime_quartet_surgery_killing_reflected_pair`)**: while single-point bilateral
   reflection already detects and rejects all one-sided `{2, 3}` and `{5, 7}` surgeries from
   `CutoffObstructions`, we construct a 5-term degree-4 positive surgery at a single prime
   `p ∈ {5, 7}` keeping `a(n) ≥ 1` and `a(2^u 3^v) = 1` that extinguishes all clocks at **both**
   `w₀` and `1 - w₀`, showing single-point reflection is sharp-insufficient against quartet surgery.
4. **Complete germ-level reflection rigidity
   (`dirichletSurgWeight_eq_one_of_frequently_reflection_vanishing`)**: for **every** finite
   Dirichlet-convolution surgery `a = dirichletSurgWeight M c` (`c(1) = 1`), if
   `bilateralReflectionDefect a K w → 0` frequently on `𝓝[≠] w₀` at any single point `w₀` in
   `0 < Re w₀ < 1`, then `c(d) = 0` for all `2 ≤ d ≤ M` and `a(n) = 1` for every `n ≥ 1`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Complex Filter Set
open scoped Topology ComplexConjugate

/-- Prime-three half-turn clock (`tailRadix = 3` at refinement `0`). -/
def primeThreeClock : ExceptionalTime := primeHalfTurnClock ⟨3, Nat.prime_three⟩

theorem tailRadix_halfTurnClock_zero : tailRadix halfTurnClock 0 = 2 := by
  rw [tailRadix, show refined halfTurnClock 0 = halfTurnClock from rfl,
    prime_clock_parameters.1.1, prime_clock_parameters.1.2,
    show (2 : ℕ) / 2 = 1 by norm_num, pow_one]

theorem tailRadix_primeThreeClock_zero : tailRadix primeThreeClock 0 = 3 :=
  prime_half_turn_radix ⟨3, Nat.prime_three⟩

/-- Weight-linear two-prime aligned shell reconstruction at `(4^K, 9^K)`, requiring no density
counterterm `ρ` and free of simultaneous base-`2` / base-`3` digit-imbalance spikes. -/
def weightedAlignedReconstructed (a : ℕ → ℝ) (K : ℕ) (w : ℂ) : ℂ :=
  (conj (contrastTransfer 2 w) *
      (weightedAdjacentCutoff a halfTurnClock 0 (2 ^ (2 * K)) w /
        (1 - (heat w 2) ^ (2 * K))) +
    conj (contrastTransfer 3 w) *
      (weightedAdjacentCutoff a primeThreeClock 0 (3 ^ (2 * K)) w /
        (1 - (heat w 3) ^ (2 * K)))) /
    (twoPrimeTransferMass w : ℂ)

/-- Two-prime aligned shell reconstruction for the actual prime-gas weights `a ≡ 1`. -/
def alignedReconstructedCutoff (K : ℕ) (w : ℂ) : ℂ :=
  weightedAlignedReconstructed (fun _ => 1) K w

/-- Elementary `|ζ(w)|`-free, pole-free error bound for `alignedReconstructedCutoff K w`,
continuous across `w = 1` as well as throughout `Re w > 0`. -/
def alignedReconstructionError (K : ℕ) (w : ℂ) : ℝ :=
  let b := 3 * ‖w * (w + 1)‖ / (2 * (w.re + 1))
  let e₂ := ((K : ℝ) + b) * (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) /
    (1 - (2 : ℝ) ^ (-(2 * K : ℝ) * w.re))
  let e₃ := (2 * (K : ℝ) + b) * (3 : ℝ) ^ (-(2 * K : ℝ) * w.re) /
    (1 - (3 : ℝ) ^ (-(2 * K : ℝ) * w.re))
  (‖contrastTransfer 2 w‖ * e₂ + ‖contrastTransfer 3 w‖ * e₃) / twoPrimeTransferMass w

theorem weightedAdjacentCutoff_one (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :
    weightedAdjacentCutoff (fun _ => 1) t j X w = adjacentCutoff t j X w := by
  have hrad : ∀ Y : ℕ, weightedRadialCutoff (fun _ => 1) Y w = radialCutoff Y w := fun Y => by
    simp [weightedRadialCutoff, radialCutoff]
  have hsh : ∀ m : ℕ, weightedShellCutoff (fun _ => 1) t m X w = shellCutoff t m X w := fun m => by
    rw [weightedShellCutoff]
    simp_rw [hrad]
    exact (shellCutoff_eq_sum_log t m X w).symm
  rw [weightedAdjacentCutoff, adjacentCutoff, hsh j, hsh (j + 1)]

/-- Pole-free, `|ζ(w)|`-free error bound for `alignedReconstructedCutoff K w` across **every**
`w` with `Re w > 0` — including `w = 1` — and every shell depth `K ≥ 1`. -/
theorem norm_alignedReconstructedCutoff_sub_le {K : ℕ} (hK : 1 ≤ K) {w : ℂ} (hw : 0 < w.re) :
    ‖alignedReconstructedCutoff K w - _root_.RHTower.zetaPoleUnit w‖ ≤
      alignedReconstructionError K w := by
  have hm_pos : 0 < twoPrimeTransferMass w := two_prime_transfer_mass_pos ⟨w, hw⟩
  have hm_ne : (twoPrimeTransferMass w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm_pos.ne'
  have h2K_pos : (0 : ℝ) < 2 * (K : ℝ) := by positivity
  -- Bound each prime channel `C ∈ {2, 3}` via `PoleFreeAdjacentExpansion`.
  have hchan2 : ‖adjacentCutoff halfTurnClock 0 (2 ^ (2 * K)) w / (1 - (heat w 2) ^ (2 * K)) -
        contrastResponse 2 w‖ ≤
      ((K : ℝ) + 3 * ‖w * (w + 1)‖ / (2 * (w.re + 1))) * (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) /
        (1 - (2 : ℝ) ^ (-(2 * K : ℝ) * w.re)) := by
    have hrpow_lt1 : (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (mul_neg_of_neg_of_pos (by linarith) hw)
    have hden_r : 0 < 1 - (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) := sub_pos.mpr hrpow_lt1
    have hden_ge : 1 - (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) ≤ ‖(1 : ℂ) - (heat w 2) ^ (2 * K)‖ := by
      have h := norm_sub_norm_le (1 : ℂ) ((heat w 2) ^ (2 * K))
      have hnorm : ‖(heat w 2) ^ (2 * K)‖ = (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) := by
        simpa [Nat.cast_mul, Nat.cast_ofNat] using norm_heat_pow 2 (2 * K) w
      rwa [norm_one, hnorm] at h
    have hden_pos : 0 < ‖(1 : ℂ) - (heat w 2) ^ (2 * K)‖ := lt_of_lt_of_le hden_r hden_ge
    have hden_ne : (1 : ℂ) - (heat w 2) ^ (2 * K) ≠ 0 := norm_pos_iff.mp hden_pos
    have hbd := norm_adjacentCutoff_radix_even_pow_sub_le halfTurnClock 0 K (by linarith : -1 < w.re)
    dsimp only at hbd
    rw [tailRadix_halfTurnClock_zero,
      zetaPoleUnit_mul_finiteContrastTransfer_eq (by change 1 < (2 : ℕ); norm_num) K hw] at hbd
    change ‖adjacentCutoff halfTurnClock 0 (2 ^ (2 * K)) w -
        (1 - (heat w 2) ^ (2 * K)) * contrastResponse 2 w‖ ≤
      (((2 : ℝ) - 1) * (K : ℝ) +
        (2 : ℝ) * ((2 : ℝ) + 1) * ‖w * (w + 1)‖ / (4 * (w.re + 1) * ((2 : ℝ) - 1))) *
        (2 : ℝ) ^ (-(2 * K : ℝ) * w.re) at hbd
    have hnum_simp : (((2 : ℝ) - 1) * (K : ℝ) +
        (2 : ℝ) * ((2 : ℝ) + 1) * ‖w * (w + 1)‖ / (4 * (w.re + 1) * ((2 : ℝ) - 1))) =
        (K : ℝ) + 3 * ‖w * (w + 1)‖ / (2 * (w.re + 1)) := by
      have hw1 : w.re + 1 ≠ 0 := by linarith
      field_simp [hw1]; ring
    rw [hnum_simp] at hbd
    have hdiv_eq : adjacentCutoff halfTurnClock 0 (2 ^ (2 * K)) w / (1 - (heat w 2) ^ (2 * K)) -
        contrastResponse 2 w =
        (adjacentCutoff halfTurnClock 0 (2 ^ (2 * K)) w -
          (1 - (heat w 2) ^ (2 * K)) * contrastResponse 2 w) / (1 - (heat w 2) ^ (2 * K)) := by
      field_simp [hden_ne]
    rw [hdiv_eq, norm_div]
    exact (div_le_div_of_nonneg_right hbd hden_pos.le).trans
      (div_le_div_of_nonneg_left (by positivity) hden_r hden_ge)
  have hchan3 : ‖adjacentCutoff primeThreeClock 0 (3 ^ (2 * K)) w / (1 - (heat w 3) ^ (2 * K)) -
        contrastResponse 3 w‖ ≤
      (2 * (K : ℝ) + 3 * ‖w * (w + 1)‖ / (2 * (w.re + 1))) * (3 : ℝ) ^ (-(2 * K : ℝ) * w.re) /
        (1 - (3 : ℝ) ^ (-(2 * K : ℝ) * w.re)) := by
    have hrpow_lt1 : (3 : ℝ) ^ (-(2 * K : ℝ) * w.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (mul_neg_of_neg_of_pos (by linarith) hw)
    have hden_r : 0 < 1 - (3 : ℝ) ^ (-(2 * K : ℝ) * w.re) := sub_pos.mpr hrpow_lt1
    have hden_ge : 1 - (3 : ℝ) ^ (-(2 * K : ℝ) * w.re) ≤ ‖(1 : ℂ) - (heat w 3) ^ (2 * K)‖ := by
      have h := norm_sub_norm_le (1 : ℂ) ((heat w 3) ^ (2 * K))
      have hnorm : ‖(heat w 3) ^ (2 * K)‖ = (3 : ℝ) ^ (-(2 * K : ℝ) * w.re) := by
        simpa [Nat.cast_mul, Nat.cast_ofNat] using norm_heat_pow 3 (2 * K) w
      rwa [norm_one, hnorm] at h
    have hden_pos : 0 < ‖(1 : ℂ) - (heat w 3) ^ (2 * K)‖ := lt_of_lt_of_le hden_r hden_ge
    have hden_ne : (1 : ℂ) - (heat w 3) ^ (2 * K) ≠ 0 := norm_pos_iff.mp hden_pos
    have hbd := norm_adjacentCutoff_radix_even_pow_sub_le primeThreeClock 0 K (by linarith : -1 < w.re)
    dsimp only at hbd
    rw [tailRadix_primeThreeClock_zero,
      zetaPoleUnit_mul_finiteContrastTransfer_eq (by change 1 < (3 : ℕ); norm_num) K hw] at hbd
    change ‖adjacentCutoff primeThreeClock 0 (3 ^ (2 * K)) w -
        (1 - (heat w 3) ^ (2 * K)) * contrastResponse 3 w‖ ≤
      (((3 : ℝ) - 1) * (K : ℝ) +
        (3 : ℝ) * ((3 : ℝ) + 1) * ‖w * (w + 1)‖ / (4 * (w.re + 1) * ((3 : ℝ) - 1))) *
        (3 : ℝ) ^ (-(2 * K : ℝ) * w.re) at hbd
    have hnum_simp : (((3 : ℝ) - 1) * (K : ℝ) +
        (3 : ℝ) * ((3 : ℝ) + 1) * ‖w * (w + 1)‖ / (4 * (w.re + 1) * ((3 : ℝ) - 1))) =
        2 * (K : ℝ) + 3 * ‖w * (w + 1)‖ / (2 * (w.re + 1)) := by
      have hw1 : w.re + 1 ≠ 0 := by linarith
      field_simp [hw1]; ring
    rw [hnum_simp] at hbd
    have hdiv_eq : adjacentCutoff primeThreeClock 0 (3 ^ (2 * K)) w / (1 - (heat w 3) ^ (2 * K)) -
        contrastResponse 3 w =
        (adjacentCutoff primeThreeClock 0 (3 ^ (2 * K)) w -
          (1 - (heat w 3) ^ (2 * K)) * contrastResponse 3 w) / (1 - (heat w 3) ^ (2 * K)) := by
      field_simp [hden_ne]
    rw [hdiv_eq, norm_div]
    exact (div_le_div_of_nonneg_right hbd hden_pos.le).trans
      (div_le_div_of_nonneg_left (by positivity) hden_r hden_ge)
  -- Assemble the weighted two-prime linear combination.
  let a₂ := contrastTransfer 2 w
  let a₃ := contrastTransfer 3 w
  let Z := _root_.RHTower.zetaPoleUnit w
  let Q₂ := adjacentCutoff halfTurnClock 0 (2 ^ (2 * K)) w / (1 - (heat w 2) ^ (2 * K))
  let Q₃ := adjacentCutoff primeThreeClock 0 (3 ^ (2 * K)) w / (1 - (heat w 3) ^ (2 * K))
  have hmass_ident : conj a₂ * contrastResponse 2 w + conj a₃ * contrastResponse 3 w =
      Z * (twoPrimeTransferMass w : ℂ) := by
    dsimp only [a₂, a₃, Z]
    rw [contrastResponse, contrastResponse]
    change _ = _root_.RHTower.zetaPoleUnit w *
      ((Complex.normSq (contrastTransfer 2 w) + Complex.normSq (contrastTransfer 3 w) : ℝ) : ℂ)
    rw [Complex.ofReal_add, ← Complex.mul_conj, ← Complex.mul_conj]
    ring
  have hcomb : alignedReconstructedCutoff K w - Z =
      (conj a₂ * (Q₂ - contrastResponse 2 w) + conj a₃ * (Q₃ - contrastResponse 3 w)) /
        (twoPrimeTransferMass w : ℂ) := by
    unfold alignedReconstructedCutoff weightedAlignedReconstructed
    rw [weightedAdjacentCutoff_one, weightedAdjacentCutoff_one]
    change (conj a₂ * Q₂ + conj a₃ * Q₃) / (twoPrimeTransferMass w : ℂ) - Z = _
    have hZ_div : Z = Z * (twoPrimeTransferMass w : ℂ) / (twoPrimeTransferMass w : ℂ) :=
      (mul_div_cancel_right₀ Z hm_ne).symm
    conv_lhs => rw [hZ_div, ← sub_div, ← hmass_ident]
    exact congrArg (· / (twoPrimeTransferMass w : ℂ)) (by ring)
  have hm_norm : ‖(twoPrimeTransferMass w : ℂ)‖ = twoPrimeTransferMass w := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm_pos]
  rw [hcomb, norm_div, hm_norm]
  unfold alignedReconstructionError
  dsimp only
  refine div_le_div_of_nonneg_right ?_ hm_pos.le
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hchan2 (norm_nonneg _))
    (mul_le_mul_of_nonneg_left hchan3 (norm_nonneg _))

theorem tendsto_alignedReconstructionError_zero {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun K : ℕ => alignedReconstructionError K w) atTop (𝓝 0) := by
  let b := 3 * ‖w * (w + 1)‖ / (2 * (w.re + 1))
  have hchan : ∀ (B : ℝ) (hB : 1 < B) (c : ℝ),
      Tendsto (fun K : ℕ => (c * (K : ℝ) + b) * B ^ (-(2 * K : ℝ) * w.re) /
        (1 - B ^ (-(2 * K : ℝ) * w.re))) atTop (𝓝 0) := by
    intro B hB c
    have hB0 : 0 < B := by linarith
    have hlogB : 0 < Real.log B := Real.log_pos hB
    set rate : ℝ := 2 * w.re * Real.log B
    have hrate : 0 < rate := by positivity
    have hrpow0 : Tendsto (fun K : ℕ => B ^ (-(2 * K : ℝ) * w.re)) atTop (𝓝 0) := by
      have hlt1 : B ^ (-2 * w.re) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hB (by linarith)
      refine (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg hB0.le _) hlt1).congr fun K => ?_
      rw [← Real.rpow_natCast (B ^ (-2 * w.re)) K, ← Real.rpow_mul hB0.le]
      congr 1; ring
    have hK_rpow0 : Tendsto (fun K : ℕ => (K : ℝ) * B ^ (-(2 * K : ℝ) * w.re)) atTop (𝓝 0) := by
      have hexp := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hrate)).const_mul (1 / rate)
      rw [mul_zero] at hexp
      refine hexp.congr fun K => ?_
      dsimp only [Function.comp_apply]
      rw [pow_one, Real.rpow_def_of_pos hB0]
      have : -(rate * (K : ℝ)) = Real.log B * (-(2 * K : ℝ) * w.re) := by dsimp only [rate]; ring
      rw [this]
      field_simp [hrate.ne']
    have hnum0 : Tendsto (fun K : ℕ => (c * (K : ℝ) + b) * B ^ (-(2 * K : ℝ) * w.re)) atTop (𝓝 0) := by
      have hc1 := hK_rpow0.const_mul c
      have hc2 := hrpow0.const_mul b
      rw [mul_zero] at hc1 hc2
      simpa only [add_zero, add_mul, mul_assoc] using hc1.add hc2
    have hden1 : Tendsto (fun K : ℕ => 1 - B ^ (-(2 * K : ℝ) * w.re)) atTop (𝓝 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hrpow0
    have hdiv := hnum0.div hden1 one_ne_zero
    rw [zero_div] at hdiv
    exact hdiv.congr fun _ => rfl
  have h2 := (hchan 2 (by norm_num) 1).const_mul ‖contrastTransfer 2 w‖
  have h3 := (hchan 3 (by norm_num) 2).const_mul ‖contrastTransfer 3 w‖
  rw [mul_zero] at h2 h3
  have hsum := (h2.add h3).div_const (twoPrimeTransferMass w)
  rw [add_zero, zero_div] at hsum
  refine hsum.congr fun K => ?_
  unfold alignedReconstructionError
  dsimp only [b]
  ring

/-- Unconditional strict `|ζ|`-free, pole-free cutoff margin right at the pole `w = 1`, where single
`renormalizedCutoff` bounds blow up as `1 / ‖1 - w‖`. -/
theorem exists_aligned_margin_at_one :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      alignedReconstructionError K₀ 1 < ‖alignedReconstructedCutoff K₀ 1‖ := by
  have herr := tendsto_alignedReconstructionError_zero (w := 1) (by norm_num)
  have hlim : Tendsto (fun K : ℕ => alignedReconstructedCutoff K 1) atTop (𝓝 1) := by
    have hsub : Tendsto (fun K : ℕ => alignedReconstructedCutoff K 1 - _root_.RHTower.zetaPoleUnit 1)
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ herr
      filter_upwards [eventually_ge_atTop 1] with K hK
      exact norm_alignedReconstructedCutoff_sub_le hK (by norm_num)
    have hadd := hsub.add (tendsto_const_nhds (x := _root_.RHTower.zetaPoleUnit 1))
    rw [zero_add, _root_.RHTower.zetaPoleUnit_one] at hadd
    exact hadd.congr fun _ => sub_add_cancel _ _
  have hnorm1 : Tendsto (fun K : ℕ => ‖alignedReconstructedCutoff K 1‖) atTop (𝓝 1) := by
    simpa only [norm_one] using hlim.norm
  obtain ⟨K₀, ⟨hK1, hhi⟩, hlo⟩ :=
    (((eventually_ge_atTop 1).and
      (herr.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))).and
      (hnorm1.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))).exists
  exact ⟨K₀, hK1, hhi.trans hlo⟩

/-! ### Bilateral functional-reflection coupling across `w ↔ 1 - w` -/

/-- Archimedean reflection multiplier for the entire function `zetaPoleUnit w = (w - 1) ζ(w)`. -/
def poleReflectionMultiplier (w : ℂ) : ℂ :=
  -((w - 1) / w) * _root_.RHTower.reflectionMultiplier w

theorem poleReflectionMultiplier_ne_zero {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    poleReflectionMultiplier w ≠ 0 := by
  have hw0 : w ≠ 0 := fun he => h0.ne' (by rw [he, Complex.zero_re])
  have hw1 : w ≠ 1 := fun he => h1.ne (by rw [he, Complex.one_re])
  exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hw1) hw0))
    (_root_.RHTower.reflectionMultiplier_ne_zero h0 h1)

theorem zetaPoleUnit_eq_poleReflectionMultiplier_mul {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    _root_.RHTower.zetaPoleUnit w =
      poleReflectionMultiplier w * _root_.RHTower.zetaPoleUnit (1 - w) := by
  have hw0 : w ≠ 0 := fun he => h0.ne' (by rw [he, Complex.zero_re])
  have hw1 : w ≠ 1 := fun he => h1.ne (by rw [he, Complex.one_re])
  have h1w_re : 0 < (1 - w).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h1w1 : 1 - w ≠ 1 := fun he =>
    h0.ne' (by have := congrArg Complex.re he; simp only [Complex.sub_re, Complex.one_re] at this; linarith)
  have hfe := _root_.RHTower.riemannZeta_eq_reflectionMultiplier_mul
    (Complex.Gammaℝ_ne_zero_of_re_pos h0) (Complex.Gammaℝ_ne_zero_of_re_pos h1w_re)
  rw [_root_.RHTower.zetaPoleUnit_of_ne hw1, _root_.RHTower.zetaPoleUnit_of_ne h1w1,
    hfe, poleReflectionMultiplier]
  field_simp [hw0]
  ring

/-- Bilateral finite-shell reflection defect coupling `(4^K, 9^K)` readings at `w` and `1 - w`. -/
def bilateralReflectionDefect (a : ℕ → ℝ) (K : ℕ) (w : ℂ) : ℂ :=
  weightedAlignedReconstructed a K w -
    poleReflectionMultiplier w * weightedAlignedReconstructed a K (1 - w)

/-- Unconditional, `|ζ|`-free, pole-free decay bound on the bilateral reflection defect of the
actual prime-gas weights `a ≡ 1` across the entire open critical strip `0 < Re w < 1`. -/
theorem norm_bilateralReflectionDefect_one_le {K : ℕ} (hK : 1 ≤ K)
    {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    ‖bilateralReflectionDefect (fun _ => 1) K w‖ ≤
      alignedReconstructionError K w +
        ‖poleReflectionMultiplier w‖ * alignedReconstructionError K (1 - w) := by
  have h1w_re : 0 < (1 - w).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hfe := zetaPoleUnit_eq_poleReflectionMultiplier_mul h0 h1
  have hsplit : bilateralReflectionDefect (fun _ => 1) K w =
      (alignedReconstructedCutoff K w - _root_.RHTower.zetaPoleUnit w) -
        poleReflectionMultiplier w *
          (alignedReconstructedCutoff K (1 - w) - _root_.RHTower.zetaPoleUnit (1 - w)) := by
    unfold bilateralReflectionDefect alignedReconstructedCutoff
    rw [hfe]
    ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  exact add_le_add (norm_alignedReconstructedCutoff_sub_le hK h0)
    (mul_le_mul_of_nonneg_left (norm_alignedReconstructedCutoff_sub_le hK h1w_re) (norm_nonneg _))

theorem tendsto_bilateralReflectionDefect_one_zero {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    Tendsto (fun K : ℕ => bilateralReflectionDefect (fun _ => 1) K w) atTop (𝓝 0) := by
  have h1w_re : 0 < (1 - w).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h0_r := tendsto_alignedReconstructionError_zero h0
  have h1_r := (tendsto_alignedReconstructionError_zero h1w_re).const_mul ‖poleReflectionMultiplier w‖
  rw [mul_zero] at h1_r
  have hsum := h0_r.add h1_r
  rw [add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with K hK
  exact norm_bilateralReflectionDefect_one_le hK h0 h1

/-! ### General finite Dirichlet-convolution surgeries, quartet obstruction, and germ rigidity -/

/-- General finite-support Dirichlet-convolution surgery weight `a(n) = ∑_{1 ≤ d ≤ M, d ∣ n} c(d)`. -/
def dirichletSurgWeight (M : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 M, if d ∣ n then c d else 0

/-- Associated finite Dirichlet polynomial `Q_{M,c}(w) = ∑_{1 ≤ d ≤ M} c(d) d^(-w)`. -/
def dirichletSurgPoly (M : ℕ) (c : ℕ → ℝ) (w : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 M, (c d : ℂ) * (d : ℂ) ^ (-w)

private theorem sum_Icc_dvd_shift {α : Type*} [AddCommMonoid α]
    {d : ℕ} (hd : 0 < d) (Y : ℕ) (f : ℕ → α) :
    (∑ n ∈ Finset.Icc 1 Y, if d ∣ n then f n else 0) =
      ∑ q ∈ Finset.Icc 1 (Y / d), f (d * q) := by
  classical
  rw [← Finset.sum_filter]
  refine (Finset.sum_bij (fun q _ => d * q) ?_ ?_ ?_ ?_).symm
  · intro q hq
    rw [Finset.mem_Icc] at hq
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.mul_pos hd hq.1, by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd).mp hq.2⟩,
      dvd_mul_right d q⟩
  · intro _ _ _ _ heq
    exact Nat.eq_of_mul_eq_mul_left hd heq
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn.2 with ⟨q, rfl⟩
    have hq1 : 1 ≤ q := by rcases Nat.eq_zero_or_pos q with rfl | hq0 <;> [simp at hn; exact hq0]
    exact ⟨q, Finset.mem_Icc.mpr ⟨hq1, (Nat.le_div_iff_mul_le hd).mpr (by rw [mul_comm]; exact hn.1.2)⟩,
      rfl⟩
  · intro _ _; rfl

theorem weightedAdjacentCutoff_dirichletSurgWeight (M : ℕ) (c : ℕ → ℝ)
    (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :
    weightedAdjacentCutoff (dirichletSurgWeight M c) t j X w =
      ∑ d ∈ Finset.Icc 1 M, (c d : ℂ) * (d : ℂ) ^ (-w) * adjacentCutoff t j (X / d) w := by
  have hrad : ∀ Y : ℕ, weightedRadialCutoff (dirichletSurgWeight M c) Y w =
      ∑ d ∈ Finset.Icc 1 M, (c d : ℂ) * (d : ℂ) ^ (-w) * radialCutoff (Y / d) w := fun Y => by
    unfold weightedRadialCutoff dirichletSurgWeight
    simp_rw [Complex.ofReal_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd_pos : 0 < d := by linarith [(Finset.mem_Icc.mp hd).1]
    have hite : ∀ n : ℕ, ((if d ∣ n then c d else 0 : ℝ) : ℂ) * (n : ℂ) ^ (-w) =
        if d ∣ n then (c d : ℂ) * (n : ℂ) ^ (-w) else 0 := fun n => by split_ifs <;> simp
    simp_rw [hite]
    rw [sum_Icc_dvd_shift hd_pos Y (fun n => (c d : ℂ) * (n : ℂ) ^ (-w)),
      radialCutoff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hdr0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hqr0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hcpow : ((d * q : ℕ) : ℂ) ^ (-w) = (d : ℂ) ^ (-w) * (q : ℂ) ^ (-w) := by
      rw [Nat.cast_mul, show (d : ℂ) * (q : ℂ) = ((d : ℝ) : ℂ) * ((q : ℝ) : ℂ) by simp,
        Complex.mul_cpow_ofReal_nonneg hdr0 hqr0]
      simp
    rw [hcpow]; ring
  have hsh : ∀ m : ℕ, weightedShellCutoff (dirichletSurgWeight M c) t m X w =
      ∑ d ∈ Finset.Icc 1 M, (c d : ℂ) * (d : ℂ) ^ (-w) * shellCutoff t m (X / d) w := fun m => by
    set C := tailRadix t m with hCdef
    set q := heat w C with hqdef
    have hC1 : 1 < C.val := radix_gt_one t m
    rw [weightedShellCutoff, ← hCdef, ← hqdef]
    simp_rw [hrad, Finset.mul_sum, Finset.sum_comm (s := Finset.range _)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hLM_le : Nat.log C.val (X / d) ≤ Nat.log C.val X := by
      rcases Nat.eq_zero_or_pos (X / d) with h0 | hpos
      · rw [h0]; simp
      · have hlt : C.val ^ Nat.log C.val (X / d) < C.val ^ (Nat.log C.val X + 1) :=
          ((Nat.pow_log_le_self C.val hpos.ne').trans (Nat.div_le_self X d)).trans_lt
            (Nat.lt_pow_succ_log_self hC1 X)
        exact Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right hC1).mp hlt)
    have hcomm : ∀ i : ℕ, X / C.val ^ (i + 1) / d = X / d / C.val ^ (i + 1) := fun i => by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    simp_rw [hcomm]
    have htrim : (∑ i ∈ Finset.range (Nat.log C.val X),
          2 * (q ^ (i + 1) * ((c d : ℂ) * (d : ℂ) ^ (-w) * radialCutoff (X / d / C.val ^ (i + 1)) w))) =
        ∑ i ∈ Finset.range (Nat.log C.val (X / d)),
          2 * (q ^ (i + 1) * ((c d : ℂ) * (d : ℂ) ^ (-w) * radialCutoff (X / d / C.val ^ (i + 1)) w)) := by
      refine (Finset.sum_subset
        (fun i hi => Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hLM_le)) ?_).symm
      intro i _ hi_not
      have hge : Nat.log C.val (X / d) ≤ i := not_lt.mp (mt Finset.mem_range.mpr hi_not)
      have hlt_pow : X / d < C.val ^ (i + 1) :=
        (Nat.lt_pow_succ_log_self hC1 (X / d)).trans_le
          (Nat.pow_le_pow_right C.pos (Nat.succ_le_succ hge))
      rw [Nat.div_eq_of_lt hlt_pow, radialCutoff_zero, mul_zero, mul_zero, mul_zero]
    rw [htrim, shellCutoff_eq_sum_log t m (X / d) w, ← hCdef, ← hqdef,
      Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [weightedAdjacentCutoff, hsh j, hsh (j + 1), Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [adjacentCutoff]; ring

/-- Holomorphic limit of `weightedAdjacentCutoff` for any finite Dirichlet surgery across `Re w > 0`
(including `w = 1`). -/
theorem tendsto_weightedAdjacentCutoff_dirichletSurgWeight (M : ℕ) (c : ℕ → ℝ)
    (t : ExceptionalTime) (j : ℕ) {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun X : ℕ => weightedAdjacentCutoff (dirichletSurgWeight M c) t j X w)
      atTop (𝓝 (dirichletSurgPoly M c w * contrastResponse (tailRadix t j) w)) := by
  have hsum : Tendsto (fun X : ℕ =>
      ∑ d ∈ Finset.Icc 1 M, (c d : ℂ) * (d : ℂ) ^ (-w) * adjacentCutoff t j (X / d) w)
      atTop (𝓝 (∑ d ∈ Finset.Icc 1 M,
        (c d : ℂ) * (d : ℂ) ^ (-w) * contrastResponse (tailRadix t j) w)) := by
    refine tendsto_finsetSum _ fun d hd => ?_
    have hd_pos : 0 < d := by linarith [(Finset.mem_Icc.mp hd).1]
    have hdiv_top : Tendsto (fun X : ℕ => X / d) atTop atTop :=
      tendsto_atTop.mpr fun B => (eventually_ge_atTop (B * d)).mono fun X hX =>
        (Nat.le_div_iff_mul_le hd_pos).mpr hX
    exact ((adjacent_cutoff_holomorphic_limit t j ⟨w, hw⟩).comp hdiv_top).const_mul _
  rw [← Finset.sum_mul] at hsum
  exact hsum.congr fun X => (weightedAdjacentCutoff_dirichletSurgWeight M c t j X w).symm

/-- Limit of `weightedAlignedReconstructed` for any finite Dirichlet surgery across `Re w > 0`. -/
theorem tendsto_weightedAlignedReconstructed_dirichletSurgWeight (M : ℕ) (c : ℕ → ℝ)
    {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun K : ℕ => weightedAlignedReconstructed (dirichletSurgWeight M c) K w)
      atTop (𝓝 (dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w)) := by
  have hm_ne : (twoPrimeTransferMass w : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (two_prime_transfer_mass_pos ⟨w, hw⟩).ne'
  have hpow_top' : ∀ b : ℕ, 1 < b → Tendsto (fun K : ℕ => b ^ (2 * K)) atTop atTop :=
    fun b hb => tendsto_atTop.mpr fun N => (eventually_ge_atTop N).mono fun K hK =>
      (by omega : N ≤ 2 * K).trans (Nat.lt_pow_self hb).le
  have hden : ∀ B : ℕ+, 1 < B.val →
      Tendsto (fun K : ℕ => (1 : ℂ) - (heat w B) ^ (2 * K)) atTop (𝓝 1) := by
    intro B hB
    have hq2 : ‖(heat w B) ^ 2‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (heat_contraction B hB w hw) (by norm_num)
    have hp := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq2
    have hp' : Tendsto (fun K : ℕ => (heat w B) ^ (2 * K)) atTop (𝓝 0) :=
      hp.congr fun K => (pow_mul (heat w B) 2 K).symm
    simpa only [sub_zero] using tendsto_const_nhds.sub hp'
  have h2 := ((tendsto_weightedAdjacentCutoff_dirichletSurgWeight M c halfTurnClock 0 hw).comp
    (hpow_top' 2 (by norm_num))).div (hden 2 (by change 1 < (2 : ℕ); norm_num)) one_ne_zero
  have h3 := ((tendsto_weightedAdjacentCutoff_dirichletSurgWeight M c primeThreeClock 0 hw).comp
    (hpow_top' 3 (by norm_num))).div (hden 3 (by change 1 < (3 : ℕ); norm_num)) one_ne_zero
  rw [tailRadix_halfTurnClock_zero, div_one] at h2
  rw [tailRadix_primeThreeClock_zero, div_one] at h3
  have hcomb := ((h2.const_mul (conj (contrastTransfer 2 w))).add
    (h3.const_mul (conj (contrastTransfer 3 w)))).div_const (twoPrimeTransferMass w : ℂ)
  have hlim_eq :
      (conj (contrastTransfer 2 w) * (dirichletSurgPoly M c w * contrastResponse 2 w) +
        conj (contrastTransfer 3 w) * (dirichletSurgPoly M c w * contrastResponse 3 w)) /
        (twoPrimeTransferMass w : ℂ) =
      dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w := by
    rw [contrastResponse, contrastResponse]
    have hmass : conj (contrastTransfer 2 w) * contrastTransfer 2 w +
        conj (contrastTransfer 3 w) * contrastTransfer 3 w = (twoPrimeTransferMass w : ℂ) := by
      change _ = ((Complex.normSq (contrastTransfer 2 w) +
        Complex.normSq (contrastTransfer 3 w) : ℝ) : ℂ)
      rw [Complex.ofReal_add, ← Complex.mul_conj, ← Complex.mul_conj]; ring
    field_simp [hm_ne]
    linear_combination dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w * hmass
  rwa [hlim_eq] at hcomb

/-- Exact limit of `bilateralReflectionDefect` for any finite Dirichlet surgery on `0 < Re w < 1`. -/
theorem tendsto_bilateralReflectionDefect_dirichletSurgWeight (M : ℕ) (c : ℕ → ℝ)
    {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    Tendsto (fun K : ℕ => bilateralReflectionDefect (dirichletSurgWeight M c) K w)
      atTop (𝓝 ((dirichletSurgPoly M c w - dirichletSurgPoly M c (1 - w)) *
        _root_.RHTower.zetaPoleUnit w)) := by
  have h1w_re : 0 < (1 - w).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hfe := zetaPoleUnit_eq_poleReflectionMultiplier_mul h0 h1
  have hl := tendsto_weightedAlignedReconstructed_dirichletSurgWeight M c h0
  have hr := (tendsto_weightedAlignedReconstructed_dirichletSurgWeight M c h1w_re).const_mul
    (poleReflectionMultiplier w)
  have hsub := hl.sub hr
  have halg : dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w -
      poleReflectionMultiplier w *
        (dirichletSurgPoly M c (1 - w) * _root_.RHTower.zetaPoleUnit (1 - w)) =
      (dirichletSurgPoly M c w - dirichletSurgPoly M c (1 - w)) *
        _root_.RHTower.zetaPoleUnit w := by
    linear_combination dirichletSurgPoly M c (1 - w) * hfe
  rwa [halg] at hsub

/-- `{5, 7}` positive quartet-surgery counterexample showing single-point reflection at `{w₀, 1 - w₀}`
is sharp-insufficient: for every nonreal `w₀` in `0 < Re w₀ < 1`, a 5-term degree-4 positive surgery
at a single prime `p ∈ {5, 7}` keeps `a(n) ≥ 1` and `a(2^u 3^v) = 1`, yet extinguishes every clock's
`weightedAdjacentCutoff` at **both** `w₀` and `1 - w₀` as well as `bilateralReflectionDefect` at `w₀`. -/
theorem exists_coprime_quartet_surgery_killing_reflected_pair {w₀ : ℂ}
    (hlo : 0 < w₀.re) (hhi : w₀.re < 1) (him : w₀.im ≠ 0) :
    ∃ (p M : ℕ) (c : ℕ → ℝ),
      (p = 5 ∨ p = 7) ∧ 1 ≤ M ∧ c 1 = 1 ∧ (∀ d : ℕ, 0 ≤ c d) ∧
      (∀ n : ℕ, 1 ≤ n → 1 ≤ dirichletSurgWeight M c n) ∧
      (∀ u v : ℕ, dirichletSurgWeight M c (2 ^ u * 3 ^ v) = 1) ∧
      (∀ (t : ExceptionalTime) (j : ℕ),
        Tendsto (fun X : ℕ => weightedAdjacentCutoff (dirichletSurgWeight M c) t j X w₀)
          atTop (𝓝 0) ∧
        Tendsto (fun X : ℕ => weightedAdjacentCutoff (dirichletSurgWeight M c) t j X (1 - w₀))
          atTop (𝓝 0)) ∧
      Tendsto (fun K : ℕ => bilateralReflectionDefect (dirichletSurgWeight M c) K w₀)
        atTop (𝓝 0) := by
  have hphase := five_seven_phase_ne_one him
  obtain ⟨p, hp57, hu_ne1⟩ : ∃ p : ℕ, (p = 5 ∨ p = 7) ∧
      Complex.exp (-(Real.log p : ℂ) * (w₀.im : ℂ) * Complex.I) ≠ 1 := by
    rcases hphase with h5 | h7
    · exact ⟨5, Or.inl rfl, by simpa using h5⟩
    · exact ⟨7, Or.inr rfl, by simpa using h7⟩
  have hp_prime : Nat.Prime p := by rcases hp57 with rfl | rfl <;> decide
  have hp_gt1 : 1 < p := hp_prime.one_lt
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_prime.pos
  set u : ℂ := Complex.exp (-(Real.log p : ℂ) * (w₀.im : ℂ) * Complex.I)
  have hu_norm : ‖u‖ = 1 := by
    dsimp only [u]; rw [Complex.norm_exp]
    have hre0 : (-(Real.log p : ℂ) * (w₀.im : ℂ) * Complex.I).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hre0, Real.exp_zero]
  obtain ⟨k, hk1, hvk_neg⟩ := PositiveAnnihilator.exists_large_pow_re_neg hu_norm hu_ne1 1
  set v : ℂ := u ^ k
  have hv_norm : ‖v‖ = 1 := by dsimp only [v]; rw [norm_pow, hu_norm, one_pow]
  set r₀ : ℝ := (p : ℝ) ^ (-(k : ℝ) * w₀.re)
  set r₁ : ℝ := (p : ℝ) ^ (-(k : ℝ) * (1 - w₀.re))
  have hr₀_pos : 0 < r₀ := Real.rpow_pos_of_pos hp_pos _
  have hr₁_pos : 0 < r₁ := Real.rpow_pos_of_pos hp_pos _
  let a₁ : ℝ := -2 * v.re * r₀⁻¹
  let a₂ : ℝ := (r₀⁻¹) ^ 2
  let b₁ : ℝ := -2 * v.re * r₁⁻¹
  let b₂ : ℝ := (r₁⁻¹) ^ 2
  have ha₁ : 0 < a₁ := mul_pos (by linarith) (inv_pos.mpr hr₀_pos)
  have ha₂ : 0 < a₂ := pow_pos (inv_pos.mpr hr₀_pos) 2
  have hb₁ : 0 < b₁ := mul_pos (by linarith) (inv_pos.mpr hr₁_pos)
  have hb₂ : 0 < b₂ := pow_pos (inv_pos.mpr hr₁_pos) 2
  let d₁ := p ^ k
  let d₂ := p ^ (2 * k)
  let d₃ := p ^ (3 * k)
  let d₄ := p ^ (4 * k)
  have h1_lt_d1 : 1 < d₁ := one_lt_pow₀ hp_gt1 (by omega)
  have hd12 : d₁ < d₂ := Nat.pow_lt_pow_right hp_gt1 (by omega)
  have hd23 : d₂ < d₃ := Nat.pow_lt_pow_right hp_gt1 (by omega)
  have hd34 : d₃ < d₄ := Nat.pow_lt_pow_right hp_gt1 (by omega)
  let c (d : ℕ) : ℝ :=
    if d = 1 then 1
    else if d = d₁ then a₁ + b₁
    else if d = d₂ then a₂ + a₁ * b₁ + b₂
    else if d = d₃ then a₁ * b₂ + a₂ * b₁
    else if d = d₄ then a₂ * b₂
    else 0
  have hc1 : c 1 = 1 := by simp [c]
  have hc_nn : ∀ d : ℕ, 0 ≤ c d := fun d => by
    dsimp only [c]; split_ifs <;> positivity
  -- Evaluate `dirichletSurgPoly d₄ c s` as the product of the two quadratic factors in `(p^k)^(-s)`.
  have hpow_Z : ∀ (m : ℕ) (s : ℂ), ((p ^ (m * k) : ℕ) : ℂ) ^ (-s) = (((p ^ k : ℕ) : ℂ) ^ (-s)) ^ m := by
    intro m s
    induction m with
    | zero => simp
    | succ m ih =>
      have ha_nn : (0 : ℝ) ≤ (p ^ (m * k) : ℕ) := Nat.cast_nonneg _
      have hb_nn : (0 : ℝ) ≤ (p ^ k : ℕ) := Nat.cast_nonneg _
      rw [Nat.succ_mul, pow_add, Nat.cast_mul,
        show ((p ^ (m * k) : ℕ) : ℂ) * ((p ^ k : ℕ) : ℂ) =
          (((p ^ (m * k) : ℕ) : ℝ) : ℂ) * (((p ^ k : ℕ) : ℝ) : ℂ) by simp,
        Complex.mul_cpow_ofReal_nonneg ha_nn hb_nn]
      simp only [Complex.ofReal_natCast]
      rw [ih, pow_succ]
  have hpoly_fac : ∀ s : ℂ, dirichletSurgPoly d₄ c s =
      (1 + (a₁ : ℂ) * ((d₁ : ℕ) : ℂ) ^ (-s) + (a₂ : ℂ) * (((d₁ : ℕ) : ℂ) ^ (-s)) ^ 2) *
      (1 + (b₁ : ℂ) * ((d₁ : ℕ) : ℂ) ^ (-s) + (b₂ : ℂ) * (((d₁ : ℕ) : ℂ) ^ (-s)) ^ 2) := by
    intro s
    classical
    let S₅ : Finset ℕ := {1, d₁, d₂, d₃, d₄}
    have hsub : S₅ ⊆ Finset.Icc 1 d₄ := by
      intro x hx
      simp only [S₅, Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
    have hzero_out : ∀ x ∈ Finset.Icc 1 d₄, x ∉ S₅ → (c x : ℂ) * (x : ℂ) ^ (-s) = 0 := by
      intro x _ hx
      simp only [S₅, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      rcases hx with ⟨h1, h2, h3, h4, h5⟩
      simp [c, h1, h2, h3, h4, h5]
    rw [dirichletSurgPoly, ← Finset.sum_subset hsub hzero_out]
    have hn1 : (1 : ℕ) ∉ ({d₁, d₂, d₃, d₄} : Finset ℕ) := by simp; omega
    have hn2 : d₁ ∉ ({d₂, d₃, d₄} : Finset ℕ) := by simp; omega
    have hn3 : d₂ ∉ ({d₃, d₄} : Finset ℕ) := by simp; omega
    have hn4 : d₃ ∉ ({d₄} : Finset ℕ) := by simp; omega
    dsimp only [S₅]
    rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_insert hn3,
      Finset.sum_insert hn4, Finset.sum_singleton]
    have hc_d1 : c d₁ = a₁ + b₁ := by simp [c, show d₁ ≠ 1 by omega]
    have hc_d2 : c d₂ = a₂ + a₁ * b₁ + b₂ := by
      simp [c, show d₂ ≠ 1 by omega, show d₂ ≠ d₁ by omega]
    have hc_d3 : c d₃ = a₁ * b₂ + a₂ * b₁ := by
      simp [c, show d₃ ≠ 1 by omega, show d₃ ≠ d₁ by omega, show d₃ ≠ d₂ by omega]
    have hc_d4 : c d₄ = a₂ * b₂ := by
      simp [c, show d₄ ≠ 1 by omega, show d₄ ≠ d₁ by omega,
        show d₄ ≠ d₂ by omega, show d₄ ≠ d₃ by omega]
    rw [hc1, hc_d1, hc_d2, hc_d3, hc_d4]
    dsimp only [d₂, d₃, d₄]
    rw [hpow_Z 2 s, hpow_Z 3 s, hpow_Z 4 s]
    dsimp only [d₁]
    push_cast
    rw [Complex.one_cpow]
    ring
  -- Show the first factor vanishes at `w₀` and the second factor vanishes at `1 - w₀`.
  have hd1_w0 : ((d₁ : ℕ) : ℂ) ^ (-w₀) = (r₀ : ℂ) * v := by
    dsimp only [d₁]
    have hpk_pos : (0 : ℝ) < (p ^ k : ℕ) := by exact_mod_cast pow_pos hp_prime.pos k
    rw [show ((p ^ k : ℕ) : ℂ) = (((p ^ k : ℕ) : ℝ) : ℂ) by simp,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpk_pos.ne'),
      ← Complex.ofReal_log hpk_pos.le, Nat.cast_pow, Real.log_pow]
    dsimp only [r₀, v, u]
    rw [Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im w₀]
    push_cast; ring
  have hd1_1w0 : ((d₁ : ℕ) : ℂ) ^ (-(1 - w₀)) = (r₁ : ℂ) * conj v := by
    dsimp only [d₁]
    have hpk_pos : (0 : ℝ) < (p ^ k : ℕ) := by exact_mod_cast pow_pos hp_prime.pos k
    have hcv : conj v = Complex.exp ((k : ℂ) * ((Real.log p : ℂ) * (w₀.im : ℂ) * Complex.I)) := by
      dsimp only [v, u]
      rw [← Complex.exp_nat_mul, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_neg, map_natCast, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [show ((p ^ k : ℕ) : ℂ) = (((p ^ k : ℕ) : ℝ) : ℂ) by simp,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpk_pos.ne'),
      ← Complex.ofReal_log hpk_pos.le, Nat.cast_pow, Real.log_pow]
    dsimp only [r₁]
    rw [hcv, Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have h1w0 : 1 - w₀ = (((1 - w₀.re : ℝ) : ℂ) - (w₀.im : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.re_add_im w₀]
      push_cast; ring
    rw [h1w0]; push_cast; ring
  have hpoly_w0 : dirichletSurgPoly d₄ c w₀ = 0 := by
    rw [hpoly_fac w₀, hd1_w0]
    have hr_ne : (r₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₀_pos.ne'
    have hq0 : 1 + (a₁ : ℂ) * ((r₀ : ℂ) * v) + (a₂ : ℂ) * ((r₀ : ℂ) * v) ^ 2 =
        1 + ((-2 * v.re : ℝ) : ℂ) * v + v ^ 2 := by
      dsimp only [a₁, a₂]; push_cast; field_simp [hr_ne]
    rw [hq0, PositiveAnnihilator.unit_quadratic hv_norm, zero_mul]
  have hpoly_1w0 : dirichletSurgPoly d₄ c (1 - w₀) = 0 := by
    rw [hpoly_fac (1 - w₀), hd1_1w0]
    have hr_ne : (r₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₁_pos.ne'
    have hcv_norm : ‖conj v‖ = 1 := by rw [Complex.norm_conj, hv_norm]
    have hq1 : 1 + (b₁ : ℂ) * ((r₁ : ℂ) * conj v) + (b₂ : ℂ) * ((r₁ : ℂ) * conj v) ^ 2 =
        1 + ((-2 * (conj v).re : ℝ) : ℂ) * conj v + (conj v) ^ 2 := by
      rw [Complex.conj_re]
      dsimp only [b₁, b₂]; push_cast; field_simp [hr_ne]
    rw [hq1, PositiveAnnihilator.unit_quadratic hcv_norm, mul_zero]
  have h1w0_re : 0 < (1 - w₀).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw_ge1 : ∀ n : ℕ, 1 ≤ n → 1 ≤ dirichletSurgWeight d₄ c n := by
    intro n _
    unfold dirichletSurgWeight
    have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 d₄ := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hle := Finset.single_le_sum (f := fun d => if d ∣ n then c d else 0)
      (fun d _ => by split_ifs <;> [exact hc_nn d; exact le_rfl]) h1_mem
    simpa only [one_dvd, ↓reduceIte, hc1] using hle
  have hsmooth : ∀ u₂ v₃ : ℕ, dirichletSurgWeight d₄ c (2 ^ u₂ * 3 ^ v₃) = 1 := by
    intro u₂ v₃
    have hcop2 : Nat.Coprime 2 p := by rcases hp57 with rfl | rfl <;> decide
    have hcop3 : Nat.Coprime 3 p := by rcases hp57 with rfl | rfl <;> decide
    have hcop : Nat.Coprime (2 ^ u₂ * 3 ^ v₃) p :=
      (hcop2.pow_left u₂).mul_left (hcop3.pow_left v₃)
    have hnot_p : ¬(p ∣ 2 ^ u₂ * 3 ^ v₃) := fun hd =>
      hp_prime.not_dvd_one (hcop ▸ Nat.dvd_gcd hd (dvd_refl p))
    unfold dirichletSurgWeight
    rw [Finset.sum_eq_single 1]
    · simp [hc1]
    · intro d _ hd1
      by_cases hd_dvd : d ∣ 2 ^ u₂ * 3 ^ v₃
      · rw [if_pos hd_dvd]
        have hnd1 : d ≠ d₁ := fun he => hnot_p ((dvd_pow_self p (by omega)).trans (he ▸ hd_dvd))
        have hnd2 : d ≠ d₂ := fun he => hnot_p ((dvd_pow_self p (by omega)).trans (he ▸ hd_dvd))
        have hnd3 : d ≠ d₃ := fun he => hnot_p ((dvd_pow_self p (by omega)).trans (he ▸ hd_dvd))
        have hnd4 : d ≠ d₄ := fun he => hnot_p ((dvd_pow_self p (by omega)).trans (he ▸ hd_dvd))
        simp [c, hd1, hnd1, hnd2, hnd3, hnd4]
      · rw [if_neg hd_dvd]
    · intro hnot
      exact False.elim (hnot (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
  refine ⟨p, d₄, c, hp57, by omega, hc1, hc_nn, hw_ge1, hsmooth, fun t j => ⟨?_, ?_⟩, ?_⟩
  · simpa only [hpoly_w0, zero_mul] using
      tendsto_weightedAdjacentCutoff_dirichletSurgWeight d₄ c t j hlo
  · simpa only [hpoly_1w0, zero_mul] using
      tendsto_weightedAdjacentCutoff_dirichletSurgWeight d₄ c t j h1w0_re
  · simpa only [hpoly_w0, hpoly_1w0, sub_self, zero_mul] using
      tendsto_bilateralReflectionDefect_dirichletSurgWeight d₄ c hlo hhi

/-- **Complete germ-level bilateral reflection rigidity:** for any finite Dirichlet-convolution
surgery `dirichletSurgWeight M c` (`M ≥ 1`, `c(1) = 1`), if `bilateralReflectionDefect` tends to
`0` frequently on `𝓝[≠] w₀` at any single point `w₀` in `0 < Re w₀ < 1`, then `c(d) = 0` for all
`2 ≤ d ≤ M` and `dirichletSurgWeight M c n = 1` for every `n ∈ ℕ`. -/
theorem dirichletSurgWeight_eq_one_of_frequently_reflection_vanishing
    {M : ℕ} (hM : 1 ≤ M) {c : ℕ → ℝ} (hc1 : c 1 = 1)
    {w₀ : ℂ} (hlo : 0 < w₀.re) (hhi : w₀.re < 1)
    (hfreq : ∃ᶠ w in 𝓝[≠] w₀,
      Tendsto (fun K : ℕ => bilateralReflectionDefect (dirichletSurgWeight M c) K w)
        atTop (𝓝 0)) :
    (∀ d ∈ Finset.Icc 2 M, c d = 0) ∧ ∀ n : ℕ, dirichletSurgWeight M c n = 1 := by
  -- Step 1: Identify `(Q(w) - Q(1 - w)) * zetaPoleUnit w = 0` frequently on `𝓝[≠] w₀`, hence on `ℂ`.
  let F (w : ℂ) : ℂ :=
    (dirichletSurgPoly M c w - dirichletSurgPoly M c (1 - w)) * _root_.RHTower.zetaPoleUnit w
  have hstrip_open : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hstrip_nhds : {z : ℂ | 0 < z.re ∧ z.re < 1} ∈ 𝓝[≠] w₀ :=
    nhdsWithin_le_nhds (hstrip_open.mem_nhds ⟨hlo, hhi⟩)
  have hF_freq : ∃ᶠ w in 𝓝[≠] w₀, F w = 0 := by
    refine (hfreq.and_eventually hstrip_nhds).mono fun w ⟨htend, hw0, hw1⟩ => ?_
    exact tendsto_nhds_unique
      (tendsto_bilateralReflectionDefect_dirichletSurgWeight M c hw0 hw1) htend
  have hpoly_diff : Differentiable ℂ (dirichletSurgPoly M c) := by
    intro z
    unfold dirichletSurgPoly
    refine DifferentiableAt.fun_sum fun d hd => ?_
    have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [(Finset.mem_Icc.mp hd).1])
    exact (differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hd0))
  have hF_diff : Differentiable ℂ F :=
    (hpoly_diff.sub (hpoly_diff.comp (differentiable_const (1 : ℂ) |>.sub differentiable_id))).mul
      _root_.RHTower.differentiable_zetaPoleUnit
  have hF_ana : AnalyticOnNhd ℂ F Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hF_diff
  have hF_zero : ∀ z : ℂ, F z = 0 := fun z =>
    hF_ana.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ w₀) hF_freq (Set.mem_univ z)
  -- Step 2: Evaluate at integers `z = (n + 2 : ℕ)` (`Re z ≥ 2 > 1`) where `zetaPoleUnit z ≠ 0`.
  have hreal_eq : ∀ n : ℕ,
      (∑ d ∈ Finset.Icc 1 M, c d * ((d : ℝ)⁻¹) ^ (n + 2)) =
        ∑ d ∈ Finset.Icc 1 M, c d * (d : ℝ) ^ (n + 1) := by
    intro n
    set σ : ℝ := ((n + 2 : ℕ) : ℝ)
    have hσ1 : 1 < σ := by dsimp only [σ]; exact_mod_cast (by omega : 1 < n + 2)
    have hσ_ne1 : (σ : ℂ) ≠ 1 := fun he => hσ1.ne' (by simpa using congrArg Complex.re he)
    have hz_ne : _root_.RHTower.zetaPoleUnit (σ : ℂ) ≠ 0 :=
      _root_.RHTower.zetaPoleUnit_ne_zero hσ_ne1
        (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ1))
    have hQ_eq : dirichletSurgPoly M c (σ : ℂ) = dirichletSurgPoly M c (1 - (σ : ℂ)) :=
      sub_eq_zero.mp ((mul_eq_zero.mp (hF_zero (σ : ℂ))).resolve_right hz_ne)
    have hre := congrArg Complex.re hQ_eq
    have hlhs : (dirichletSurgPoly M c (σ : ℂ)).re =
        ∑ d ∈ Finset.Icc 1 M, c d * ((d : ℝ)⁻¹) ^ (n + 2) := by
      unfold dirichletSurgPoly
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by linarith [(Finset.mem_Icc.mp hd).1])
      have hcpow : ((d : ℂ) ^ (-(σ : ℂ))) = (((((d : ℝ)⁻¹) ^ (n + 2) : ℝ)) : ℂ) := by
        rw [show (d : ℂ) = ((d : ℝ) : ℂ) by simp, ← Complex.ofReal_neg,
          ← Complex.ofReal_cpow hd_pos.le, Real.rpow_neg hd_pos.le]
        dsimp only [σ]
        rw [Real.rpow_natCast, inv_pow]
      rw [hcpow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hrhs : (dirichletSurgPoly M c (1 - (σ : ℂ))).re =
        ∑ d ∈ Finset.Icc 1 M, c d * (d : ℝ) ^ (n + 1) := by
      unfold dirichletSurgPoly
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by linarith [(Finset.mem_Icc.mp hd).1])
      have h1σ : (1 : ℂ) - (σ : ℂ) = ((-(n + 1 : ℕ) : ℝ) : ℂ) := by
        dsimp only [σ]; push_cast; ring
      have hcpow : ((d : ℂ) ^ (-(1 - (σ : ℂ)))) = ((((d : ℝ) ^ (n + 1) : ℝ)) : ℂ) := by
        rw [h1σ, ← Complex.ofReal_neg, neg_neg, show (d : ℂ) = ((d : ℝ) : ℂ) by simp,
          ← Complex.ofReal_cpow hd_pos.le, Real.rpow_natCast]
      rw [hcpow, ← Complex.ofReal_mul, Complex.ofReal_re]
    rwa [hlhs, hrhs] at hre
  -- Step 3: Extract leading exponent `dStar = max {d ∈ [2, M] | c d ≠ 0}` if nonempty.
  have hc_zero : ∀ d ∈ Finset.Icc 2 M, c d = 0 := by
    classical
    by_contra! hne
    rcases hne with ⟨d₀, hd₀_mem, hd₀_ne⟩
    let S := (Finset.Icc 2 M).filter (fun d => c d ≠ 0)
    have hSne : S.Nonempty := ⟨d₀, Finset.mem_filter.mpr ⟨hd₀_mem, hd₀_ne⟩⟩
    set dStar := S.max' hSne
    have hdStar_mem : dStar ∈ S := Finset.max'_mem S hSne
    obtain ⟨hdStar_Icc, hc_dStar_ne⟩ := Finset.mem_filter.mp hdStar_mem
    obtain ⟨hdStar_ge2, hdStar_leM⟩ := Finset.mem_Icc.mp hdStar_Icc
    have hdStar_gt1 : (1 : ℝ) < dStar := by exact_mod_cast (by omega : 1 < dStar)
    have hdStar_pos : (0 : ℝ) < dStar := by positivity
    -- Rescale `hreal_eq n` by `(dStar⁻¹)^(n + 1)` and send `n → ∞`.
    have hlhs_tendsto : Tendsto (fun n : ℕ =>
        ((dStar : ℝ)⁻¹) ^ (n + 1) * ∑ d ∈ Finset.Icc 1 M, c d * ((d : ℝ)⁻¹) ^ (n + 2))
        atTop (𝓝 0) := by
      have hsum : Tendsto (fun n : ℕ =>
          ∑ d ∈ Finset.Icc 1 M, c d * ((d : ℝ)⁻¹) * (((dStar : ℝ)⁻¹ * (d : ℝ)⁻¹) ^ (n + 1)))
          atTop (𝓝 (∑ _d ∈ Finset.Icc 1 M, (0 : ℝ))) := by
        refine tendsto_finsetSum _ fun d hd => ?_
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
        have hd_inv_le1 : (d : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd1
        have hlt1 : (dStar : ℝ)⁻¹ * (d : ℝ)⁻¹ < 1 :=
          (mul_le_of_le_one_right (by positivity) hd_inv_le1).trans_lt (inv_lt_one_of_one_lt₀ hdStar_gt1)
        have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt1).comp
          (tendsto_add_atTop_nat 1)
        simpa only [mul_zero, Function.comp_def] using hp.const_mul (c d * (d : ℝ)⁻¹)
      rw [Finset.sum_const_zero] at hsum
      refine hsum.congr fun n => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [mul_pow, show n + 2 = (n + 1) + 1 by rfl, pow_succ]
      ring
    have hrhs_tendsto : Tendsto (fun n : ℕ =>
        ((dStar : ℝ)⁻¹) ^ (n + 1) * ∑ d ∈ Finset.Icc 1 M, c d * (d : ℝ) ^ (n + 1))
        atTop (𝓝 (c dStar)) := by
      have hsum : Tendsto (fun n : ℕ =>
          ∑ d ∈ Finset.Icc 1 M, c d * ((d : ℝ) / (dStar : ℝ)) ^ (n + 1))
          atTop (𝓝 (∑ d ∈ Finset.Icc 1 M, if d = dStar then c dStar else 0)) := by
        refine tendsto_finsetSum _ fun d hd => ?_
        rcases lt_trichotomy d dStar with hlt | rfl | hgt
        · rw [if_neg hlt.ne]
          have hd_lt : (d : ℝ) / (dStar : ℝ) < 1 :=
            (div_lt_one hdStar_pos).mpr (by exact_mod_cast hlt)
          have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hd_lt).comp
            (tendsto_add_atTop_nat 1)
          simpa only [mul_zero, Function.comp_def] using hp.const_mul (c d)
        · rw [if_pos rfl]
          have h1 : ((dStar : ℝ) / (dStar : ℝ)) = 1 := div_self hdStar_pos.ne'
          simpa only [h1, one_pow, mul_one] using (tendsto_const_nhds (x := c dStar))
        · rw [if_neg hgt.ne']
          have hd_ge2 : 2 ≤ d := by omega
          have hd_Icc2 : d ∈ Finset.Icc 2 M :=
            Finset.mem_Icc.mpr ⟨hd_ge2, (Finset.mem_Icc.mp hd).2⟩
          have hc0 : c d = 0 := by
            by_contra hc_nz
            exact hgt.not_ge (Finset.le_max' S d (Finset.mem_filter.mpr ⟨hd_Icc2, hc_nz⟩))
          simp [hc0]
      have hsum_val : (∑ d ∈ Finset.Icc 1 M, if d = dStar then c dStar else 0) = c dStar := by
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_Icc.mpr ⟨by omega, hdStar_leM⟩)]
      rw [hsum_val] at hsum
      refine hsum.congr fun n => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [div_eq_mul_inv, mul_pow]
      ring
    have heq_seq : ∀ n : ℕ,
        ((dStar : ℝ)⁻¹) ^ (n + 1) * (∑ d ∈ Finset.Icc 1 M, c d * ((d : ℝ)⁻¹) ^ (n + 2)) =
        ((dStar : ℝ)⁻¹) ^ (n + 1) * (∑ d ∈ Finset.Icc 1 M, c d * (d : ℝ) ^ (n + 1)) :=
      fun n => congrArg (((dStar : ℝ)⁻¹) ^ (n + 1) * ·) (hreal_eq n)
    exact hc_dStar_ne (tendsto_nhds_unique (hrhs_tendsto.congr fun n => (heq_seq n).symm) hlhs_tendsto)
  refine ⟨hc_zero, fun n => ?_⟩
  unfold dirichletSurgWeight
  rw [Finset.sum_eq_single 1]
  · simp [hc1]
  · intro d hd hd1
    have hd2 : d ∈ Finset.Icc 2 M :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega, (Finset.mem_Icc.mp hd).2⟩
    simp [hc_zero d hd2]
  · intro hnot
    exact False.elim (hnot (Finset.mem_Icc.mpr ⟨le_rfl, hM⟩))

#print axioms norm_alignedReconstructedCutoff_sub_le
#print axioms exists_aligned_margin_at_one
#print axioms norm_bilateralReflectionDefect_one_le
#print axioms tendsto_bilateralReflectionDefect_one_zero
#print axioms exists_coprime_quartet_surgery_killing_reflected_pair
#print axioms dirichletSurgWeight_eq_one_of_frequently_reflection_vanishing

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
