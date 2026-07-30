import GaloisForLFunctions.RHTower.CompletePositiveKolchinFreeRiemannResolution
import GaloisForLFunctions.RHTower.XiWoldPoissonBivariateConormal
import GaloisForLFunctions.HTGeometry.LeastAtomModularTransferLaw

/-!
# Least-atom asymptotic of the positive high-exponent shell

For

`Hₙ(s) = ζ((n+1)s)⁻¹ - ζ(ns)⁻¹`,

the least Dirichlet atom gives the exact ray asymptotic

`2^(ns) Hₙ(s) → 1 - 2^(-s)`

for every `Re s > 0`.  The result is quantitative before passage to the
limit: after the atom `2⁻ʷ` is removed from `ζ(w) - 1`, multiplication by
`2ʷ` leaves an error at most `2 / (Re w - 1)`.
-/

open Complex Filter Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Quantitative prime-two extraction for zeta on `Re w > 1`. -/
theorem norm_two_cpow_mul_riemannZeta_sub_one_sub_one_le
    {w : ℂ} (hw : 1 < w.re) :
    ‖(2 : ℂ) ^ w * (riemannZeta w - 1) - 1‖ ≤ 2 / (w.re - 1) := by
  have hre0 : w.re ≠ 0 := by linarith
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ w) :=
    summable_one_div_nat_cpow.mpr hw
  have htailSum : Summable (fun i : ℕ => 1 / ((i + 3 : ℕ) : ℂ) ^ w) := by
    simpa [Function.comp_def] using hsum.comp_injective
      (fun i j hij => Nat.add_right_cancel hij :
        Function.Injective (fun i : ℕ => i + 3))
  have hsplit := hsum.sum_add_tsum_nat_add 3
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have h012 :
      ∑ i ∈ Finset.range 3, 1 / (i : ℂ) ^ w =
        1 + 1 / (2 : ℂ) ^ w := by
    simp [Finset.sum_range_succ, Complex.zero_cpow hw0]
  have htailEq :
      riemannZeta w - 1 - 1 / (2 : ℂ) ^ w =
        ∑' i : ℕ, 1 / ((i + 3 : ℕ) : ℂ) ^ w := by
    rw [zeta_eq_tsum_one_div_nat_cpow hw, ← hsplit, h012]
    ring
  have hterm : ∀ i : ℕ,
      ‖1 / ((i + 3 : ℕ) : ℂ) ^ w‖ =
        1 / ((i + 3 : ℕ) : ℝ) ^ w.re := by
    intro i
    rw [norm_div, norm_one,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < i + 3)]
  have halgebra :
      (2 : ℂ) ^ w * (riemannZeta w - 1) - 1 =
        (2 : ℂ) ^ w *
          (riemannZeta w - 1 - 1 / (2 : ℂ) ^ w) := by
    field_simp
  have hnormtwo : ‖(2 : ℂ) ^ w‖ = (2 : ℝ) ^ w.re := by
    exact Complex.norm_natCast_cpow_of_pos (n := 2) (by norm_num) w
  rw [halgebra, htailEq, norm_mul, hnormtwo]
  calc
    (2 : ℝ) ^ w.re *
          ‖∑' i : ℕ, 1 / ((i + 3 : ℕ) : ℂ) ^ w‖
        ≤ (2 : ℝ) ^ w.re *
          ∑' i : ℕ, ‖1 / ((i + 3 : ℕ) : ℂ) ^ w‖ := by
      gcongr
      exact norm_tsum_le_tsum_norm htailSum.norm
    _ = (2 : ℝ) ^ w.re *
          ∑' i : ℕ, 1 / ((i + 3 : ℕ) : ℝ) ^ w.re := by
      congr 1
      exact tsum_congr hterm
    _ ≤ (2 : ℝ) ^ w.re *
          ((2 : ℝ) ^ (1 - w.re) / (w.re - 1)) := by
      gcongr
      have hb := tsum_add_rpow_neg_le hw (M := 2) (by omega)
      refine le_trans (le_of_eq (tsum_congr fun i => ?_)) hb
      rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
    _ = 2 / (w.re - 1) := by
      rw [div_eq_mul_inv, ← mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
      rfl

/-- Along every ray in the open right half-plane, the first nontrivial
Dirichlet atom of zeta is asymptotically exact. -/
theorem tendsto_two_cpow_nat_mul_riemannZeta_sub_one
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ =>
        (2 : ℂ) ^ ((n : ℂ) * s) *
          (riemannZeta ((n : ℂ) * s) - 1))
      atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hre :
      Tendsto (fun n : ℕ => (((n : ℂ) * s).re))
        atTop atTop := by
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    exact tendsto_natCast_atTop_atTop.atTop_mul_const hs
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1
      (hre.eventually_gt_atTop (1 + 2 / ε))
  refine ⟨N, fun n hn => ?_⟩
  have hnlarge := hN n hn
  have hw : 1 < (((n : ℂ) * s).re) := by
    have hpos : 0 < 2 / ε := div_pos (by norm_num) hε
    linarith
  have hbound :=
    norm_two_cpow_mul_riemannZeta_sub_one_sub_one_le hw
  rw [dist_eq]
  refine hbound.trans_lt ?_
  have hden : 2 / ε < (((n : ℂ) * s).re) - 1 := by
    linarith
  have hdenpos : 0 < (((n : ℂ) * s).re) - 1 := by
    linarith
  apply (div_lt_iff₀ hdenpos).2
  have hscaled := (div_lt_iff₀ hε).mp hden
  nlinarith

/-- Reciprocal zeta has leading normalized atom `-1` on every open
right-half-plane ray. -/
theorem tendsto_two_cpow_nat_mul_inv_riemannZeta_sub_one
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ =>
        (2 : ℂ) ^ ((n : ℂ) * s) *
          ((riemannZeta ((n : ℂ) * s))⁻¹ - 1))
      atTop (nhds (-1)) := by
  have hfirst := tendsto_two_cpow_nat_mul_riemannZeta_sub_one hs
  have hinv := tendsto_inv_riemannZeta_nat_dilation_one (K := 0) hs
  have hproduct := hfirst.mul hinv
  have hneg : Tendsto
      (fun n : ℕ =>
        -((2 : ℂ) ^ ((n : ℂ) * s) *
          (riemannZeta ((n : ℂ) * s) - 1) *
          (riemannZeta ((n : ℂ) * s))⁻¹))
      atTop (nhds (-1)) := by
    simpa using hproduct.neg
  refine hneg.congr' ?_
  have hre :
      Tendsto (fun n : ℕ => (((n : ℂ) * s).re))
        atTop atTop := by
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    exact tendsto_natCast_atTop_atTop.atTop_mul_const hs
  filter_upwards [hre.eventually_gt_atTop 1] with n hn
  have hz : riemannZeta ((n : ℂ) * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hn
  field_simp
  ring

/-- **Least-atom shell law.**  The positive largest-exponent shell has
exact asymptotic character `1 - 2⁻ˢ` on every ray `Re s > 0`. -/
theorem tendsto_two_cpow_nat_mul_shellMultiplier
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ =>
        (2 : ℂ) ^ ((n : ℂ) * s) * shellMultiplier n s)
      atTop (nhds (1 - (2 : ℂ) ^ (-s))) := by
  let B : ℕ → ℂ := fun n =>
    (2 : ℂ) ^ ((n : ℂ) * s) *
      ((riemannZeta ((n : ℂ) * s))⁻¹ - 1)
  have hB : Tendsto B atTop (nhds (-1)) := by
    simpa [B] using
      tendsto_two_cpow_nat_mul_inv_riemannZeta_sub_one hs
  have hsucc : Tendsto (fun n : ℕ => B (n + 1))
      atTop (nhds (-1)) := by
    exact hB.comp (by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat 1)
  have hlim := (hsucc.const_mul ((2 : ℂ) ^ (-s))).sub hB
  have htarget :
      (2 : ℂ) ^ (-s) * (-1) - (-1) =
        1 - (2 : ℂ) ^ (-s) := by ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [] with n
  have hpow :
      (2 : ℂ) ^ (-s) *
          (2 : ℂ) ^ (((n + 1 : ℕ) : ℂ) * s) =
        (2 : ℂ) ^ ((n : ℂ) * s) := by
    rw [← Complex.cpow_add _ _ (by norm_num)]
    congr 2
    push_cast
    ring
  dsimp only [B]
  rw [shellMultiplier, ← mul_assoc, hpow]
  push_cast
  ring

/-! ## The renormalization-transfer character -/

/-- The least-atom amplitude never vanishes in the open right
half-plane. -/
theorem one_sub_two_cpow_neg_ne_zero
    {rho : ℂ} (hrho : 0 < rho.re) :
    1 - (2 : ℂ) ^ (-rho) ≠ 0 := by
  have hbase : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  have hnorm :
      ‖(2 : ℂ) ^ (-rho)‖ < 1 := by
    rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos
      (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num) (by simp only [Complex.neg_re]; linarith)
  intro hzero
  have heq : (2 : ℂ) ^ (-rho) = 1 :=
    (sub_eq_zero.mp hzero).symm
  rw [heq, norm_one] at hnorm
  exact (lt_irrefl 1 hnorm)

/-- Raw transport between two adjacent positive shells. -/
def shellAdjacentTransfer (n : ℕ) (s : ℂ) : ℂ :=
  shellMultiplier (n + 1) s / shellMultiplier n s

/-- Adjacent shells have the exact asymptotic transfer character `2⁻ˢ`. -/
theorem tendsto_shellAdjacentTransfer
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => shellAdjacentTransfer n s)
      atTop (nhds ((2 : ℂ) ^ (-s))) := by
  let B : ℕ → ℂ := fun n =>
    (2 : ℂ) ^ ((n : ℂ) * s) * shellMultiplier n s
  have hB : Tendsto B atTop
      (nhds (1 - (2 : ℂ) ^ (-s))) := by
    simpa only [B] using
      tendsto_two_cpow_nat_mul_shellMultiplier hs
  have hlim_ne : 1 - (2 : ℂ) ^ (-s) ≠ 0 :=
    one_sub_two_cpow_neg_ne_zero hs
  have hBsucc : Tendsto (fun n : ℕ => B (n + 1)) atTop
      (nhds (1 - (2 : ℂ) ^ (-s))) :=
    hB.comp (by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat 1)
  have hratio :
      Tendsto (fun n : ℕ => B (n + 1) / B n)
        atTop (nhds 1) := by
    have h := hBsucc.div hB hlim_ne
    have hvalue :
        (1 - (2 : ℂ) ^ (-s)) /
            (1 - (2 : ℂ) ^ (-s)) = 1 :=
      div_self hlim_ne
    rw [hvalue] at h
    change Tendsto ((fun n : ℕ => B (n + 1)) / B)
      atTop (nhds 1)
    exact h
  have hscaled :=
    (tendsto_const_nhds.mul hratio :
      Tendsto
        (fun n : ℕ =>
          (2 : ℂ) ^ (-s) * (B (n + 1) / B n))
        atTop (nhds ((2 : ℂ) ^ (-s) * 1)))
  rw [mul_one] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [hB.eventually_ne hlim_ne] with n hn
  have hpow :
      (2 : ℂ) ^ (((n + 1 : ℕ) : ℂ) * s) =
        (2 : ℂ) ^ ((n : ℂ) * s) * (2 : ℂ) ^ s := by
    rw [← Complex.cpow_add _ _ (by norm_num)]
    congr 2
    push_cast
    ring
  have hpow_ne :
      (2 : ℂ) ^ ((n : ℂ) * s) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    simp
  have htwo_s_ne : (2 : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    simp
  dsimp only [shellAdjacentTransfer, B] at hn ⊢
  rw [hpow]
  field_simp
  rw [Complex.cpow_neg, inv_mul_cancel₀ htwo_s_ne]
  rw [one_mul]

/-- Source-normalized asymptotic character of the adjacent-shell
renormalization flow. -/
def shellTransferCharacter (s : ℂ) : ℂ :=
  (2 : ℂ) ^ ((1 / 2 : ℂ) - s)

/-- The Riemann shell character is the least-atom modular character
with atom scale two and marked source coordinate one. -/
theorem shellTransferCharacter_eq_leastAtomTransferCharacter
    (s : ℂ) :
    shellTransferCharacter s =
      HTGeometry.leastAtomTransferCharacter 2 1 s := by
  simp [shellTransferCharacter,
    HTGeometry.leastAtomTransferCharacter]

/-- Adjacent-shell transport normalized by the asymptotic square-root
source-mass ratio. -/
def normalizedShellAdjacentTransfer (n : ℕ) (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (1 / 2 : ℂ) * shellAdjacentTransfer n s

/-- The complex principal half-power of two is the positive real
square root used by source-mass normalization. -/
theorem two_cpow_half_eq_sqrt :
    (2 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
  have hexp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    norm_num
  rw [hexp]
  apply Complex.ext
  · rw [Complex.cpow_ofReal_re]
    simp [Complex.ofNat_arg, Real.sqrt_eq_rpow]
  · rw [Complex.cpow_ofReal_im]
    simp [Complex.ofNat_arg]

/-- **Hypertranscendental shell-transfer law.**  The normalized
adjacent-shell transport converges to `2^(1/2-s)`. -/
theorem tendsto_normalizedShellAdjacentTransfer
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => normalizedShellAdjacentTransfer n s)
      atTop (nhds (shellTransferCharacter s)) := by
  have h :=
    (tendsto_shellAdjacentTransfer hs).const_mul
      ((2 : ℂ) ^ (1 / 2 : ℂ))
  change Tendsto
    (fun n : ℕ =>
      (2 : ℂ) ^ (1 / 2 : ℂ) *
        shellAdjacentTransfer n s)
    atTop (nhds (shellTransferCharacter s))
  rw [shellTransferCharacter,
    show (1 / 2 : ℂ) - s = (1 / 2 : ℂ) + (-s) by ring,
    Complex.cpow_add _ _ (by norm_num)]
  exact h

/-- Horizontal position is exactly the modulus of the shell-transfer
character. -/
theorem norm_shellTransferCharacter (s : ℂ) :
    ‖shellTransferCharacter s‖ =
      (2 : ℝ) ^ (1 / 2 - s.re) := by
  rw [shellTransferCharacter,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num),
    Complex.sub_re]
  norm_num

/-- The logarithmic shell-transfer modulus is the signed transverse
displacement times the least-atom clock `log 2`. -/
theorem log_norm_shellTransferCharacter (s : ℂ) :
    Real.log ‖shellTransferCharacter s‖ =
      (1 / 2 - s.re) * Real.log 2 := by
  rw [norm_shellTransferCharacter,
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)]

/-- The critical line is exactly the unitary locus of the normalized
shell-transfer character. -/
theorem norm_shellTransferCharacter_eq_one_iff (s : ℂ) :
    ‖shellTransferCharacter s‖ = 1 ↔
      s.re = 1 / 2 := by
  rw [norm_shellTransferCharacter s,
    ← Real.rpow_zero 2,
    Real.rpow_right_inj (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Right-of-line points are exactly the strictly contractive shell
characters. -/
theorem norm_shellTransferCharacter_lt_one_iff (s : ℂ) :
    ‖shellTransferCharacter s‖ < 1 ↔
      1 / 2 < s.re := by
  rw [norm_shellTransferCharacter s,
    Real.rpow_lt_one_iff_of_pos (by norm_num)]
  norm_num

/-- Left-of-line points are exactly the strictly expansive shell
characters. -/
theorem one_lt_norm_shellTransferCharacter_iff (s : ℂ) :
    1 < ‖shellTransferCharacter s‖ ↔
      s.re < 1 / 2 := by
  rw [norm_shellTransferCharacter s,
    Real.one_lt_rpow_iff_of_pos (by norm_num)]
  norm_num

/-- Functional-equation reflection pairs shell characters
reciprocally.  Reflection therefore gives an indefinite unit-determinant
pair even away from the critical line. -/
theorem shellTransferCharacter_reflection_pair (s : ℂ) :
    shellTransferCharacter s *
        star (shellTransferCharacter (1 - star s)) = 1 := by
  have harg : (2 : ℂ).arg ≠ Real.pi := by
    rw [Complex.ofNat_arg]
    exact Real.pi_ne_zero.symm
  have hstar (z : ℂ) :
      star ((2 : ℂ) ^ z) =
        (2 : ℂ) ^ (star z) := by
    rw [Complex.star_def]
    symm
    simpa only [map_ofNat] using
      Complex.cpow_conj (2 : ℂ) z harg
  rw [shellTransferCharacter,
    shellTransferCharacter, hstar,
    ← Complex.cpow_add _ _ (by norm_num)]
  convert Complex.cpow_zero 2 using 2
  simp
  ring

/-! ## Two-clock characteristic energy -/

/-- Positive source mass carried by the `n`th shell at the marked source
point `s = 1`. -/
def shellSourceMass (n : ℕ) : ℝ :=
  (shellMultiplier n 1).re

/-- Prime-two normalization of the source mass. -/
def scaledShellSourceMass (n : ℕ) : ℝ :=
  ((2 : ℂ) ^ ((n : ℂ) * (1 : ℂ)) * shellMultiplier n 1).re

/-- The Wold-depth normalization of a shell conormal, followed by
Poisson evolution for residual source time `u`. -/
def twoClockCharacteristicEnergy
    (rho : ℂ) (u : ℝ) (n : ℕ) : ℝ :=
  ‖(2 : ℂ) ^ ((n : ℂ) * rho) * shellMultiplier n rho‖ ^ 2 /
      scaledShellSourceMass n *
    Real.exp (HTGeometry.sourceCayleyTransverseRate 1 rho * u)

/-- Unrenormalized joint Wold--Poisson energy at independent shell depth
`n` and source time `tau`. -/
def twoClockSourceShellEnergy
    (rho : ℂ) (tau : ℝ) (n : ℕ) : ℝ :=
  ‖shellMultiplier n rho‖ ^ 2 / shellSourceMass n *
    Real.exp (HTGeometry.sourceCayleyTransverseRate 1 rho * tau)

/-- The source mass is strictly positive on every genuine high-exponent
shell. -/
theorem shellSourceMass_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < shellSourceMass n := by
  obtain ⟨r, hr, hvalue⟩ := shellMultiplier_one_eq_ofReal_pos hn
  rw [shellSourceMass, hvalue]
  simpa using hr

/-- Prime-two scaling of the marked source mass is literal real
multiplication by `2ⁿ`. -/
theorem scaledShellSourceMass_eq (n : ℕ) :
    scaledShellSourceMass n = (2 : ℝ) ^ n * shellSourceMass n := by
  have hparts :
      ((2 : ℂ) ^ n).re = (2 : ℝ) ^ n ∧
        ((2 : ℂ) ^ n).im = 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ]
        simp [Complex.mul_re, Complex.mul_im, ih.1, ih.2]
  rw [scaledShellSourceMass, mul_one, Complex.cpow_natCast,
    Complex.mul_re, hparts.1, hparts.2, zero_mul, sub_zero,
    shellSourceMass]

/-- Exact norm of the prime-two shell normalization. -/
theorem norm_two_cpow_nat_mul_shellMultiplier_sq
    (n : ℕ) (rho : ℂ) :
    ‖(2 : ℂ) ^ ((n : ℂ) * rho) * shellMultiplier n rho‖ ^ 2 =
      Real.exp (2 * (n : ℝ) * rho.re * Real.log 2) *
        ‖shellMultiplier n rho‖ ^ 2 := by
  have hnorm :
      ‖(2 : ℂ) ^ ((n : ℂ) * rho)‖ =
        Real.exp ((n : ℝ) * rho.re * Real.log 2) := by
    have hbase : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos
      (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    congr 1
    ring
  rw [norm_mul, hnorm]
  rw [mul_pow]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The characteristic energy is exactly the independent two-clock
energy restricted to the co-moving ray `tau = n log 2 + u`. -/
theorem twoClockSourceShellEnergy_characteristic
    {n : ℕ} (hn : 2 ≤ n) (rho : ℂ) (u : ℝ) :
    twoClockSourceShellEnergy rho ((n : ℝ) * Real.log 2 + u) n =
      twoClockCharacteristicEnergy rho u n := by
  rw [twoClockSourceShellEnergy, twoClockCharacteristicEnergy,
    scaledShellSourceMass_eq,
    norm_two_cpow_nat_mul_shellMultiplier_sq]
  have hmass : shellSourceMass n ≠ 0 :=
    ne_of_gt (shellSourceMass_pos hn)
  have htwo : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have htwoexp :
      (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ n = Real.exp (Real.log 2) ^ n := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((n : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul]
  rw [htwoexp]
  have hrate :
      HTGeometry.sourceCayleyTransverseRate 1 rho =
        2 * rho.re - 1 := by
    rw [HTGeometry.sourceCayleyTransverseRate]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  rw [hrate, mul_add, Real.exp_add]
  have hexp :
      Real.exp ((2 * rho.re - 1) * ((n : ℝ) * Real.log 2)) *
          Real.exp ((n : ℝ) * Real.log 2) =
        Real.exp (2 * rho.re * (n : ℝ) * Real.log 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  field_simp [hmass, Real.exp_ne_zero]
  rw [← hexp]
  ring

/-- The normalized positive source masses converge to `1/2`. -/
theorem tendsto_scaledShellSourceMass :
    Tendsto scaledShellSourceMass atTop (nhds (1 / 2)) := by
  have h := tendsto_two_cpow_nat_mul_shellMultiplier
    (s := (1 : ℂ)) (by norm_num)
  have hre :=
    (Complex.continuous_re.tendsto
      (1 - (2 : ℂ) ^ (-(1 : ℂ)))).comp h
  have hpow : (2 : ℂ) ^ (-(1 : ℂ)) = 1 / 2 := by
    rw [Complex.cpow_neg]
    norm_num
  rw [hpow] at hre
  norm_num at hre
  have hfun :
      scaledShellSourceMass =
        fun n : ℕ => ((2 : ℂ) ^ n * shellMultiplier n 1).re := by
    funext n
    simp [scaledShellSourceMass, Complex.cpow_natCast]
  rw [hfun]
  exact hre

/-- The source-mass ratio of adjacent positive shells converges to two. -/
theorem tendsto_shellSourceMass_div_succ :
    Tendsto
      (fun n : ℕ =>
        shellSourceMass n / shellSourceMass (n + 1))
      atTop (nhds 2) := by
  have hmass := tendsto_scaledShellSourceMass
  have hmassSucc :
      Tendsto (fun n : ℕ => scaledShellSourceMass (n + 1))
        atTop (nhds (1 / 2)) :=
    hmass.comp (by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat 1)
  have hratio0 := hmass.div hmassSucc (by norm_num)
  have hratio :
      Tendsto
        (fun n : ℕ =>
          scaledShellSourceMass n /
            scaledShellSourceMass (n + 1))
        atTop (nhds 1) := by
    have hvalue : (1 / 2 : ℝ) / (1 / 2) = 1 := by norm_num
    rw [hvalue] at hratio0
    change Tendsto
      (scaledShellSourceMass /
        fun n : ℕ => scaledShellSourceMass (n + 1))
      atTop (nhds 1)
    exact hratio0
  have htwice :=
    (hratio.const_mul 2 :
      Tendsto
        (fun n : ℕ =>
          2 * (scaledShellSourceMass n /
            scaledShellSourceMass (n + 1)))
        atTop (nhds (2 * 1)))
  rw [mul_one] at htwice
  refine htwice.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hmassn : shellSourceMass n ≠ 0 :=
    ne_of_gt (shellSourceMass_pos hn)
  have hmassSuccn : shellSourceMass (n + 1) ≠ 0 :=
    ne_of_gt (shellSourceMass_pos (by omega))
  have hpow : (2 : ℝ) ^ n ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  rw [scaledShellSourceMass_eq,
    scaledShellSourceMass_eq, pow_succ]
  field_simp

/-- Actual adjacent-shell transport normalized by the square root of
the source-mass ratio. -/
def sourceNormalizedShellAdjacentTransfer
    (n : ℕ) (s : ℂ) : ℂ :=
  (Real.sqrt
      (shellSourceMass n / shellSourceMass (n + 1)) : ℂ) *
    shellAdjacentTransfer n s

/-- **Source-normalized shell-transfer law.**  Literal source-mass
normalization has the same limiting character `2^(1/2-s)`. -/
theorem tendsto_sourceNormalizedShellAdjacentTransfer
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => sourceNormalizedShellAdjacentTransfer n s)
      atTop (nhds (shellTransferCharacter s)) := by
  have hsqrt :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt
            (shellSourceMass n / shellSourceMass (n + 1)))
        atTop (nhds (Real.sqrt 2)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp
      tendsto_shellSourceMass_div_succ
  have hcast :
      Tendsto
        (fun n : ℕ =>
          (Real.sqrt
            (shellSourceMass n / shellSourceMass (n + 1)) : ℂ))
        atTop (nhds (Real.sqrt 2 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hsqrt
  have hproduct :=
    hcast.mul (tendsto_shellAdjacentTransfer hs)
  change Tendsto
    (fun n : ℕ =>
      (Real.sqrt
        (shellSourceMass n / shellSourceMass (n + 1)) : ℂ) *
        shellAdjacentTransfer n s)
    atTop (nhds (shellTransferCharacter s))
  convert hproduct using 1
  rw [shellTransferCharacter,
    show (1 / 2 : ℂ) - s = (1 / 2 : ℂ) + (-s) by ring,
    Complex.cpow_add _ _ (by norm_num),
    two_cpow_half_eq_sqrt]

/-- **Two-clock characteristic conservation.**  Along the co-moving
source ray, Wold shell depth and Poisson time cancel their opposite
transverse rates.  Every point of the open right half-plane, not merely
points on the neutral horizon, has a finite nonzero characteristic
profile whenever its least-atom amplitude is nonzero. -/
theorem tendsto_twoClockCharacteristicEnergy
    {rho : ℂ} (hrho : 0 < rho.re) (u : ℝ) :
    Tendsto
      (twoClockCharacteristicEnergy rho u)
      atTop
      (nhds
        (2 * ‖1 - (2 : ℂ) ^ (-rho)‖ ^ 2 *
          Real.exp
            (HTGeometry.sourceCayleyTransverseRate 1 rho * u))) := by
  have hshell :=
    tendsto_two_cpow_nat_mul_shellMultiplier (s := rho) hrho
  have hnormsq :
      Tendsto
        (fun n : ℕ =>
          ‖(2 : ℂ) ^ ((n : ℂ) * rho) *
            shellMultiplier n rho‖ ^ 2)
        atTop
        (nhds (‖1 - (2 : ℂ) ^ (-rho)‖ ^ 2)) :=
    hshell.norm.pow 2
  have hmass := tendsto_scaledShellSourceMass
  have hdiv := hnormsq.div hmass (by norm_num)
  have hmul :
      Tendsto
        (twoClockCharacteristicEnergy rho u)
        atTop
        (nhds
          ((‖1 - (2 : ℂ) ^ (-rho)‖ ^ 2 / (1 / 2)) *
            Real.exp
              (HTGeometry.sourceCayleyTransverseRate 1 rho * u))) := by
    change Tendsto
      (fun n : ℕ =>
        ‖(2 : ℂ) ^ ((n : ℂ) * rho) *
            shellMultiplier n rho‖ ^ 2 /
          scaledShellSourceMass n *
            Real.exp
              (HTGeometry.sourceCayleyTransverseRate 1 rho * u))
      atTop _
    simpa only [Pi.div_apply] using
      hdiv.mul_const
        (Real.exp
          (HTGeometry.sourceCayleyTransverseRate 1 rho * u))
  convert hmul using 1
  norm_num
  ring

/-- **Source--shell traveling-wave law.**  The original independent
two-clock energy has a finite characteristic limit on
`tau = n log 2 + u`.  The limit retains the residual transverse
coordinate `u` but is finite for every `Re rho > 0`. -/
theorem tendsto_twoClockSourceShellEnergy_characteristic
    {rho : ℂ} (hrho : 0 < rho.re) (u : ℝ) :
    Tendsto
      (fun n : ℕ =>
        twoClockSourceShellEnergy rho
          ((n : ℝ) * Real.log 2 + u) n)
      atTop
      (nhds
        (2 * ‖1 - (2 : ℂ) ^ (-rho)‖ ^ 2 *
          Real.exp
            (HTGeometry.sourceCayleyTransverseRate 1 rho * u))) := by
  refine (tendsto_twoClockCharacteristicEnergy hrho u).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (twoClockSourceShellEnergy_characteristic hn rho u).symm

/-- Joint two-clock energy with an arbitrary residue amplitude. -/
def twoClockResidueEnergy
    (m rho : ℂ) (tau : ℝ) (n : ℕ) : ℝ :=
  ‖m‖ ^ 2 * twoClockSourceShellEnergy rho tau n

/-- Traveling-wave law with the full residue multiplicity/amplitude. -/
theorem tendsto_twoClockResidueEnergy_characteristic
    (m : ℂ) {rho : ℂ} (hrho : 0 < rho.re) (u : ℝ) :
    Tendsto
      (fun n : ℕ =>
        twoClockResidueEnergy m rho
          ((n : ℝ) * Real.log 2 + u) n)
      atTop
      (nhds
        (2 * ‖m‖ ^ 2 * ‖1 - (2 : ℂ) ^ (-rho)‖ ^ 2 *
          Real.exp
            (HTGeometry.sourceCayleyTransverseRate 1 rho * u))) := by
  have hbase :=
    (tendsto_twoClockSourceShellEnergy_characteristic hrho u).const_mul
      (‖m‖ ^ 2)
  have h :
      Tendsto
        (fun n : ℕ =>
          twoClockResidueEnergy m rho
            ((n : ℝ) * Real.log 2 + u) n)
        atTop
        (nhds
          (‖m‖ ^ 2 *
            (2 * ‖1 - (2 : ℂ) ^ (-rho)‖ ^ 2 *
              Real.exp
                (HTGeometry.sourceCayleyTransverseRate 1 rho * u)))) := by
    change Tendsto
      (fun n : ℕ =>
        ‖m‖ ^ 2 *
          twoClockSourceShellEnergy rho
            ((n : ℝ) * Real.log 2 + u) n)
      atTop _
    exact hbase
  convert h using 1
  ring

/-! ## Exact Poisson-order realization -/

/-- The algebraic Poisson order weights have total mass one. -/
theorem tsum_poissonOrderWeight (lam : ℝ) :
    ∑' r : ℕ, HTGeometry.poissonOrderWeight lam r = 1 := by
  have hexp : ∑' r : ℕ, lam ^ r / r.factorial = Real.exp lam := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp_rw [HTGeometry.poissonOrderWeight, mul_div_assoc]
  rw [tsum_mul_left, hexp, ← Real.exp_add]
  simp

/-- Factorially normalized derivative-order energy of the shell-labelled
transported residue. -/
def twoClockPoissonOrderEnergy
    (m rho : ℂ) (tau : ℝ) (n r : ℕ) : ℝ :=
  let x := HTGeometry.sourceCayleyObservationTime 1 rho tau
  (1 / shellSourceMass n) *
    (x ^ r / r.factorial *
      ‖iteratedDeriv r
        (HTGeometry.cayleyPoleResidueMode
          (m * shellMultiplier n rho) 1 rho)
        (x : ℂ)‖ ^ 2)

/-- Total derivative-order energy before the shell/time coordinates are
identified. -/
def twoClockPoissonTotalEnergy
    (m rho : ℂ) (tau : ℝ) (n : ℕ) : ℝ :=
  ∑' r : ℕ, twoClockPoissonOrderEnergy m rho tau n r

/-- The complete Poisson-order sum is exactly the closed two-clock
residue energy. -/
theorem twoClockPoissonTotalEnergy_eq
    (m : ℂ) {rho : ℂ} (hrho : rho ≠ 1) (tau : ℝ) (n : ℕ) :
    twoClockPoissonTotalEnergy m rho tau n =
      twoClockResidueEnergy m rho tau n := by
  let C : ℝ :=
    (1 / shellSourceMass n) *
      (‖m * shellMultiplier n rho‖ ^ 2 *
        Real.exp
          (HTGeometry.sourceCayleyTransverseRate 1 rho * tau))
  have hterm : ∀ r : ℕ,
      twoClockPoissonOrderEnergy m rho tau n r =
        C * HTGeometry.poissonOrderWeight tau r := by
    intro r
    rw [twoClockPoissonOrderEnergy]
    rw [HTGeometry.sourceCayleyResidueMode_horizon_conservation
      (m * shellMultiplier n rho) 1 rho tau r hrho]
    dsimp only [C]
    ring
  rw [twoClockPoissonTotalEnergy, tsum_congr hterm, tsum_mul_left,
    tsum_poissonOrderWeight, mul_one]
  dsimp only [C]
  rw [twoClockResidueEnergy, twoClockSourceShellEnergy, norm_mul]
  ring

/-- The literal derivative-order energy therefore obeys the same
traveling-wave law. -/
theorem tendsto_twoClockPoissonTotalEnergy_characteristic
    (m : ℂ) {rho : ℂ} (hrho0 : 0 < rho.re) (hrho1 : rho ≠ 1)
    (u : ℝ) :
    Tendsto
      (fun n : ℕ =>
        twoClockPoissonTotalEnergy m rho
          ((n : ℝ) * Real.log 2 + u) n)
      atTop
      (nhds
        (2 * ‖m‖ ^ 2 * ‖1 - (2 : ℂ) ^ (-rho)‖ ^ 2 *
          Real.exp
            (HTGeometry.sourceCayleyTransverseRate 1 rho * u))) := by
  refine (tendsto_twoClockResidueEnergy_characteristic
    m hrho0 u).congr' ?_
  filter_upwards [] with n
  exact (twoClockPoissonTotalEnergy_eq m hrho1
    ((n : ℝ) * Real.log 2 + u) n).symm

/-- Literal Xi multiplicity specialization of the total two-clock
Poisson energy. -/
def xiTwoClockPoissonTotalEnergy
    (rho : ℂ) (tau : ℝ) (n : ℕ) : ℝ :=
  twoClockPoissonTotalEnergy
    (((analyticOrderAt xi rho).toNat : ℕ) : ℂ) rho tau n

/-- **Xi source--shell reciprocity.**  Every Xi divisor multiplicity
obeys the exact two-clock traveling-wave law. -/
theorem tendsto_xiTwoClockPoissonTotalEnergy_characteristic
    {rho : ℂ} (hrho0 : 0 < rho.re) (hrho1 : rho ≠ 1)
    (u : ℝ) :
    Tendsto
      (fun n : ℕ =>
        xiTwoClockPoissonTotalEnergy rho
          ((n : ℝ) * Real.log 2 + u) n)
      atTop
      (nhds
        (2 * ((analyticOrderAt xi rho).toNat : ℝ) ^ 2 *
          ‖1 - (2 : ℂ) ^ (-rho)‖ ^ 2 *
          Real.exp
            (HTGeometry.sourceCayleyTransverseRate 1 rho * u))) := by
  simpa [xiTwoClockPoissonTotalEnergy] using
    tendsto_twoClockPoissonTotalEnergy_characteristic
      (((analyticOrderAt xi rho).toNat : ℕ) : ℂ)
      hrho0 hrho1 u

/-- Every nonzero residue has a strictly positive characteristic
profile, including residues away from the neutral horizon. -/
theorem twoClockCharacteristicLimit_pos
    {m rho : ℂ} (hm : m ≠ 0) (hrho : 0 < rho.re) (u : ℝ) :
    0 <
      2 * ‖m‖ ^ 2 * ‖1 - (2 : ℂ) ^ (-rho)‖ ^ 2 *
        Real.exp
          (HTGeometry.sourceCayleyTransverseRate 1 rho * u) := by
  have hmnorm : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hatom : 0 < ‖1 - (2 : ℂ) ^ (-rho)‖ :=
    norm_pos_iff.mpr (one_sub_two_cpow_neg_ne_zero hrho)
  positivity

/-! ## Universal rank-two clock law -/

/-- Universal character carried by two conjugate nonnegative clocks. -/
def conjugateTwoClockCharacter (nu tau depth : ℝ) : ℝ :=
  Real.exp (nu * (tau - depth))

/-- Uniform boundedness on the full independent nonnegative quadrant. -/
def ConjugateTwoClockQuadrantBounded (nu : ℝ) : Prop :=
  ∃ C : ℝ, ∀ tau depth : ℝ,
    0 ≤ tau → 0 ≤ depth →
      conjugateTwoClockCharacter nu tau depth ≤ C

/-- Every conjugate character becomes conservative on every
characteristic line `tau = depth + u`. -/
theorem conjugateTwoClockCharacter_characteristic
    (nu depth u : ℝ) :
    conjugateTwoClockCharacter nu (depth + u) depth =
      Real.exp (nu * u) := by
  rw [conjugateTwoClockCharacter]
  congr 1
  ring

/-- **Rank-two detection law.**  A conjugate two-clock character is
uniformly bounded on the independent nonnegative quadrant exactly when
its transverse rate vanishes.  Restriction to a characteristic line
therefore destroys precisely the information detected by the full
quadrant. -/
theorem conjugateTwoClockQuadrantBounded_iff
    (nu : ℝ) :
    ConjugateTwoClockQuadrantBounded nu ↔ nu = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hnu
    rcases lt_or_gt_of_ne hnu with hneg | hpos
    · have hgrow :
          Tendsto
            (fun depth : ℝ =>
              conjugateTwoClockCharacter nu 0 depth)
            atTop atTop := by
        have hlinear :
            Tendsto (fun depth : ℝ => (-nu) * depth)
              atTop atTop :=
          tendsto_id.const_mul_atTop (by linarith)
        have hexp := Real.tendsto_exp_atTop.comp hlinear
        have hfun :
            (fun depth : ℝ =>
              conjugateTwoClockCharacter nu 0 depth) =
              fun depth : ℝ => Real.exp ((-nu) * depth) := by
          funext depth
          rw [conjugateTwoClockCharacter]
          apply congrArg Real.exp
          ring
        rw [hfun]
        change Tendsto
          (Real.exp ∘ fun depth : ℝ => (-nu) * depth)
          atTop atTop
        exact hexp
      obtain ⟨D, hD⟩ :=
        eventually_atTop.1 (hgrow.eventually_gt_atTop C)
      let depth := max D 0
      have hlarge := hD depth (le_max_left D 0)
      have hbound := hC 0 depth (le_refl 0) (le_max_right D 0)
      exact (not_lt_of_ge hbound) hlarge
    · have hgrow :
          Tendsto
            (fun tau : ℝ =>
              conjugateTwoClockCharacter nu tau 0)
            atTop atTop := by
        have hlinear :
            Tendsto (fun tau : ℝ => nu * tau)
              atTop atTop :=
          tendsto_id.const_mul_atTop hpos
        have hexp := Real.tendsto_exp_atTop.comp hlinear
        have hfun :
            (fun tau : ℝ =>
              conjugateTwoClockCharacter nu tau 0) =
              fun tau : ℝ => Real.exp (nu * tau) := by
          funext tau
          rw [conjugateTwoClockCharacter]
          apply congrArg Real.exp
          ring
        rw [hfun]
        change Tendsto
          (Real.exp ∘ fun tau : ℝ => nu * tau)
          atTop atTop
        exact hexp
      obtain ⟨T, hT⟩ :=
        eventually_atTop.1 (hgrow.eventually_gt_atTop C)
      let tau := max T 0
      have hlarge := hT tau (le_max_left T 0)
      have hbound := hC tau 0 (le_max_right T 0) (le_refl 0)
      exact (not_lt_of_ge hbound) hlarge
  · rintro rfl
    refine ⟨1, fun tau depth htau hdepth => ?_⟩
    simp [conjugateTwoClockCharacter]

end

end RHTower
