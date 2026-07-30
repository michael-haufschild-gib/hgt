import GaloisForLFunctions.RHTower.CompletePositiveKolchinFreeRiemannResolution
import GaloisForLFunctions.RHTower.XiWoldPoissonBivariateConormal

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

end

end RHTower
