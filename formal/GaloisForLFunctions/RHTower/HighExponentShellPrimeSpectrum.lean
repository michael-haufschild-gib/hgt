import GaloisForLFunctions.RHTower.HighExponentShellLeastAtomAsymptotic
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock

/-!
# Prime-spectrum tomography of the positive high-exponent shell

After removing the leading prime-two atom from the positive shell
multiplier, the next asymptotic layer is the prime-three atom:

`3^(ns) (H_n(s) - 2^(-ns) (1 - 2^(-s))) → 1 - 3^(-s)`.

Its adjacent normalized transfer tends to `3^(1/2-s)`.  Together with
the leading character `2^(1/2-s)`, this gives a globally injective
two-prime spectrum: the common modulus slope recovers the real part,
and irrationality of `log 3 / log 2` makes the two phases recover the
imaginary part without aliasing.
-/

open Complex Filter Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

theorem dpoly2_moebiusCoeff_Icc_one_three (w : ℂ) :
    dpoly2 moebiusCoeff (Finset.Icc 1 3) w =
      1 - (2 : ℂ) ^ (-w) - (3 : ℂ) ^ (-w) := by
  have hIcc : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [dpoly2, hIcc]
  norm_num [moebiusCoeff, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime]
  ring

/-- Effective remainder estimate after the first two nontrivial
Möbius atoms have been extracted from reciprocal zeta. -/
theorem norm_three_cpow_mul_inv_riemannZeta_secondAtom_sub_negOne_le
    {w : ℂ} (hw : 1 < w.re) :
    ‖(3 : ℂ) ^ w *
        ((riemannZeta w)⁻¹ - 1 + (2 : ℂ) ^ (-w)) - (-1)‖
      ≤ 3 / (w.re - 1) := by
  have htail :=
    norm_inv_riemannZeta_sub_dpoly2_moebiusCoeff_le
      hw (M := 3) (by norm_num)
  rw [dpoly2_moebiusCoeff_Icc_one_three] at htail
  have hrewrite :
      (3 : ℂ) ^ w *
          ((riemannZeta w)⁻¹ - 1 + (2 : ℂ) ^ (-w)) - (-1) =
        (3 : ℂ) ^ w *
          ((riemannZeta w)⁻¹ -
            (1 - (2 : ℂ) ^ (-w) - (3 : ℂ) ^ (-w))) := by
    have h3 : (3 : ℂ) ^ w * (3 : ℂ) ^ (-w) = 1 := by
      rw [← Complex.cpow_add _ _ (by norm_num)]
      simp
    calc
      (3 : ℂ) ^ w *
          ((riemannZeta w)⁻¹ - 1 + (2 : ℂ) ^ (-w)) - (-1)
          =
        (3 : ℂ) ^ w *
          ((riemannZeta w)⁻¹ - 1 + (2 : ℂ) ^ (-w)) +
            (3 : ℂ) ^ w * (3 : ℂ) ^ (-w) := by rw [h3]; ring
      _ = _ := by ring
  rw [hrewrite, norm_mul]
  have hnorm : ‖(3 : ℂ) ^ w‖ = (3 : ℝ) ^ w.re := by
    exact Complex.norm_natCast_cpow_of_pos (by norm_num) w
  rw [hnorm]
  refine (mul_le_mul_of_nonneg_left htail
    (Real.rpow_nonneg (by norm_num) _)).trans ?_
  have hpow :
      (3 : ℝ) ^ w.re * (3 : ℝ) ^ (1 - w.re) = 3 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  calc
    (3 : ℝ) ^ w.re *
          (((3 : ℕ) : ℝ) ^ (1 - w.re) / (w.re - 1))
        = ((3 : ℝ) ^ w.re * (3 : ℝ) ^ (1 - w.re)) /
            (w.re - 1) := by norm_num; ring
    _ = 3 / (w.re - 1) := by rw [hpow]
    _ ≤ 3 / (w.re - 1) := le_rfl

/-- The second reciprocal-zeta atom is asymptotically exact on every
open right-half-plane ray. -/
theorem tendsto_three_cpow_nat_mul_inv_riemannZeta_secondAtom
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ =>
        (3 : ℂ) ^ ((n : ℂ) * s) *
          ((riemannZeta ((n : ℂ) * s))⁻¹ - 1 +
            (2 : ℂ) ^ (-((n : ℂ) * s))))
      atTop (nhds (-1)) := by
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
      (hre.eventually_gt_atTop (1 + 3 / ε))
  refine ⟨N, fun n hn => ?_⟩
  have hnlarge := hN n hn
  have hw : 1 < (((n : ℂ) * s).re) := by
    have hpos : 0 < 3 / ε := div_pos (by norm_num) hε
    linarith
  have hbound :=
    norm_three_cpow_mul_inv_riemannZeta_secondAtom_sub_negOne_le hw
  rw [dist_eq]
  refine hbound.trans_lt ?_
  have hden : 3 / ε < (((n : ℂ) * s).re) - 1 := by
    linarith
  have hdenpos : 0 < (((n : ℂ) * s).re) - 1 := by
    linarith
  apply (div_lt_iff₀ hdenpos).2
  have hscaled := (div_lt_iff₀ hε).mp hden
  nlinarith

/-- The positive shell after exact removal of its leading prime-two
asymptotic atom. -/
def shellSecondAtomResidual (n : ℕ) (s : ℂ) : ℂ :=
  shellMultiplier n s -
    (2 : ℂ) ^ (-((n : ℂ) * s)) *
      (1 - (2 : ℂ) ^ (-s))

/-- The prime-three atom is the exact second asymptotic layer of the
same positive shell multiplier. -/
theorem tendsto_three_cpow_nat_mul_shellSecondAtomResidual
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ =>
        (3 : ℂ) ^ ((n : ℂ) * s) *
          shellSecondAtomResidual n s)
      atTop (nhds (1 - (3 : ℂ) ^ (-s))) := by
  let B : ℕ → ℂ := fun n =>
    (3 : ℂ) ^ ((n : ℂ) * s) *
      ((riemannZeta ((n : ℂ) * s))⁻¹ - 1 +
        (2 : ℂ) ^ (-((n : ℂ) * s)))
  have hB : Tendsto B atTop (nhds (-1)) := by
    simpa [B] using
      tendsto_three_cpow_nat_mul_inv_riemannZeta_secondAtom hs
  have hsucc : Tendsto (fun n : ℕ => B (n + 1))
      atTop (nhds (-1)) := by
    exact hB.comp (by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat 1)
  have hlim := (hsucc.const_mul ((3 : ℂ) ^ (-s))).sub hB
  have htarget :
      (3 : ℂ) ^ (-s) * (-1) - (-1) =
        1 - (3 : ℂ) ^ (-s) := by ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [] with n
  have hpow3 :
      (3 : ℂ) ^ (-s) *
          (3 : ℂ) ^ (((n + 1 : ℕ) : ℂ) * s) =
        (3 : ℂ) ^ ((n : ℂ) * s) := by
    rw [← Complex.cpow_add _ _ (by norm_num)]
    congr 2
    push_cast
    ring
  have hpow2 :
      (2 : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) * s)) -
          (2 : ℂ) ^ (-((n : ℂ) * s)) =
        -(2 : ℂ) ^ (-((n : ℂ) * s)) *
          (1 - (2 : ℂ) ^ (-s)) := by
    have hfactor :
        (2 : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) * s)) =
          (2 : ℂ) ^ (-((n : ℂ) * s)) *
            (2 : ℂ) ^ (-s) := by
      rw [← Complex.cpow_add _ _ (by norm_num)]
      congr 2
      push_cast
      ring
    rw [hfactor]
    ring
  dsimp only [B, shellSecondAtomResidual]
  rw [shellMultiplier, ← mul_assoc, hpow3]
  push_cast
  have hpow2' :
      (2 : ℂ) ^ (-(((n : ℂ) + 1) * s)) -
          (2 : ℂ) ^ (-((n : ℂ) * s)) =
        -(2 : ℂ) ^ (-((n : ℂ) * s)) *
          (1 - (2 : ℂ) ^ (-s)) := by
    simpa using hpow2
  linear_combination (3 : ℂ) ^ ((n : ℂ) * s) * hpow2'

theorem one_sub_three_cpow_neg_ne_zero
    {rho : ℂ} (hrho : 0 < rho.re) :
    1 - (3 : ℂ) ^ (-rho) ≠ 0 := by
  have hbase : (3 : ℂ) = ((3 : ℝ) : ℂ) := by norm_num
  have hnorm :
      ‖(3 : ℂ) ^ (-rho)‖ < 1 := by
    rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos
      (by norm_num : (0 : ℝ) < 3)]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num) (by simp only [Complex.neg_re]; linarith)
  intro hzero
  have heq : (3 : ℂ) ^ (-rho) = 1 :=
    (sub_eq_zero.mp hzero).symm
  rw [heq, norm_one] at hnorm
  exact (lt_irrefl 1 hnorm)

/-- Adjacent-depth transfer in the residual second asymptotic layer. -/
def shellSecondAtomAdjacentTransfer (n : ℕ) (s : ℂ) : ℂ :=
  shellSecondAtomResidual (n + 1) s /
    shellSecondAtomResidual n s

/-- The residual adjacent transfer converges to the prime-three
character. -/
theorem tendsto_shellSecondAtomAdjacentTransfer
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => shellSecondAtomAdjacentTransfer n s)
      atTop (nhds ((3 : ℂ) ^ (-s))) := by
  let B : ℕ → ℂ := fun n =>
    (3 : ℂ) ^ ((n : ℂ) * s) *
      shellSecondAtomResidual n s
  have hB : Tendsto B atTop
      (nhds (1 - (3 : ℂ) ^ (-s))) := by
    simpa only [B] using
      tendsto_three_cpow_nat_mul_shellSecondAtomResidual hs
  have hlim_ne : 1 - (3 : ℂ) ^ (-s) ≠ 0 :=
    one_sub_three_cpow_neg_ne_zero hs
  have hBsucc : Tendsto (fun n : ℕ => B (n + 1)) atTop
      (nhds (1 - (3 : ℂ) ^ (-s))) :=
    hB.comp (by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat 1)
  have hratio :
      Tendsto (fun n : ℕ => B (n + 1) / B n)
        atTop (nhds 1) := by
    have hratio' := hBsucc.div hB hlim_ne
    change Tendsto ((fun n : ℕ => B (n + 1)) / B)
      atTop (nhds 1)
    simpa only [div_self hlim_ne] using hratio'
  have hrewrite :
      ∀ n : ℕ,
        B (n + 1) / B n =
          (3 : ℂ) ^ s * shellSecondAtomAdjacentTransfer n s := by
    intro n
    dsimp only [B, shellSecondAtomAdjacentTransfer]
    have hpow :
        (3 : ℂ) ^ ((((n + 1 : ℕ) : ℂ) * s)) =
          (3 : ℂ) ^ ((n : ℂ) * s) * (3 : ℂ) ^ s := by
      rw [← Complex.cpow_add _ _ (by norm_num)]
      congr 2
      push_cast
      ring
    rw [hpow]
    field_simp
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          (3 : ℂ) ^ s * shellSecondAtomAdjacentTransfer n s)
        atTop (nhds 1) := by
    exact hratio.congr' (Filter.Eventually.of_forall hrewrite)
  have := hscaled.const_mul ((3 : ℂ) ^ (-s))
  have hcancel :
      (3 : ℂ) ^ (-s) * (3 : ℂ) ^ s = 1 := by
    rw [← Complex.cpow_add _ _ (by norm_num)]
    simp
  simpa only [← mul_assoc, hcancel, one_mul, mul_one] using this

/-- Half-density-normalized prime-three transfer character. -/
def shellSecondAtomTransferCharacter (s : ℂ) : ℂ :=
  (3 : ℂ) ^ ((1 / 2 : ℂ) - s)

def normalizedShellSecondAtomAdjacentTransfer
    (n : ℕ) (s : ℂ) : ℂ :=
  (Real.sqrt 3 : ℂ) * shellSecondAtomAdjacentTransfer n s

theorem tendsto_normalizedShellSecondAtomAdjacentTransfer
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => normalizedShellSecondAtomAdjacentTransfer n s)
      atTop (nhds (shellSecondAtomTransferCharacter s)) := by
  have h := (tendsto_shellSecondAtomAdjacentTransfer hs).const_mul
    (Real.sqrt 3 : ℂ)
  have hsqrt :
      (Real.sqrt 3 : ℂ) = (3 : ℂ) ^ (1 / 2 : ℂ) := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    have hbase : (3 : ℂ) = ((3 : ℝ) : ℂ) := by norm_num
    rw [hhalf, hbase,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.sqrt_eq_rpow]
  have hprod :
      (Real.sqrt 3 : ℂ) * (3 : ℂ) ^ (-s) =
        shellSecondAtomTransferCharacter s := by
    rw [shellSecondAtomTransferCharacter, hsqrt,
      ← Complex.cpow_add _ _ (by norm_num)]
    congr 2
  simpa [normalizedShellSecondAtomAdjacentTransfer, hprod] using h

/-- Radial/phase decomposition of every least-atom transfer
character. -/
theorem leastAtomTransferCharacter_eq_radial_mul_phase
    {q : ℝ} (hq : 0 < q) (c : ℝ) (s : ℂ) :
    HTGeometry.leastAtomTransferCharacter q c s =
      Complex.exp
          ((((Real.log q) * (c / 2 - s.re) : ℝ) : ℂ)) *
        HTGeometry.phaseClockValue (Real.log q) (-s.im) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hlog :
      Complex.log (q : ℂ) = ((Real.log q : ℝ) : ℂ) := by
    exact (Complex.ofReal_log hq.le).symm
  rw [HTGeometry.leastAtomTransferCharacter,
    Complex.cpow_def_of_ne_zero hqC, hlog,
    HTGeometry.phaseClockValue]
  rw [← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp [Complex.mul_re, Complex.sub_re]
  · simp [Complex.mul_im, Complex.sub_im]

/-- The first two asymptotic atom characters of the same shell. -/
def twoPrimeShellTransferSpectrum (s : ℂ) : ℂ × ℂ :=
  (HTGeometry.leastAtomTransferCharacter 2 1 s,
    HTGeometry.leastAtomTransferCharacter 3 1 s)

/-- **Two-prime shell tomography.**  The first two cofinal atom
characters recover the entire complex spectral coordinate exactly. -/
theorem twoPrimeShellTransferSpectrum_injective :
    Function.Injective twoPrimeShellTransferSpectrum := by
  intro s t hst
  have h2 :
      HTGeometry.leastAtomTransferCharacter 2 1 s =
        HTGeometry.leastAtomTransferCharacter 2 1 t :=
    congrArg Prod.fst hst
  have h3 :
      HTGeometry.leastAtomTransferCharacter 3 1 s =
        HTGeometry.leastAtomTransferCharacter 3 1 t :=
    congrArg Prod.snd hst
  have hnorm := congrArg norm h2
  rw [HTGeometry.norm_leastAtomTransferCharacter
      (by norm_num : (0 : ℝ) < 2),
    HTGeometry.norm_leastAtomTransferCharacter
      (by norm_num : (0 : ℝ) < 2)] at hnorm
  have hreExponent : 1 / 2 - s.re = 1 / 2 - t.re :=
    (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)).mp hnorm
  have hre : s.re = t.re := by linarith
  have hphase2 :
      HTGeometry.phaseClockValue (Real.log 2) (-s.im) =
        HTGeometry.phaseClockValue (Real.log 2) (-t.im) := by
    rw [leastAtomTransferCharacter_eq_radial_mul_phase
        (by norm_num : (0 : ℝ) < 2) 1 s,
      leastAtomTransferCharacter_eq_radial_mul_phase
        (by norm_num : (0 : ℝ) < 2) 1 t] at h2
    rw [hre] at h2
    exact mul_left_cancel₀ (Complex.exp_ne_zero
      (((Real.log 2) * (1 / 2 - t.re) : ℝ) : ℂ)) h2
  have hphase3 :
      HTGeometry.phaseClockValue (Real.log 3) (-s.im) =
        HTGeometry.phaseClockValue (Real.log 3) (-t.im) := by
    rw [leastAtomTransferCharacter_eq_radial_mul_phase
        (by norm_num : (0 : ℝ) < 3) 1 s,
      leastAtomTransferCharacter_eq_radial_mul_phase
        (by norm_num : (0 : ℝ) < 3) 1 t] at h3
    rw [hre] at h3
    exact mul_left_cancel₀ (Complex.exp_ne_zero
      (((Real.log 3) * (1 / 2 - t.re) : ℝ) : ℂ)) h3
  have hpair :
      primeLogPhaseClockPair 2 3 (-s.im) =
        primeLogPhaseClockPair 2 3 (-t.im) := by
    exact Prod.ext hphase2 hphase3
  have himneg :=
    primeLogPhaseClockPair_two_three_injective hpair
  have him : s.im = t.im := by linarith
  exact Complex.ext hre him

theorem twoPrimeShellTransferSpectrum_eq_iff (s t : ℂ) :
    twoPrimeShellTransferSpectrum s =
        twoPrimeShellTransferSpectrum t ↔
      s = t := by
  constructor
  · intro h
    exact twoPrimeShellTransferSpectrum_injective h
  · rintro rfl
    rfl

end

end RHTower
