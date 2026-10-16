import GaloisForLFunctions.RHTower.EvenSectorDetunedPackets

/-!
# Signed arithmetic forms from even pole-free tests

Rationally shifted reflection removes the extra arithmetic interactions without
restricting coefficient signs. The logarithmic cost of resolving the finite
packet allows the full primitive-set argument on the even pole-free cone.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section
namespace RHTower.EvenSector.Detuned
open ResonatorProfile WeilOneSided

def toeplitzConstant : ℝ := Real.log 6 + 9 / 2 + profileRatio / 2

private theorem packet_mass {N : ℕ} (hN : 1 ≤ N) {c : ℕ → ℝ}
    (hc : ∀ m, N < m → c m = 0) {g : ℝ → ℂ} {r k : ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgs : ∀ u, r < |u| → g u = 0)
    (hvan : ∀ y, width N ≤ |y| → EF.weilTest g g y = 0)
    (hk : EF.weilTest g g 0 = (k : ℂ)) :
    ∫ t : ℝ, ‖paperFT (packet N c g) t‖ ^ 2 =
      4 * Real.pi * k * ∑ m ∈ Finset.Icc 1 N, c m ^ 2 := by
  have h := integral_normSq_paperFT_mul_cos_eq (f := packet N c g)
    (contDiff_packet hg) (packet_tsupport hgs) 0
  simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
  have hz := weilTest_packet_log hN hg.continuous hgc hvan hc (n := 1) le_rfl
  simp only [Nat.cast_one, Real.log_one, one_mul, ← pow_two] at hz
  rw [h, hz, hk]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
    mul_zero, sub_zero]
  ring

/-- Arbitrary real coefficient signs are admitted by the detuned even packet. -/
theorem signed_toeplitz {lam : ℕ → ℝ} (hpf : WeilPositiveEvenPolar lam)
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (hc : ∀ m, N < m → c m = 0) :
    2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m ≤
      (4 * Real.log N + toeplitzConstant) * ∑ m ∈ Finset.Icc 1 N, c m ^ 2 := by
  let w := width N
  have hw : 0 < w := width_pos N
  have hw1 : w ≤ 1 := by
    unfold w width
    exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) (height N)]) (by positivity)
  have hwD : w * ((height N : ℝ) + 1) = 1 := by
    dsimp [w, width]
    field_simp
  let a := Real.log N + shift N + w / 4
  have ha : 0 ≤ a := by
    dsimp [a]
    linarith [Real.log_natCast_nonneg N, shift_pos N]
  let F := packet N c (gC w)
  let F' := packet N c (deriv (gC w))
  have hF2 : ContDiff ℝ 2 F := contDiff_packet (contDiff_gC w 2)
  have hF'2 : ContDiff ℝ 2 F' := contDiff_packet (contDiff_deriv_gC w 2)
  have hFcs : HasCompactSupport F := hasCompactSupport_packet (hasCompactSupport_gC hw)
  have hFs : tsupport F ⊆ Icc (-a) a := packet_tsupport fun u hu => gC_eq_zero hw hu
  have hF's : tsupport F' ⊆ Icc (-a) a := packet_tsupport fun u hu => deriv_gC_eq_zero hw hu
  have hFe : ∀ u, F (-u) = F u := packet_neg fun u => by
    change (gR w (-u) : ℂ) = (gR w u : ℂ)
    rw [gR_neg]
  obtain ⟨hg0, hg1⟩ := paperFT_gC_pole hw
  have hp0 : paperFT F (I / 2) = 0 := by
    rw [paperFT_packet (contDiff_gC w 0).continuous (hasCompactSupport_gC hw), hg0, mul_zero]
  have hp1 : paperFT F (-(I / 2)) = 0 := by
    rw [paperFT_packet (contDiff_gC w 0).continuous (hasCompactSupport_gC hw), hg1, mul_zero]
  have hpos := integral_weilAtomSymbol_nonneg_of_polar ha hF2 hFs hp0 hp1
    (hpf F hF2 hFcs hFe hp0)
  rw [integral_weilAtomSymbol_eq_arch_sub hF2 hFs lam] at hpos
  let k0 : ℝ := ∫ u, gR w u ^ 2
  let k1 : ℝ := ∫ u, gR' w u ^ 2
  have hk0 : EF.weilTest (gC w) (gC w) 0 = (k0 : ℂ) := weilTest_self_zero_ofReal
  have hk1 : EF.weilTest (deriv (gC w)) (deriv (gC w)) 0 = (k1 : ℂ) := by
    rw [deriv_gC]
    exact weilTest_self_zero_ofReal
  have hk0pos : 0 < k0 := lt_of_lt_of_le (div_pos integral_d2_sq_pos (by positivity))
    (integral_gR_sq_ge hw)
  have hvan0 : ∀ y, width N ≤ |y| → EF.weilTest (gC w) (gC w) y = 0 := fun y hy =>
    weilTest_self_eq_zero (fun u hu => gC_eq_zero hw hu) (by change w ≤ |y| at hy; linarith)
  have hvan1 : ∀ y, width N ≤ |y| → EF.weilTest (deriv (gC w)) (deriv (gC w)) y = 0 :=
    fun y hy => weilTest_self_eq_zero (fun u hu => deriv_gC_eq_zero hw hu)
      (by change w ≤ |y| at hy; linarith)
  let S : ℕ → ℝ := fun n => ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m
  have hsel : ∀ n : ℕ, 1 ≤ n →
      (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re = 4 * k0 * S n := by
    intro n hn
    rw [weilTest_packet_log hN (contDiff_gC w 0).continuous (hasCompactSupport_gC hw) hvan0 hc hn,
      weilTest_packet_neg_log hN (contDiff_gC w 0).continuous (hasCompactSupport_gC hw) hvan0 hc hn,
      hk0]
    norm_num [Complex.add_re, Complex.mul_re, S]
    ring
  have hS0 : ∀ n, N < n → S n = 0 := by
    intro n hn
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm1 := (Finset.mem_Icc.mp hm).1
    rw [hc (n * m) (by nlinarith), zero_mul]
  have hM : N ≤ ⌊Real.exp (2 * a)⌋₊ := by
    apply Nat.le_floor
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hle : Real.log N ≤ 2 * a := by
      dsimp [a]
      linarith [Real.log_natCast_nonneg N, shift_pos N]
    simpa only [Real.exp_log hNr] using Real.exp_le_exp.mpr hle
  have hatoms : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, lam n / Real.sqrt n *
      (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re =
      4 * k0 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * S n := by
    calc _ = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        4 * k0 * (lam n / Real.sqrt n * S n) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hsel n (by have := (Finset.mem_Icc.mp hn).1; omega)]
          ring
      _ = ∑ n ∈ Finset.Icc 2 N, 4 * k0 * (lam n / Real.sqrt n * S n) := by
          refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hM) fun n hn hnot => ?_).symm
          have hnN : N < n := by
            have hn2 := (Finset.mem_Icc.mp hn).1
            have : ¬(2 ≤ n ∧ n ≤ N) := by simpa only [Finset.mem_Icc] using hnot
            omega
          rw [hS0 n hnN]
          ring
      _ = _ := by rw [Finset.mul_sum]
  let sumc : ℝ := ∑ m ∈ Finset.Icc 1 N, c m ^ 2
  have hsum : 0 ≤ sumc := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmass0 : ∫ t : ℝ, ‖paperFT F t‖ ^ 2 = 4 * Real.pi * k0 * sumc :=
    packet_mass hN hc (contDiff_gC w 2) (hasCompactSupport_gC hw)
      (fun u hu => gC_eq_zero hw hu) hvan0 hk0
  have hmass1 : ∫ t : ℝ, ‖paperFT F' t‖ ^ 2 = 4 * Real.pi * k1 * sumc :=
    packet_mass hN hc (contDiff_deriv_gC w 2) (hasCompactSupport_deriv_gC hw)
      (fun u hu => deriv_gC_eq_zero hw hu) hvan1 hk1
  have hderiv : ∀ t : ℝ, ‖paperFT F' t‖ ^ 2 = t ^ 2 * ‖paperFT F t‖ ^ 2 := by
    intro t
    change ‖paperFT (packet N c (deriv (gC w))) t‖ ^ 2 = _
    rw [← deriv_packet ((contDiff_gC w 1).differentiable (by norm_num)),
      paperFT_deriv (contDiff_packet (contDiff_gC w 1)) hFcs]
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_pow, sq_abs]
  let A : ℝ := Real.log ((height N : ℝ) + 1) + 9 / 2
  let B : ℝ := w ^ 2 / 2
  have hpt : ∀ t : ℝ,
      ‖paperFT F t‖ ^ 2 * archimedeanWeilSymbol (t / (2 * Real.pi)) ≤
        A * ‖paperFT F t‖ ^ 2 + B * ‖paperFT F' t‖ ^ 2 := by
    intro t
    have hA := archimedeanWeilSymbol_le_log_add t
    have hle : 1 + |t| ≤ ((height N : ℝ) + 1) * (1 + w * |t|) := by
      have heq : ((height N : ℝ) + 1) * (1 + w * |t|) = (height N : ℝ) + 1 + |t| := by
        rw [mul_add, mul_one, ← mul_assoc, mul_comm ((height N : ℝ) + 1) w, hwD, one_mul]
      rw [heq]
      linarith [Nat.cast_nonneg (α := ℝ) (height N)]
    have hlog : Real.log (1 + |t|) ≤ Real.log ((height N : ℝ) + 1) + w * |t| := by
      calc _ ≤ Real.log (((height N : ℝ) + 1) * (1 + w * |t|)) :=
          Real.log_le_log (by positivity) hle
        _ = Real.log ((height N : ℝ) + 1) + Real.log (1 + w * |t|) :=
          Real.log_mul (by positivity) (by positivity)
        _ ≤ _ := by
          have := Real.log_le_sub_one_of_pos (show 0 < 1 + w * |t| by positivity)
          linarith
    have hamgm : w * |t| ≤ 1 / 2 + w ^ 2 * t ^ 2 / 2 := by
      nlinarith [sq_nonneg (w * |t| - 1), sq_abs t]
    have hpol : archimedeanWeilSymbol (t / (2 * Real.pi)) ≤ A + B * t ^ 2 := by
      dsimp [A, B]
      linarith
    rw [hderiv t]
    nlinarith only [mul_le_mul_of_nonneg_left hpol (sq_nonneg ‖paperFT F t‖)]
  have hint1 := integrable_normSq_paperFT_mul_arch hF2 hFs
  have hint2 := integrable_normSq_paperFT hF2 hFs
  have hint3 := integrable_normSq_paperFT hF'2 hF's
  have harch : (∫ t : ℝ, ‖paperFT F t‖ ^ 2 * archimedeanWeilSymbol (t / (2 * Real.pi))) ≤
      A * (4 * Real.pi * k0 * sumc) + B * (4 * Real.pi * k1 * sumc) := by
    have h := integral_mono hint1 ((hint2.const_mul A).add (hint3.const_mul B)) hpt
    change (∫ t : ℝ, ‖paperFT F t‖ ^ 2 * archimedeanWeilSymbol (t / (2 * Real.pi))) ≤
      ∫ t : ℝ, A * ‖paperFT F t‖ ^ 2 + B * ‖paperFT F' t‖ ^ 2 at h
    rwa [integral_add (hint2.const_mul A) (hint3.const_mul B), integral_const_mul,
      integral_const_mul, hmass0, hmass1] at h
  have hratio : B * k1 ≤ profileRatio / 2 * k0 := by
    have h := sq_mul_integral_gR'_le hw hw1
    dsimp [B, k0, k1]
    nlinarith only [h]
  rw [hatoms] at hpos
  have hbudget : 2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * S n ≤
      (A + profileRatio / 2) * sumc := by
    have hscaled := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ 4 * Real.pi * sumc by positivity)
    have hmain : 4 * Real.pi * k0 * (2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * S n) ≤
        4 * Real.pi * k0 * ((A + profileRatio / 2) * sumc) := by
      nlinarith only [hpos, harch, hscaled]
    exact le_of_mul_le_mul_left hmain (by positivity)
  refine hbudget.trans (mul_le_mul_of_nonneg_right ?_ hsum)
  dsimp [A, toeplitzConstant]
  linarith [log_height_le hN]

end RHTower.EvenSector.Detuned
end
