import GaloisForLFunctions.RHTower.XiRayComplexTiltedTransforms

/-!
# Complex-tilted separated-packet positive semidefiniteness of the Bezoutian matrices

Combining the off-ray logarithmic-derivative bounds with the log-ratio contraction of the
real-packet theory, the critical logarithmic-derivative kernel matrices — and hence the theta
tail first-moment Bezoutian matrices of the Riemann-hypothesis criterion — are positive
semidefinite at every finite node system whose real parts form a separated packet (base
`xiRayPacketBase`, consecutive ratio `xiRayPacketBase ^ 2`) and whose imaginary parts obey the
tilt budget `|Im W| ≤ 1/(32(log Re W + 3))`.  This is an arbitrary-rank unconditional stratum
of the criterion family at genuinely complex nodes.
-/

open Complex Real MeasureTheory Set
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Packet facts and constants -/

theorem xiRayPacketBase_ge' : (9216 : ℝ) ≤ xiRayPacketBase := by
  have hγ1 := one_le_xiRayEnvelopeRatio
  have hlogγ : 0 ≤ Real.log xiRayEnvelopeRatio := Real.log_nonneg hγ1
  have hlog8γ : 0 ≤ Real.log (8 * xiRayEnvelopeRatio) :=
    Real.log_nonneg (by nlinarith)
  have hπe4 : 0 < Real.pi * Real.exp 4 := mul_pos Real.pi_pos (Real.exp_pos _)
  have h36 : (36 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have h256 : (256 : ℝ) ≤ Real.exp (2 * Real.exp 1 + 8) := by
    have h8 : (8 : ℝ) ≤ 2 * Real.exp 1 + 8 := by nlinarith [Real.exp_pos 1]
    have hmono : Real.exp 8 ≤ Real.exp (2 * Real.exp 1 + 8) := Real.exp_le_exp.mpr h8
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have hpow : (2 : ℝ) ^ 8 ≤ (Real.exp 1) ^ 8 :=
      pow_le_pow_left₀ (by norm_num) h2e 8
    have hexp8 : (Real.exp 1) ^ 8 = Real.exp 8 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h2 : (256 : ℝ) = 2 ^ 8 := by norm_num
    linarith [hexp8 ▸ hpow]
  have hprod : (9216 : ℝ) ≤ (2 * Real.pi) ^ 2 * Real.exp (2 * Real.exp 1 + 8) := by
    have := mul_le_mul h36 h256 (by norm_num) (le_trans (by norm_num) h36)
    linarith
  have hupper : (0 : ℝ) ≤ xiRayUpperBase := by
    have h1 : xiRayUpperBase = Real.pi * Real.exp 4 + Real.log xiRayEnvelopeRatio + 12 := rfl
    linarith
  have hlower : (9216 : ℝ) ≤ xiRayLowerBase := by
    have h1 : xiRayLowerBase = (2 * Real.pi) ^ 2 * Real.exp (2 * Real.exp 1 + 8)
        + 4 * Real.log (8 * xiRayEnvelopeRatio) + 16 := rfl
    linarith
  have h1 : xiRayPacketBase = xiRayUpperBase + xiRayLowerBase := rfl
  linarith

private theorem packet_le' {W : ℕ → ℂ} (hbase : xiRayPacketBase ≤ (W 0).re)
    (hstep : ∀ m, xiRayPacketBase ^ 2 * (W m).re ≤ (W (m + 1)).re) :
    ∀ i : ℕ, xiRayPacketBase ≤ (W i).re := by
  have hR256 := xiRayPacketBase_ge
  have hR0 : (0 : ℝ) < xiRayPacketBase := by linarith
  intro i
  induction i with
  | zero => exact hbase
  | succ m ih =>
    have h1 := hstep m
    have hxm : 0 < (W m).re := lt_of_lt_of_le hR0 ih
    have hsq : xiRayPacketBase ≤ xiRayPacketBase ^ 2 := by nlinarith
    have h2 : xiRayPacketBase ≤ xiRayPacketBase ^ 2 * (W m).re := by nlinarith
    linarith

private theorem packet_gap' {W : ℕ → ℂ}
    (hstep : ∀ m, xiRayPacketBase ^ 2 * (W m).re ≤ (W (m + 1)).re) :
    ∀ i j : ℕ, i ≤ j → xiRayPacketBase ^ (2 * (j - i)) * (W i).re ≤ (W j).re := by
  intro i j hij
  induction j with
  | zero =>
    have h0 : i = 0 := Nat.le_zero.mp hij
    subst h0
    simp
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · have him : i ≤ m := by omega
      have h1 := ih him
      have h2 := hstep m
      have hcast : 2 * (m + 1 - i) = 2 * (m - i) + 2 := by omega
      rw [hcast, pow_add]
      have hpow0 : (0 : ℝ) ≤ xiRayPacketBase ^ 2 := sq_nonneg _
      calc xiRayPacketBase ^ (2 * (m - i)) * xiRayPacketBase ^ 2 * (W i).re
          = xiRayPacketBase ^ 2 * (xiRayPacketBase ^ (2 * (m - i)) * (W i).re) := by ring
        _ ≤ xiRayPacketBase ^ 2 * (W m).re := mul_le_mul_of_nonneg_left h1 hpow0
        _ ≤ (W (m + 1)).re := h2
    · have h0 : i = m + 1 := by omega
      subst h0
      simp

/-! ## Diagonal and off-diagonal kernel bounds at tilted nodes -/

private theorem criticalKernel_tilted_diag (W : ℂ) :
    criticalLogDerivKernel W W = (((logDeriv xiCent W).re / W.re : ℝ) : ℂ) := by
  unfold criticalLogDerivKernel
  rw [Complex.add_conj, Complex.add_conj, ← Complex.ofReal_div]
  exact congrArg _ (mul_div_mul_left _ _ two_ne_zero)

private theorem tilted_diag_lower {W : ℂ} (hb : xiRayPacketBase ≤ W.re)
    (ht : |W.im| ≤ xiRayTiltBudget W.re) :
    Real.log W.re / (16 * W.re) ≤ (logDeriv xiCent W).re / W.re := by
  have hR := xiRayPacketBase_ge
  have hre0 : (0 : ℝ) < W.re := by linarith
  have h1 := re_logDeriv_xiCent_tilted_ge hb ht
  rw [Complex.re_add_im W] at h1
  have h2 : Real.log W.re / 16 / W.re ≤ (logDeriv xiCent W).re / W.re :=
    div_le_div_of_nonneg_right h1 hre0.le
  have h3 : Real.log W.re / 16 / W.re = Real.log W.re / (16 * W.re) := by
    rw [div_div]
  linarith [h3 ▸ h2]

private theorem tilted_norm_le {W : ℂ} (hb : xiRayPacketBase ≤ W.re)
    (ht : |W.im| ≤ xiRayTiltBudget W.re) :
    ‖logDeriv xiCent W‖ ≤ 4 * Real.log W.re := by
  have h1 := norm_logDeriv_xiCent_tilted_le hb ht
  rwa [Complex.re_add_im W] at h1

/-! ## The tilted-packet positivity of the critical-kernel matrices -/

private theorem fin_erase_sum_eq {n : ℕ} (j : Fin n) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.univ.erase j, g (k : ℕ)
      = ∑ m ∈ (Finset.range n).erase (j : ℕ), g m := by
  have h1 : g (j : ℕ) + ∑ k ∈ Finset.univ.erase j, g (k : ℕ)
      = ∑ k : Fin n, g (k : ℕ) :=
    Finset.add_sum_erase Finset.univ (fun k : Fin n => g (k : ℕ)) (Finset.mem_univ j)
  have h2 : g (j : ℕ) + ∑ m ∈ (Finset.range n).erase (j : ℕ), g m
      = ∑ m ∈ Finset.range n, g m :=
    Finset.add_sum_erase _ _ (Finset.mem_range.mpr j.isLt)
  have h3 := Fin.sum_univ_eq_sum_range g n
  linarith

/-- **Tilted separated packets give positive semidefinite critical-kernel matrices.**
An arbitrary-rank unconditional stratum of the RH-critical kernel family at genuinely
complex nodes: real parts form a separated packet, imaginary parts obey the tilt budget. -/
theorem posSemidef_criticalLogDerivKernel_tiltedPacket
    {W : ℕ → ℂ} (hbase : xiRayPacketBase ≤ (W 0).re)
    (hstep : ∀ m, xiRayPacketBase ^ 2 * (W m).re ≤ (W (m + 1)).re)
    (htilt : ∀ m, |(W m).im| ≤ xiRayTiltBudget (W m).re) (n : ℕ) :
    (Matrix.of fun j k : Fin n => criticalLogDerivKernel (W j) (W k)).PosSemidef := by
  classical
  have hR256 := xiRayPacketBase_ge
  have hR9216 := xiRayPacketBase_ge'
  have hR0 : (0 : ℝ) < xiRayPacketBase := by linarith
  have hR1 : (1 : ℝ) ≤ xiRayPacketBase := by linarith
  have hone := packet_le' hbase hstep
  have hgap := packet_gap' hstep
  have hrepos : ∀ i : ℕ, (0 : ℝ) < (W i).re := fun i => lt_of_lt_of_le hR0 (hone i)
  have hlog1 : ∀ i : ℕ, 1 ≤ Real.log (W i).re := by
    intro i
    rw [Real.le_log_iff_exp_le (hrepos i)]
    have := Real.exp_one_lt_d9
    linarith [hone i]
  -- the real diagonal data
  set D : ℕ → ℝ := fun i => (logDeriv xiCent (W i)).re / (W i).re with hDdef
  have hD_lo : ∀ i : ℕ, Real.log (W i).re / (16 * (W i).re) ≤ D i := fun i =>
    tilted_diag_lower (hone i) (htilt i)
  have hD0 : ∀ i : ℕ, 0 ≤ D i := by
    intro i
    have h1 : 0 ≤ Real.log (W i).re / (16 * (W i).re) := by
      apply div_nonneg _ (by linarith [hrepos i])
      linarith [hlog1 i]
    linarith [hD_lo i]
  have hdiag : ∀ i : ℕ, criticalLogDerivKernel (W i) (W i) = ((D i : ℝ) : ℂ) := fun i =>
    criticalKernel_tilted_diag (W i)
  -- correlation bound
  have hcorr : ∀ i j : ℕ, i < j →
      ‖criticalLogDerivKernel (W i) (W j)‖
        ≤ 128 * (2 / xiRayPacketBase) ^ (j - i) * (Real.sqrt (D i) * Real.sqrt (D j)) := by
    intro i j hij
    have hnormK : ‖criticalLogDerivKernel (W i) (W j)‖
        ≤ (4 * Real.log (W i).re + 4 * Real.log (W j).re) / ((W i).re + (W j).re) := by
      unfold criticalLogDerivKernel
      rw [norm_div]
      have hden : (W i).re + (W j).re ≤ ‖W i + conj (W j)‖ := by
        have h := Complex.re_le_norm (W i + conj (W j))
        rwa [Complex.add_re, Complex.conj_re] at h
      have hnum : ‖logDeriv xiCent (W i) + conj (logDeriv xiCent (W j))‖
          ≤ 4 * Real.log (W i).re + 4 * Real.log (W j).re := by
        calc ‖logDeriv xiCent (W i) + conj (logDeriv xiCent (W j))‖
            ≤ ‖logDeriv xiCent (W i)‖ + ‖conj (logDeriv xiCent (W j))‖ := norm_add_le _ _
          _ = ‖logDeriv xiCent (W i)‖ + ‖logDeriv xiCent (W j)‖ := by
              rw [Complex.norm_conj]
          _ ≤ 4 * Real.log (W i).re + 4 * Real.log (W j).re :=
              add_le_add (tilted_norm_le (hone i) (htilt i))
                (tilted_norm_le (hone j) (htilt j))
      have hden0 : (0 : ℝ) < (W i).re + (W j).re := by
        linarith [hrepos i, hrepos j]
      calc ‖logDeriv xiCent (W i) + conj (logDeriv xiCent (W j))‖ / ‖W i + conj (W j)‖
          ≤ ‖logDeriv xiCent (W i) + conj (logDeriv xiCent (W j))‖
              / ((W i).re + (W j).re) :=
            div_le_div_of_nonneg_left (norm_nonneg _) hden0 hden
        _ ≤ (4 * Real.log (W i).re + 4 * Real.log (W j).re) / ((W i).re + (W j).re) :=
            div_le_div_of_nonneg_right hnum hden0.le
    have hloguv : Real.log (W i).re ≤ Real.log (W j).re := by
      apply Real.log_le_log (hrepos i)
      have h := hgap i j hij.le
      have hpow : (1 : ℝ) ≤ xiRayPacketBase ^ (2 * (j - i)) := one_le_pow₀ hR1
      nlinarith [hrepos i]
    have hstep8 : (4 * Real.log (W i).re + 4 * Real.log (W j).re) / ((W i).re + (W j).re)
        ≤ 8 * Real.log (W j).re / (W j).re := by
      have hnum8 : 4 * Real.log (W i).re + 4 * Real.log (W j).re
          ≤ 8 * Real.log (W j).re := by linarith
      have hnum0 : 0 ≤ 4 * Real.log (W i).re + 4 * Real.log (W j).re := by
        linarith [hlog1 i, hlog1 j]
      calc (4 * Real.log (W i).re + 4 * Real.log (W j).re) / ((W i).re + (W j).re)
          ≤ (4 * Real.log (W i).re + 4 * Real.log (W j).re) / (W j).re := by
            apply div_le_div_of_nonneg_left hnum0 (hrepos j)
            linarith [hrepos i]
        _ ≤ 8 * Real.log (W j).re / (W j).re :=
            div_le_div_of_nonneg_right hnum8 (hrepos j).le
    -- log-ratio contraction and square roots
    have hkey := xiRayLog_div_self_contraction (hone i) (d := j - i)
      (hgap i j hij.le)
    set q : ℝ := 2 / xiRayPacketBase with hqdef
    have hq0 : 0 < q := div_pos (by norm_num) hR0
    set A : ℝ := Real.log (W j).re / (W j).re with hAdef
    set B : ℝ := Real.log (W i).re / (W i).re with hBdef
    have hA0 : 0 ≤ A := div_nonneg (by linarith [hlog1 j]) (hrepos j).le
    have hB0 : 0 ≤ B := div_nonneg (by linarith [hlog1 i]) (hrepos i).le
    have hkey' : A ≤ q ^ (2 * (j - i)) * B := hkey
    have hsqrt : A ≤ q ^ (j - i) * Real.sqrt (B * A) := by
      have h1 : A * A ≤ (q ^ (2 * (j - i)) * B) * A := mul_le_mul_of_nonneg_right hkey' hA0
      have h2 : Real.sqrt (A * A) ≤ Real.sqrt ((q ^ (2 * (j - i)) * B) * A) :=
        Real.sqrt_le_sqrt h1
      have h3 : Real.sqrt (A * A) = A := Real.sqrt_mul_self hA0
      have h4 : (q ^ (2 * (j - i)) * B) * A = (q ^ (j - i)) ^ 2 * (B * A) := by
        rw [show 2 * (j - i) = (j - i) * 2 from Nat.mul_comm 2 (j - i), pow_mul]
        ring
      have h5 : Real.sqrt ((q ^ (j - i)) ^ 2 * (B * A))
          = q ^ (j - i) * Real.sqrt (B * A) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hq0.le _)]
      calc A = Real.sqrt (A * A) := h3.symm
        _ ≤ Real.sqrt ((q ^ (2 * (j - i)) * B) * A) := h2
        _ = Real.sqrt ((q ^ (j - i)) ^ 2 * (B * A)) := by rw [h4]
        _ = q ^ (j - i) * Real.sqrt (B * A) := h5
    have hsq16 : Real.sqrt (B / 16) * Real.sqrt (A / 16) = Real.sqrt (B * A) / 16 := by
      rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ B / 16)]
      have h1 : B / 16 * (A / 16) = B * A * (1 / 256) := by ring
      rw [h1, Real.sqrt_mul (mul_nonneg hB0 hA0),
        show (1 : ℝ) / 256 = (1 / 16) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 16)]
      ring
    have hDi16 : B / 16 ≤ D i := by
      have h := hD_lo i
      have h2 : B / 16 = Real.log (W i).re / (16 * (W i).re) := by
        rw [hBdef, div_div]
        ring_nf
      linarith [h2 ▸ h]
    have hDj16 : A / 16 ≤ D j := by
      have h := hD_lo j
      have h2 : A / 16 = Real.log (W j).re / (16 * (W j).re) := by
        rw [hAdef, div_div]
        ring_nf
      linarith [h2 ▸ h]
    have h3 : Real.sqrt (B / 16) * Real.sqrt (A / 16)
        ≤ Real.sqrt (D i) * Real.sqrt (D j) :=
      mul_le_mul (Real.sqrt_le_sqrt hDi16) (Real.sqrt_le_sqrt hDj16)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc ‖criticalLogDerivKernel (W i) (W j)‖
        ≤ (4 * Real.log (W i).re + 4 * Real.log (W j).re) / ((W i).re + (W j).re) := hnormK
      _ ≤ 8 * Real.log (W j).re / (W j).re := hstep8
      _ = 8 * A := by rw [hAdef]; ring
      _ ≤ 8 * (q ^ (j - i) * Real.sqrt (B * A)) := by
          linarith [mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 8)]
      _ = 128 * q ^ (j - i) * (Real.sqrt (B * A) / 16) := by ring
      _ = 128 * q ^ (j - i) * (Real.sqrt (B / 16) * Real.sqrt (A / 16)) := by rw [hsq16]
      _ ≤ 128 * q ^ (j - i) * (Real.sqrt (D i) * Real.sqrt (D j)) := by
          exact mul_le_mul_of_nonneg_left h3
            (mul_nonneg (by norm_num) (pow_nonneg hq0.le _))
  -- Hermitian
  have hherm : (Matrix.of fun j k : Fin n =>
      criticalLogDerivKernel (W j) (W k)).IsHermitian := by
    ext j k
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, RCLike.star_def]
    exact criticalLogDerivKernel_conj_symm (W (k : ℕ)) (W (j : ℕ))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun cv => ?_)
  -- expand the quadratic form
  have hval : star cv ⬝ᵥ (Matrix.of fun j k : Fin n =>
      criticalLogDerivKernel (W j) (W k)).mulVec cv
      = ∑ j : Fin n, ∑ k : Fin n,
          (starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hval]
  -- the imaginary part vanishes by Hermitian pairing
  have hterm_conj : ∀ j k : Fin n,
      (starRingEnd ℂ) ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k))
        = (starRingEnd ℂ) (cv k) * cv j * criticalLogDerivKernel (W k) (W j) := by
    intro j k
    rw [map_mul, map_mul, Complex.conj_conj, criticalLogDerivKernel_conj_symm]
    ring
  have him : (∑ j : Fin n, ∑ k : Fin n,
      (starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).im = 0 := by
    rw [Complex.im_sum]
    have hstep1 : ∀ j : Fin n, (∑ k : Fin n,
        (starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).im
        = ∑ k : Fin n,
            ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).im := by
      intro j
      rw [Complex.im_sum]
    have hanti : ∀ j k : Fin n,
        ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).im
        = -(((starRingEnd ℂ) (cv k) * cv j * criticalLogDerivKernel (W k) (W j)).im) := by
      intro j k
      have h := congrArg Complex.im (hterm_conj j k)
      rw [Complex.conj_im] at h
      linarith [h]
    calc (∑ j : Fin n, (∑ k : Fin n,
        (starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).im)
        = ∑ j : Fin n, ∑ k : Fin n,
            ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).im := by
          exact Finset.sum_congr rfl fun j _ => hstep1 j
      _ = 0 := by
          have hswap : (∑ j : Fin n, ∑ k : Fin n,
              ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).im)
              = ∑ k : Fin n, ∑ j : Fin n,
                ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).im :=
            Finset.sum_comm
          have hneg : (∑ k : Fin n, ∑ j : Fin n,
              ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).im)
              = -(∑ k : Fin n, ∑ j : Fin n,
                ((starRingEnd ℂ) (cv k) * cv j * criticalLogDerivKernel (W k) (W j)).im) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun j _ => hanti j k
          have hsame : (∑ k : Fin n, ∑ j : Fin n,
              ((starRingEnd ℂ) (cv k) * cv j * criticalLogDerivKernel (W k) (W j)).im)
              = ∑ j : Fin n, ∑ k : Fin n,
                ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).im := rfl
          linarith [hswap, hneg, hsame ▸ hneg]
  -- the real part is a scaled-Gershgorin-dominated real form
  set b : ℕ → ℝ := fun i => if h : i < n then ‖cv ⟨i, h⟩‖ * Real.sqrt (D i) else 0
    with hbdef
  have hbfin : ∀ j : Fin n, b (j : ℕ) = ‖cv j‖ * Real.sqrt (D (j : ℕ)) := by
    intro j
    rw [hbdef]
    dsimp only
    rw [dif_pos j.isLt]
  have hb0 : ∀ i : ℕ, 0 ≤ b i := by
    intro i
    rw [hbdef]
    dsimp only
    split
    · exact mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    · exact le_refl 0
  have hrediag : ∀ j : Fin n,
      ((starRingEnd ℂ) (cv j) * cv j * criticalLogDerivKernel (W j) (W j)).re
        = b (j : ℕ) ^ 2 := by
    intro j
    rw [hdiag (j : ℕ)]
    have h1 : (starRingEnd ℂ) (cv j) * cv j = ((Complex.normSq (cv j) : ℝ) : ℂ) := by
      rw [mul_comm]
      exact Complex.mul_conj (cv j)
    rw [h1, ← Complex.ofReal_mul]
    rw [Complex.ofReal_re]
    rw [hbfin j, mul_pow, Real.sq_sqrt (hD0 (j : ℕ)), ← Complex.normSq_eq_norm_sq]
  have hreoff : ∀ j k : Fin n, j ≠ k →
      -(128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
          * ((b (j : ℕ) ^ 2 + b (k : ℕ) ^ 2) / 2))
        ≤ ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re := by
    have hq0 : 0 < 2 / xiRayPacketBase := div_pos (by norm_num) hR0
    have hmain : ∀ j k : Fin n, (j : ℕ) < (k : ℕ) →
        ‖criticalLogDerivKernel (W j) (W k)‖
          ≤ 128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
            * (Real.sqrt (D (j : ℕ)) * Real.sqrt (D (k : ℕ))) := by
      intro j k hjk
      rw [Nat.dist_eq_sub_of_le hjk.le]
      exact hcorr (j : ℕ) (k : ℕ) hjk
    intro j k hjk
    have hnorm : ‖criticalLogDerivKernel (W j) (W k)‖
        ≤ 128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
          * (Real.sqrt (D (j : ℕ)) * Real.sqrt (D (k : ℕ))) := by
      rcases Nat.lt_or_ge (j : ℕ) (k : ℕ) with hlt | hge
      · exact hmain j k hlt
      · have hlt : (k : ℕ) < (j : ℕ) := by
          rcases Nat.lt_or_ge (k : ℕ) (j : ℕ) with h | h
          · exact h
          · exact absurd (Fin.ext (Nat.le_antisymm hge h)).symm hjk
        have h := hmain k j hlt
        have hsymm : ‖criticalLogDerivKernel (W j) (W k)‖
            = ‖criticalLogDerivKernel (W k) (W j)‖ := by
          rw [← criticalLogDerivKernel_conj_symm, Complex.norm_conj]
        rw [hsymm, Nat.dist_comm]
        calc ‖criticalLogDerivKernel (W k) (W j)‖
            ≤ 128 * (2 / xiRayPacketBase) ^ Nat.dist (k : ℕ) (j : ℕ)
              * (Real.sqrt (D (k : ℕ)) * Real.sqrt (D (j : ℕ))) := h
          _ = 128 * (2 / xiRayPacketBase) ^ Nat.dist (k : ℕ) (j : ℕ)
              * (Real.sqrt (D (j : ℕ)) * Real.sqrt (D (k : ℕ))) := by ring
    have habs : |((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re|
        ≤ b (j : ℕ) * b (k : ℕ)
          * (128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)) := by
      have h1 : |((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re|
          ≤ ‖(starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)‖ := by
        rcases abs_cases ((starRingEnd ℂ) (cv j) * cv k
            * criticalLogDerivKernel (W j) (W k)).re with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]
          exact Complex.re_le_norm _
        · rw [h]
          have := Complex.re_le_norm (-((starRingEnd ℂ) (cv j) * cv k
            * criticalLogDerivKernel (W j) (W k)))
          simpa using this
      have h2 : ‖(starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)‖
          = ‖cv j‖ * ‖cv k‖ * ‖criticalLogDerivKernel (W j) (W k)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_conj]
      have h3 : ‖cv j‖ * ‖cv k‖ * ‖criticalLogDerivKernel (W j) (W k)‖
          ≤ ‖cv j‖ * ‖cv k‖ * (128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
            * (Real.sqrt (D (j : ℕ)) * Real.sqrt (D (k : ℕ)))) := by
        apply mul_le_mul_of_nonneg_left hnorm
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have h4 : ‖cv j‖ * ‖cv k‖ * (128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
            * (Real.sqrt (D (j : ℕ)) * Real.sqrt (D (k : ℕ))))
          = b (j : ℕ) * b (k : ℕ)
            * (128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)) := by
        rw [hbfin j, hbfin k]
        ring
      linarith [h1, h2 ▸ h1, h3, h4 ▸ h3]
    have hamgm : b (j : ℕ) * b (k : ℕ) ≤ (b (j : ℕ) ^ 2 + b (k : ℕ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (b (j : ℕ) - b (k : ℕ))]
    have hKq0 : (0 : ℝ) ≤ 128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) :=
      mul_nonneg (by norm_num) (pow_nonneg hq0.le _)
    have h5 := abs_le.mp habs
    have h6 : b (j : ℕ) * b (k : ℕ)
          * (128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ))
        ≤ (b (j : ℕ) ^ 2 + b (k : ℕ) ^ 2) / 2
          * (128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)) :=
      mul_le_mul_of_nonneg_right hamgm hKq0
    have h7 := h5.1
    nlinarith [h6, h7]
  -- row sums
  have hq0 : (0 : ℝ) < 2 / xiRayPacketBase := div_pos (by norm_num) hR0
  have hq513 : 2 / xiRayPacketBase ≤ 1 / 513 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 1026) (by linarith : (1026 : ℝ) ≤ xiRayPacketBase)
    calc 2 / xiRayPacketBase ≤ 2 / 1026 := h
      _ = 1 / 513 := by norm_num
  have hq1 : 2 / xiRayPacketBase < 1 := by linarith
  have h1q : (0 : ℝ) < 1 - 2 / xiRayPacketBase := by linarith
  have hrow : ∀ j : Fin n,
      ∑ k ∈ Finset.univ.erase j,
        128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) ≤ 1 := by
    intro j
    have heq := fin_erase_sum_eq j
      (fun m => 128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) m)
    rw [heq]
    have hg : ∑ m ∈ (Finset.range n).erase (j : ℕ),
        128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) m
        = 128 * ∑ m ∈ (Finset.range n).erase (j : ℕ),
            (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) m := by
      rw [Finset.mul_sum]
    rw [hg]
    have hgeom := natDist_geom_row_sum_le hq0.le hq1 n (j : ℕ)
    have hclose : (128 : ℝ) * (2 * (2 / xiRayPacketBase / (1 - 2 / xiRayPacketBase))) ≤ 1 := by
      have h2 : (128 : ℝ) * (2 * (2 / xiRayPacketBase / (1 - 2 / xiRayPacketBase)))
          = 256 * (2 / xiRayPacketBase) / (1 - 2 / xiRayPacketBase) := by ring
      rw [h2, div_le_one h1q]
      linarith
    calc (128 : ℝ) * ∑ m ∈ (Finset.range n).erase (j : ℕ),
          (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) m
        ≤ 128 * (2 * (2 / xiRayPacketBase / (1 - 2 / xiRayPacketBase))) :=
          mul_le_mul_of_nonneg_left hgeom (by norm_num)
      _ ≤ 1 := hclose
  -- assemble the real part
  have hre : 0 ≤ (∑ j : Fin n, ∑ k : Fin n,
      (starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re := by
    rw [Complex.re_sum]
    have hrowre : ∀ j : Fin n, (∑ k : Fin n,
        (starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re
        = ∑ k : Fin n,
            ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re :=
      fun j => Complex.re_sum _ _
    have hlower : ∀ j : Fin n,
        b (j : ℕ) ^ 2 - (∑ k ∈ Finset.univ.erase j,
            128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
              * ((b (j : ℕ) ^ 2 + b (k : ℕ) ^ 2) / 2))
          ≤ ∑ k : Fin n,
              ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re := by
      intro j
      have hsplit : ∑ k : Fin n,
          ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re
          = ((starRingEnd ℂ) (cv j) * cv j * criticalLogDerivKernel (W j) (W j)).re
            + ∑ k ∈ Finset.univ.erase j,
                ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
      rw [hsplit, hrediag j]
      have hsum := Finset.sum_le_sum (s := Finset.univ.erase j)
        (f := fun k : Fin n => -(128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
          * ((b (j : ℕ) ^ 2 + b (k : ℕ) ^ 2) / 2)))
        (g := fun k : Fin n =>
          ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re)
        (fun k hk => hreoff j k (Ne.symm (Finset.mem_erase.mp hk).1))
      rw [Finset.sum_neg_distrib] at hsum
      linarith
    have hswap : ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j,
        128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) * b (k : ℕ) ^ 2
        = ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j,
            128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) * b (j : ℕ) ^ 2 := by
      rw [Finset.sum_comm' (t' := Finset.univ)
        (s' := fun k => Finset.univ.erase k)
        (by
          intro x y
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, true_and]
          exact ne_comm)]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.dist_comm]
    have hW : ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j,
        128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
          * ((b (j : ℕ) ^ 2 + b (k : ℕ) ^ 2) / 2)
        ≤ ∑ j : Fin n, b (j : ℕ) ^ 2 := by
      have hsplit2 : ∀ j : Fin n, ∑ k ∈ Finset.univ.erase j,
          128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
            * ((b (j : ℕ) ^ 2 + b (k : ℕ) ^ 2) / 2)
          = (∑ k ∈ Finset.univ.erase j,
              128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) * b (j : ℕ) ^ 2) / 2
            + (∑ k ∈ Finset.univ.erase j,
              128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) * b (k : ℕ) ^ 2) / 2 := by
        intro j
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      have hA : ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j,
          128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) * b (j : ℕ) ^ 2
          ≤ ∑ j : Fin n, b (j : ℕ) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : ∑ k ∈ Finset.univ.erase j,
            128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) * b (j : ℕ) ^ 2
            = (∑ k ∈ Finset.univ.erase j,
                128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)) * b (j : ℕ) ^ 2 := by
          rw [Finset.sum_mul]
        rw [h1]
        calc (∑ k ∈ Finset.univ.erase j,
              128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)) * b (j : ℕ) ^ 2
            ≤ 1 * b (j : ℕ) ^ 2 :=
              mul_le_mul_of_nonneg_right (hrow j) (sq_nonneg _)
          _ = b (j : ℕ) ^ 2 := one_mul _
      calc ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j,
            128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
              * ((b (j : ℕ) ^ 2 + b (k : ℕ) ^ 2) / 2)
          = (∑ j : Fin n, ∑ k ∈ Finset.univ.erase j,
              128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) * b (j : ℕ) ^ 2) / 2
            + (∑ j : Fin n, ∑ k ∈ Finset.univ.erase j,
              128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) * b (k : ℕ) ^ 2) / 2 := by
            rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => hsplit2 j
        _ = ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j,
              128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ) * b (j : ℕ) ^ 2 := by
            rw [hswap]
            ring
        _ ≤ ∑ j : Fin n, b (j : ℕ) ^ 2 := hA
    have htotal : ∑ j : Fin n, (b (j : ℕ) ^ 2 - ∑ k ∈ Finset.univ.erase j,
        128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
          * ((b (j : ℕ) ^ 2 + b (k : ℕ) ^ 2) / 2))
        ≤ ∑ j : Fin n, ∑ k : Fin n,
            ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re :=
      Finset.sum_le_sum fun j _ => hlower j
    have hnonneg : 0 ≤ ∑ j : Fin n, (b (j : ℕ) ^ 2 - ∑ k ∈ Finset.univ.erase j,
        128 * (2 / xiRayPacketBase) ^ Nat.dist (j : ℕ) (k : ℕ)
          * ((b (j : ℕ) ^ 2 + b (k : ℕ) ^ 2) / 2)) := by
      rw [Finset.sum_sub_distrib]
      linarith [hW]
    have hfinal : ∑ j : Fin n, (∑ k : Fin n,
        (starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re
        = ∑ j : Fin n, ∑ k : Fin n,
            ((starRingEnd ℂ) (cv j) * cv k * criticalLogDerivKernel (W j) (W k)).re :=
      Finset.sum_congr rfl fun j _ => hrowre j
    rw [hfinal]
    linarith [htotal, hnonneg]
  rw [Complex.le_def]
  constructor
  · simp only [Complex.zero_re]
    exact hre
  · rw [him]
    simp only [Complex.zero_im]

end RHTower

namespace RHTower

/-! ## The Bezoutian matrices at tilted packets -/

/-- **Tilted separated packets give positive semidefinite Bezoutian matrices**: an
arbitrary-rank unconditional stratum of the theta tail first-moment Bezoutian criterion
family at genuinely complex nodes of the cofinal Euler half-plane. -/
theorem posSemidef_thetaTailFirstMomentBezoutian_tiltedPacket
    {W : ℕ → ℂ} (hbase : xiRayPacketBase ≤ (W 0).re)
    (hstep : ∀ m, xiRayPacketBase ^ 2 * (W m).re ≤ (W (m + 1)).re)
    (htilt : ∀ m, |(W m).im| ≤ xiRayTiltBudget (W m).re) (n : ℕ) :
    (Matrix.of fun j k : Fin n =>
      thetaTailFirstMomentBezoutian (W j) ((starRingEnd ℂ) (W k))).PosSemidef := by
  have hK := posSemidef_criticalLogDerivKernel_tiltedPacket hbase hstep htilt n
  have hR256 := xiRayPacketBase_ge
  have hone := packet_le' hbase hstep
  have hhalf : ∀ i : ℕ, 1 / 2 < (W i).re := fun i => by linarith [hone i]
  have hentry : ∀ j k : Fin n,
      thetaTailFirstMomentBezoutian (W j) ((starRingEnd ℂ) (W k))
        = xiCent (W j) * (starRingEnd ℂ) (xiCent (W k))
          * criticalLogDerivKernel (W j) (W k) := by
    intro j k
    have h := xiCentBezoutian_eq_mul_criticalKernel (hhalf (j : ℕ)) (hhalf (k : ℕ))
    unfold thetaTailFirstMomentBezoutian
    exact h
  have hherm : (Matrix.of fun j k : Fin n =>
      thetaTailFirstMomentBezoutian (W j) ((starRingEnd ℂ) (W k))).IsHermitian := by
    ext j k
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, RCLike.star_def,
      hentry, hentry]
    rw [map_mul, map_mul, Complex.conj_conj, criticalLogDerivKernel_conj_symm]
    ring
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun cv => ?_)
  have hquad := hK.dotProduct_mulVec_nonneg
    (fun j : Fin n => (starRingEnd ℂ) (xiCent (W j)) * cv j)
  have hval : star cv ⬝ᵥ (Matrix.of fun j k : Fin n =>
      thetaTailFirstMomentBezoutian (W j) ((starRingEnd ℂ) (W k))).mulVec cv
      = star (fun j : Fin n => (starRingEnd ℂ) (xiCent (W j)) * cv j) ⬝ᵥ
          (Matrix.of fun j k : Fin n =>
            criticalLogDerivKernel (W j) (W k)).mulVec
          (fun j : Fin n => (starRingEnd ℂ) (xiCent (W j)) * cv j) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hentry]
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [hval]
  exact hquad

/-- Instantiation in the literal quantifier shape of the Bezoutian Riemann-hypothesis
criterion: every tilted separated packet, read as a node system of the cofinal Euler
half-plane, yields a positive semidefinite criterion matrix. -/
theorem posSemidef_thetaTailFirstMomentBezoutian_tiltedPacket_nodes
    {W : ℕ → ℂ} (hbase : xiRayPacketBase ≤ (W 0).re)
    (hstep : ∀ m, xiRayPacketBase ^ 2 * (W m).re ≤ (W (m + 1)).re)
    (htilt : ∀ m, |(W m).im| ≤ xiRayTiltBudget (W m).re) (n : ℕ)
    (w : Fin n → {V : ℂ // 1 / 2 < V.re}) (hw : ∀ j, (w j : ℂ) = W (j : ℕ)) :
    (Matrix.of fun j k =>
      thetaTailFirstMomentBezoutian ((w j : ℂ))
        ((starRingEnd ℂ) ((w k : ℂ)))).PosSemidef := by
  have heq : (Matrix.of fun j k : Fin n =>
      thetaTailFirstMomentBezoutian ((w j : ℂ)) ((starRingEnd ℂ) ((w k : ℂ))))
      = Matrix.of fun j k : Fin n =>
        thetaTailFirstMomentBezoutian (W (j : ℕ)) ((starRingEnd ℂ) (W (k : ℕ))) := by
    ext j k
    rw [Matrix.of_apply, Matrix.of_apply, hw j, hw k]
  rw [heq]
  exact posSemidef_thetaTailFirstMomentBezoutian_tiltedPacket hbase hstep htilt n

end RHTower
