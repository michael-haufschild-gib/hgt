import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePairingOfTheDegreePointsIsThePoleMinusWeilsFunctional
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TemperedConfigurationPontryaginLaw
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-!
# The pairing of the degree points weighs the zeros

For a packet `f ∈ C²_c` write `f̂(z) = ∫ f(u) e^{izu} du`, `γ_ρ = (ρ − ½)/i` for a nontrivial zero
`ρ` of `ζ`, and `Z(f) = Re Σ_ρ m_ρ f̂(γ_ρ) conj f̂(conj γ_ρ)` for the sum over the zeros. By the
explicit formula `Z(f)` is Weil's functional of the packet, so the theorems on the pairing of the
degree points are statements on the zeros.

* **The pairing** (`tendsto_degreePairing_degrees_sub_zeroSum`): jets plus contacts minus the
  counterterm `log(n/2π)` tend to `2 d₁ d₂ − Z(f)`, `d₁ = ∫ f e^{−u/2}`, `d₂ = ∫ f e^{u/2}`.
* **The contacts are the fluctuation of the zeros** (`tendsto_degreeContact_fluctuation`): twice
  the contacts of a packet tend to the pole and archimedean part of Weil's functional minus
  `Z(f)`. The pole and archimedean part is the mean of the zero sum, carried by the jets; what the
  zeros add to it is carried by the contacts of the square.
* **Short packets see no fluctuation** (`zeroSum_eq_weilArchRe_of_short`): a packet of width at
  most `log 2` meets no contact, and its zero sum is its pole and archimedean part.
* **The inequality up to the zeros off the line**
  (`tendsto_degreePairing_le_degrees_add_offLineDefect`): for every packet the limit of the
  pairing is at most `2 d₁ d₂ + Σ_ρ m_ρ |f̂(γ_ρ) − f̂(conj γ_ρ)|²/4`. A zero on the line has
  `γ_ρ` real and contributes nothing to the defect (`offLineTerm_eq_zero_of_re`), and the
  Riemann hypothesis holds iff the defect vanishes on every packet
  (`riemannHypothesis_iff_offLineDefect_eq_zero`).
* **Short packets of any sign** (`tendsto_degreePairing_le_degrees_of_signed_short`): for a
  packet of width at most `1/130`, of any sign, the inequality `D·D ≤ 2 d₁ d₂` holds.
-/

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {f : ℝ → ℝ}

/-! ### The sum over the zeros -/

/-- The sum over the zeros of a packet, `Re Σ_ρ m_ρ f̂(γ_ρ) conj f̂(conj γ_ρ)`. -/
def zeroSum (f : ℝ → ℝ) : ℝ :=
  (zetaZeroConfig.W (fun u => (f u : ℂ)) (fun u => (f u : ℂ))).re

theorem contDiff_ofReal_packet (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 fun u => (f u : ℂ) :=
  Complex.ofRealCLM.contDiff.comp hf

theorem hasCompactSupport_ofReal_packet (hfc : HasCompactSupport f) :
    HasCompactSupport fun u => (f u : ℂ) :=
  hfc.comp_left Complex.ofReal_zero

/-- The explicit formula on a packet: the sum over the zeros is Weil's functional. -/
theorem zeroSum_eq_weilFullFunctional (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    zeroSum f = (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  rw [zeroSum, _root_.RHTower.zeta_W_eq_weilFullFunctional_mixed (contDiff_ofReal_packet hf)
    (hasCompactSupport_ofReal_packet hfc) (contDiff_ofReal_packet hf)
    (hasCompactSupport_ofReal_packet hfc)]

/-- **The pairing of the degree points is twice the product of the degrees minus the sum over
the zeros.** -/
theorem tendsto_degreePairing_degrees_sub_zeroSum (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * degreeContact f (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) - zeroSum f)) := by
  have h := tendsto_degreeForm_add_contacts hf hfc hK hsupp
  have e1 : (_root_.RHTower.weilPoleTerm
        (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re =
      2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) :=
    weilPoleTerm_packet hf.continuous hfc
  have e2 : (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
        (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re = zeroSum f :=
    (zeroSum_eq_weilFullFunctional hf hfc).symm
  rwa [e1, e2] at h

/-- **The contacts of a packet are the fluctuation of its zeros.** Twice the contacts tend to the
pole and archimedean part of Weil's functional minus the sum over the zeros. -/
theorem tendsto_degreeContact_fluctuation (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {K : ℕ} (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => 2 * degreeContact f (3 * K) N) atTop
      (𝓝 (_root_.RHTower.WeilOneSided.weilArchRe
          (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) - zeroSum f)) := by
  have h1 := tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp
  have h2 : Tendsto (degreeForm f (3 * K)) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re))) :=
    tendsto_degreeForm hf hfc hK hsupp
  have e := weilPoleTerm_packet hf.continuous hfc
  have h := h1.sub h2
  rw [e] at h
  have hval : 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) - zeroSum f -
        -(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
          2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))) =
      _root_.RHTower.WeilOneSided.weilArchRe
          (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) - zeroSum f := by
    ring
  rw [hval] at h
  exact h.congr fun N => by ring

/-- **A short packet sees no fluctuation.** For a packet of width at most `log 2` the sum over the
zeros is the pole and archimedean part of Weil's functional. -/
theorem zeroSum_eq_weilArchRe_of_short (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {a L : ℝ} (hL : L ≤ Real.log 2) (hshort : ∀ u ∉ Set.Ioo a (a + L), f u = 0) :
    zeroSum f = _root_.RHTower.WeilOneSided.weilArchRe
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hQ : ∀ n : ℕ, 1 < n → packetAutocorr f (Real.log n) = 0 := fun n hn =>
    packetAutocorr_eq_zero_of_width hshort
      (hL.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn)))
  rw [zeroSum_eq_weilFullFunctional hf hfc, re_weilFullFunctional_packet f hQ,
    Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, mul_zero, sub_zero]

/-! ### The defect of the zeros off the line -/

/-- The defect of a zero on a packet, `m_ρ |f̂(γ_ρ) − f̂(conj γ_ρ)|²/4`. -/
def offLineTerm (f : ℝ → ℝ) (ρ : ℂ) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) *
    ‖paperFT (fun u => (f u : ℂ)) (gammaOf ρ) -
      paperFT (fun u => (f u : ℂ)) (conj (gammaOf ρ))‖ ^ 2 / 4

/-- The defect of a packet: the sum of the defects of the zeros. -/
def offLineDefect (f : ℝ → ℝ) : ℝ := ∑' ρ : zetaZeroConfig.carrier, offLineTerm f ρ

theorem offLineTerm_nonneg (f : ℝ → ℝ) (ρ : ℂ) : 0 ≤ offLineTerm f ρ := by
  unfold offLineTerm
  positivity

/-- A zero on the line has a real ordinate and no defect. -/
theorem offLineTerm_eq_zero_of_re (f : ℝ → ℝ) {ρ : ℂ} (h : ρ.re = 1 / 2) :
    offLineTerm f ρ = 0 := by
  rw [offLineTerm, SquareRootThreshold.gammaOf_eq_ofReal_of_re h, Complex.conj_ofReal, sub_self,
    norm_zero]
  ring

/-- A summand of the sum over the zeros is at least minus the defect of its zero:
`Re(a·conj b) ≥ −|a − b|²/4`. -/
theorem neg_offLineTerm_le_re_Wsummand (f : ℝ → ℝ) (ρ : ℂ) :
    -offLineTerm f ρ ≤
      (zetaZeroConfig.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re := by
  set a := paperFT (fun u => (f u : ℂ)) (gammaOf ρ) with ha
  set b := paperFT (fun u => (f u : ℂ)) (conj (gammaOf ρ)) with hb
  have hab : -(‖a - b‖ ^ 2 / 4) ≤ (a * conj b).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]
  have hre : (zetaZeroConfig.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re =
      (zetaZeroConfig.mult ρ : ℝ) * (a * conj b).re := by
    rw [ZeroConfig.Wsummand, mul_assoc, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  rw [hre, offLineTerm]
  nlinarith [mul_le_mul_of_nonneg_left hab hm]

/-- The defects of the zeros are summable: the transform of a packet decays like the inverse
square of the height on the critical strip. -/
theorem summable_offLineTerm (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Summable fun ρ : zetaZeroConfig.carrier => offLineTerm f ρ := by
  obtain ⟨C, hC, hdec⟩ := ArithmeticCastelnuovoSeveri.exists_paperFT_decay
    (contDiff_ofReal_packet hf) (hasCompactSupport_ofReal_packet hfc)
  have hZ : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) :=
    SquareRootThreshold.temperedConfig_zetaZeroConfig
  refine Summable.of_nonneg_of_le (fun ρ => offLineTerm_nonneg f ρ) (fun ρ => ?_)
    (hZ.mul_left (4 / 3 * C ^ 2))
  have him := ArithmeticCastelnuovoSeveri.abs_im_gammaOf_le zetaZeroConfig ρ
  have him' : |(conj (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by rwa [Complex.conj_im, abs_neg]
  have hr : 0 ≤ |(gammaOf (ρ : ℂ)).re| := abs_nonneg _
  have hd : 0 < (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2 := by positivity
  have hu := hdec _ him
  have hv := hdec _ him'
  rw [Complex.conj_re] at hv
  have huv : ‖paperFT (fun u => (f u : ℂ)) (gammaOf ρ) -
        paperFT (fun u => (f u : ℂ)) (conj (gammaOf ρ))‖ ≤
      2 * C * (1 / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2) := by
    refine (norm_sub_le _ _).trans ?_
    have e : 2 * C * (1 / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2) =
        C / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2 + C / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2 := by ring
    rw [e]
    exact add_le_add hu hv
  have ht0 : 0 ≤ 1 / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2 := by positivity
  have ht1 : 1 / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2 ≤ 1 := by
    rw [div_le_one hd]
    nlinarith
  have hden : 1 / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2 ≤
      (4 / 3) / (1 + Complex.normSq (gammaOf ρ)) := by
    rw [Complex.normSq_apply, div_le_div_iff₀ (by positivity)
      (by nlinarith [mul_self_nonneg (gammaOf (ρ : ℂ)).re, mul_self_nonneg (gammaOf (ρ : ℂ)).im])]
    have h1 : (gammaOf (ρ : ℂ)).im * (gammaOf (ρ : ℂ)).im ≤ 1 / 4 := by nlinarith [abs_le.mp him]
    nlinarith [abs_nonneg (gammaOf (ρ : ℂ)).re, sq_abs (gammaOf (ρ : ℂ)).re]
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hsq : ‖paperFT (fun u => (f u : ℂ)) (gammaOf ρ) -
        paperFT (fun u => (f u : ℂ)) (conj (gammaOf ρ))‖ ^ 2 ≤
      (2 * C * (1 / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) huv 2
  have hquad : (1 / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2) ^ 2 ≤
      (4 / 3) / (1 + Complex.normSq (gammaOf ρ)) := by
    rw [sq]
    exact (mul_le_of_le_one_right ht0 ht1).trans hden
  calc offLineTerm f ρ
      ≤ (zetaZeroConfig.mult ρ : ℝ) *
          (2 * C * (1 / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2)) ^ 2 / 4 := by
        unfold offLineTerm
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hm) (by norm_num)
    _ = (zetaZeroConfig.mult ρ : ℝ) * C ^ 2 * (1 / (1 + |(gammaOf (ρ : ℂ)).re|) ^ 2) ^ 2 := by
        ring
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) * C ^ 2 * ((4 / 3) / (1 + Complex.normSq (gammaOf ρ))) :=
        mul_le_mul_of_nonneg_left hquad (mul_nonneg hm (sq_nonneg C))
    _ = 4 / 3 * C ^ 2 *
          ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by ring

theorem offLineDefect_nonneg (f : ℝ → ℝ) : 0 ≤ offLineDefect f :=
  tsum_nonneg fun ρ => offLineTerm_nonneg f ρ

/-- The sum over the zeros is at least minus the defect. -/
theorem neg_offLineDefect_le_zeroSum (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    -offLineDefect f ≤ zeroSum f := by
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  have hF := contDiff_ofReal_packet hf
  have hFc := hasCompactSupport_ofReal_packet hfc
  have hs := ArithmeticCastelnuovoSeveri.summable_Wsummand zetaZeroConfig hZ hF hFc hF hFc
  have hsr := ArithmeticCastelnuovoSeveri.summable_re_Wsummand zetaZeroConfig hZ hF hFc hF hFc
  have hd := summable_offLineTerm hf hfc
  rw [zeroSum, ZeroConfig.W, Complex.re_tsum hs, offLineDefect, ← tsum_neg]
  exact hd.neg.tsum_le_tsum (fun ρ => neg_offLineTerm_le_re_Wsummand f ρ) hsr

/-- **The inequality of Castelnuovo and Severi up to the zeros off the line.** For every packet
the pairing of the degree points has a limit, at most twice the product of the degrees plus the
defect of the zeros. -/
theorem tendsto_degreePairing_le_degrees_add_offLineDefect (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    ∃ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * degreeContact f (3 * K) N)
        atTop (𝓝 l) ∧
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) +
        offLineDefect f :=
  ⟨_, tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp, by
    linarith [neg_offLineDefect_le_zeroSum hf hfc]⟩

/-- With every zero on the line the defect of every packet vanishes. -/
theorem offLineDefect_eq_zero_of_onLine (f : ℝ → ℝ)
    (h : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) : offLineDefect f = 0 := by
  rw [offLineDefect]
  exact (tsum_congr fun ρ : zetaZeroConfig.carrier =>
    offLineTerm_eq_zero_of_re f (h ρ ρ.2)).trans tsum_zero

/-- **The Riemann hypothesis is the vanishing of the defect on every packet.** -/
theorem riemannHypothesis_iff_offLineDefect_eq_zero :
    RiemannHypothesis ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → offLineDefect f = 0 := by
  constructor
  · intro hRH f _ _
    exact offLineDefect_eq_zero_of_onLine f
      (SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH)
  · intro h
    rw [riemannHypothesis_iff_degreePairing_le_degrees]
    intro f hf hfc K hK hsupp l hl
    obtain ⟨l', hl', hle⟩ := tendsto_degreePairing_le_degrees_add_offLineDefect hf hfc hK hsupp
    rw [tendsto_nhds_unique hl hl']
    linarith [h f hf hfc]

/-! ### Short packets of any sign -/

/-- **The inequality on short packets of any sign.** For a packet of width at most `1/130` the
pairing of the degree points has a limit, at most twice the product of the degrees. -/
theorem tendsto_degreePairing_le_degrees_of_signed_short (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) {a L : ℝ} (hL0 : 0 < L)
    (hL : L ≤ 1 / 130) (hshort : ∀ u ∉ Set.Icc a (a + L), f u = 0) :
    ∃ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * degreeContact f (3 * K) N)
        atTop (𝓝 l) ∧
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) := by
  have hpos :=
    _root_.RHTower.WeilLevyCoshCrossover.weilArchRe_nonneg_of_signed_support_Icc_le_inv_130
      hf hfc hL0 hL hshort
  have hlog2 : L + 2 / 130 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hshort' : ∀ u ∉ Set.Ioo (a - 1 / 130) (a - 1 / 130 + (L + 2 / 130)), f u = 0 :=
    fun u hu => hshort u fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
  have hz := zeroSum_eq_weilArchRe_of_short hf hfc hlog2 hshort'
  exact ⟨_, tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp, by
    rw [hz]
    linarith⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
