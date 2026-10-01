import GaloisForLFunctions.RHTower.WeilFullConeHerglotzCriticalHalfPlane
import GaloisForLFunctions.RHTower.WeilIntegerMassAtomicRigidity
import GaloisForLFunctions.RHTower.CrystallineProducerRigidity

/-!
# A converse of Weil's explicit formula

Weil's explicit formula says that the Weil form of the von Mangoldt weights is the zero sum
`W_Λ(f ⋆ f̃) = Σ_ρ m_ρ f̂(γ_ρ) conj f̂(conj γ_ρ)`.  Conversely:

**Theorem** (`converse_explicit_formula`).  Let `lam : ℕ → ℝ`, integers `m_j ≥ 0` and real
ordinates `t_j ≥ 1` with `Σ m_j/t_j² < ∞`.  If for every `C²` compactly supported test `f`

`W_lam(f ⋆ f̃) = Σ_j m_j (|f̂(t_j)|² + |f̂(−t_j)|²)`,

then `lam(n) = Λ(n)` for all `n ≥ 2` and the Riemann hypothesis holds.  So the weights are
determined by the Weil form being a zero sum over *some* real configuration with integer
multiplicities, and the configuration is then the set of ordinates of the nontrivial zeros of ζ.

**Proof.**  The hypothesis makes `lam` full-cone Weil-positive.  On `Re s > 1`, `w = s − ½`, the
stage-1 tests `h_j` give `Re W_lam(h_j ⋆ h̃_j) → Re Φ_lam(s)/Re w` (`tendsto_re_autoCorr`), while the
zero sum tends to `Σ m_j(|w − it_j|⁻² + |w + it_j|⁻²)` (dominated convergence, `|ĥ_j| ≤ 2|ĥ|`).  So
`Re Φ_lam = Re A` on `Re s > 1` for the atomic Herglotz series `A(s) = 2(s−½)Σ m_j/((s−½)² + t_j²)`.
The difference `Φ_lam − A` is holomorphic with zero real part on the convex set `Re s > 1`, hence
constant; it is real at `s = 2`, so it vanishes.  The integer-mass rigidity theorem
(`IntegerMassRigidity.integer_mass_rigidity`) concludes.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-- The integer zero sum `Σ_j m_j (|f̂(t_j)|² + |f̂(−t_j)|²)`. -/
def zeroSumForm (m : ℕ → ℕ) (t : ℕ → ℝ) (f : ℝ → ℂ) : ℝ :=
  ∑' j, (m j : ℝ) * (‖paperFT f (t j)‖ ^ 2 + ‖paperFT f (-(t j) : ℝ)‖ ^ 2)

theorem zeroSumForm_nonneg (m : ℕ → ℕ) (t : ℕ → ℝ) (f : ℝ → ℂ) : 0 ≤ zeroSumForm m t f :=
  tsum_nonneg fun _ => by positivity

/-- `|w ∓ it|⁻² ≤ K/t²` for `t ≥ 1`. -/
theorem inv_normSq_sub_le {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 1 ≤ t) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ‖1 / (w - I * ((ε * t : ℝ) : ℂ))‖ ^ 2 ≤ (4 + 4 * w.im ^ 2 / w.re ^ 2) / t ^ 2 := by
  have hne : w - I * ((ε * t : ℝ) : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [re_sub_I_mul_ofReal] at this
    simp at this
    linarith
  rw [norm_div, norm_one, div_pow, one_pow, Complex.sq_norm, WeilHerglotz.normSq_sub_I_mul]
  have hb2 : 0 < w.re ^ 2 := by positivity
  have hD : 0 < w.re ^ 2 + (ε * t - w.im) ^ 2 := by positivity
  have hε2 : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  rw [div_le_div_iff₀ hD (by positivity), one_mul]
  have hkey : t ^ 2 ≤ (4 + 4 * w.im ^ 2 / w.re ^ 2) * (w.re ^ 2 + (ε * t - w.im) ^ 2) := by
    rcases le_or_gt (2 * |w.im|) t with h | h
    · have h1 : t / 2 ≤ |ε * t - w.im| := by
        have h2 : |ε * t| = t := by
          rw [abs_mul, show |ε| = 1 by rcases hε with h | h <;> rw [h] <;> norm_num,
            one_mul, abs_of_pos (by linarith)]
        have := abs_sub_abs_le_abs_sub (ε * t) w.im
        linarith
      have h3 : t ^ 2 / 4 ≤ (ε * t - w.im) ^ 2 := by
        have := pow_le_pow_left₀ (by linarith) h1 2
        rw [sq_abs] at this
        nlinarith
      have h4 : 0 ≤ 4 * w.im ^ 2 / w.re ^ 2 * (w.re ^ 2 + (ε * t - w.im) ^ 2) := by positivity
      nlinarith [sq_nonneg (ε * t - w.im)]
    · have h1 : t ^ 2 ≤ 4 * w.im ^ 2 := by
        have : t ^ 2 < (2 * |w.im|) ^ 2 := pow_lt_pow_left₀ h (by linarith) (by norm_num)
        rw [mul_pow, sq_abs] at this
        linarith
      have h2 : 4 * w.im ^ 2 = 4 * w.im ^ 2 / w.re ^ 2 * w.re ^ 2 := by field_simp
      nlinarith [sq_nonneg (ε * t - w.im), sq_nonneg w.re]
  exact hkey

/-- The zero sum of the stage-1 tests converges. -/
theorem tendsto_zeroSumForm_testFn {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun k : ℕ => zeroSumForm m t (testFn w k)) atTop
      (𝓝 (∑' j, (m j : ℝ) * (‖1 / (w - I * (t j : ℂ))‖ ^ 2 +
        ‖1 / (w - I * ((-(t j) : ℝ) : ℂ))‖ ^ 2))) := by
  set K : ℝ := 4 + 4 * w.im ^ 2 / w.re ^ 2 with hK
  have hbound : Summable fun j => 4 * (m j : ℝ) * (2 * K / t j ^ 2) := by
    have := hsum.mul_left (8 * K)
    refine this.congr fun j => ?_
    ring
  refine tendsto_tsum_of_dominated_convergence hbound (fun j => ?_)
    (Eventually.of_forall fun k j => ?_)
  · have hre1 : 0 < (w - I * ((t j : ℝ) : ℂ)).re := by rw [re_sub_I_mul_ofReal]; exact hw
    have hre2 : 0 < (w - I * ((-(t j) : ℝ) : ℂ)).re := by rw [re_sub_I_mul_ofReal]; exact hw
    have h1 := tendsto_paperFT_testFn hre1
    have h2 := tendsto_paperFT_testFn hre2
    exact ((((continuous_norm.tendsto _).comp h1).pow 2).add
      (((continuous_norm.tendsto _).comp h2).pow 2)).const_mul _
  · have hb1 : ‖paperFT (testFn w k) (t j : ℝ)‖ ^ 2 ≤ 4 * ‖1 / (w - I * ((t j : ℝ) : ℂ))‖ ^ 2 := by
      have := norm_paperFT_testFn_le hw k (t j)
      rw [norm_div, norm_one]
      have hpos : 0 ≤ ‖paperFT (testFn w k) (t j : ℝ)‖ := norm_nonneg _
      calc ‖paperFT (testFn w k) (t j : ℝ)‖ ^ 2 ≤ (2 / ‖w - I * ((t j : ℝ) : ℂ)‖) ^ 2 :=
            pow_le_pow_left₀ hpos this 2
        _ = 4 * (1 / ‖w - I * ((t j : ℝ) : ℂ)‖) ^ 2 := by ring
    have hb2 : ‖paperFT (testFn w k) ((-(t j) : ℝ) : ℂ)‖ ^ 2 ≤
        4 * ‖1 / (w - I * ((-(t j) : ℝ) : ℂ))‖ ^ 2 := by
      have := norm_paperFT_testFn_le hw k (-(t j))
      rw [norm_div, norm_one]
      have hpos : 0 ≤ ‖paperFT (testFn w k) ((-(t j) : ℝ) : ℂ)‖ := norm_nonneg _
      calc ‖paperFT (testFn w k) ((-(t j) : ℝ) : ℂ)‖ ^ 2 ≤
            (2 / ‖w - I * ((-(t j) : ℝ) : ℂ)‖) ^ 2 := pow_le_pow_left₀ hpos this 2
        _ = 4 * (1 / ‖w - I * ((-(t j) : ℝ) : ℂ)‖) ^ 2 := by ring
    have hk1 := inv_normSq_sub_le hw (hone j) 1 (Or.inl rfl)
    have hk2 := inv_normSq_sub_le hw (hone j) (-1) (Or.inr rfl)
    simp only [one_mul, neg_one_mul] at hk1 hk2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hm : (0 : ℝ) ≤ m j := Nat.cast_nonneg _
    calc (m j : ℝ) * (‖paperFT (testFn w k) (t j : ℝ)‖ ^ 2 +
          ‖paperFT (testFn w k) ((-(t j) : ℝ) : ℂ)‖ ^ 2)
        ≤ (m j : ℝ) * (4 * (K / t j ^ 2) + 4 * (K / t j ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add (hb1.trans ?_) (hb2.trans ?_)) hm
          · exact mul_le_mul_of_nonneg_left hk1 (by norm_num)
          · exact mul_le_mul_of_nonneg_left hk2 (by norm_num)
      _ = 4 * (m j : ℝ) * (2 * K / t j ^ 2) := by ring

/-- `Re(2w/(w² + t²)) = Re w (|w − it|⁻² + |w + it|⁻²)`. -/
theorem re_two_mul_div {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    (2 * w / (w ^ 2 + (t : ℂ) ^ 2)).re =
      w.re * (‖1 / (w - I * (t : ℂ))‖ ^ 2 + ‖1 / (w - I * ((-t : ℝ) : ℂ))‖ ^ 2) := by
  have h1 : w - I * (t : ℂ) ≠ 0 := WeilSpectral.sub_I_mul_ne_zero hw t
  have h2 : w - I * ((-t : ℝ) : ℂ) ≠ 0 := WeilSpectral.sub_I_mul_ne_zero hw (-t)
  have hsplit : 2 * w / (w ^ 2 + (t : ℂ) ^ 2) = 1 / (w - I * (t : ℂ)) + 1 / (w - I * ((-t : ℝ) : ℂ)) := by
    have hprod : (w - I * (t : ℂ)) * (w - I * ((-t : ℝ) : ℂ)) = w ^ 2 + (t : ℂ) ^ 2 := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    have hd : w ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by rw [← hprod]; exact mul_ne_zero h1 h2
    rw [← hprod, div_add_div _ _ h1 h2]
    congr 1
    push_cast
    ring
  rw [hsplit, Complex.add_re]
  have hr : ∀ u : ℝ, (1 / (w - I * (u : ℂ))).re = w.re * ‖1 / (w - I * (u : ℂ))‖ ^ 2 := by
    intro u
    rw [one_div, Complex.inv_re, norm_inv, inv_pow, Complex.sq_norm, re_sub_I_mul_ofReal]
    ring
  rw [hr, hr]
  ring

theorem norm_two_mul_div_le {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 1 ≤ t) :
    ‖2 * w / (w ^ 2 + (t : ℂ) ^ 2)‖ ≤ 2 * ‖w‖ * ((4 + 4 * w.im ^ 2 / w.re ^ 2) / t ^ 2) := by
  set K : ℝ := 4 + 4 * w.im ^ 2 / w.re ^ 2 with hK
  have h1 : w - I * (t : ℂ) ≠ 0 := WeilSpectral.sub_I_mul_ne_zero hw t
  have h2 : w - I * ((-t : ℝ) : ℂ) ≠ 0 := WeilSpectral.sub_I_mul_ne_zero hw (-t)
  have hprod : (w - I * (t : ℂ)) * (w - I * ((-t : ℝ) : ℂ)) = w ^ 2 + (t : ℂ) ^ 2 := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hk1 := inv_normSq_sub_le hw ht 1 (Or.inl rfl)
  have hk2 := inv_normSq_sub_le hw ht (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at hk1 hk2
  rw [← hK] at hk1 hk2
  have hK0 : 0 ≤ K / t ^ 2 := by rw [hK]; positivity
  have hp : ‖1 / (w - I * (t : ℂ))‖ * ‖1 / (w - I * ((-t : ℝ) : ℂ))‖ ≤ K / t ^ 2 := by
    have hsq : (‖1 / (w - I * (t : ℂ))‖ * ‖1 / (w - I * ((-t : ℝ) : ℂ))‖) ^ 2 ≤ (K / t ^ 2) ^ 2 := by
      rw [mul_pow, sq (K / t ^ 2)]
      exact mul_le_mul hk1 hk2 (by positivity) hK0
    exact (pow_le_pow_iff_left₀ (by positivity) hK0 two_ne_zero).mp hsq
  rw [← hprod, norm_div, norm_mul, norm_mul, Complex.norm_two]
  have e : 2 * ‖w‖ / (‖w - I * (t : ℂ)‖ * ‖w - I * ((-t : ℝ) : ℂ)‖) =
      2 * ‖w‖ * (‖1 / (w - I * (t : ℂ))‖ * ‖1 / (w - I * ((-t : ℝ) : ℂ))‖) := by
    rw [norm_div, norm_div, norm_one]
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hp (by positivity)

/-- **A converse of Weil's explicit formula.** -/
theorem converse_explicit_formula {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hform : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      weilFullFunctional lam (EF.weilTest f f) = (zeroSumForm m t f : ℂ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  -- Weil positivity
  have hW : WeilPositiveFull lam := fun f hf hfc => by
    rw [hform f hf hfc, Complex.ofReal_re]
    exact zeroSumForm_nonneg m t f
  set A : ℂ → ℂ := atomicPairSeries (fun j => Real.pi * m j) t with hA
  have hsumA : Summable fun j => |Real.pi * (m j : ℝ)| / t j ^ 2 := by
    refine (hsum.mul_left Real.pi).congr fun j => ?_
    rw [abs_of_nonneg (by positivity)]
    ring
  -- equality of real parts on `Re s > 1`
  have hre : ∀ s : ℂ, 1 < s.re → (weilFunction lam s).re = (A s).re := by
    intro s hs
    set w : ℂ := s - 1 / 2 with hwdef
    have hw0 : 0 < w.re := by rw [hwdef]; norm_num; linarith
    have hlim1 := tendsto_re_autoCorr hW hs
    have hlim2 := tendsto_zeroSumForm_testFn hone hsum hw0
    have hlim2' : Tendsto (fun k : ℕ => (weilFullFunctional lam (autoCorr w k)).re) atTop
        (𝓝 (∑' j, (m j : ℝ) * (‖1 / (w - I * (t j : ℂ))‖ ^ 2 +
          ‖1 / (w - I * ((-(t j) : ℝ) : ℂ))‖ ^ 2))) := by
      refine hlim2.congr fun k => ?_
      rw [autoCorr, hform _ (contDiff_testFn w k) (hasCompactSupport_testFn w k), Complex.ofReal_re]
    have heq := tendsto_nhds_unique hlim1 hlim2'
    -- the atomic series
    have hAre : (A s).re = w.re * ∑' j, (m j : ℝ) * (‖1 / (w - I * (t j : ℂ))‖ ^ 2 +
        ‖1 / (w - I * ((-(t j) : ℝ) : ℂ))‖ ^ 2) := by
      have hAeq : A s = ∑' j, ((m j : ℝ) : ℂ) * (2 * w / (w ^ 2 + (t j : ℂ) ^ 2)) := by
        rw [hA, atomicPairSeries, ← tsum_mul_left]
        refine tsum_congr fun j => ?_
        have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        rw [← hwdef]
        push_cast
        field_simp
      have hsumC : Summable fun j => ((m j : ℝ) : ℂ) * (2 * w / (w ^ 2 + (t j : ℂ) ^ 2)) := by
        refine Summable.of_norm_bounded
          ((hsum.mul_left (2 * ‖w‖ * (4 + 4 * w.im ^ 2 / w.re ^ 2)))) fun j => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := norm_two_mul_div_le hw0 (hone j)
        calc (m j : ℝ) * ‖2 * w / (w ^ 2 + (t j : ℂ) ^ 2)‖
            ≤ (m j : ℝ) * (2 * ‖w‖ * ((4 + 4 * w.im ^ 2 / w.re ^ 2) / t j ^ 2)) :=
              mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
          _ = 2 * ‖w‖ * (4 + 4 * w.im ^ 2 / w.re ^ 2) * ((m j : ℝ) / t j ^ 2) := by ring
      rw [hAeq, Complex.re_tsum hsumC, ← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [Complex.re_ofReal_mul, re_two_mul_div hw0]
      ring
    rw [hAre, ← heq, show (s - 1 / 2).re = w.re by rw [hwdef], mul_div_assoc',
      mul_div_cancel_left₀ _ hw0.ne']
  -- the difference is constant on `Re s > 1`
  set U : Set ℂ := {z | 1 < z.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ U := convex_halfSpace_re_gt 1
  have hAd := differentiableOn_atomicPairSeries hone hsumA
  have hgd : DifferentiableOn ℂ (fun z => weilFunction lam z - A z) U := by
    intro z hz
    have hz' : 1 < z.re := hz
    have hAz : DifferentiableAt ℂ A z := hAd.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        show 1 / 2 < z.re; linarith))
    exact ((differentiableAt_weilFunction hW hz').sub hAz).differentiableWithinAt
  have hgre : ∀ z ∈ U, (weilFunction lam z - A z).re = 0 := by
    intro z hz
    rw [Complex.sub_re, hre z hz, sub_self]
  have h2U : (2 : ℂ) ∈ U := by show 1 < (2 : ℂ).re; norm_num
  -- the constant is real at `s = 2`, hence zero
  have him : (weilFunction lam 2 - A 2).im = 0 := by
    have hL : (LSeries (lamC lam) 2).im = 0 := by
      rw [LSeries, Complex.im_tsum (summable_term_lamC hW (by norm_num))]
      refine (tsum_congr fun n => ?_).trans tsum_zero
      rw [LSeries.term_def]
      split_ifs with hn
      · simp
      · rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, lamC]
        rw [show ((n : ℂ) ^ 2) = (((n : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_div]
        exact Complex.ofReal_im _
    have hA2 : (A 2).im = 0 := by
      rw [hA, atomicPairSeries]
      have hreal : (∑' j, ((Real.pi * m j : ℝ) : ℂ) / ((2 - 1 / 2) ^ 2 + (t j : ℂ) ^ 2)) =
          ((∑' j, (Real.pi * m j) / ((3 / 2) ^ 2 + t j ^ 2) : ℝ) : ℂ) := by
        rw [Complex.ofReal_tsum]
        refine tsum_congr fun j => ?_
        push_cast
        ring
      rw [hreal]
      have : (2 * ((2 : ℂ) - 1 / 2) / (Real.pi : ℂ)) = ((2 * (3 / 2) / Real.pi : ℝ) : ℂ) := by
        push_cast
        ring
      rw [this, ← Complex.ofReal_mul, Complex.ofReal_im]
    rw [Complex.sub_im, hA2, weilFunction]
    simp only [Complex.sub_im, Complex.add_im, hL]
    rw [show (2 : ℂ) / 2 = 1 by norm_num, Complex.digamma_one]
    simp
  have hzero : weilFunction lam 2 - A 2 = 0 :=
    Complex.ext (by rw [hgre 2 h2U]; rfl) (by rw [him]; rfl)
  have hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s := by
    intro s hs
    have hc := eq_of_re_eq_zero hU hUc hgd hgre hs h2U
    rw [hzero, sub_eq_zero] at hc
    rw [← hA, ← hc, weilFunction, zetaArchimedeanDatum]
    have hfun : (fun n => if 2 ≤ n then (lam n : ℂ) else 0) = lamC lam := by
      funext n
      rw [lamC]
      split_ifs <;> simp
    rw [hfun]
  exact IntegerMassRigidity.integer_mass_rigidity hone hsum
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ) hid

end RHTower.WeilSpectral

end
