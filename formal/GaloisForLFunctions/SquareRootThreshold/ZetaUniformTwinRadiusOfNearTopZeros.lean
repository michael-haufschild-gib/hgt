import GaloisForLFunctions.SquareRootThreshold.ZetaTwinRadiusAtTheUncertaintyScale
import GaloisForLFunctions.RHTower.LorentzianZeroMass

/-!
# A uniform twin radius for near-top zeros of `ζ`

`ZetaTwinRadiusAtTheUncertaintyScale` gives the twin radius `73(κ + π log L + 4π)/V` with the depth
offset `κ = log(3 + e(|M| + W)/(60 L a_w²))`, in which `M = 2 Re S(0)` and `W = Σ_z |D(z)|` are the
mass terms of the family modulated to the height `γ₀` of a near-top zero. Here they are bounded
uniformly, so the radius depends on `w` and `γ₀` only.

**Mass** (`sum_mult_le_tsum_copies`, `sum_norm_lagCoeff_modScaledBump_le`,
`tsum_norm_evenCoeff_modScaledBump_le`, `abs_two_re_lagStructure_zero_le`). A zero at height `γ`
enters the modulated family with `|F_c| ≤ m (e^{w/2}B_w)²(1 + |γ − c|)^{−4} ≤ m (e^{w/2}B_w)²/(1 + (c − γ)²)`,
so `|M| ≤ W ≤ 2(e^{w/2}B_w)² Σ_ρ 1/(1 + (c − γ)²) ≤ 16(e^{w/2}B_w)²(C + log(c + 4))` by the
Lorentzian zero mass of the corpus (`RHTower.lorentzMass_le_log`, from `Re ξ'/ξ` on `Re s = 2`).

**Record heights** (`half_le_abs_im_of_norm_evenCoeff_modScaledBump_ge`). Once
`80 log(90γ₀)(e^{w/2}B_w)²/(1 + γ₀/2)⁴ < a_w²/(2e)`, a loud record has `|Im z*| ≥ γ₀/2`, so
`log(γ₀ + 4) ≤ L`; with `L ≥ 1` this makes `(|M| + W)/L` bounded and
`κ ≤ κ_w = log(3 + 32e(e^{w/2}B_w)²(C + 1)/(60a_w²))` (`uniformTwinDepth`,
`twinDepth_le_uniformTwinDepth`). From above, `|Im z*| ≤ Γ = recordHeightEnvelope w γ₀`, and the
record depth is at least `Re z₀/2` once `V Re z₀ ≥ 2 log(160 log(180Γ)(e^{w/2}B_w)²/a_w²)`.

**Uniform twin radius** (`zeta_uniform_twin_radius`). For a near-top zero at height `γ₀` (beyond an
explicit height depending on `w`), positivity of the modulated difference tests on `[0, V]`, with
`V ≥ 73(κ_w + π log log(180(Γ + 6)) + 4π) max(1, 4/Re z₀)`, forces a zero within
`73(κ_w + π log log(180(Γ + 6)) + 4π)/V` of `(Re z* − κ_w/V) + i Im z*`, where `Γ ≤ 2γ₀` for large
`γ₀`. Every constant is explicit in the width `w`: hiding at a near-top zero costs a twin at
distance `O_w((1 + log log γ₀)/V)`, uniformly in the zero.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Multiplicity-weighted sums and zero copies -/

/-- A multiplicity-weighted finite sum over zeros of `ζ` is at most the sum over all zero copies. -/
theorem sum_mult_le_tsum_copies (g : ℂ → ℝ) (hg : ∀ q : XiZeroCopy, 0 ≤ g (q.1 : ℂ))
    (hsum : Summable fun q : XiZeroCopy => g (q.1 : ℂ)) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier) :
    ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * g ρ ≤ ∑' q : XiZeroCopy, g (q.1 : ℂ) := by
  classical
  set d : S → XiDivisorSupport := fun ρ => xiDivisorZetaCarrierEquiv.symm ⟨ρ, hS ρ ρ.2⟩ with hd
  have hdv : ∀ ρ : S, ((d ρ : XiDivisorSupport) : ℂ) = ρ := fun ρ => rfl
  have hdm : ∀ ρ : S, (MeromorphicOn.divisor xi Set.univ ((d ρ : XiDivisorSupport) : ℂ)).toNat =
      zetaZeroConfig.mult ρ := fun ρ => by
    rw [xiDivisorZetaCarrierEquiv_multiplicity, hd]; simp only [Equiv.apply_symm_apply]
  have hinj : Function.Injective d := fun a b h => by
    have := congrArg (fun x : XiDivisorSupport => (x : ℂ)) h
    simp only [hdv] at this
    exact Subtype.ext this
  set W : Finset XiDivisorSupport := S.attach.image d with hW
  calc ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * g ρ
      = ∑ ρ ∈ S.attach, (zetaZeroConfig.mult ρ : ℝ) * g ρ := (Finset.sum_attach S _).symm
    _ = ∑ ρ ∈ S.attach, ((MeromorphicOn.divisor xi Set.univ ((d ρ : XiDivisorSupport) : ℂ)).toNat
          : ℝ) * g ((d ρ : XiDivisorSupport) : ℂ) :=
        Finset.sum_congr rfl fun ρ _ => by rw [hdm, hdv]
    _ = ∑ δ ∈ W, ((MeromorphicOn.divisor xi Set.univ (δ : ℂ)).toNat : ℝ) * g (δ : ℂ) := by
        rw [hW, Finset.sum_image fun a _ b _ h => hinj h]
    _ = ∑ q ∈ W.sigma (fun δ => (Finset.univ :
          Finset (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (δ : ℂ)))))),
          g ((q.1 : XiDivisorSupport) : ℂ) := by
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl fun δ _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑' q : XiZeroCopy, g (q.1 : ℂ) := hsum.sum_le_tsum _ (fun q _ => hg q)

/-! ### The mass of the modulated family -/

/-- `(1 + |x|)⁴ ≥ 1 + x²`. -/
theorem one_add_sq_le_one_add_abs_pow_four (x : ℝ) : 1 + x ^ 2 ≤ (1 + |x|) ^ 4 := by
  have h := abs_nonneg x
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + |x|) (le_refl _) 2,
    sq_nonneg (|x|), mul_nonneg h h, mul_nonneg (mul_nonneg h h) h]

/-- **The modulated coefficients have Lorentzian mass.** For the bump modulated to `c`, every finite
sum of `|F_c(z)|` is at most `(e^{w/2}B_w)² Σ_ρ 1/(1 + (c − γ)²)`. -/
theorem sum_norm_lagCoeff_modScaledBump_le {w : ℝ} (hw : 0 < w) (c : ℝ) (F : Finset ℂ) :
    ∑ z ∈ F, ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 * lorentzMass c := by
  classical
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  have hK0 : 0 ≤ K₀ := by positivity
  set g : ℂ → ℝ := fun ρ => K₀ * (1 / (1 + (c - ρ.im) ^ 2)) with hg
  set F' := F.filter fun z => (1 / 2 + z) ∈ zetaZeroConfig.carrier with hF'
  have hshift : Function.Injective fun z : ℂ => 1 / 2 + z := fun a b h => by simpa using h
  have h1 : ∑ z ∈ F, ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      ∑ z ∈ F', (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * g (1 / 2 + z) := by
    rw [hF', Finset.sum_filter]
    refine Finset.sum_le_sum fun z _ => ?_
    split_ifs with hc
    · refine (norm_lagCoeff_modScaledBump_le zetaZeroConfig hw c hc).trans ?_
      have him : (1 / 2 + z).im = z.im := by simp
      show _ ≤ (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * (K₀ * (1 / (1 + (c - (1 / 2 + z).im) ^ 2)))
      rw [him, hK₀]
      have hpos : 0 < 1 + (c - z.im) ^ 2 := by positivity
      have hle : 1 + (c - z.im) ^ 2 ≤ (1 + |z.im - c|) ^ 4 := by
        have := one_add_sq_le_one_add_abs_pow_four (z.im - c)
        rwa [show (z.im - c) ^ 2 = (c - z.im) ^ 2 by ring] at this
      have : 1 / (1 + |z.im - c|) ^ 4 ≤ 1 / (1 + (c - z.im) ^ 2) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hle
      calc (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * K₀ / (1 + |z.im - c|) ^ 4
          = (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * K₀ * (1 / (1 + |z.im - c|) ^ 4) := by ring
        _ ≤ (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * K₀ * (1 / (1 + (c - z.im) ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    · rw [lagCoeff, Set.indicator_of_notMem hc, norm_zero]
  have h2 : ∑ z ∈ F', (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * g (1 / 2 + z) =
      ∑ ρ ∈ F'.image (fun z => 1 / 2 + z), (zetaZeroConfig.mult ρ : ℝ) * g ρ :=
    (Finset.sum_image (f := fun ρ => (zetaZeroConfig.mult ρ : ℝ) * g ρ)
      fun a _ b _ h => hshift h).symm
  have hgq : ∀ q : XiZeroCopy, 0 ≤ g (q.1 : ℂ) := fun q => by rw [hg]; positivity
  have hsg : Summable fun q : XiZeroCopy => g (q.1 : ℂ) :=
    ((summable_lorentzMassTerm c).mul_left K₀).congr fun q => by
      simp only [hg, lorentzMassTerm]
  have h3 := sum_mult_le_tsum_copies g hgq hsg (F'.image fun z => 1 / 2 + z) fun ρ hρ => by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hρ
    exact (Finset.mem_filter.mp hz).2
  have h4 : ∑' q : XiZeroCopy, g (q.1 : ℂ) = K₀ * lorentzMass c := by
    rw [lorentzMass, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    simp only [hg, lorentzMassTerm]
  linarith

/-- **The total mass of the modulated family is logarithmic.**
`W_c = Σ_z |D_c(z)| ≤ 2(e^{w/2}B_w)² Σ_ρ 1/(1 + (c − γ)²) ≤ 16(e^{w/2}B_w)²(C + log(|c| + 4))`,
`C = xiLineTwoLogDerivConstant`. -/
theorem tsum_norm_evenCoeff_modScaledBump_le {w : ℝ} (hw : 0 < w) (c : ℝ) :
    ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      16 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
        (xiLineTwoLogDerivConstant + Real.log (|c| + 4)) := by
  classical
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  have hK0 : 0 ≤ K₀ := by positivity
  have hfin : ∀ F : Finset ℂ, ∑ z ∈ F, ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      2 * K₀ * lorentzMass c := fun F => by
    have hconj : Function.Injective fun z : ℂ => conj z := star_injective
    calc ∑ z ∈ F, ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖
        ≤ ∑ z ∈ F, (‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ +
            ‖lagCoeff zetaZeroConfig (modScaledBump w c) (conj z)‖) :=
          Finset.sum_le_sum fun z _ => by
            rw [evenCoeff]; exact (norm_add_le _ _).trans (le_of_eq (by rw [Complex.norm_conj]))
      _ = ∑ z ∈ F, ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ +
            ∑ z ∈ F.image (fun z => conj z), ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ := by
          rw [Finset.sum_add_distrib, Finset.sum_image fun a _ b _ h => hconj h]
      _ ≤ K₀ * lorentzMass c + K₀ * lorentzMass c :=
          add_le_add (sum_norm_lagCoeff_modScaledBump_le hw c F)
            (sum_norm_lagCoeff_modScaledBump_le hw c _)
      _ = 2 * K₀ * lorentzMass c := by ring
  refine (tsum_le_of_sum_le' (mul_nonneg (by positivity)
    (tsum_nonneg (lorentzMassTerm_nonneg c))) hfin).trans ?_
  have := lorentzMass_le_log c
  calc 2 * K₀ * lorentzMass c ≤ 2 * K₀ * (8 * (xiLineTwoLogDerivConstant + Real.log (|c| + 4))) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- `|2 Re S(0)| ≤ Σ_z |D(z)|`. -/
theorem abs_two_re_lagStructure_zero_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) :
    |2 * (lagStructure Z b 0).re| ≤ ∑' z : ℂ, ‖evenCoeff Z b z‖ := by
  have h := two_re_lagStructure_eq Z hZ hb hbs 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h.2]
  exact norm_tsum_le_tsum_norm h.1.norm

/-- Coefficients of the modulated family are at most `80 log(180|Im z|)(e^{w/2}B_w)²`. -/
theorem norm_evenCoeff_modScaledBump_le_log {w : ℝ} (hw : 0 < w) (c : ℝ) {z : ℂ}
    (hz : evenCoeff zetaZeroConfig (modScaledBump w c) z ≠ 0) :
    ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      80 * Real.log (180 * |z.im|) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := by
  have h := norm_evenCoeff_modScaledBump_le hw c hz
  have h4 := four_le_abs_im_of_evenCoeff_zeta hz
  have hL : 0 ≤ Real.log (180 * |z.im|) := Real.log_nonneg (by linarith)
  have h1 : 1 / (1 + |z.im - c|) ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by linarith [abs_nonneg (z.im - c)])
  have h2 : 1 / (1 + |z.im + c|) ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by linarith [abs_nonneg (z.im + c)])
  refine h.trans ?_
  calc 40 * Real.log (180 * |z.im|) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
        (1 / (1 + |z.im - c|) ^ 4 + 1 / (1 + |z.im + c|) ^ 4)
      ≤ 40 * Real.log (180 * |z.im|) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- **Loud coefficients sit near `±c`.** For `c > 0`, an exponent with `|D_c(z)| ≥ ε` and
`80 log(90c)(e^{w/2}B_w)²/(1 + c/2)⁴ < ε` has `|Im z| ≥ c/2`. -/
theorem half_le_abs_im_of_norm_evenCoeff_modScaledBump_ge {w c ε : ℝ} (hw : 0 < w) (hc : 0 < c)
    {z : ℂ} (hz : evenCoeff zetaZeroConfig (modScaledBump w c) z ≠ 0)
    (hge : ε ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖)
    (hsmall : 80 * Real.log (90 * c) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
      (1 + c / 2) ^ 4 < ε) :
    c / 2 ≤ |z.im| := by
  by_contra hy; push Not at hy
  set y := |z.im| with hydef
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  have hK0 : 0 ≤ K₀ := by positivity
  have h4 : 4 ≤ y := four_le_abs_im_of_evenCoeff_zeta hz
  have hd1 : c / 2 ≤ |z.im - c| := by
    have := abs_sub_abs_le_abs_sub c z.im
    rw [abs_of_pos hc, abs_sub_comm] at this; linarith
  have hd2 : c / 2 ≤ |z.im + c| := by
    have := abs_sub_abs_le_abs_sub c (-z.im)
    rw [abs_of_pos hc, abs_neg, sub_neg_eq_add, add_comm] at this; linarith
  have hb := norm_evenCoeff_modScaledBump_le hw c hz
  rw [← hydef, ← hK₀] at hb
  have hq : (0 : ℝ) < (1 + c / 2) ^ 4 := by positivity
  have hi1 : 1 / (1 + |z.im - c|) ^ 4 ≤ 1 / (1 + c / 2) ^ 4 :=
    div_le_div_of_nonneg_left (by norm_num) hq (pow_le_pow_left₀ (by positivity) (by linarith) 4)
  have hi2 : 1 / (1 + |z.im + c|) ^ 4 ≤ 1 / (1 + c / 2) ^ 4 :=
    div_le_div_of_nonneg_left (by norm_num) hq (pow_le_pow_left₀ (by positivity) (by linarith) 4)
  have hlog : Real.log (180 * y) ≤ Real.log (90 * c) :=
    Real.log_le_log (by linarith) (by linarith)
  have hL0 : 0 ≤ Real.log (180 * y) := Real.log_nonneg (by linarith)
  have hL90 : 0 ≤ Real.log (90 * c) := Real.log_nonneg (by linarith)
  have : ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      80 * Real.log (90 * c) * K₀ / (1 + c / 2) ^ 4 := by
    refine hb.trans ?_
    calc 40 * Real.log (180 * y) * K₀ * (1 / (1 + |z.im - c|) ^ 4 + 1 / (1 + |z.im + c|) ^ 4)
        ≤ 40 * Real.log (90 * c) * K₀ * (1 / (1 + c / 2) ^ 4 + 1 / (1 + c / 2) ^ 4) := by
          gcongr
      _ = _ := by ring
  linarith

/-! ### The uniform twin radius -/

/-- The uniform depth offset `κ_w = log(3 + 32e(e^{w/2}B_w)²(C + 1)/(60a_w²))`. -/
def uniformTwinDepth (w : ℝ) : ℝ :=
  Real.log (3 + Real.exp 1 * (32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
    (xiLineTwoLogDerivConstant + 1)) / (60 * centerAmplitude w ^ 2))

/-- The height envelope `Γ_w(γ₀) = max(2γ₀, (2880 · 80(e^{w/2}B_w)² · 2e/a_w²)^{1/3})` of the loud
records of the family modulated to `γ₀`. -/
def recordHeightEnvelope (w γ₀ : ℝ) : ℝ :=
  max (2 * γ₀) ((2880 * (80 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
    (centerAmplitude w ^ 2 / (2 * Real.exp 1)))) ^ ((1 : ℝ) / 3))

theorem twinDepth_le_uniformTwinDepth {w M W L c : ℝ} (hw : 0 < w) (hMW : |M| ≤ W)
    (hW : W ≤ 16 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log (|c| + 4)))
    (hcL : Real.log (|c| + 4) ≤ L) (hL : 1 ≤ L) :
    twinDepth M W L (centerAmplitude w) ≤ uniformTwinDepth w := by
  unfold twinDepth uniformTwinDepth
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set C := xiLineTwoLogDerivConstant with hC
  set a := centerAmplitude w with ha
  have hC0 : 0 ≤ C := xiLineTwoLogDerivConstant_nonneg
  have hK0 : 0 ≤ K₀ := by positivity
  have ha0 : 0 < a := centerAmplitude_pos hw
  have hW0 : 0 ≤ W := (abs_nonneg M).trans hMW
  have hE := Real.exp_pos 1
  refine Real.log_le_log (by positivity) (add_le_add_right ?_ 3)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |M| + W ≤ 32 * K₀ * (C + L) := by
    have : 16 * K₀ * (C + Real.log (|c| + 4)) ≤ 16 * K₀ * (C + L) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have h2 : C + L ≤ (C + 1) * L := by nlinarith
  have h3 : |M| + W ≤ 32 * K₀ * ((C + 1) * L) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ Real.exp 1 * (60 * a ^ 2) by positivity)
  nlinarith

/-- **The uniform twin radius of near-top zeros of `ζ`.** Fix `w > 0` and let `½ + z₀` be a zero right
of the line at height `γ₀ = Im z₀ > 0` with
`40 log(180γ₀)(e^{w/2}B_w)²(1 + 2γ₀)^{−4} ≤ a_w²/2` and `80 log(90γ₀)(e^{w/2}B_w)²/(1 + γ₀/2)⁴ < a_w²/(2e)`,
`1/V`-near the top of the family modulated to `γ₀`. Put `Γ = recordHeightEnvelope w γ₀`,
`ℓ = log log(180(Γ + 6))`, `κ_w = uniformTwinDepth w`, `R = 73(κ_w + πℓ + 4π)`, and let
`V ≥ R max(1, 4/Re z₀)` and `V Re z₀ ≥ 2 log(160 log(180Γ)(e^{w/2}B_w)²/a_w²)`. If the modulated
difference tests are Weil nonnegative on `[0, V]`, then the Legendre record `z*` at lag `V`, which has
`Re z* ≥ Re z₀/2`, `γ₀/2 ≤ |Im z*| ≤ Γ` and `|D(z*)| ≥ a_w²/(2e)`, has a twin: another zero within `R/V` of
`(Re z* − κ_w/V) + i Im z*`. -/
theorem zeta_uniform_twin_radius {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re) (him₀ : 0 < z₀.im)
    (hΓ : 40 * Real.log (180 * z₀.im) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
      (1 + 2 * z₀.im) ^ 4 ≤ centerAmplitude w ^ 2 / 2)
    (hsmall : 80 * Real.log (90 * z₀.im) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
      (1 + z₀.im / 2) ^ 4 < centerAmplitude w ^ 2 / (2 * Real.exp 1))
    (htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → z.re ≤ z₀.re + 1 / V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re)
    (hV1 : 73 * (uniformTwinDepth w +
        π * Real.log (Real.log (180 * (recordHeightEnvelope w z₀.im + 6))) + 4 * π) *
        max 1 (4 / z₀.re) ≤ V)
    (hV2 : 2 * Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) ≤ z₀.re * V) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      z₀.im / 2 ≤ |z₁.im| ∧ |z₁.im| ≤ recordHeightEnvelope w z₀.im ∧
      centerAmplitude w ^ 2 / (2 * Real.exp 1) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ ∧
      (∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V)) ∧
      ∃ z, z ≠ z₁ ∧ evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
        ‖z - ((z₁.re - uniformTwinDepth w / V : ℝ) + z₁.im * I)‖ <
          73 * (uniformTwinDepth w +
            π * Real.log (Real.log (180 * (recordHeightEnvelope w z₀.im + 6))) + 4 * π) / V := by
  obtain ⟨z₁, hz₁, hre₁, hD₁, hrec, htwin⟩ :=
    zeta_near_top_twin_radius_log_log hw hV hz₀ hre₀ him₀ hΓ htop hm
  suffices H : z₀.re / 2 ≤ z₁.re ∧ z₀.im / 2 ≤ |z₁.im| ∧ |z₁.im| ≤ recordHeightEnvelope w z₀.im ∧
      ∃ z, z ≠ z₁ ∧ evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
        ‖z - ((z₁.re - uniformTwinDepth w / V : ℝ) + z₁.im * I)‖ <
          73 * (uniformTwinDepth w +
            π * Real.log (Real.log (180 * (recordHeightEnvelope w z₀.im + 6))) + 4 * π) / V by
    obtain ⟨h1, h2, h3, h4⟩ := H
    exact ⟨z₁, hz₁, h1, h2, h3, hD₁, hrec, h4⟩
  set b := modScaledBump w z₀.im with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set a := centerAmplitude w with ha
  set Γ := recordHeightEnvelope w z₀.im with hΓdef
  set κ := uniformTwinDepth w with hκ
  have ha0 : 0 < a := centerAmplitude_pos hw
  have hK0 : 0 ≤ K₀ := by positivity
  have hε : 0 < a ^ 2 / (2 * Real.exp 1) := by positivity
  -- the record sits at height between `γ₀/2` and `Γ`
  have hup : |z₁.im| ≤ Γ := abs_im_le_of_norm_evenCoeff_modScaledBump_ge hw him₀.le hε hz₁ hD₁
  have hlow : z₀.im / 2 ≤ |z₁.im| :=
    half_le_abs_im_of_norm_evenCoeff_modScaledBump_ge hw him₀ hz₁ hD₁ hsmall
  have h4 : 4 ≤ |z₁.im| := four_le_abs_im_of_evenCoeff_zeta hz₁
  set L := Real.log (180 * (|z₁.im| + 6)) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    nlinarith [abs_nonneg z₁.im]
  have hcL : Real.log (|z₀.im| + 4) ≤ L := by
    rw [abs_of_pos him₀]
    exact Real.log_le_log (by positivity) (by linarith)
  -- the depth offset is uniform
  have hW := tsum_norm_evenCoeff_modScaledBump_le hw z₀.im
  have hMW := abs_two_re_lagStructure_zero_le zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w z₀.im) (modScaledBump_support hw z₀.im)
  have hκd := twinDepth_le_uniformTwinDepth hw hMW hW hcL hL1
  -- the record is at depth at least `Re z₀/2`
  have hD₀ : a ^ 2 / 2 ≤ ‖D z₀‖ := by
    have := norm_evenCoeff_modScaledBump_center_ge hw hz₀ hre₀ him₀
    rw [show 4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)) = a from rfl] at this
    linarith
  have hD₀ne : D z₀ ≠ 0 := fun h => by rw [h, norm_zero] at hD₀; nlinarith
  have hDmax : ‖D z₁‖ ≤ 80 * Real.log (180 * Γ) * K₀ := by
    refine (norm_evenCoeff_modScaledBump_le_log hw z₀.im hz₁).trans ?_
    have : Real.log (180 * |z₁.im|) ≤ Real.log (180 * Γ) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) hK0
  have hre : z₀.re / 2 ≤ z₁.re := by
    have h1 := hrec z₀ hD₀ne hre₀
    have hD1pos : 0 < ‖D z₁‖ := norm_pos_iff.mpr hz₁
    have hq : 0 < 160 * Real.log (180 * Γ) * K₀ / a ^ 2 := by
      have : 0 < 80 * Real.log (180 * Γ) * K₀ := lt_of_lt_of_le hD1pos hDmax
      have : 0 < 160 * Real.log (180 * Γ) * K₀ := by linarith
      positivity
    have h2 : Real.exp ((z₀.re - z₁.re) * V) ≤ 160 * Real.log (180 * Γ) * K₀ / a ^ 2 := by
      have hE0 := Real.exp_pos (z₀.re * V)
      have hE1 := Real.exp_pos (z₁.re * V)
      have e : Real.exp ((z₀.re - z₁.re) * V) = Real.exp (z₀.re * V) / Real.exp (z₁.re * V) := by
        rw [← Real.exp_sub]; ring_nf
      rw [e, div_le_iff₀ hE1]
      have : a ^ 2 / 2 * Real.exp (z₀.re * V) ≤ 80 * Real.log (180 * Γ) * K₀ * Real.exp (z₁.re * V) :=
        calc a ^ 2 / 2 * Real.exp (z₀.re * V) ≤ ‖D z₀‖ * Real.exp (z₀.re * V) :=
              mul_le_mul_of_nonneg_right hD₀ hE0.le
          _ ≤ ‖D z₁‖ * Real.exp (z₁.re * V) := h1
          _ ≤ _ := mul_le_mul_of_nonneg_right hDmax hE1.le
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h3 := Real.log_le_log (Real.exp_pos _) h2
    rw [Real.log_exp] at h3
    nlinarith
  -- the lag conditions in terms of the record
  set ℓ₀ := Real.log (Real.log (180 * (Γ + 6))) with hℓ₀
  have hℓ : Real.log L ≤ ℓ₀ := by
    rw [hℓ₀]
    refine Real.log_le_log (by linarith) (Real.log_le_log (by positivity) (by linarith))
  have hmax : max 1 (2 / z₁.re) ≤ max 1 (4 / z₀.re) := by
    refine max_le_max le_rfl ?_
    rw [div_le_div_iff₀ hre₁ hre₀]; linarith
  have hR0 : 0 ≤ κ + π * Real.log L + 4 * π := by
    have := Real.log_nonneg hL1
    have : 0 ≤ κ := le_trans (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))
      (le_trans (log_three_le_twinDepth ((abs_nonneg _).trans hMW) (by linarith) ha0) hκd)
    positivity
  have hVk : 73 * (κ + π * Real.log L + 4 * π) * max 1 (2 / z₁.re) ≤ V := by
    refine le_trans ?_ hV1
    have h1 : κ + π * Real.log L + 4 * π ≤ κ + π * ℓ₀ + 4 * π := by
      have := mul_le_mul_of_nonneg_left hℓ Real.pi_pos.le; linarith
    exact mul_le_mul (by linarith) hmax (le_trans zero_le_one (le_max_left _ _)) (by linarith)
  obtain ⟨z, hz, hDz, hdist⟩ := htwin κ hκd hVk
  refine ⟨hre, hlow, hup, z, hz, hDz, lt_of_lt_of_le hdist (div_le_div_of_nonneg_right ?_ hV.le)⟩
  have := mul_le_mul_of_nonneg_left hℓ Real.pi_pos.le
  linarith

end GaloisForLFunctions.SquareRootThreshold
