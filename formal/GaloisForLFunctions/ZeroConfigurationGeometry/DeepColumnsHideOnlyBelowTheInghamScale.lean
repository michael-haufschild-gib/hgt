import GaloisForLFunctions.ZeroConfigurationGeometry.EulerColumnsAreSeenJustAboveTheirPrime

/-!
# Deep columns hide only below the Ingham scale

Mimics need near-collisions below every `g > π/a` at every depth (`exists_near_pair_of_mimic_of_lt`),
and below every `g > π/(2a)` if shallow (`exists_near_pair_or_deep_of_mimic_at_ingham_scale`). Could
depth let a configuration hide at separations between the two? Euler-type columns are the natural
deep fakes. Here they are calibrated: depth buys them nothing.

Take the off-line FE-pair column `{½ ± δ + 2πik/L}` (any depth `0 < δ ≤ ½`) and the doubled on-line
column offset by half a spacing, `{½ + 2πi(k + ½)/L}` (`shiftedLatticeConfig`). Their union is
height-separated at `g = π/L` apart from FE partners.

* **The lag formula of the shifted column** (`W_shiftedLatticeConfig_lagFormula`). Its image is
  `L Σ_m k(mL) · 2(−1)^m`, `k = f ⋆ f̃`. The proof is Poisson summation after modulation by
  `e^{iπu/L}`. The off-line column has weights `2 cosh(δmL)`.
* **Mimicry exactly up to the Ingham scale** (`deepColumn_mimic_iff`). The two columns are mimics at
  aperture `a` exactly when `a ≤ L/2 = π/(2g)`. Below it only the lag `0` is seen and both images
  are `2L‖f‖²`. Above it the two-bump window at lag `L` reads `4L‖κ‖²(1 − cosh δL) < 0` from the
  deep column and `8L‖κ‖² > 0` from the shifted one.

So this deep configuration is resolved at the Ingham scale `π/(2a)`, as shallow ones are. It does not
hide in `(π/(2a), π/a]`.
-/

open MeasureTheory Complex Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 _root_.RHTower SquareRootThreshold

/-- The point `½ + 2πi(k + ½)/L` of the half-shifted column. -/
def shiftPoint (L : ℝ) (k : ℤ) : ℂ := verticalLatticePoint (2 * L) 0 (2 * k + 1)

theorem shiftPoint_injective {L : ℝ} (hL : 0 < L) : Function.Injective (shiftPoint L) := by
  intro j k h
  have := verticalLatticePoint_injective (by positivity : 0 < 2 * L) 0 h
  omega

/-- The doubled on-line column `{½ + 2πi(k + ½)/L}`, offset by half a spacing. -/
def shiftedLatticeConfig {L : ℝ} (hL : 0 < L) : ZeroConfig where
  carrier := Set.range (shiftPoint L)
  mult := fun _ => 2
  one_le_mult := fun _ _ => by norm_num
  strip := by
    rintro _ ⟨k, rfl⟩
    simp only [shiftPoint, verticalLatticePoint]
    norm_num
  reflect_mem := by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, by rw [shiftPoint, reflect_verticalLatticePoint, neg_zero]⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    refine ((onLineLatticeConfig (by positivity : 0 < 2 * L)).finite_window T₁ T₂).subset ?_
    rintro z ⟨⟨k, rfl⟩, h1, h2⟩
    exact ⟨⟨2 * k + 1, rfl⟩, h1, h2⟩

/-- Modulation by `e^{icu}` shifts the transform by `c`. -/
theorem paperFT_modulate (K : ℝ → ℂ) (c x : ℝ) :
    paperFT (fun u => K u * cexp (I * c * u)) x = paperFT K ((x + c : ℝ) : ℂ) := by
  rw [paperFT_def, paperFT_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem cexp_half_lattice (L : ℝ) (hL : 0 < L) (m : ℤ) :
    cexp (I * ((π / L : ℝ) : ℂ) * ((m * L : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : I * ((π / L : ℝ) : ℂ) * ((m * L : ℝ) : ℂ) = (m : ℂ) * (π * I) := by
    push_cast
    field_simp
  rw [e, Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- **The lag formula of the shifted column.** -/
theorem W_shiftedLatticeConfig_lagFormula {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (shiftedLatticeConfig hL).W f f =
      ((L : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * L) * (2 * (-1 : ℂ) ^ m) := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hs : tsupport f ⊆ Icc (-((2 * R) / 2)) ((2 * R) / 2) := fun u hu => by
    have := hR hu
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    rw [show 2 * R / 2 = R by ring]
    exact abs_le.mp this
  have hK := EF.weilTest_contDiff hf hf.continuous hfc
  have hKs := weilTest_abs_le hs hs
  -- the modulated kernel
  set K : ℝ → ℂ := EF.weilTest f f with hKdef
  set M : ℝ → ℂ := fun u => K u * cexp (I * ((π / L : ℝ) : ℂ) * u) with hM
  have hMc : ContDiff ℝ 2 M :=
    hK.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  have hMs : ∀ u, M u ≠ 0 → |u| ≤ 2 * R := fun u hu =>
    hKs u (fun h0 => hu (by rw [hM]; simp only; rw [h0, zero_mul]))
  have hP := hasSum_paperFT_lattice hL hMc hMs
  have hpt : ∀ k : ℤ, (shiftedLatticeConfig hL).Wsummand f f (shiftPoint L k) =
      2 * paperFT M ((k : ℝ) * (2 * π / L) : ℝ) := by
    intro k
    rw [shiftPoint, Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc,
      paperFT_modulate]
    simp only [shiftedLatticeConfig]
    congr 2
    push_cast
    field_simp
    ring
  have hsum : HasSum (fun ρ : Set.range (shiftPoint L) =>
      (shiftedLatticeConfig hL).Wsummand f f ρ)
      (2 * (L * ∑' m : ℤ, M (m * L))) := by
    rw [(shiftPoint_injective hL).hasSum_range_iff]
    exact (hP.mul_left 2).congr_fun fun k => by simp only [Function.comp_apply]; exact hpt k
  rw [ZeroConfig.W]
  have e1 : ∀ m : ℤ, M (m * L) = K (m * L) * (-1 : ℂ) ^ m := fun m => by
    rw [hM]
    simp only
    rw [← cexp_half_lattice L hL m]
  calc ∑' ρ : (shiftedLatticeConfig hL).carrier, (shiftedLatticeConfig hL).Wsummand f f ρ
      = 2 * (L * ∑' m : ℤ, M (m * L)) := hsum.tsum_eq
    _ = ((L : ℝ) : ℂ) * ∑' m : ℤ, K (m * L) * (2 * (-1 : ℂ) ^ m) := by
        have e2 : ∑' m : ℤ, K (m * L) * (2 * (-1 : ℂ) ^ m) =
            2 * ∑' m : ℤ, K (m * L) * (-1 : ℂ) ^ m := by
          rw [← tsum_mul_left]; exact tsum_congr fun m => by ring
        rw [tsum_congr e1, e2]
        ring

/-- **The deep column and the shifted column are mimics exactly up to the Ingham scale.** Their
union is height-separated at `g = π/L`, and they have the same image at aperture `a` exactly when
`a ≤ L/2 = π/(2g)`, whatever the depth `δ`. -/
theorem deepColumn_mimic_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (a : ℝ) :
    (∀ f, ApertureWindow a f →
      (offLineLatticeConfig hL hδ hδ').W f f = (shiftedLatticeConfig hL).W f f) ↔ a ≤ L / 2 := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨w, hw⟩ : ∃ w, w = min (a - L / 2) (L / 8) := ⟨_, rfl⟩
    have hw0 : 0 < w := by rw [hw]; exact lt_min (by linarith) (by positivity)
    have hwL : 4 * w < L := by have := min_le_right (a - L / 2) (L / 8); rw [hw]; linarith
    have hwa : ((1 : ℕ) : ℝ) * L / 2 + w ≤ a := by
      have := min_le_left (a - L / 2) (L / 8); rw [hw]; push_cast; linarith
    have hwin : ApertureWindow a (twoBump (modScaledBump w 0) ((1 : ℕ) * L) (-1)) :=
      ⟨contDiff_bumpTest (contDiff_modScaledBump_two w 0) _ _,
        (tsupport_twoBump_modScaledBump_subset hw0 (by positivity)).trans
          (Icc_subset_Icc (by linarith) hwa)⟩
    have h1 := h _ hwin
    rw [W_offLineLattice_lag_nat_mul hL hδ hδ' hw0 hwL le_rfl,
      W_lag_nat_mul_of_lagFormula (shiftedLatticeConfig hL) (fun m => 2 * (-1 : ℂ) ^ m)
        (W_shiftedLatticeConfig_lagFormula hL) hw0 hwL le_rfl] at h1
    have hκ := integral_norm_sq_modScaledBump_pos hw0
    have hc : 1 < Real.cosh (((1 : ℕ) : ℝ) * δ * L) :=
      Real.one_lt_cosh.mpr (by push_cast; positivity)
    have e : (2 * (2 * (-1 : ℂ) ^ (0 : ℤ)) - 2 * (-1 : ℂ) ^ (((1 : ℕ) : ℤ)) -
        2 * (-1 : ℂ) ^ (-((1 : ℕ) : ℤ))) = ((8 : ℝ) : ℂ) := by
      norm_num
    rw [e] at h1
    have h1' : ((4 * L * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) *
        (1 - Real.cosh (((1 : ℕ) : ℝ) * δ * L)) : ℝ) : ℂ) =
          ((L * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * 8 : ℝ) : ℂ) := by
      rw [h1]; push_cast; ring
    have h2 := Complex.ofReal_injective h1'
    have hneg : 4 * L * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) *
        (1 - Real.cosh (((1 : ℕ) : ℝ) * δ * L)) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (by linarith)
    have hpos : 0 < L * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * 8 := by positivity
    linarith
  · intro ha f hf
    have hs : tsupport f ⊆ Icc (-(L / 2)) (L / 2) := hf.2.trans (Icc_subset_Icc (by linarith) ha)
    rw [W_offLineLatticeConfig_of_le_nyquist hL hδ hδ' hf.1 hf.1.continuous hs hs,
      W_shiftedLatticeConfig_lagFormula hL f hf.1 hf.hasCompactSupport]
    have h := tsum_weilTest_lattice_eq hL hf.1 hf.1.continuous hs hs
      (fun m : ℤ => (-1 : ℂ) ^ m) (by simp)
    have e : ∑' m : ℤ, EF.weilTest f f (m * L) * (2 * (-1 : ℂ) ^ m) =
        2 * ∑' m : ℤ, EF.weilTest f f (m * L) * (-1 : ℂ) ^ m := by
      rw [← tsum_mul_left]; exact tsum_congr fun m => by ring
    rw [e, h]
    ring

end GaloisForLFunctions.ZeroConfigurationGeometry
