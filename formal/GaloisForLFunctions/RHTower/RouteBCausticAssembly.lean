/-
The dyadic caustic assembly, part I: pieces + the pointwise cover
(doc 87 App B, the (L3) base case).

The third-phase domain splits into finitely many pieces graded by the
distance of the squared center modulus `y(η) = ‖c + Ce^{iη}‖²` from the
two caustic values `y₊ = (ρ+‖B‖)²`, `y₋ = (ρ−‖B‖)²`:

* `coreSetM`/`coreSetP` — the caustic cores (√-law arm);
* `shellSetP σ`/`shellSetM σ` — dyadic shells at scale `σ = 2^j σ0`
  (transversal linear arm, margin from the inversion);
* `midSet` — the mid-annulus, distance ≥ G/3 from both caustics
  (linear arm at the top margin);
* everything else — EMPTY radial band (triangle lemmas).

`annulus_cover` is the pointwise disjunction: every `η ∈ [0, 2π]` lands in
a piece or its radial band is null.  `vol_K_le_shell` is the one arm
serving every shell AND the mid piece: distance `≥ σ` from both caustics
plus half-width control gives the linear law at margin
`min(σκ/2, 1/2)`, `κ = causticKappa`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBDyadicCore

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- The caustic margin rate: tangency margin per unit of squared-modulus
distance from the caustics. -/
noncomputable def causticKappa (ρ b : ℝ) : ℝ :=
  ((ρ + b) ^ 2 - (ρ - b) ^ 2) / (16 * ((ρ + b) ^ 2 * b ^ 2))

/-- Upper dyadic shell at scale `σ`: distance to the OUTER caustic in
`[σ, 2σ]`, distance to the inner caustic `≥ σ`. -/
def shellSetP (c C B : ℂ) (ρ σ : ℝ) : Set ℝ :=
  {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
    σ ≤ (ρ + ‖B‖) ^ 2 - ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∧
    (ρ + ‖B‖) ^ 2 - ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2
      ≤ 2 * σ ∧
    σ ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 - (ρ - ‖B‖) ^ 2}

/-- Lower dyadic shell at scale `σ`: distance to the INNER caustic in
`[σ, 2σ]`, distance to the outer caustic `≥ σ`. -/
def shellSetM (c C B : ℂ) (ρ σ : ℝ) : Set ℝ :=
  {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
    σ ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 - (ρ - ‖B‖) ^ 2 ∧
    ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 - (ρ - ‖B‖) ^ 2
      ≤ 2 * σ ∧
    σ ≤ (ρ + ‖B‖) ^ 2 - ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2}

/-- Outer caustic core: squared modulus within `σ` below `y₊`, up to the
reachability edge `(ρ+‖B‖+r)²`. -/
def coreSetP (c C B : ℂ) (ρ r σ : ℝ) : Set ℝ :=
  {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
    (ρ + ‖B‖) ^ 2 - σ ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∧
    ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ≤ (ρ + ‖B‖ + r) ^ 2}

/-- Inner caustic core: squared modulus within `σ` above `y₋`, down to the
reachability edge `(ρ−‖B‖−r)²`. -/
def coreSetM (c C B : ℂ) (ρ r σ : ℝ) : Set ℝ :=
  {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
    (ρ - ‖B‖ - r) ^ 2 ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∧
    ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ≤ (ρ - ‖B‖) ^ 2 + σ}

/-- The mid-annulus: distance ≥ G/3 from both caustics. -/
def midSet (c C B : ℂ) (ρ : ℝ) : Set ℝ :=
  {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
    ((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3
      ≤ (ρ + ‖B‖) ^ 2 - ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∧
    ((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3
      ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 - (ρ - ‖B‖) ^ 2}

section Measurability

variable (c C B : ℂ) (ρ r σ : ℝ)

private theorem continuous_ysq :
    Continuous fun η : ℝ =>
      ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 :=
  ((continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul continuous_const)))).norm).pow 2

theorem measurableSet_shellSetP : MeasurableSet (shellSetP c C B ρ σ) := by
  apply IsClosed.measurableSet
  have hy := continuous_ysq c C
  exact isClosed_Icc.inter
    ((isClosed_le continuous_const (continuous_const.sub hy)).inter
      ((isClosed_le (continuous_const.sub hy) continuous_const).inter
        (isClosed_le continuous_const (hy.sub continuous_const))))

theorem measurableSet_shellSetM : MeasurableSet (shellSetM c C B ρ σ) := by
  apply IsClosed.measurableSet
  have hy := continuous_ysq c C
  exact isClosed_Icc.inter
    ((isClosed_le continuous_const (hy.sub continuous_const)).inter
      ((isClosed_le (hy.sub continuous_const) continuous_const).inter
        (isClosed_le continuous_const (continuous_const.sub hy))))

private theorem measurableSet_ysq_band (lo hi : ℝ) :
    MeasurableSet
      {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
        lo ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∧
        ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ≤ hi} := by
  apply IsClosed.measurableSet
  have hy := continuous_ysq c C
  exact isClosed_Icc.inter
    ((isClosed_le continuous_const hy).inter
      (isClosed_le hy continuous_const))

theorem measurableSet_coreSetP : MeasurableSet (coreSetP c C B ρ r σ) := by
  change MeasurableSet
    {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
      (ρ + ‖B‖) ^ 2 - σ ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∧
      ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ≤ (ρ + ‖B‖ + r) ^ 2}
  exact measurableSet_ysq_band (c := c) (C := C) ((ρ + ‖B‖) ^ 2 - σ) ((ρ + ‖B‖ + r) ^ 2)

theorem measurableSet_coreSetM : MeasurableSet (coreSetM c C B ρ r σ) := by
  change MeasurableSet
    {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
      (ρ - ‖B‖ - r) ^ 2 ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∧
      ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ≤ (ρ - ‖B‖) ^ 2 + σ}
  exact measurableSet_ysq_band (c := c) (C := C) ((ρ - ‖B‖ - r) ^ 2) ((ρ - ‖B‖) ^ 2 + σ)

theorem measurableSet_midSet : MeasurableSet (midSet c C B ρ) := by
  apply IsClosed.measurableSet
  have hy := continuous_ysq c C
  exact isClosed_Icc.inter
    ((isClosed_le continuous_const (continuous_const.sub hy)).inter
      (isClosed_le continuous_const (hy.sub continuous_const)))

end Measurability

/-- **The unified shell/mid arm.**  Squared-modulus distance `≥ σ` from
BOTH caustics, with the half-width dominated by `σ·κ/2`, gives the linear
law at margin `min(σκ/2, 1/2)`. -/
theorem vol_K_le_shell {B c' : ℂ} {ρ r σ xmin Hbar : ℝ} (hB : B ≠ 0)
    (hρ : 0 ≤ ρ) (hr : 0 ≤ r) (hσ : 0 < σ) (hx0 : 0 < xmin)
    (hxm : xmin ≤ ‖c'‖) (hHb : bandHalf c' B ρ r ≤ Hbar)
    (hHσ : 2 * Hbar ≤ σ * causticKappa ρ ‖B‖)
    (hdp : σ ≤ (ρ + ‖B‖) ^ 2 - ‖c'‖ ^ 2)
    (hdm : σ ≤ ‖c'‖ ^ 2 - (ρ - ‖B‖) ^ 2) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c' + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
      ≤ ENNReal.ofReal (2 * Real.pi * (r * (2 * ρ + r))
          / (Real.sqrt (min (σ * causticKappa ρ ‖B‖ / 2) (1 / 2))
            * (xmin * ‖B‖))) := by
  have hc' : c' ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxm
    linarith
  have hb0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hσG : 2 * σ ≤ (ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2 := by linarith
  have hinv := one_sub_abs_bandCenter_of_dist hc' hB hσ hdp hdm hσG
  have hpb : (0 : ℝ) < ρ + ‖B‖ := by linarith
  have hκeq : σ * causticKappa ρ ‖B‖
      = σ * ((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2)
        / (16 * ((ρ + ‖B‖) ^ 2 * ‖B‖ ^ 2)) := by
    rw [causticKappa]
    ring
  have hκpos : (0 : ℝ) < σ * causticKappa ρ ‖B‖ := by
    rw [hκeq]
    have hGpos : (0 : ℝ) < (ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2 := by linarith
    positivity
  have hm : (0 : ℝ) < min (σ * causticKappa ρ ‖B‖ / 2) (1 / 2) :=
    lt_min (by linarith) (by norm_num)
  have hm1 : min (σ * causticKappa ρ ‖B‖ / 2) (1 / 2) ≤ 1 :=
    le_trans (min_le_right _ _) (by norm_num)
  have hmarg : min (σ * causticKappa ρ ‖B‖ / 2) (1 / 2)
      + bandHalf c' B ρ r ≤ 1 - |bandCenter c' B ρ| := by
    have h1 : min (σ * causticKappa ρ ‖B‖ / 2) (1 / 2)
        ≤ σ * causticKappa ρ ‖B‖ / 2 := min_le_left _ _
    have h2 : bandHalf c' B ρ r ≤ σ * causticKappa ρ ‖B‖ / 2 := by linarith
    have h3 : σ * causticKappa ρ ‖B‖
        ≤ 1 - |bandCenter c' B ρ| := by
      rw [hκeq]
      exact hinv
    linarith
  exact vol_K_le_of_margin hB hρ hr hm hm1 hx0 hxm hmarg

/-- **The pointwise cover.**  Every `η ∈ [0, 2π]` either has a NULL radial
band, or lies in a core, the mid-annulus, or a dyadic shell of scale
`2^j σ0` with `j < J`. -/
theorem annulus_cover {B C c : ℂ} {ρ r σ0 : ℝ} {J : ℕ} {η : ℝ}
    (hρB : ‖B‖ < ρ) (hr2 : 2 * r ≤ ρ - ‖B‖) (hσ0 : 0 < σ0)
    (hJ : ((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3 < 2 ^ J * σ0)
    (hη : η ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
          + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r} = 0
    ∨ η ∈ coreSetM c C B ρ r σ0 ∨ η ∈ coreSetP c C B ρ r σ0
    ∨ η ∈ midSet c C B ρ
    ∨ ∃ j < J, η ∈ shellSetP c C B ρ (2 ^ j * σ0)
        ∨ η ∈ shellSetM c C B ρ (2 ^ j * σ0) := by
  have hb0 : 0 ≤ ‖B‖ := norm_nonneg B
  have hx0 : 0 ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ := norm_nonneg _
  rcases lt_or_ge (ρ + r + ‖B‖)
      ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ with hbig | hle1
  · left
    rw [radial_band_empty_of_norm_large hbig]
    exact measure_empty
  rcases lt_or_ge (‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ + ‖B‖)
      (ρ - r) with hsm | hge1
  · left
    rw [radial_band_empty_of_norm_small hsm]
    exact measure_empty
  set x : ℝ := ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ with hxdef
  have hxlo : ρ - ‖B‖ - r ≤ x := by linarith
  have hxhi : x ≤ ρ + ‖B‖ + r := by linarith
  have hylo : (ρ - ‖B‖ - r) ^ 2 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxlo)
      (by linarith : (0 : ℝ) ≤ x + (ρ - ‖B‖ - r))]
  have hyhi : x ^ 2 ≤ (ρ + ‖B‖ + r) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxhi)
      (by linarith : (0 : ℝ) ≤ x + (ρ + ‖B‖ + r))]
  rcases le_or_gt (x ^ 2) ((ρ - ‖B‖) ^ 2 + σ0) with hcm | hcm
  · refine Or.inr (Or.inl ⟨hη, ?_, ?_⟩) <;> (rw [← hxdef]; linarith)
  rcases le_or_gt ((ρ + ‖B‖) ^ 2 - σ0) (x ^ 2) with hcp | hcp
  · refine Or.inr (Or.inr (Or.inl ⟨hη, ?_, ?_⟩)) <;> (rw [← hxdef]; linarith)
  set dp : ℝ := (ρ + ‖B‖) ^ 2 - x ^ 2 with hdpdef
  set dm : ℝ := x ^ 2 - (ρ - ‖B‖) ^ 2 with hdmdef
  have hdppos : σ0 < dp := by rw [hdpdef]; linarith
  have hdmpos : σ0 < dm := by rw [hdmdef]; linarith
  set d : ℝ := min dp dm with hddef
  have hd0 : σ0 < d := lt_min hdppos hdmpos
  have hdle1 : d ≤ dp := min_le_left _ _
  have hdle2 : d ≤ dm := min_le_right _ _
  rcases le_or_gt d (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3) with hdG | hdG
  · right; right; right; right
    have h1 : 1 ≤ d / σ0 := by
      rw [le_div_iff₀ hσ0]
      linarith
    have h2 : d / σ0 < 2 ^ J := by
      rw [div_lt_iff₀ hσ0]
      linarith
    obtain ⟨j, hjJ, hjle, hjlt⟩ := exists_dyadic_cover h1 h2
    have hσj : (2 : ℝ) ^ j * σ0 ≤ d := by
      rw [← le_div_iff₀ hσ0]
      exact hjle
    have hσj2 : d ≤ 2 * ((2 : ℝ) ^ j * σ0) := by
      have hlt := (div_lt_iff₀ hσ0).mp hjlt
      have hpow : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [hpow] at hlt
      linarith
    refine ⟨j, hjJ, ?_⟩
    rcases le_total dp dm with hside | hside
    · have hdd : d = dp := min_eq_left hside
      refine Or.inl ⟨hη, ?_, ?_, ?_⟩ <;> (rw [← hxdef]; linarith)
    · have hdd : d = dm := min_eq_right hside
      refine Or.inr ⟨hη, ?_, ?_, ?_⟩ <;> (rw [← hxdef]; linarith)
  · right; right; right; left
    refine ⟨hη, ?_, ?_⟩ <;> (rw [← hxdef]; linarith)

end Sublevel
end RHTower
