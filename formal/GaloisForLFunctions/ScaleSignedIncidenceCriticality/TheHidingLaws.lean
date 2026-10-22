import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLaw
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheApertureCertificateIsBlindInEveryUnit
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.SquareRootThreshold.IsolatedPairInArbitraryBackground
import GaloisForLFunctions.SquareRootThreshold.DilutedOffLineLatticeHidingLaw

/-!
# The hiding laws

What must an off-line configuration spend to stay invisible to a certificate? This module collects
the exact prices.

* **Hiding needs a crystal.** A single off-line pair in an arbitrary background cannot hold the
  floor: an isolated pair in mass `M` over height `v` forces `δ ≤ arsinh(M/|Q| + 1)/v`
  (`depth_le_of_isolatedPair_floor`). Only an infinite off-line lattice sustains the floors.
* **Mass buys aperture, exponentially.** For a diluted lattice of spacing `ℓ` inside on-line mass
  `L`, invisibility at aperture `a` costs `ℓ e^{δ(2a − ℓ)} ≤ 2L + 2a + ℓ`
  (`massApertureExchange`), so the aperture reach of a structured counterexample is
  `a ≤ log((3L + ℓ)/ℓ)/(2δ) + ℓ/2` (`reach_upper`) — logarithmic in the mass it hires.
* **Aliasing is free below Nyquist, and exactly there.** Inside any background, a sub-lattice of
  spacing `ℓ` is invisible to every aperture below `ℓ/2` at no cost (`aliasing_is_free`), and the
  free regime ends exactly at `ℓ/2`: at and above it the ground energy turns negative
  (`latticeFloor_neg_of_two_le`).

Together these say the floors of `TheApertureCertificateIsBlindInEveryUnit` are not cheap tricks:
a counterexample that defeats a certificate of aperture `a` must be an infinite crystal, and must
pay either an exponential amount of on-line mass or a spacing above twice the aperture. That is the
quantitative content the sign readings hide, and the magnitudes of
`TwoAliasingBandsDetermineTheDepth` are what expose it.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold
open Zeta23 _root_.RHTower

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

-- from TheFloorsRequireAnOffLineCrystal.lean
/-! ### 1. Positivity forces mass -/

/-- **Positivity at a finite aperture forces local on-line mass.** For a configuration with a
single simple off-line pair, hiding depth `δ` up to lag `v` costs mass `|Q| (sinh (δ v) − 1)`. -/
theorem onLineMass_ge_of_aperturePositivity (Z : ZeroConfig) (hZ : TemperedConfig Z) {δ γ₀ : ℝ}
    (hδ : 0 < δ) (hp : heightPoint δ γ₀ ∈ Z.carrier) (hm : heightPoint (-δ) γ₀ ∈ Z.carrier)
    (hmp : Z.mult (heightPoint δ γ₀) = 1) (hmm : Z.mult (heightPoint (-δ) γ₀) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = heightPoint δ γ₀ ∨ ρ = heightPoint (-δ) γ₀)
    {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) {w : ℝ} (hβs : ∀ u, β u ≠ 0 → |u| ≤ w) {v : ℝ}
    (hv : 0 ≤ v)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) →
      0 ≤ (Z.W f f).re) :
    ‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖ * (Real.sinh (δ * v) - 1) ≤
      onLineMass Z β γ₀ := by
  by_contra hlt
  obtain ⟨f, hf, hfs, hneg⟩ :=
    isolatedPair_visible Z hZ hδ hp hm hmp hmm hon hβ hβs hv (not_le.mp hlt)
  exact absurd (hpos f hf hfs) (not_le.mpr hneg)

/-! ### 2. The depth bound -/

/-- **A finite aperture bounds the depth of a sparse off-line set.** The bound is logarithmic in
the local on-line mass. -/
theorem depth_le_of_aperturePositivity_of_mass (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {δ γ₀ : ℝ} (hδ : 0 < δ) (hp : heightPoint δ γ₀ ∈ Z.carrier)
    (hm : heightPoint (-δ) γ₀ ∈ Z.carrier) (hmp : Z.mult (heightPoint δ γ₀) = 1)
    (hmm : Z.mult (heightPoint (-δ) γ₀) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = heightPoint δ γ₀ ∨ ρ = heightPoint (-δ) γ₀)
    {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) {w : ℝ} (hβs : ∀ u, β u ≠ 0 → |u| ≤ w) {v : ℝ}
    (hv : 0 < v)
    (hQ : 0 < ‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) →
      0 ≤ (Z.W f f).re) :
    δ ≤ Real.arsinh (onLineMass Z β γ₀ /
      (‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖) + 1) / v := by
  have hmass := onLineMass_ge_of_aperturePositivity Z hZ hδ hp hm hmp hmm hon hβ hβs hv.le hpos
  have h1 : Real.sinh (δ * v) - 1 ≤
      onLineMass Z β γ₀ / (‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖) := by
    rw [le_div_iff₀ hQ]
    linarith [hmass]
  have hsinh : Real.sinh (δ * v) ≤
      onLineMass Z β γ₀ / (‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖) + 1 := by
    linarith
  have hbound := (Real.sinh_le_sinh (x := δ * v)
      (y := Real.arsinh (onLineMass Z β γ₀ /
        (‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖) + 1))).mp
    (by rw [Real.sinh_arsinh]; exact hsinh)
  rw [le_div_iff₀ hv]
  linarith [hbound]

/-! ### 3. The floors are about crystals -/

/-- **The floors require a crystal.** At every aperture and every coercivity level there is a
width-`½` configuration passing the certificate — but each such witness has *all* of its zeros off
the line. For a configuration with a single off-line pair the same certificate bounds the depth by
the logarithm of the local mass, so the trivial floors are statements about off-line crystals and
not about sparse off-line sets. -/
theorem theFloorsRequireACrystal {a η : ℝ} (ha : 0 < a) :
    (∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain a η Z) ∧
      ∀ (Z : ZeroConfig), TemperedConfig Z → ∀ δ γ₀ : ℝ, 0 < δ →
        heightPoint δ γ₀ ∈ Z.carrier → heightPoint (-δ) γ₀ ∈ Z.carrier →
        Z.mult (heightPoint δ γ₀) = 1 → Z.mult (heightPoint (-δ) γ₀) = 1 →
        (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = heightPoint δ γ₀ ∨ ρ = heightPoint (-δ) γ₀) →
        ∀ (β : ℝ → ℂ), ContDiff ℝ 2 β → ∀ w : ℝ, (∀ u, β u ≠ 0 → |u| ≤ w) → ∀ v : ℝ, 0 < v →
        0 < ‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖ →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) →
          0 ≤ (Z.W f f).re) →
        δ ≤ Real.arsinh (onLineMass Z β γ₀ /
          (‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖) + 1) / v :=
  ⟨exists_width_eq_half_apertureGain ha η,
    fun Z hZ _ _ hδ hp hm hmp hmm hon _ hβ _ hβs _ hv hQ hpos =>
      depth_le_of_aperturePositivity_of_mass Z hZ hδ hp hm hmp hmm hon hβ hβs hv hQ hpos⟩

-- from TheMassApertureExchangeLaw.lean
/-! ### 1. Positivity of a diluted lattice forces exponential mass -/

/-- **The exchange law.** If the diluted configuration — an off-line sub-lattice of spacing
parameter `ℓ` and depth `δ` inside an on-line background of mass `2L` — is Weil-positive at
aperture `a`, then the mass is at least exponential in `δa`. -/
theorem mass_ge_of_dilutedLattice_positive {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (ha : 0 < a) (haL : a ≤ L / 2)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) :
    ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 2 * L + 2 * a + ℓ := by
  have hcover := (dilutedLattice_weil_nonneg_iff hℓ hL hδ hδ' ha haL).mp hpos
  have hdeep := (latticeFloor_aperture_bounds hℓ hδ ha).2
  linarith

/-- **A mass budget caps the aperture at which an off-line sub-lattice can hide.** -/
theorem aperture_le_of_mass_bound {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (ha : 0 < a) (haL : a ≤ L / 2)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) :
    Real.exp (δ * (2 * a - ℓ)) ≤ (2 * L + 2 * a + ℓ) / ℓ := by
  rw [le_div_iff₀ hℓ]
  have := mass_ge_of_dilutedLattice_positive hℓ hL hδ hδ' ha haL hpos
  linarith

/-! ### 2. The floors need exponential mass -/

/-- **The floors need exponentially growing mass.** At every aperture and level there is a
width-`½` configuration passing the certificate; but any such witness built as a diluted lattice
must carry on-line mass exponential in the aperture, so the trivial floors are mass-dominated
phenomena and the on-line zeros of a configuration act as a detector of its off-line ones. -/
theorem theFloorsNeedExponentialMass {a η : ℝ} (ha : 0 < a) :
    (∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain a η Z) ∧
      ∀ (ℓ L δ : ℝ) (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2), a ≤ L / 2 →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) →
        ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 2 * L + 2 * a + ℓ :=
  ⟨exists_width_eq_half_apertureGain ha η,
    fun _ _ _ hℓ hL hδ hδ' haL hpos =>
      mass_ge_of_dilutedLattice_positive hℓ hL hδ hδ' ha haL hpos⟩

-- from TheApertureMassSeamIsProductive.lean
/-! ### 1. The exchange law inverted -/

/-- **A certificate together with a mass bound bounds the depth.** -/
theorem depth_le_log_of_positive_of_mass {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (ha : 0 < a) (haL : a ≤ L / 2) (hgap : ℓ < 2 * a)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) :
    δ ≤ Real.log ((2 * L + 2 * a + ℓ) / ℓ) / (2 * a - ℓ) := by
  have hcover := (dilutedLattice_weil_nonneg_iff hℓ hL hδ hδ' ha haL).mp hpos
  have hdeep := (latticeFloor_aperture_bounds hℓ hδ ha).2
  have hmass : ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 2 * L + 2 * a + ℓ := by linarith
  have hquot : Real.exp (δ * (2 * a - ℓ)) ≤ (2 * L + 2 * a + ℓ) / ℓ := by
    rw [le_div_iff₀ hℓ]; linarith
  have hpos' : (0 : ℝ) < (2 * L + 2 * a + ℓ) / ℓ := by positivity
  have hlog : δ * (2 * a - ℓ) ≤ Real.log ((2 * L + 2 * a + ℓ) / ℓ) :=
    (Real.le_log_iff_exp_le hpos').mpr hquot
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * a - ℓ)]
  linarith

/-! ### 2. The seam in the calculus -/

/-- The aperture-`a` certificate of a diluted configuration of known dilution and mass. -/
def dilutedReading {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (a : ℝ) (d : DepthDatum) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    0 ≤ ((dilutedLatticeConfig hℓ hL d.2.1 d.2.2).W f f).re

/-- **The productive seam.** With the mass and the dilution known, the aperture-`a` certificate
certifies an explicit nontrivial bound on the depth. -/
theorem certifies_depth_dilutedReading {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (ha : 0 < a)
    (haL : a ≤ L / 2) (hgap : ℓ < 2 * a) {d₀ : DepthDatum} (hd₀ : dilutedReading hℓ hL a d₀) :
    Certifies depth (dilutedReading hℓ hL a) d₀
      (Real.log ((2 * L + 2 * a + ℓ) / ℓ) / (2 * a - ℓ)) := by
  intro d hd
  have hread : dilutedReading hℓ hL a d := (mem_shadow_iff.mp hd) ▸ hd₀
  exact depth_le_log_of_positive_of_mass hℓ hL d.2.1 d.2.2 ha haL hgap hread

/-- **A seam that beats the floor.** The certificate alone is floored at `½` in the depth unit; the
same certificate on data of known mass and dilution certifies the explicit bound, which is below
`½` as soon as the aperture is large enough for the mass at hand. -/
theorem theProductiveSeam {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (ha : 0 < a) (haL : a ≤ L / 2)
    (hgap : ℓ < 2 * a) {d₀ : DepthDatum} (hd₀ : dilutedReading hℓ hL a d₀) :
    Certifies depth (dilutedReading hℓ hL a) d₀
        (Real.log ((2 * L + 2 * a + ℓ) / ℓ) / (2 * a - ℓ)) ∧
      ∀ b η : ℝ, 0 < b → ∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain b η Z :=
  ⟨certifies_depth_dilutedReading hℓ hL ha haL hgap hd₀,
    fun _ η hb => exists_width_eq_half_apertureGain hb η⟩

-- from AliasingIsFreeInsideAnyBackground.lean
/-! ### 1. Below its own Nyquist aperture the sub-lattice aliases -/

/-- At an aperture below half the sub-lattice spacing parameter the aliasing index is one. -/
theorem ceil_two_mul_div_eq_one {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) (haℓ : a ≤ ℓ / 2) :
    ⌈2 * a / ℓ⌉₊ = 1 := by
  rw [Nat.ceil_eq_iff (by norm_num : (1 : ℕ) ≠ 0)]
  refine ⟨?_, ?_⟩
  · rw [show ((1 : ℕ) - 1 : ℕ) = 0 from rfl]
    push_cast
    positivity
  · push_cast
    rw [div_le_one hℓ]
    linarith

/-- **Aliasing is free inside any background.** Below the sub-lattice's own Nyquist aperture the
diluted configuration is Weil-positive at every depth, whatever the on-line mass. -/
theorem dilutedLattice_hides_below_own_nyquist {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (ha : 0 < a) (haℓ : a ≤ ℓ / 2) (haL : a ≤ L / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re := by
  refine dilutedLattice_weil_nonneg_of_floor hℓ hL hδ hδ' haL ?_ hf hfs
  rw [ceil_two_mul_div_eq_one hℓ ha haℓ, latticeFloor_one]
  simp only [mul_zero, neg_zero]
  linarith

/-! ### 2. The two regimes -/

/-- **The two regimes of a mixed configuration.** Below half the sub-lattice spacing the
configuration hides for free at every depth; above it, hiding costs on-line mass exponential in the
depth times the aperture. -/
theorem theTwoRegimesOfAMixedConfiguration {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    (∀ a : ℝ, 0 < a → a ≤ ℓ / 2 → a ≤ L / 2 → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-a) a → 0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) ∧
      ∀ a : ℝ, 0 < a → a ≤ L / 2 →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) →
        ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 2 * L + 2 * a + ℓ :=
  ⟨fun _ ha haℓ haL _ hf hfs =>
      dilutedLattice_hides_below_own_nyquist hℓ hL hδ hδ' ha haℓ haL hf hfs,
    fun _ ha haL hpos => mass_ge_of_dilutedLattice_positive hℓ hL hδ hδ' ha haL hpos⟩

-- from TheFreeRegimeEndsExactlyAtNyquist.lean
/-! ### 1. Strict superadditivity of `sinh` -/

/-- `n sinh x < sinh (n x)` for `x > 0` and `n ≥ 2`. -/
theorem natCast_mul_sinh_lt_sinh_of_two_le {x : ℝ} (hx : 0 < x) :
    ∀ n : ℕ, 2 ≤ n → (n : ℝ) * Real.sinh x < Real.sinh ((n : ℝ) * x) := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · -- the base case `m + 1 = 2`
      have hm2 : m = 1 := by omega
      subst hm2
      have hs : (0 : ℝ) < Real.sinh x := Real.sinh_pos_iff.mpr hx
      have hc : (1 : ℝ) < Real.cosh x := Real.one_lt_cosh.mpr (ne_of_gt hx)
      have hid : ((1 : ℕ) + 1 : ℝ) * x = 2 * x := by push_cast; ring
      rw [show (((1 : ℕ) + 1 : ℕ) : ℝ) = 2 by push_cast; ring, Real.sinh_two_mul]
      nlinarith
    · -- the inductive step
      have hprev := ih hm
      have hs : (0 : ℝ) < Real.sinh x := Real.sinh_pos_iff.mpr hx
      have hcx : (1 : ℝ) ≤ Real.cosh x := Real.one_le_cosh x
      have hcm : (1 : ℝ) ≤ Real.cosh ((m : ℝ) * x) := Real.one_le_cosh _
      have hsm : (0 : ℝ) ≤ Real.sinh ((m : ℝ) * x) :=
        Real.sinh_nonneg_iff.mpr (by positivity)
      have hid : (((m + 1 : ℕ)) : ℝ) * x = (m : ℝ) * x + x := by push_cast; ring
      rw [hid, Real.sinh_add]
      push_cast
      nlinarith [hprev, hcx, hcm, hsm, hs]

/-! ### 2. The ground energy is negative above index one -/

/-- **Above aliasing index one the lattice ground energy is strictly negative.** -/
theorem latticeFloor_neg_of_two_le {ℓ δ : ℝ} (hδℓ : 0 < δ * ℓ) {n : ℕ} (hn : 2 ≤ n) :
    latticeFloor ℓ δ n < 0 := by
  have hs : (0 : ℝ) < Real.sinh (δ * ℓ) := Real.sinh_pos_iff.mpr hδℓ
  have hlt := natCast_mul_sinh_lt_sinh_of_two_le hδℓ n hn
  rw [latticeFloor_eq hδℓ n, sub_neg]
  rw [lt_div_iff₀ hs]
  linarith

/-- Above half the spacing parameter the aliasing index is at least two. -/
theorem ceil_two_le_of_half_lt {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : ℓ / 2 < a) : 2 ≤ ⌈2 * a / ℓ⌉₊ := by
  have h1 : (1 : ℝ) < 2 * a / ℓ := by
    rw [lt_div_iff₀ hℓ]
    linarith
  have := Nat.lt_ceil.mpr (by exact_mod_cast h1 : ((1 : ℕ) : ℝ) < 2 * a / ℓ)
  omega

/-! ### 3. Sharpness -/

/-- **The free regime is sharp.** At or below half the sub-lattice spacing parameter the off-line
ground energy vanishes and hiding is free at every depth; above it the ground energy is strictly
negative, so every further aperture must be paid for with on-line mass. -/
theorem theFreeRegimeIsSharp {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    (∀ a : ℝ, 0 < a → a ≤ ℓ / 2 → a ≤ L / 2 → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-a) a → 0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) ∧
      ∀ a : ℝ, ℓ / 2 < a → latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊ < 0 :=
  ⟨fun _ ha haℓ haL _ hf hfs =>
      dilutedLattice_hides_below_own_nyquist hℓ hL hδ hδ' ha haℓ haL hf hfs,
    fun _ ha => latticeFloor_neg_of_two_le (by positivity) (ceil_two_le_of_half_lt hℓ ha)⟩

-- from TheReachLawOfAStructuredCounterexample.lean
/-! ### 1. The lower reach: aliasing, free -/

/-- **Lower reach.** Below the sub-lattice's own Nyquist aperture positivity is free. -/
theorem reach_lower {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (ha : 0 < a) (haℓ : a ≤ ℓ / 2) (haL : a ≤ L / 2) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re :=
  dilutedLattice_hides_below_own_nyquist hℓ hL hδ hδ' ha haℓ haL hf hfs

/-! ### 2. The upper reach: a logarithm of the mass -/

/-- **Upper reach.** Positivity at aperture `a` forces `a` below the aliasing scale plus a
logarithm of the mass-to-dilution ratio, divided by twice the depth. -/
theorem reach_upper {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (ha : 0 < a) (haL : a ≤ L / 2)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) :
    a ≤ Real.log ((3 * L + ℓ) / ℓ) / (2 * δ) + ℓ / 2 := by
  have hmass := mass_ge_of_dilutedLattice_positive hℓ hL hδ hδ' ha haL hpos
  have hcap : ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 3 * L + ℓ := by
    have h2a : 2 * a ≤ L := by linarith
    linarith
  have hquot : Real.exp (δ * (2 * a - ℓ)) ≤ (3 * L + ℓ) / ℓ := by
    rw [le_div_iff₀ hℓ]; linarith
  have hposq : (0 : ℝ) < (3 * L + ℓ) / ℓ := by positivity
  have hlog : δ * (2 * a - ℓ) ≤ Real.log ((3 * L + ℓ) / ℓ) :=
    (Real.le_log_iff_exp_le hposq).mpr hquot
  rw [← sub_le_iff_le_add, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * δ)]
  nlinarith [hlog]

/-! ### 3. The law -/

/-- **The reach law.** The hiding reach of a structured off-line set lies between its own aliasing
scale, which is free, and that scale plus a logarithm of the mass-to-dilution ratio divided by twice
the depth, which must be bought. -/
theorem theReachLaw {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    (∀ a : ℝ, 0 < a → a ≤ ℓ / 2 → a ≤ L / 2 → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-a) a → 0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) ∧
      ∀ a : ℝ, 0 < a → a ≤ L / 2 →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) →
        a ≤ Real.log ((3 * L + ℓ) / ℓ) / (2 * δ) + ℓ / 2 :=
  ⟨fun _ ha haℓ haL _ hf hfs => reach_lower hℓ hL hδ hδ' ha haℓ haL hf hfs,
    fun _ ha haL hpos => reach_upper hℓ hL hδ hδ' ha haL hpos⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
