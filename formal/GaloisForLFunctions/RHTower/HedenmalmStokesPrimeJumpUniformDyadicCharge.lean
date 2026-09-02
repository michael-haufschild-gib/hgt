import GaloisForLFunctions.RHTower.HedenmalmStokesPrimeJumpScalingShell

/-!
# Uniform dyadic prime--Stokes charge

This strengthens `HCF-SX2` from fixed moving coordinates to a uniform closed-band estimate.  One
local bound for the explicit regular pole--Gamma--von-Mangoldt anomaly controls both sides of both
apertures.  If `2*a < δ` and `a*M < 2/25`, every `c` in `[1/2,1]` receives squared dyadic-shell
charge strictly greater than `21/100`.  The endpoints are included: their limiting shell charge is
`1/2`, rather than zero.

The statement remains source-only.  It does not sum over `XiZeroCopy`.  A deterministic infinite
dyadic grid is represented by uniform bounds for every finite prefix; this removes every hidden
minimum-depth choice.  The next required weld is a height-summed prefix bound against the finite
HCF Plemelj/source-piece covariance.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Quantitative half-jump error at the moving aperture boundary. -/
theorem abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary_sub_half_le
    {a M : ℝ} (ha : 0 < a) (_hM : 0 ≤ M)
    (hA : |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly (2 * a)| ≤ M) :
    |gammaSewnMobiusApertureStokesPrimeJumpProjector a a - 1 / 2| ≤
      a * M / 4 := by
  rw [gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary_eq ha,
    add_sub_cancel_left, abs_div, abs_mul, abs_of_pos ha]
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA ha.le) (by norm_num)

/-- In the open dyadic band, shell charge differs from one by at most `a*M/2`. -/
theorem abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_interior_sub_one_le
    {δ M a c : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (h2aδ : 2 * a < δ)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M)
    (hcLower : 1 / 2 < c) (hcUpper : c < 1) :
    |gammaSewnMobiusApertureStokesPrimeDyadicShell a (c * a) - 1| ≤
      a * M / 2 := by
  have hcAbs : |c| < 1 := by
    rw [abs_of_pos (by linarith : 0 < c)]
    exact hcUpper
  have houterPlus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 + c) * a)| ≤ M := by
    apply hbound _ (mul_pos (by linarith) ha)
    exact (mul_lt_mul_of_pos_right (by linarith : 1 + c < 2) ha).trans h2aδ
  have houterMinus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly ((1 - c) * a)| ≤ M := by
    apply hbound _ (mul_pos (by linarith) ha)
    exact (mul_lt_mul_of_pos_right (by linarith : 1 - c < 2) ha).trans h2aδ
  have houter :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_sub_one_le
      ha hcAbs hM houterPlus houterMinus
  have hb : 0 < a / 2 := div_pos ha (by norm_num)
  have hinnerPlus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly
        ((2 * c + 1) * (a / 2))| ≤ M := by
    apply hbound _ (mul_pos (by linarith) hb)
    have : (2 * c + 1) * (a / 2) < 2 * a := by
      nlinarith
    exact this.trans h2aδ
  have hinnerMinus :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly
        ((2 * c - 1) * (a / 2))| ≤ M := by
    apply hbound _ (mul_pos (by linarith) hb)
    have : (2 * c - 1) * (a / 2) < 2 * a := by
      nlinarith
    exact this.trans h2aδ
  have hinner :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_outside_le
      hb (show 1 < 2 * c by linarith) hM hinnerPlus hinnerMinus
  have hinner' :
      |gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a)| ≤
        a * M / 4 := by
    have hrewrite :
        gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2)
            ((2 * c) * (a / 2)) =
          gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a) := by
      congr 1
      ring
    rw [hrewrite] at hinner
    calc
      _ ≤ (2 * c) * (a / 2) * M / 4 := hinner
      _ ≤ a * M / 4 := by
        have hca : c * (a * M) ≤ 1 * (a * M) :=
          mul_le_mul_of_nonneg_right hcUpper.le (mul_nonneg ha.le hM)
        nlinarith
  have htri :
      |gammaSewnMobiusApertureStokesPrimeDyadicShell a (c * a) - 1| ≤
        |gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) - 1| +
        |gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a)| := by
    rw [gammaSewnMobiusApertureStokesPrimeDyadicShell]
    rw [show
      gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) -
          gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a) - 1 =
        (gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) - 1) +
          (-gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a)) by ring]
    simpa only [abs_neg] using abs_add_le
      (gammaSewnMobiusApertureStokesPrimeJumpProjector a (c * a) - 1)
      (-gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (c * a))
  exact htri.trans <| (add_le_add houter hinner').trans_eq (by ring)

/-- Inner band endpoint has half-charge with the same coarse `a*M/2` error. -/
theorem abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_lowerBoundary_sub_half_le
    {δ M a : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (h2aδ : 2 * a < δ)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M) :
    |gammaSewnMobiusApertureStokesPrimeDyadicShell a (a / 2) - 1 / 2| ≤
      a * M / 2 := by
  have houterPlus := hbound ((1 + (1 / 2 : ℝ)) * a)
    (mul_pos (by norm_num) ha)
    ((mul_lt_mul_of_pos_right (by norm_num : (1 + (1 / 2 : ℝ)) < 2) ha).trans h2aδ)
  have houterMinus := hbound ((1 - (1 / 2 : ℝ)) * a)
    (mul_pos (by norm_num) ha)
    ((mul_lt_mul_of_pos_right (by norm_num : (1 - (1 / 2 : ℝ)) < 2) ha).trans h2aδ)
  have houter :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_sub_one_le
      ha (by norm_num : |(1 / 2 : ℝ)| < 1) hM houterPlus houterMinus
  have hb : 0 < a / 2 := div_pos ha (by norm_num)
  have hinnerA :
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly (2 * (a / 2))| ≤ M := by
    apply hbound _ (by nlinarith)
    nlinarith
  have hinner :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary_sub_half_le
      hb hM hinnerA
  have htri :
      |gammaSewnMobiusApertureStokesPrimeDyadicShell a (a / 2) - 1 / 2| ≤
        |gammaSewnMobiusApertureStokesPrimeJumpProjector a (a / 2) - 1| +
        |gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (a / 2) - 1 / 2| := by
    rw [gammaSewnMobiusApertureStokesPrimeDyadicShell]
    rw [show
      gammaSewnMobiusApertureStokesPrimeJumpProjector a (a / 2) -
          gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (a / 2) - 1 / 2 =
        (gammaSewnMobiusApertureStokesPrimeJumpProjector a (a / 2) - 1) -
          (gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (a / 2) - 1 / 2) by ring]
    rw [sub_eq_add_neg]
    simpa only [abs_neg] using abs_add_le
      (gammaSewnMobiusApertureStokesPrimeJumpProjector a (a / 2) - 1)
      (-(gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) (a / 2) - 1 / 2))
  have houter' :
      |gammaSewnMobiusApertureStokesPrimeJumpProjector a (a / 2) - 1| ≤
        a * M / 4 := by
    convert houter using 1 <;> ring
  calc
    _ ≤ _ := htri
    _ ≤ a * M / 4 + (a / 2) * M / 4 := add_le_add houter' hinner
    _ ≤ a * M / 2 := by
      have haM : 0 ≤ a * M := mul_nonneg ha.le hM
      nlinarith

/-- Outer band endpoint has half-charge with error `a*M/2`. -/
theorem abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_upperBoundary_sub_half_le
    {δ M a : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (h2aδ : 2 * a < δ)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M) :
    |gammaSewnMobiusApertureStokesPrimeDyadicShell a a - 1 / 2| ≤
      a * M / 2 := by
  have houterA := hbound (2 * a) (by positivity) h2aδ
  have houter :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_boundary_sub_half_le
      ha hM houterA
  have hb : 0 < a / 2 := div_pos ha (by norm_num)
  have hinnerPlus := hbound ((2 + 1 : ℝ) * (a / 2))
    (mul_pos (by norm_num) hb) (by nlinarith)
  have hinnerMinus := hbound ((2 - 1 : ℝ) * (a / 2))
    (mul_pos (by norm_num) hb) (by nlinarith)
  have hinner :=
    abs_gammaSewnMobiusApertureStokesPrimeJumpProjector_scaled_outside_le
      hb (by norm_num : (1 : ℝ) < 2) hM hinnerPlus hinnerMinus
  have hinner' :
      |gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) a| ≤
        a * M / 4 := by
    convert hinner using 1 <;> ring
  have htri :
      |gammaSewnMobiusApertureStokesPrimeDyadicShell a a - 1 / 2| ≤
        |gammaSewnMobiusApertureStokesPrimeJumpProjector a a - 1 / 2| +
        |gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) a| := by
    rw [gammaSewnMobiusApertureStokesPrimeDyadicShell]
    rw [show
      gammaSewnMobiusApertureStokesPrimeJumpProjector a a -
          gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) a - 1 / 2 =
        (gammaSewnMobiusApertureStokesPrimeJumpProjector a a - 1 / 2) +
          (-gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) a) by ring]
    simpa only [abs_neg] using abs_add_le
      (gammaSewnMobiusApertureStokesPrimeJumpProjector a a - 1 / 2)
      (-gammaSewnMobiusApertureStokesPrimeJumpProjector (a / 2) a)
  exact htri.trans <| (add_le_add houter hinner').trans_eq (by ring)

/-- **Uniform closed-band quantum.**  One source anomaly bound gives squared shell charge
strictly above `21/100` at every coordinate `c` in the closed dyadic band. -/
theorem twentyOneHundred_lt_sq_gammaSewnMobiusApertureStokesPrimeDyadicShell_of_small
    {δ M a c : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (h2aδ : 2 * a < δ)
    (haM : a * M < 2 / 25)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M)
    (hcLower : 1 / 2 ≤ c) (hcUpper : c ≤ 1) :
    (21 / 100 : ℝ) <
      gammaSewnMobiusApertureStokesPrimeDyadicShell a (c * a) ^ 2 := by
  let shell := gammaSewnMobiusApertureStokesPrimeDyadicShell a (c * a)
  have square_of_half_error (herror : |shell - 1 / 2| ≤ a * M / 2) :
      (21 / 100 : ℝ) < shell ^ 2 := by
    have hshell : (23 / 50 : ℝ) < shell := by
      have hlower := (abs_le.mp herror).1
      nlinarith
    have hprod : 0 < (shell - 23 / 50) * (shell + 23 / 50) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  by_cases hcLowerEq : c = 1 / 2
  · subst c
    apply square_of_half_error
    dsimp only [shell]
    convert
      abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_lowerBoundary_sub_half_le
        hM ha h2aδ hbound using 1 <;> ring
  by_cases hcUpperEq : c = 1
  · subst c
    apply square_of_half_error
    simpa only [one_mul, shell] using
      abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_upperBoundary_sub_half_le
        hM ha h2aδ hbound
  · have herror :=
      abs_gammaSewnMobiusApertureStokesPrimeDyadicShell_scaled_interior_sub_one_le
        hM ha h2aδ hbound
        (lt_of_le_of_ne hcLower (Ne.symm hcLowerEq))
        (lt_of_le_of_ne hcUpper hcUpperEq)
    have hshell : (24 / 25 : ℝ) < shell := by
      have hlower := (abs_le.mp herror).1
      dsimp only [shell]
      nlinarith
    have hprod : 0 < (shell - 24 / 25) * (shell + 24 / 25) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

/-! ## Fixed-grid finite frame receiver -/

/-- Positive shell-frame energy for finite packets and a source scale grid fixed in advance. -/
def finiteGammaSewnMobiusApertureStokesPrimeDyadicFrameEnergy
    {ι κ : Type*} (S : Finset ι) (J : Finset κ)
    (depth mass : ι → ℝ) (scale : κ → ℝ) : ℝ :=
  ∑ i ∈ S, mass i * ∑ j ∈ J,
    gammaSewnMobiusApertureStokesPrimeDyadicShell (scale j) (depth i) ^ 2

/-- Every atom covered by one member of the fixed source grid contributes at least `21/100` of
its mass to total frame energy.  The selected scale is used only in the proof of the lower bound;
the observable contains the complete predeclared grid. -/
theorem twentyOneHundred_mul_mass_le_finitePrimeStokesDyadicFrameEnergy
    {ι κ : Type*} (S : Finset ι) (J : Finset κ)
    (depth mass : ι → ℝ) (scale : κ → ℝ) {δ M : ℝ}
    (hM : 0 ≤ M)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M)
    (hmass : ∀ i ∈ S, 0 ≤ mass i)
    (hscalePos : ∀ j ∈ J, 0 < scale j)
    (hscaleSmall : ∀ j ∈ J, 2 * scale j < δ)
    (hscaleError : ∀ j ∈ J, scale j * M < 2 / 25)
    (hcover : ∀ i ∈ S, ∃ j ∈ J, ∃ c : ℝ,
      depth i = c * scale j ∧ 1 / 2 ≤ c ∧ c ≤ 1) :
    (21 / 100 : ℝ) * ∑ i ∈ S, mass i ≤
      finiteGammaSewnMobiusApertureStokesPrimeDyadicFrameEnergy
        S J depth mass scale := by
  rw [finiteGammaSewnMobiusApertureStokesPrimeDyadicFrameEnergy,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨j, hj, c, hdepth, hcLower, hcUpper⟩ := hcover i hi
  have hcharge : (21 / 100 : ℝ) <
      gammaSewnMobiusApertureStokesPrimeDyadicShell
        (scale j) (depth i) ^ 2 := by
    rw [hdepth]
    exact twentyOneHundred_lt_sq_gammaSewnMobiusApertureStokesPrimeDyadicShell_of_small
      hM (hscalePos j hj) (hscaleSmall j hj) (hscaleError j hj)
      hbound hcLower hcUpper
  have hterm :
      gammaSewnMobiusApertureStokesPrimeDyadicShell (scale j) (depth i) ^ 2 ≤
        ∑ k ∈ J,
          gammaSewnMobiusApertureStokesPrimeDyadicShell
            (scale k) (depth i) ^ 2 := by
    exact Finset.single_le_sum
      (fun k _ => sq_nonneg
        (gammaSewnMobiusApertureStokesPrimeDyadicShell (scale k) (depth i))) hj
  calc
    (21 / 100 : ℝ) * mass i = mass i * (21 / 100 : ℝ) := by ring
    _ ≤ mass i *
        gammaSewnMobiusApertureStokesPrimeDyadicShell (scale j) (depth i) ^ 2 :=
      mul_le_mul_of_nonneg_left hcharge.le (hmass i hi)
    _ ≤ mass i * ∑ k ∈ J,
        gammaSewnMobiusApertureStokesPrimeDyadicShell
          (scale k) (depth i) ^ 2 :=
      mul_le_mul_of_nonneg_left hterm (hmass i hi)

/-! ## Zero-independent all-scale prefix receiver -/

/-- Deterministic dyadic source scale. -/
def gammaSewnMobiusApertureStokesPrimeDyadicSourceScale (a : ℝ) (j : ℕ) : ℝ :=
  a / (2 : ℝ) ^ j

/-- Finite prefix of the deterministic all-scale source frame. -/
def finiteGammaSewnMobiusApertureStokesPrimeDyadicPrefixEnergy
    {ι : Type*} (S : Finset ι) (K : ℕ)
    (depth mass : ι → ℝ) (a : ℝ) : ℝ :=
  finiteGammaSewnMobiusApertureStokesPrimeDyadicFrameEnergy
    S (Finset.range K) depth mass
      (gammaSewnMobiusApertureStokesPrimeDyadicSourceScale a)

/-- Every positive depth below a fixed source aperture lies in one deterministic dyadic band.
This is the exact Archimedean step that removes packet-dependent minimum-depth selection. -/
theorem exists_gammaSewnMobiusApertureStokesPrimeDyadicSourceScale_cover
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (hta : t ≤ a) :
    ∃ j : ℕ, ∃ c : ℝ,
      t = c * gammaSewnMobiusApertureStokesPrimeDyadicSourceScale a j ∧
        1 / 2 ≤ c ∧ c ≤ 1 := by
  have hex : ∃ n : ℕ, a / (2 : ℝ) ^ n < t := by
    obtain ⟨n, hn⟩ := exists_nat_gt (a / t)
    refine ⟨n, ?_⟩
    have hnat : (n : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_two_pow_self
    have hpow : a / t < (2 : ℝ) ^ n := by
      have hcast : (((2 ^ n : ℕ) : ℝ)) = (2 : ℝ) ^ n := by norm_num
      rw [← hcast]
      exact hn.trans hnat
    have hpow0 : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
    rw [div_lt_iff₀ hpow0]
    rw [div_lt_iff₀ ht] at hpow
    simpa only [mul_comm] using hpow
  let n := Nat.find hex
  have hn : a / (2 : ℝ) ^ n < t := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    change Nat.find hex ≠ 0
    intro hnzero
    dsimp [n] at hn
    rw [hnzero] at hn
    norm_num at hn
    linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hprev : t ≤ a / (2 : ℝ) ^ j := by
    by_contra hnot
    have hjprop : a / (2 : ℝ) ^ j < t := lt_of_not_ge hnot
    have hmin : n ≤ j := Nat.find_min' hex hjprop
    omega
  have hscale0 : 0 < a / (2 : ℝ) ^ j :=
    div_pos ha (pow_pos (by norm_num) _)
  have hhalf : (a / (2 : ℝ) ^ j) / 2 < t := by
    rw [hj, pow_succ] at hn
    convert hn using 1 <;> ring
  refine ⟨j, t / (a / (2 : ℝ) ^ j), ?_, ?_, ?_⟩
  · rw [gammaSewnMobiusApertureStokesPrimeDyadicSourceScale]
    field_simp
  · rw [le_div_iff₀ hscale0]
    linarith
  · exact (div_le_one hscale0).2 hprev

/-- **All-scale source-frame receiver.**  Suppose every finite prefix of one deterministic dyadic
source grid has a common upper budget `B`.  Then every finite packet of arbitrarily shallow
positive depths below the base aperture has total multiplicity at most `(100/21) B`.

The prefix upper bound is fixed before any divisor packet is inspected.  Only the proof chooses a
large enough prefix, so no zero-dependent scale occurs in the observable. -/
theorem twentyOneHundred_mul_mass_le_of_all_dyadicPrefixEnergy_le
    {ι : Type*} (S : Finset ι) (depth mass : ι → ℝ)
    {δ M a B : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) (h2aδ : 2 * a < δ)
    (haM : a * M < 2 / 25)
    (hbound : ∀ d : ℝ, 0 < d → d < δ →
      |thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d| ≤ M)
    (hmass : ∀ i ∈ S, 0 ≤ mass i)
    (hdepthPos : ∀ i, 0 < depth i)
    (hdepthUpper : ∀ i, depth i ≤ a)
    (hprefix : ∀ K : ℕ,
      finiteGammaSewnMobiusApertureStokesPrimeDyadicPrefixEnergy
        S K depth mass a ≤ B) :
    (21 / 100 : ℝ) * ∑ i ∈ S, mass i ≤ B := by
  have hcoverAll : ∀ i : ι, ∃ j : ℕ, ∃ c : ℝ,
      depth i = c * gammaSewnMobiusApertureStokesPrimeDyadicSourceScale a j ∧
        1 / 2 ≤ c ∧ c ≤ 1 := by
    intro i
    exact exists_gammaSewnMobiusApertureStokesPrimeDyadicSourceScale_cover
      ha (hdepthPos i) (hdepthUpper i)
  choose j c hc using hcoverAll
  let K : ℕ := S.sup j + 1
  have hscalePos : ∀ k ∈ Finset.range K,
      0 < gammaSewnMobiusApertureStokesPrimeDyadicSourceScale a k := by
    intro k hk
    exact div_pos ha (pow_pos (by norm_num) _)
  have hscaleLe : ∀ k : ℕ,
      gammaSewnMobiusApertureStokesPrimeDyadicSourceScale a k ≤ a := by
    intro k
    exact div_le_self ha.le (one_le_pow₀ (by norm_num))
  have hscaleSmall : ∀ k ∈ Finset.range K,
      2 * gammaSewnMobiusApertureStokesPrimeDyadicSourceScale a k < δ := by
    intro k hk
    nlinarith [hscaleLe k]
  have hscaleError : ∀ k ∈ Finset.range K,
      gammaSewnMobiusApertureStokesPrimeDyadicSourceScale a k * M < 2 / 25 := by
    intro k hk
    have hmul := mul_le_mul_of_nonneg_right (hscaleLe k) hM
    exact hmul.trans_lt haM
  have hcover : ∀ i ∈ S, ∃ k ∈ Finset.range K, ∃ c' : ℝ,
      depth i = c' * gammaSewnMobiusApertureStokesPrimeDyadicSourceScale a k ∧
        1 / 2 ≤ c' ∧ c' ≤ 1 := by
    intro i hi
    refine ⟨j i, Finset.mem_range.mpr ?_, c i,
      (hc i).1, (hc i).2.1, (hc i).2.2⟩
    dsimp only [K]
    exact Nat.lt_succ_of_le (Finset.le_sup hi)
  have hframe := twentyOneHundred_mul_mass_le_finitePrimeStokesDyadicFrameEnergy
    S (Finset.range K) depth mass
      (gammaSewnMobiusApertureStokesPrimeDyadicSourceScale a)
    hM hbound hmass hscalePos hscaleSmall hscaleError hcover
  have hframe' : (21 / 100 : ℝ) * ∑ i ∈ S, mass i ≤
      finiteGammaSewnMobiusApertureStokesPrimeDyadicPrefixEnergy
        S K depth mass a := by
    simpa only [finiteGammaSewnMobiusApertureStokesPrimeDyadicPrefixEnergy] using hframe
  exact hframe'.trans (hprefix K)

end

end RHTower
