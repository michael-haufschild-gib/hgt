import GaloisForLFunctions.SquareRootThreshold.ZetaNearTopZerosAreVisibleBelowAnExplicitHeight

/-!
# The one-parameter lag family sees near-top zeros

The family of the problem itself: `P_v = Re W(κ_w(t + v/2) − κ_w(t − v/2))`, the unmodulated
(`c = 0`) difference tests. `OneParameterLagFamilyHidesOnlyInCollapsedClusters` leaves it one way to
hide a near-top zero `½ + z₀` with `η = |h_w(γ₀ − iδ₀)| > 0`: a collapsed cluster at the record
`z*`, which sits below the height `Γ₀(η)`. This file closes that door, as
`ZetaNearTopZerosAreVisibleBelowAnExplicitHeight` does for the modulated family.

* **Coefficients** (`evenCoeff_modScaledBump_zero_eq_two_mul`). For `ζ`, `D(z) = 2m h_w(−iz)²`: the
  conjugate zero contributes the same square, so no reflected term arises.
* **Coherence** (`re_one_param_mul_conj_nonneg`). Nearby zeros have coefficients of nonnegative
  inner product as soon as `|h_w(−iz*)| ≥ H₀` and `8w e^{w/2}J_w|z − z*| ≤ H₀`. Unlike the
  modulated family, no height condition is needed.
* **Comparability** (`norm_evenCoeff_zero_le_of_near`). Near the record the coefficients are at most
  `(125/2) log(180Γ)` times the record coefficient, so the core mass condition is relative and
  independent of the loudness of the record.
* **Loud records** (`le_norm_paperFT_of_loud_zero`). `|D(z*)| ≥ ε₀` and `m ≤ 40 log(180Γ₀)` give
  `|h_w(−iz*)|² ≥ ε₀/(80 log(180Γ₀))`.
* **A loud record is visible** (`one_param_record_visible`). For the Legendre record `z*` at lag `V`
  with `|D(z*)| ≥ a`, `|Im z*| ≤ Γ`, `Re z* ≥ σ`: scale separation, partial elimination of the loose
  members and the coherent core give, against the elimination noise `B(a, Γ; p)`
  (`recordCollapseBound`), `(ρκ₀/(2(P + 1)G^P))^p V^{2k+p+1}(σ/4)^{2k+1} ≤ 2B(a, Γ; p)`. Under the
  reverse inequality some `P_v`, `v ∈ [0, V]`, is negative.
* **Near-top zeros** (`one_param_near_top_visible`). A zero `1/V`-near the top makes a record with
  `a = 2η²/e`, `Γ = Γ₀(η)`, `σ = δ₀/2` (`one_param_record_facts`). The top need not be attained.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- For `ζ` the unmodulated coefficient is `D(z) = 2m h_w(−iz)²`. -/
theorem evenCoeff_modScaledBump_zero_eq_two_mul {w : ℝ} (hw : 0 < w) {z : ℂ}
    (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier) :
    evenCoeff zetaZeroConfig (modScaledBump w 0) z =
      ((2 * zetaZeroConfig.mult (1 / 2 + z) : ℕ) : ℂ) * paperFT (scaledBump w) (-(I * z)) ^ 2 := by
  have e : conj (1 / 2 + z) = 1 / 2 + conj z := by apply Complex.ext <;> simp
  have hzc : (1 / 2 + conj z) ∈ zetaZeroConfig.carrier := by
    have := conj_mem_zetaZeroConfig hz; rwa [e] at this
  have hmc : zetaZeroConfig.mult (1 / 2 + conj z) = zetaZeroConfig.mult (1 / 2 + z) := by
    have := mult_conj_zetaZeroConfig hz; rwa [e] at this
  rw [evenCoeff_modScaledBump_zero zetaZeroConfig hw hz, Set.indicator_of_mem hzc, hmc]
  push_cast; ring

/-- **The transform moves little near a loud record.** For a zero `½ + z₁` with
`|h_w(−iz₁)| ≥ H₀`, `8w e^{w/2} J_w |z − z₁| ≤ H₀` and `w|z − z₁| ≤ 1`:
`|h_w(−iz) − h_w(−iz₁)| ≤ |h_w(−iz₁)|/4`. -/
theorem norm_paperFT_sub_le_quarter {w : ℝ} (hw : 0 < w) {z₁ z : ℂ}
    (hz₁ : (1 / 2 + z₁) ∈ zetaZeroConfig.carrier) {H₀ : ℝ}
    (hh₁ : H₀ ≤ ‖paperFT (scaledBump w) (-(I * z₁))‖)
    (hL : 8 * w * Real.exp (w / 2) * bumpMass w * ‖z - z₁‖ ≤ H₀) (hwz : w * ‖z - z₁‖ ≤ 1) :
    ‖paperFT (scaledBump w) (-(I * z)) - paperFT (scaledBump w) (-(I * z₁))‖ ≤
      ‖paperFT (scaledBump w) (-(I * z₁))‖ / 4 := by
  have hxy : w * ‖-(I * z) - -(I * z₁)‖ ≤ 1 := by
    rw [show -(I * z) - -(I * z₁) = -I * (z - z₁) by ring, norm_mul, norm_neg, Complex.norm_I,
      one_mul]
    exact hwz
  have hy : |(-(I * z₁)).im| ≤ 1 / 2 := by
    have hs := zetaZeroConfig.strip _ hz₁
    have e : (1 / 2 + z₁).re = 1 / 2 + z₁.re := by simp
    have : |z₁.re| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    simpa using this
  have h := norm_paperFT_scaledBump_sub_le hw hxy hy
  rw [show -(I * z) - -(I * z₁) = -I * (z - z₁) by ring, norm_mul, norm_neg, Complex.norm_I,
    one_mul] at h
  have : 2 * w * Real.exp (w / 2) * bumpMass w * ‖z - z₁‖ ≤ H₀ / 4 := by linarith
  linarith

/-- **Unmodulated coefficients of nearby zeros are coherent.** For zeros `½ + z₁`, `½ + z` with
`|h_w(−iz₁)| ≥ H₀`, `8w e^{w/2} J_w |z − z₁| ≤ H₀` and `w|z − z₁| ≤ 1`:
`Re(D(z) conj D(z₁)) ≥ 0`. No reflected term arises, since both conjugate zeros carry `h_w(−iz)²`. -/
theorem re_one_param_mul_conj_nonneg {w : ℝ} (hw : 0 < w) {z₁ z : ℂ}
    (hz₁ : (1 / 2 + z₁) ∈ zetaZeroConfig.carrier) (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier)
    {H₀ : ℝ} (hh₁ : H₀ ≤ ‖paperFT (scaledBump w) (-(I * z₁))‖)
    (hL : 8 * w * Real.exp (w / 2) * bumpMass w * ‖z - z₁‖ ≤ H₀) (hwz : w * ‖z - z₁‖ ≤ 1) :
    0 ≤ (evenCoeff zetaZeroConfig (modScaledBump w 0) z *
      conj (evenCoeff zetaZeroConfig (modScaledBump w 0) z₁)).re := by
  have hdiff := norm_paperFT_sub_le_quarter hw hz₁ hh₁ hL hwz
  rw [evenCoeff_modScaledBump_zero_eq_two_mul hw hz₁, evenCoeff_modScaledBump_zero_eq_two_mul hw hz]
  set h₁ := paperFT (scaledBump w) (-(I * z₁)) with hh₁def
  set h₂ := paperFT (scaledBump w) (-(I * z)) with hh₂def
  have h0 : ‖(0 : ℂ)‖ ≤ ‖h₁‖ ^ 2 / 16 := by rw [norm_zero]; positivity
  have hcoh := re_coherent_squares_nonneg hdiff h0 h0
  simp only [add_zero] at hcoh
  have e : ((2 * zetaZeroConfig.mult (1 / 2 + z) : ℕ) : ℂ) * h₂ ^ 2 *
      conj (((2 * zetaZeroConfig.mult (1 / 2 + z₁) : ℕ) : ℂ) * h₁ ^ 2) =
      ((((2 * zetaZeroConfig.mult (1 / 2 + z)) * (2 * zetaZeroConfig.mult (1 / 2 + z₁)) : ℕ) : ℝ) : ℂ) *
        (h₂ ^ 2 * conj (h₁ ^ 2)) := by
    rw [map_mul, Complex.conj_natCast]; push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _) hcoh

/-- **Coefficients near a loud record are comparable to it.** Under the hypotheses of
`norm_paperFT_sub_le_quarter`, for a zero `½ + z` with `|Im z| ≤ Γ'`:
`|D(z)| ≤ (125/2) log(180Γ') |D(z₁)|`, since `|h_w(−iz)| ≤ (5/4)|h_w(−iz₁)|` and `m ≤ 40 log(180Γ')`. -/
theorem norm_evenCoeff_zero_le_of_near {w : ℝ} (hw : 0 < w) {z₁ z : ℂ}
    (hz₁ : (1 / 2 + z₁) ∈ zetaZeroConfig.carrier) (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier)
    {H₀ Γ' : ℝ} (hh₁ : H₀ ≤ ‖paperFT (scaledBump w) (-(I * z₁))‖)
    (hL : 8 * w * Real.exp (w / 2) * bumpMass w * ‖z - z₁‖ ≤ H₀) (hwz : w * ‖z - z₁‖ ≤ 1)
    (hΓ' : |z.im| ≤ Γ') :
    ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ ≤
      125 / 2 * Real.log (180 * Γ') * ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ := by
  have hdiff := norm_paperFT_sub_le_quarter hw hz₁ hh₁ hL hwz
  set h₁ := paperFT (scaledBump w) (-(I * z₁)) with hh₁def
  set h₂ := paperFT (scaledBump w) (-(I * z)) with hh₂def
  have hh₂ : ‖h₂‖ ≤ 5 / 4 * ‖h₁‖ := by
    have := norm_sub_norm_le h₂ h₁; linarith
  have hD : ∀ y, (1 / 2 + y) ∈ zetaZeroConfig.carrier →
      ‖evenCoeff zetaZeroConfig (modScaledBump w 0) y‖ =
        2 * zetaZeroConfig.mult (1 / 2 + y) * ‖paperFT (scaledBump w) (-(I * y))‖ ^ 2 :=
    fun y hy => by
      rw [evenCoeff_modScaledBump_zero_eq_two_mul hw hy, norm_mul, norm_pow, Complex.norm_natCast]
      push_cast; ring
  rw [hD z hz, hD z₁ hz₁, ← hh₁def, ← hh₂def]
  have him' : (1 / 2 + z).im = z.im := by simp
  have h4 : 4 ≤ |z.im| := by have := four_le_abs_im_of_mem_zetaCarrier hz; rwa [him'] at this
  have hm := mult_le_log_zeta hz
  rw [him'] at hm
  have hmΓ : (zetaZeroConfig.mult (1 / 2 + z) : ℝ) ≤ 40 * Real.log (180 * Γ') :=
    hm.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) (by norm_num))
  have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + z₁) := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ hz₁
  have hsq : ‖h₂‖ ^ 2 ≤ 25 / 16 * ‖h₁‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hh₂ 2; nlinarith
  have hm0 : (0 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + z) := Nat.cast_nonneg _
  have h1 : 2 * (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * ‖h₂‖ ^ 2 ≤
      2 * (40 * Real.log (180 * Γ')) * (25 / 16 * ‖h₁‖ ^ 2) :=
    mul_le_mul (by linarith) hsq (sq_nonneg _) (by linarith)
  have hL0 : 0 ≤ Real.log (180 * Γ') := Real.log_nonneg (by linarith)
  have h2 : 2 * ‖h₁‖ ^ 2 ≤ 2 * (zetaZeroConfig.mult (1 / 2 + z₁) : ℝ) * ‖h₁‖ ^ 2 := by
    have := sq_nonneg ‖h₁‖; nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 125 / 4 * Real.log (180 * Γ') by positivity)
  linarith

/-- **A loud unmodulated coefficient has a large transform.** For a zero `½ + y` with `|Im y| ≤ Γ'`,
`|D(y)| ≥ ε₀` and `H₀² ≤ ε₀/(80 log(180Γ'))`: `|h_w(−iy)| ≥ H₀`. -/
theorem le_norm_paperFT_of_loud_zero {w : ℝ} (hw : 0 < w) {y : ℂ}
    (hy : (1 / 2 + y) ∈ zetaZeroConfig.carrier) {Γ' ε₀ H₀ : ℝ} (hΓ' : |y.im| ≤ Γ')
    (hD : ε₀ ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w 0) y‖)
    (hH : H₀ ^ 2 ≤ ε₀ / (80 * Real.log (180 * Γ'))) :
    H₀ ≤ ‖paperFT (scaledBump w) (-(I * y))‖ := by
  have h4 : 4 ≤ |(1 / 2 + y).im| := four_le_abs_im_of_mem_zetaCarrier hy
  have him' : (1 / 2 + y).im = y.im := by simp
  rw [him'] at h4
  have hm := mult_le_log_zeta hy
  rw [him'] at hm
  have hmΓ : (zetaZeroConfig.mult (1 / 2 + y) : ℝ) ≤ 40 * Real.log (180 * Γ') :=
    hm.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) (by norm_num))
  have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + y) := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ hy
  have hDn : ‖evenCoeff zetaZeroConfig (modScaledBump w 0) y‖ =
      2 * zetaZeroConfig.mult (1 / 2 + y) * ‖paperFT (scaledBump w) (-(I * y))‖ ^ 2 := by
    rw [evenCoeff_modScaledBump_zero_eq_two_mul hw hy, norm_mul, norm_pow, Complex.norm_natCast]
    push_cast; ring
  have hL : 0 < 80 * Real.log (180 * Γ') := by linarith
  have h1 : ε₀ / (80 * Real.log (180 * Γ')) ≤ ‖paperFT (scaledBump w) (-(I * y))‖ ^ 2 := by
    rw [div_le_iff₀ hL]
    have h2 : 2 * (zetaZeroConfig.mult (1 / 2 + y) : ℝ) *
        ‖paperFT (scaledBump w) (-(I * y))‖ ^ 2 ≤
        80 * Real.log (180 * Γ') * ‖paperFT (scaledBump w) (-(I * y))‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) (hH.trans h1)

/-- The collapse bound `B(a, Γ; p) = (8/3)^p (4/3)^k 2κ₀ (4κ₀² + 4π²(k + p)²)^{k+p}
(4m₀/((e − 1)a) + 6144 log(180(Γ + 6)))`, `m₀ = 32(e^{w/2}B_w)²(C_ξ + log 4)`, for a record coefficient
`≥ a` below the height `Γ`. -/
def recordCollapseBound (w a Γ κ₀ : ℝ) (k p : ℕ) : ℝ :=
  (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀) * (4 * κ₀ ^ 2 + 4 * π ^ 2 * (k + p : ℕ) ^ 2) ^ (k + p) *
    (4 * (32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
        (xiLineTwoLogDerivConstant + Real.log 4)) / ((Real.exp 1 - 1) * a) +
      6144 * Real.log (180 * (Γ + 6)))

theorem oneParamCollapseBound_eq_record (w η κ₀ : ℝ) (k p : ℕ) :
    oneParamCollapseBound w η κ₀ k p =
      recordCollapseBound w (2 * η ^ 2 / Real.exp 1) (oneParamRecordHeight w η) κ₀ k p := rfl

/-- **A loud record is visible.** Let `z*` be the Legendre record of the unmodulated family at lag
`V` with `|D(z*)| ≥ a > 0`, `|Im z*| ≤ Γ`, `Re z* ≥ σ`, `0 < σ ≤ ½`, `P ≥ 80 log(180Γ)`. Let `k ≥ 1`,
`κ₀ ≥ 1`, `2κ₀/V ≤ σ/8`, `V ≥ π(k + P)`, `Vσ/4 ≥ 4π(k + P)`, `H₀² ≤ a/(80 log(180Γ))`, and a core
scale `ρ > 0` and gap `G ≥ 1` with `ρV ≤ 1`, `wρ ≤ 1`, `8w e^{w/2} J_w ρ ≤ H₀`, `ρ ≤ σ/8`,
`((1 + τ)·2ρV + τ)(P + 1)·(125/2) log(180(Γ + 1)) ≤ 1/2` (`τ = coreFactorPerturbation`),
and for every `p ≤ P`, `2B(a, Γ; p) < (ρκ₀/(2(P + 1)G^P))^p V^{2k+p+1}(σ/4)^{2k+1}`
(`recordCollapseBound`). Then `P_v < 0` for some `v ∈ [0, V]`. -/
theorem one_param_record_visible {w : ℝ} (hw : 0 < w) {V : ℝ} (hV : 0 < V) {z₁ : ℂ}
    (hz₁ : evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 2) (hre₁ : σ ≤ z₁.re) {a Γ : ℝ} (ha : 0 < a)
    (hD₁ : a ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖) (hup : |z₁.im| ≤ Γ)
    (hrec : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * Real.exp (z₁.re * V)) {P : ℕ}
    (hP : 80 * Real.log (180 * Γ) ≤ P) {κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀)
    (hκV : 2 * κ₀ / V ≤ σ / 8) (hVk : π * (k + P : ℕ) ≤ V)
    (hVr : 4 * π * (k + P : ℕ) ≤ V * (σ / 4)) {H₀ : ℝ}
    (hH : H₀ ^ 2 ≤ a / (80 * Real.log (180 * Γ)))
    {ρ G : ℝ} (hρ : 0 < ρ) (hG : 1 ≤ G) (hρV : ρ * V ≤ 1) (hρw : w * ρ ≤ 1)
    (hρL : 8 * w * Real.exp (w / 2) * bumpMass w * ρ ≤ H₀) (hρr : ρ ≤ σ / 8)
    (hηm : ((1 + coreFactorPerturbation P κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation P κ₀ V ρ G) * ((P + 1) * (125 / 2 * Real.log (180 * (Γ + 1)))) ≤
          1 / 2)
    (hmain : ∀ p : ℕ, p ≤ P → 2 * recordCollapseBound w a Γ κ₀ k p <
      (ρ * κ₀ / (2 * (P + 1) * G ^ P)) ^ p * V ^ (2 * k + p + 1) * (σ / 4) ^ (2 * k + 1)) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  by_contra hneg
  push Not at hneg
  classical
  set b := modScaledBump w 0 with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set r : ℝ := σ / 4 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · exact h
    · have := conj_mem_zetaZeroConfig h
      have e : conj (1 / 2 + conj x) = 1 / 2 + x := by apply Complex.ext <;> simp
      rwa [e] at this
  have hκ₀0 : 0 < κ₀ := by linarith
  have h2κ : 2 * κ₀ / V ≤ r / 2 := by rw [hr]; linarith
  -- the companions of the record, independent of the depth
  set R₀ : ℝ := r + 2 * κ₀ / V with hR₀
  set T : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b z₁ R₀).toFinset.erase z₁ with hT
  have hTcard : T.card ≤ P := by
    have h4 : 4 ≤ |z₁.im| := four_le_abs_im_of_evenCoeff_zeta hz₁
    have hloc := card_exponent_window_le (b := b) h4 T fun z hz => by
      rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset] at hz
      obtain ⟨-, hDz, hzr⟩ := hz
      refine ⟨hDz, ?_⟩
      have := Complex.abs_im_le_norm (z - z₁)
      rw [Complex.sub_im] at this
      have : R₀ ≤ 1 := by rw [hR₀]; linarith
      linarith
    have hlog : Real.log (180 * |z₁.im|) ≤ Real.log (180 * Γ) :=
      Real.log_le_log (by linarith) (by linarith)
    have : (T.card : ℝ) ≤ P := by linarith
    exact_mod_cast this
  -- a depth avoiding the mirror points of all companions
  obtain ⟨κ, hκ1, hκ2, hmirror⟩ := exists_depth_avoiding_mirrors T z₁ hTcard hκ₀0 hV
  set ε : ℝ := κ₀ / (2 * (P + 1) * V) with hε
  have hκ0 : 0 < κ := by linarith
  have hκV' : κ / V ≤ 2 * κ₀ / V := div_le_div_of_nonneg_right hκ2 hV.le
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hz₁s : ‖z₁ - s‖ = κ / V := by
    have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hκ0 hV)]
  set S : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b s r).toFinset with hS
  have hz₁S : z₁ ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]; exact ⟨hz₁, by rw [hz₁s]; linarith⟩
  have hSr : ∀ z ∈ S, ‖z - s‖ ≤ r := fun z hz => by
    rw [hS, Set.Finite.mem_toFinset] at hz; exact hz.2
  have hiso : ∀ z, z ∉ S → D z ≠ 0 → r ≤ ‖z - s‖ := fun z hz hDz => by
    rw [hS, Set.Finite.mem_toFinset] at hz
    by_contra h; push Not at h; exact hz ⟨hDz, h.le⟩
  have hST : S.erase z₁ ⊆ T := fun z hz => by
    rw [Finset.mem_erase] at hz
    have hzS := hz.2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset]
    refine ⟨hz.1, hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    have := hSr z hz.2
    rw [hR₀]; linarith
  have hrσ : r ≤ z₁.re - κ / V := by rw [hr] at h2κ ⊢; linarith
  -- the empty annulus splits the companions into a core and loose members
  obtain ⟨j, hjP, hann⟩ := exists_empty_annulus T z₁ hTcard hρ hG
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = ρ / G ^ (j + 1) := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = ρ / G ^ j := ⟨_, rfl⟩
  rw [← hρ₀, ← hρ₁] at hann
  have hG0 : 0 < G := by linarith only [hG]
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hρ₀ρ : ρ₀ ≤ ρ := by rw [hρ₀]; exact div_le_self hρ.le (one_le_pow₀ hG)
  have hρ₁ρ₀ : ρ₁ = G * ρ₀ := by rw [hρ₁, hρ₀, pow_succ]; field_simp
  have hρ₁P : ρ / G ^ P ≤ ρ₁ := by
    rw [hρ₁]; exact div_le_div_of_nonneg_left hρ.le (by positivity) (pow_le_pow_right₀ hG hjP)
  obtain ⟨SL, hSL⟩ : ∃ SL : Finset ℂ, SL = (S.erase z₁).filter fun z => ρ₁ < ‖z - z₁‖ :=
    ⟨_, rfl⟩
  have hSLmem : ∀ z, z ∈ SL ↔ (z ≠ z₁ ∧ z ∈ S) ∧ ρ₁ < ‖z - z₁‖ := fun z => by
    rw [hSL, Finset.mem_filter, Finset.mem_erase]
  have hSLS : SL ⊆ S := fun z hz => ((hSLmem z).mp hz).1.2
  have hSLT : SL ⊆ T := fun z hz => hST (Finset.mem_erase.mpr ((hSLmem z).mp hz).1)
  have hpP : SL.card ≤ P := (Finset.card_le_card hSLT).trans hTcard
  have hpP' : ((k + SL.card : ℕ) : ℝ) ≤ (k + P : ℕ) := by exact_mod_cast (by omega : k + SL.card ≤ k + P)
  have hPE := zeta_partial_elimination_le (contDiff_modScaledBump_two w _)
    (modScaledBump_support hw _) hneg hz₁ hrec hκ0 hr0 hr1 hrσ hk S SL hSLS hSr hiso
    (le_trans (mul_le_mul_of_nonneg_left hpP' Real.pi_pos.le) hVk)
    (le_trans (mul_le_mul_of_nonneg_left hpP' (by positivity)) hVr)
  rw [← hs] at hPE
  have hz₁C : z₁ ∈ S.filter fun z => z ∉ SL :=
    Finset.mem_filter.mpr ⟨hz₁S, fun h => ((hSLmem z₁).mp h).1.1 rfl⟩
  have hcρ₀ : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖c - z₁‖ ≤ ρ₀ := fun c hc => by
    obtain ⟨hcS, hcL⟩ := Finset.mem_filter.mp hc
    by_cases hne : c = z₁
    · rw [hne, sub_self, norm_zero]; exact hρ₀0.le
    · rcases hann c (hST (Finset.mem_erase.mpr ⟨hne, hcS⟩)) with h | h
      · exact h
      · exact absurd ((hSLmem c).mpr ⟨⟨hne, hcS⟩, h⟩) hcL
  have hcρ : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖c - z₁‖ ≤ ρ := fun c hc => (hcρ₀ c hc).trans hρ₀ρ
  -- the loose members stay away from the record and from its mirror point
  have hθc : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
  have hε0' : 0 < ε := by rw [hε]; positivity
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁ρ₀]; positivity
  have hbig : ∀ y ∈ SL, ρ₁ * ε ≤ ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖ := fun y hy => by
    have e : (y - s) ^ 2 - (z₁ - s) ^ 2 = (y - z₁) * ((y - z₁) + ((2 * κ / V : ℝ) : ℂ)) := by
      have e1 : y - s = (y - z₁) + ((κ / V : ℝ) : ℂ) := by rw [← hθc]; ring
      rw [e1, hθc]; push_cast; ring
    rw [e, norm_mul]
    exact mul_le_mul ((hSLmem y).mp hy).2.le (hmirror y (hSLT hy)) hε0'.le (norm_nonneg _)
  -- the core is coherent with the record
  have hDS : ∀ c ∈ S, D c ≠ 0 := fun c hc => by
    rw [hS, Set.Finite.mem_toFinset] at hc; exact hc.1
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hh₁ := le_norm_paperFT_of_loud_zero hw (hmem z₁ hz₁) hup hD₁ hH
  have hcoh : ∀ c ∈ S.filter (fun z => z ∉ SL), 0 ≤ (D c * conj (D z₁)).re := fun c hc => by
    have hcS := (Finset.mem_filter.mp hc).1
    have hcz := hcρ c hc
    exact re_one_param_mul_conj_nonneg hw (hmem z₁ hz₁) (hmem c (hDS c hcS)) hh₁
      (le_trans (mul_le_mul_of_nonneg_left hcz (mul_nonneg (by positivity) hJ0)) hρL)
      (le_trans (mul_le_mul_of_nonneg_left hcz hw.le) hρw)
  -- the mass of the core, relative to the record
  obtain ⟨Dm, hDm⟩ : ∃ Dm : ℝ, Dm = 125 / 2 * Real.log (180 * (Γ + 1)) * ‖D z₁‖ := ⟨_, rfl⟩
  have hDc : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤ Dm := fun c hc => by
    have hcS := (Finset.mem_filter.mp hc).1
    have hcz := hcρ c hc
    have himc : |c.im| ≤ Γ + 1 := by
      have h1 := Complex.abs_im_le_norm (c - z₁)
      rw [Complex.sub_im] at h1
      have h2 := abs_sub_abs_le_abs_sub c.im z₁.im
      linarith only [h1, h2, hcz, hup, hρr, hσ1]
    rw [hDm]
    exact norm_evenCoeff_zero_le_of_near hw (hmem z₁ hz₁) (hmem c (hDS c hcS)) hh₁
      (le_trans (mul_le_mul_of_nonneg_left hcz (mul_nonneg (by positivity) hJ0)) hρL)
      (le_trans (mul_le_mul_of_nonneg_left hcz hw.le) hρw) himc
  have hCcard : (S.filter fun z => z ∉ SL).card ≤ P + 1 :=
    (Finset.card_filter_le _ _).trans (by
      rw [← Finset.card_erase_add_one hz₁S]
      exact Nat.succ_le_succ ((Finset.card_le_card hST).trans hTcard))
  have hsumD : ∑ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤ (P + 1) * Dm := by
    have h := Finset.sum_le_card_nsmul _ (fun c => ‖D c‖) Dm hDc
    rw [nsmul_eq_mul] at h
    have hD0 : 0 ≤ Dm := le_trans (norm_nonneg _) (hDc z₁ hz₁C)
    have hc : ((S.filter fun z => z ∉ SL).card : ℝ) ≤ P + 1 := by exact_mod_cast hCcard
    exact h.trans (mul_le_mul_of_nonneg_right hc hD0)
  -- the perturbation over the core
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = (4 * κ₀ / V + ρ) * (2 * (P + 1) * V) / (G * κ₀) := ⟨_, rfl⟩
  have ht₀0 : 0 ≤ t₀ := by rw [ht₀]; positivity
  have hτ : (1 + t₀) ^ SL.card - 1 ≤ coreFactorPerturbation P κ₀ V ρ G := by
    rw [coreFactorPerturbation, ← ht₀]
    have := pow_le_pow_right₀ (by linarith only [ht₀0] : (1 : ℝ) ≤ 1 + t₀) hpP
    linarith only [this]
  have hτ0 : 0 ≤ coreFactorPerturbation P κ₀ V ρ G := by
    have := one_le_pow₀ (n := SL.card) (by linarith only [ht₀0] : (1 : ℝ) ≤ 1 + t₀)
    linarith only [this, hτ]
  have hmass : ((1 + coreFactorPerturbation P κ₀ V ρ G) * (2 * (ρ * V)) +
      coreFactorPerturbation P κ₀ V ρ G) * ∑ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤
        ‖D z₁‖ / 2 := by
    have hη0 : 0 ≤ (1 + coreFactorPerturbation P κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation P κ₀ V ρ G := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsumD hη0
    have h2 := mul_le_mul_of_nonneg_right hηm (norm_nonneg (D z₁))
    rw [hDm] at h1
    linarith only [h1, h2]
  have hgap : ρ₀ * (2 * (κ / V) + ρ₀) ≤ t₀ * (ρ₁ * ε) := by
    rw [ht₀, hρ₁ρ₀, hε]
    exact core_gap_arith hρ₀0.le hρ₀ρ hG0 hκ₀0 hV (Nat.cast_nonneg P) hκ2
  have hθ0 : 0 < κ / V := div_pos hκ0 hV
  have hcore_ge := eliminated_core_ge hz₁C D (k + SL.card) hV hθc hθ0.le hρ₀0.le
    (mul_pos hρ₁0 hε0') hbig hcρ₀ hgap hτ (mul_le_mul_of_nonneg_right hρ₀ρ hV.le) hρV hcoh hmass
  have hcol := hcore_ge.trans hPE
  -- the arithmetic of `one_param_cluster_collapse` with `Π|y − z*|` replaced by `ρ₁^p/2`
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = SL.card := ⟨_, rfl⟩
  rw [← hp] at hcol hpP
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (180 * (|z₁.im| + 6)) := ⟨_, rfl⟩
  obtain ⟨LΓ, hLΓ⟩ : ∃ LΓ : ℝ, LΓ = Real.log (180 * (Γ + 6)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : ℝ, Q₂ = (4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (2 * (k + p)).factorial * (π / V) ^ (2 * (k + p)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos Real.pi_pos hV) _)
  have hbase : ∀ t : ℝ, 0 < t → 0 < t ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := fun t ht =>
    add_pos_of_pos_of_nonneg (pow_pos ht 2)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg π)) (sq_nonneg _))
  have hQ0 : 0 < Q := by rw [hQ]; exact pow_pos (hbase κ hκ0) _
  have hKlow : u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q) ≤
      ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (norm_fejerPowWin_ofReal_ge hV (k + p) hθ0)
    have hVne : V ≠ 0 := hV.ne'
    have hκne : κ ≠ 0 := hκ0.ne'
    have e : (κ / V) ^ 2 + (2 * π * ((k + p : ℕ) : ℝ) / V) ^ 2 =
        (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) / V ^ 2 := by
      field_simp; ring
    rw [e, div_mul_cancel₀ κ hVne, hu, hQ, div_pow, div_pow, ← pow_mul V 2 (k + p), pow_succ]
    field_simp
  rw [← hu, ← hL] at hcol
  -- the mass of the unmodulated family is bounded
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = 32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log 4) := ⟨_, rfl⟩
  have hWb := tsum_norm_evenCoeff_modScaledBump_le hw 0
  have hMb := abs_two_re_lagStructure_zero_le zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w 0) (modScaledBump_support hw 0)
  rw [abs_zero, zero_add] at hWb
  have hW0 : 0 ≤ ∑' z : ℂ, ‖D z‖ := tsum_nonneg fun z => norm_nonneg _
  have hMW : |2 * (lagStructure zetaZeroConfig b 0).re| + ∑' z : ℂ, ‖D z‖ ≤ m₀ := by
    rw [hm₀]; linarith only [hWb, hMb]
  have hL0 : 0 ≤ L := by
    rw [hL]; exact Real.log_nonneg (by have := abs_nonneg z₁.im; linarith only [this])
  have hLL : L ≤ LΓ := by
    rw [hL, hLΓ]
    exact Real.log_le_log (by have := abs_nonneg z₁.im; positivity) (by linarith only [hup])
  have hκ1' : 1 ≤ κ := hκ₀.trans hκ1
  have hε₀ : 0 < a := ha
  have hΞ := xi_ratio_le_general hκ1' hε₀ hD₁ hL0 hW0 hMW
  have hQQ : κ * Q ≤ 2 * κ₀ * Q₂ := by
    have hq : Q ≤ Q₂ := by
      rw [hQ, hQ₂]
      refine pow_le_pow_left₀ (hbase κ hκ0).le ?_ _
      have h2 : κ ^ 2 ≤ (2 * κ₀) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [h2, e]
    exact mul_le_mul hκ2 hq hQ0.le (by linarith only [hκ₀0])
  have he1 : 0 < Real.exp 1 - 1 := by linarith only [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hm00 : 0 ≤ m₀ := le_trans (add_nonneg (abs_nonneg _) hW0) hMW
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 4 * m₀ / ((Real.exp 1 - 1) * a) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; exact div_nonneg (by linarith only [hm00]) (mul_pos he1 hε₀).le
  rw [← hX] at hΞ
  have hΞ' : 4 * |2 * (lagStructure zetaZeroConfig b 0).re| + 4 * ∑' z : ℂ, ‖D z‖ +
      3840 * L * ‖D z₁‖ * Real.exp κ ≤ (X + 6144 * L) * 1 * (‖D z₁‖ * (Real.exp κ - 1)) := by
    rw [mul_one]; exact hΞ
  have hE : 0 < Real.exp κ - 1 := by linarith only [Real.add_one_lt_exp hκ0.ne', hκ0]
  have hc0 : (0 : ℝ) ≤ (8 / 3) ^ p * (4 / 3) ^ k :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have hPr0 : 0 ≤ ρ₁ ^ p / 2 := by positivity
  have hXL : 0 ≤ (X + 6144 * L) * 1 := by rw [mul_one]; linarith only [hX0, hL0]
  have hcol' : ‖D z₁‖ * (ρ₁ ^ p / 2) * ε ^ p * ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ ≤
      u * ((8 / 3) ^ p * (4 / 3) ^ k *
        (4 * |2 * (lagStructure zetaZeroConfig b 0).re| + 4 * (∑' z : ℂ, ‖D z‖) +
          3840 * L * ‖D z₁‖ * Real.exp κ) / r ^ (2 * k + 1)) :=
    le_trans (le_of_eq (by rw [mul_pow]; ring)) hcol
  have hfin := cluster_log_arith (D := ‖D z₁‖) (u := u) (E := Real.exp κ - 1)
    (norm_pos_iff.mpr hz₁) hu0 hE hε0'.le hPr0 hr0 hV (mul_pos hκ0 hQ0) hcol' hKlow hΞ' hc0 hQQ
    hXL (p := p) (m := 2 * (k + p) + 1) (k := k)
  have e : ε ^ p * V ^ (2 * (k + p) + 1) = (κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) := by
    have hVne : V ≠ 0 := hV.ne'
    rw [hε, show 2 * (k + p) + 1 = (2 * k + p + 1) + p by ring, pow_add, div_pow, div_pow, mul_pow]
    field_simp
  have hQ₂0 : 0 ≤ Q₂ := by
    rw [hQ₂]
    have : 0 < 4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := by
      have := hbase (2 * κ₀) (by linarith only [hκ₀0])
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [this, e]
    exact (pow_pos this _).le
  have h1 : (X + 6144 * L) * 1 ≤ X + 6144 * LΓ := by rw [mul_one]; linarith only [hLL]
  have h2 : 0 ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) :=
    mul_nonneg hc0 (mul_nonneg (by linarith only [hκ₀0]) hQ₂0)
  have hb : (ρ₁ ^ p * (κ₀ / (2 * (P + 1))) ^ p) / 2 * (V ^ (2 * k + p + 1) * r ^ (2 * k + 1)) ≤
      recordCollapseBound w a Γ κ₀ k p :=
    calc (ρ₁ ^ p * (κ₀ / (2 * (P + 1))) ^ p) / 2 * (V ^ (2 * k + p + 1) * r ^ (2 * k + 1))
        = ρ₁ ^ p / 2 * (ε ^ p * V ^ (2 * (k + p) + 1)) * r ^ (2 * k + 1) := by rw [e]; ring
      _ = ρ₁ ^ p / 2 * ε ^ p * V ^ (2 * (k + p) + 1) * r ^ (2 * k + 1) := by ring
      _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * ((X + 6144 * L) * 1) := hfin
      _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (X + 6144 * LΓ) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = recordCollapseBound w a Γ κ₀ k p := by
          rw [recordCollapseBound, ← hLΓ, ← hQ₂, hX, hm₀]; ring
  -- the gap ladder bounds the loose radius from below
  have hab : (ρ * κ₀ / (2 * (P + 1) * G ^ P)) ^ p ≤ ρ₁ ^ p * (κ₀ / (2 * (P + 1))) ^ p := by
    rw [← mul_pow]
    have e2 : ρ * κ₀ / (2 * (P + 1) * G ^ P) = ρ / G ^ P * (κ₀ / (2 * (P + 1))) := by
      field_simp
    refine pow_le_pow_left₀ (by positivity) ?_ p
    rw [e2]
    exact mul_le_mul_of_nonneg_right hρ₁P (by positivity)
  exact visible_final_arith hab (by positivity) hb (hmain p hpP)


/-- **The one-parameter family sees near-top zeros.** Let `½ + z₀` be a zero right of the line,
`δ₀ = Re z₀`, with `η = |h_w(γ₀ − iδ₀)| > 0`, `1/V`-near the top, `Γ₀ = Γ₀(η)`, `P ≥ 80 log(180Γ₀)`.
Let `k ≥ 1`, `κ₀ ≥ 1`, `2κ₀/V ≤ δ₀/16`, `V ≥ π(k + P)`, `Vδ₀/8 ≥ 4π(k + P)`, the record-depth
condition, `H₀² ≤ (2η²/e)/(80 log(180Γ₀))`, and a core scale `ρ > 0` and gap `G ≥ 1` with
`ρV ≤ 1`, `wρ ≤ 1`, `8w e^{w/2} J_w ρ ≤ H₀`, `ρ ≤ δ₀/16`,
`((1 + τ)·2ρV + τ)(P + 1)·(125/2) log(180(Γ₀ + 1)) ≤ 1/2` (`τ = coreFactorPerturbation`),
and for every `p ≤ P`, `2B₀(p) < (ρκ₀/(2(P + 1)G^P))^p V^{2k+p+1}(δ₀/8)^{2k+1}`
(`oneParamCollapseBound`). Then `P_v < 0` for some lag `v ∈ [0, V]`, where `P_v` is the Weil form of
`κ_w(t + v/2) − κ_w(t − v/2)`. -/
theorem one_param_near_top_visible {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : 0 < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) {P : ℕ}
    (hP : 80 * Real.log (180 * oneParamRecordHeight w η) ≤ P)
    {κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀)
    (hV2 : 2 * Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2)) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + P : ℕ) ≤ V)
    (hVr : 4 * π * (k + P : ℕ) ≤ V * (z₀.re / 8)) {H₀ : ℝ}
    (hH : H₀ ^ 2 ≤ 2 * η ^ 2 / Real.exp 1 / (80 * Real.log (180 * oneParamRecordHeight w η)))
    {ρ G : ℝ} (hρ : 0 < ρ) (hG : 1 ≤ G) (hρV : ρ * V ≤ 1) (hρw : w * ρ ≤ 1)
    (hρL : 8 * w * Real.exp (w / 2) * bumpMass w * ρ ≤ H₀) (hρr : ρ ≤ z₀.re / 16)
    (hηm : ((1 + coreFactorPerturbation P κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation P κ₀ V ρ G) * ((P + 1) * (125 / 2 * Real.log (180 *
          (oneParamRecordHeight w η + 1)))) ≤ 1 / 2)
    (hmain : ∀ p : ℕ, p ≤ P → 2 * oneParamCollapseBound w η κ₀ k p <
      (ρ * κ₀ / (2 * (P + 1) * G ^ P)) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1)) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  have htop' : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 →
      z.re ≤ z₀.re + 1 / V := fun z hz => by
    have hmem : (1 / 2 + z) ∈ zetaZeroConfig.carrier := by
      rcases mem_of_evenCoeff_ne_zero hz with h | h
      · exact h
      · have := conj_mem_zetaZeroConfig h
        have e : conj (1 / 2 + conj z) = 1 / 2 + z := by apply Complex.ext <;> simp
        rwa [e] at this
    have := htop _ hmem
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    linarith
  obtain ⟨z₁, hz₁, hre₁, hup, hD₁, hrec⟩ := one_param_record_facts hw hV hz₀ hre₀ hη hηle htop' hV2
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1 : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have e8 : z₀.re / 2 / 4 = z₀.re / 8 := by ring
  exact one_param_record_visible hw hV hz₁ (half_pos hre₀) (by linarith) hre₁ (by positivity) hD₁ hup
    hrec hP hk hκ₀ (by linarith) hVk (by rw [e8]; exact hVr) hH hρ hG hρV hρw hρL (by linarith) hηm
    (fun p hp => by rw [e8, ← oneParamCollapseBound_eq_record]; exact hmain p hp)

end GaloisForLFunctions.SquareRootThreshold
