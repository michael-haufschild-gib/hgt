import GaloisForLFunctions.ZeroConfigurationGeometry.TheLocalCameraConstantIsQuasiPolynomial
import GaloisForLFunctions.ZeroConfigurationGeometry.SplineBumpsDecayAtAnExplicitRate
import GaloisForLFunctions.ZeroConfigurationGeometry.ZetaZerosHaveTheSharpLocalDensity

/-!
# The local camera fixes the isolated zeros of ζ

**Theorem** (`multDiff_zeta_eq_zero_of_isolated`). Let `μ ≥ 0`, `A' ≥ 0`, `S'` and a bandwidth
`λ > 1/4 + πμ/2`. For every large height `X` the following holds. Let `Z'` be a tempered
configuration with the same image as the zeros of `ζ` at aperture `λ log X`, with at most
`μ log X (y − x) + A' log X` points at heights in `[x, y] ⊆ [X/2, 3X/2]`, and with
`Σ |c|/(1 + |γ|²) ≤ S'`. Then `ζ` and `Z'` have the same multiplicity at every point `z₀` of height
`X` that is `π/(λ log X)`-isolated from the rest of their cluster within height distance `X/2`.

For a mimic with the density of `ζ`, `μ = 1/(2π)`, the bandwidth condition is `λ > ½`. This is
the square-root threshold of `rvmLattice_mimic_iff`, now for the zeros of `ζ` themselves: at
bandwidth `λ > ½` the arithmetic image fixes every zero of `ζ` that is isolated at a fixed fraction
`1/(2λ)` of the mean spacing `2π/log X`.

Proof. Apply the local camera with the bump `exists_explicit_bump`, at density
`D = (2/π)(λ − β/2) log X`, where `β = λ − 1/4 − πμ/2`. The cluster has at most the count of `ζ`
(`exists_card_le_sharp_centred`) plus that of `Z'`, of density `≤ D` and error `O(log X)`.
Write `L = log X`. The window constants give `log B = O(L²)`
(`TheLocalCameraConstantIsQuasiPolynomial`): `D (1 + log D)² ≤ 4D²` and `D ≤ λL`, and the bump of
order `m ≍ L` at aperture `ε ≍ L` has `log C_m = O(L)`. With decay order `k = ⌈(c + 1) L⌉`,
`(1 + X/2)^{2k−2} ≥ X^{k−1} = e^{(k−1)L}` beats `B (1 + X)² S'`.
-/

open MeasureTheory Complex Set Filter Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

theorem one_add_log_sq_le {D : ℝ} (hD : 1 ≤ D) : (1 + Real.log D) ^ 2 ≤ 4 * D := by
  have hD0 : 0 < D := by linarith
  have ht : 0 ≤ Real.log D := Real.log_nonneg hD
  have h := Real.quadratic_le_exp_of_nonneg ht
  rw [Real.exp_log hD0] at h
  nlinarith

theorem one_add_log_le {D : ℝ} (hD : 1 ≤ D) : 1 + Real.log D ≤ D := by
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < D)
  linarith

theorem nfRate_nonneg {σ : ℝ} (hσ : 0 ≤ σ) : 0 ≤ nfRate σ := by
  unfold nfRate
  have : 0 ≤ Real.log (2 * σ + 9) := Real.log_nonneg (by linarith)
  positivity

theorem growthRate_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : 0 ≤ growthRate ℓ := by
  have hσ : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have := nfRate_nonneg hσ
  unfold growthRate
  positivity

theorem floorRate_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : 0 ≤ floorRate ℓ := by
  have hσ : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have := nfRate_nonneg hσ
  unfold floorRate
  positivity

theorem windowGrowth_pos {H L : ℝ} (hH : 0 < H) (hL : 0 ≤ L) : 0 < windowGrowth H L := by
  have hS : 0 ≤ windowSlack H L := by rw [windowSlack]; linarith
  rw [windowGrowth, nearestConstStrip]
  exact mul_pos (mul_pos (by positivity) (Real.exp_pos _)) (Real.exp_pos _)

/-- **The local camera constant in exponential form.** -/
theorem localCameraConst_le {a D C₀ η ε Cm ℓ : ℝ} (hD : 1 ≤ D) (hC : |C₀| ≤ ℓ * D)
    (hη : D⁻¹ ≤ η) (hCm : 0 < Cm) :
    localCameraConst a D C₀ η ε Cm 1 ≤ 5 / 4 * Real.exp (2 * (growthRate ℓ * D *
      (1 + Real.log D)) + 2 * Real.log Cm + 2 * ε + a + 2 * (floorRate ℓ * D *
        (1 + Real.log D) ^ 2)) := by
  have hD0 : 0 < D := by linarith
  have hL0 := localSlack_nonneg (C₀ := C₀) hD0
  obtain ⟨G, hG⟩ : ∃ G, G = windowGrowth (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = windowFloor (2 * D⁻¹) (localSlack D C₀) η := ⟨_, rfl⟩
  have hG0 : 0 < G := by rw [hG]; exact windowGrowth_pos (by positivity) hL0
  have hF0 : 0 < F := by
    rw [hF]; exact windowFloor_pos (by positivity) hL0 (lt_of_lt_of_le (inv_pos.mpr hD0) hη)
  have hGl := log_windowGrowth_le hD hC
  have hFl := log_inv_windowFloor_le hD hC hη
  rw [← hG] at hGl
  rw [← hF] at hFl
  have hx : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
    rw [sq, ← Real.exp_add, two_mul]
  have e : localCameraConst a D C₀ η ε Cm 1 = 5 / 4 * Real.exp (2 * Real.log G +
      2 * Real.log Cm + 2 * ε + a + 2 * Real.log F⁻¹) := by
    rw [localCameraConst, ← hG, ← hF, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
      ← hx, ← hx, ← hx, ← hx, Real.exp_log hG0, Real.exp_log hCm,
      Real.exp_log (inv_pos.mpr hF0)]
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

/-! ### The parameters at height `X` -/

section Parameters

variable {lam μ β L D : ℝ}

theorem camera_aperture_eq (hβ : β = lam - 1 / 4 - π * μ / 2)
    (hD : D = (β / π + 1 / (2 * π) + μ) * L) : π * D / 2 + 2 * (β * L / 4) ≤ lam * L := by
  refine le_of_eq ?_
  rw [hD, hβ]
  field_simp
  ring

theorem camera_density_ge (hμ : 0 ≤ μ) (hβ : β = lam - 1 / 4 - π * μ / 2) (hL : 0 ≤ L)
    (hD : D = (β / π + 1 / (2 * π) + μ) * L) : lam * L / π ≤ D := by
  have hπ := Real.pi_pos
  have e : lam / π = β / π + 1 / (4 * π) + μ / 2 := by rw [hβ]; field_simp; ring
  have h1 : 1 / (4 * π) ≤ 1 / (2 * π) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  rw [hD, show lam * L / π = lam / π * L by ring, e]
  exact mul_le_mul_of_nonneg_right (by linarith) hL

theorem camera_density_le (hμ : 0 ≤ μ) (hβ : β = lam - 1 / 4 - π * μ / 2) (hβ0 : 0 < β)
    (hL : 0 ≤ L) (hD : D = (β / π + 1 / (2 * π) + μ) * L) : D ≤ lam * L := by
  have hπ := Real.pi_gt_three
  have h1 : β / π ≤ β := div_le_self hβ0.le (by linarith)
  have h2 : 1 / (2 * π) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h3 : μ ≤ π * μ / 2 := by nlinarith
  have hlam : lam = β + 1 / 4 + π * μ / 2 := by rw [hβ]; ring
  rw [hD, hlam]
  exact mul_le_mul_of_nonneg_right (by linarith) hL

theorem camera_density_count (hβ0 : 0 < β) (hLβ : 1 / (2 * β) ≤ L)
    (hD : D = (β / π + 1 / (2 * π) + μ) * L) : (L + 1) / (2 * π) + μ * L ≤ D := by
  have hπ := Real.pi_pos
  have h3 : 1 ≤ 2 * β * L := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * β)).mp hLβ
    linarith
  rw [hD, show (β / π + 1 / (2 * π) + μ) * L = (2 * β * L + L) / (2 * π) + μ * L by
    field_simp]
  have : (L + 1) / (2 * π) ≤ (2 * β * L + L) / (2 * π) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

end Parameters

/-! ### The count of `ζ` at height `X` -/

theorem log_count_arg_le {X : ℝ} (hX : 32 ≤ X) :
    0 ≤ Real.log ((X + X / 2 + 2) / (2 * Real.pi)) ∧
      Real.log ((X + X / 2 + 2) / (2 * Real.pi)) ≤ Real.log X := by
  have hπ := Real.pi_gt_three
  have hπ4 := Real.pi_le_four
  have hX0 : 0 < X := by linarith
  refine ⟨Real.log_nonneg ?_, Real.log_le_log (by positivity) ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

theorem six_div_le {X : ℝ} (hX : 32 ≤ X) :
    0 ≤ 6 / (X - X / 2 - 2) ∧ 6 / (X - X / 2 - 2) ≤ 1 :=
  ⟨div_nonneg (by norm_num) (by linarith), by rw [div_le_one (by linarith)]; linarith⟩

theorem log_count_le {X : ℝ} (hX : 32 ≤ X) :
    0 ≤ Real.log (X + X / 2 + 2) ∧ Real.log (X + X / 2 + 2) ≤ 2 * Real.log X := by
  have hX0 : 0 < X := by linarith
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  rw [← Real.log_rpow hX0, show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact Real.log_le_log (by positivity) (by nlinarith)

/-- **The cluster of `ζ` and a mimic is counted by both.** -/
theorem card_cluster_le {Z' : ZeroConfig} {X R Dζ Cζ D' C' x y : ℝ} {s : Finset ℂ}
    (hζ : ∀ t : Finset ℂ, (∀ z ∈ t, IsNontrivialZero z ∧ |z.im - X| ≤ R ∧ z.im ∈ Icc x y) →
      (t.card : ℝ) ≤ Dζ * (y - x) + Cζ)
    (hZ' : ∀ t : Finset ℂ, (∀ z ∈ t, z ∈ Z'.carrier ∧ |z.im - X| ≤ R ∧ z.im ∈ Icc x y) →
      (t.card : ℝ) ≤ D' * (y - x) + C')
    (hs : ∀ z ∈ s, multDiff zetaZeroConfig Z' z ≠ 0 ∧ |z.im - X| ≤ R ∧ z.im ∈ Icc x y) :
    (s.card : ℝ) ≤ (Dζ + D') * (y - x) + (Cζ + C') := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := s)
    (fun z => z ∈ zetaZeroConfig.carrier)
  have h1 := hζ (s.filter fun z => z ∈ zetaZeroConfig.carrier) fun z hz => by
    obtain ⟨hzs, hzc⟩ := Finset.mem_filter.mp hz
    obtain ⟨_, h2, h3⟩ := hs z hzs
    exact ⟨hzc, h2, h3⟩
  have h2 := hZ' (s.filter fun z => ¬ z ∈ zetaZeroConfig.carrier) fun z hz => by
    obtain ⟨hzs, hzc⟩ := Finset.mem_filter.mp hz
    obtain ⟨h1, h2, h3⟩ := hs z hzs
    refine ⟨?_, h2, h3⟩
    rcases mem_carrier_of_multDiff_ne_zero h1 with h | h
    · exact absurd h hzc
    · exact h
  have hcard : (s.card : ℝ) = ((s.filter fun z => z ∈ zetaZeroConfig.carrier).card : ℝ) +
      ((s.filter fun z => ¬ z ∈ zetaZeroConfig.carrier).card : ℝ) := by
    exact_mod_cast hsplit.symm
  rw [hcard]
  linarith

/-! ### The budget -/

/-- The exponent of the camera constant is quadratic in `L = log X`. -/
theorem camera_exponent_le {lam β L D ε a m q e K g f lCm : ℝ} (hβlam : β ≤ lam) (hβ0 : 0 ≤ β)
    (hL : 0 ≤ L) (hq : 0 ≤ q) (hε : ε = β * L / 4) (ha : a = lam * L)
    (hG : g * D * (1 + Real.log D) ≤ 2 * g * lam ^ 2 * L ^ 2)
    (hF : f * D * (1 + Real.log D) ^ 2 ≤ 4 * f * lam ^ 2 * L ^ 2)
    (hlogCm : lCm ≤ m * q) (hmle : m ≤ (e * lam + K + 2) * L) :
    2 * (g * D * (1 + Real.log D)) + 2 * lCm + 2 * ε + a + 2 * (f * D * (1 + Real.log D) ^ 2) ≤
      (4 * g * lam ^ 2 + 8 * f * lam ^ 2) * L ^ 2 +
        (2 * q * (e * lam + K + 2) + 2 * lam) * L := by
  have h1 : m * q ≤ (e * lam + K + 2) * L * q := mul_le_mul_of_nonneg_right hmle hq
  have h2 : β * L ≤ lam * L := mul_le_mul_of_nonneg_right hβlam hL
  have h3 : 0 ≤ β * L := mul_nonneg hβ0 hL
  rw [hε, ha]
  linarith

/-- The final comparison: `e^{(k−1)L}` beats `e^{Φ + 2L + log S + 2}`. -/
theorem camera_budget_false {L c K k Φ b₁ lS : ℝ} (hL1 : 1 ≤ L) (hK : K = c + 1)
    (hkL : K * L ≤ k) (hΦ : Φ ≤ c * L ^ 2 + (b₁ - 3) * L) (hLb : b₁ + lS + 4 ≤ L)
    (hlS : 0 ≤ lS) (h : (k - 1) * L ≤ Φ + 2 * L + lS + 2) : False := by
  have h1 : (K * L - 1) * L ≤ (k - 1) * L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : (b₁ + lS + 4) * L ≤ L * L := mul_le_mul_of_nonneg_right hLb (by linarith)
  have h3 : lS + 4 ≤ (lS + 4) * L := le_mul_of_one_le_right (by linarith) hL1
  rw [hK] at h1
  nlinarith

theorem camera_lower_bound {X L : ℝ} {k : ℕ} (hX : 0 < X) (hXL : X = Real.exp L) (hk : 1 ≤ k) :
    Real.exp ((k - 1 : ℝ) * L) ≤ (1 + X / 2) ^ (2 * k - 2) := by
  have e1 : 2 * k - 2 = 2 * (k - 1) := by omega
  have e2 : ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) := by push_cast [hk]; ring
  rw [e1, pow_mul, e2, Real.exp_nat_mul, ← hXL]
  exact pow_le_pow_left₀ hX.le (by nlinarith) _

theorem camera_upper_bound {B Y S S'' Φ L : ℝ} (hB : B ≤ 5 / 4 * Real.exp Φ)
    (hY : Y ≤ 4 * Real.exp (2 * L)) (hY0 : 0 ≤ Y) (hS0 : 0 ≤ S) (hS : S ≤ S'')
    (hS'' : 1 ≤ S'') : B * Y * S ≤ Real.exp (Φ + 2 * L + Real.log S'' + 2) := by
  have h5 : (5 : ℝ) ≤ Real.exp 2 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  calc B * Y * S ≤ 5 / 4 * Real.exp Φ * (4 * Real.exp (2 * L)) * S'' :=
        mul_le_mul (mul_le_mul hB hY hY0 (by positivity)) hS hS0 (by positivity)
    _ = 5 * (Real.exp Φ * Real.exp (2 * L) * Real.exp (Real.log S'')) := by
        rw [Real.exp_log (by linarith)]; ring
    _ ≤ Real.exp 2 * (Real.exp Φ * Real.exp (2 * L) * Real.exp (Real.log S'')) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = Real.exp (Φ + 2 * L + Real.log S'' + 2) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring

theorem growth_term_le {g D lam L : ℝ} (hg : 0 ≤ g) (hD1 : 1 ≤ D) (hDup : D ≤ lam * L) :
    g * D * (1 + Real.log D) ≤ 2 * g * lam ^ 2 * L ^ 2 := by
  have hD0 : 0 ≤ D := by linarith
  have h1 : D * (1 + Real.log D) ≤ D ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_left (one_add_log_le hD1) hD0
  have h2 : D ^ 2 ≤ (lam * L) ^ 2 := pow_le_pow_left₀ hD0 hDup 2
  have h3 : g * (D * (1 + Real.log D)) ≤ g * (lam * L) ^ 2 :=
    mul_le_mul_of_nonneg_left (h1.trans h2) hg
  nlinarith [mul_nonneg hg (sq_nonneg (lam * L))]

theorem floor_term_le {f D lam L : ℝ} (hf : 0 ≤ f) (hD1 : 1 ≤ D) (hDup : D ≤ lam * L) :
    f * D * (1 + Real.log D) ^ 2 ≤ 4 * f * lam ^ 2 * L ^ 2 := by
  have hD0 : 0 ≤ D := by linarith
  have h1 : D * (1 + Real.log D) ^ 2 ≤ 4 * D ^ 2 := by
    have := mul_le_mul_of_nonneg_left (one_add_log_sq_le hD1) hD0
    nlinarith
  have h2 : D ^ 2 ≤ (lam * L) ^ 2 := pow_le_pow_left₀ hD0 hDup 2
  have h3 : f * (D * (1 + Real.log D) ^ 2) ≤ f * (4 * (lam * L) ^ 2) :=
    mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hf
  nlinarith

/-! ### The cluster count and the budget at height `X` -/

/-- **The cluster count at height `X`.** The cluster of `ζ` and a mimic of local density
`≤ μ log X` has count `(D, C₀)` near `X`, with `|C₀| ≤ ℓD`. -/
theorem zeta_cluster_count {Z' : ZeroConfig} {T₀ A A' μ ℓ lam L D X : ℝ} (hA : 0 ≤ A)
    (hA' : 0 ≤ A') (hμ : 0 ≤ μ) (hlam0 : 0 < lam)
    (hζ : ∀ X R : ℝ, 0 ≤ R → T₀ ≤ X - R → ∀ x y : ℝ, x ≤ y → ∀ s : Finset ℂ,
      (∀ z ∈ s, IsNontrivialZero z ∧ |z.im - X| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ (Real.log ((X + R + 2) / (2 * Real.pi)) + 6 / (X - R - 2)) /
            (2 * Real.pi) * (y - x) +
          (3 * ((Real.log ((X + R + 2) / (2 * Real.pi)) + 6 / (X - R - 2)) / (2 * Real.pi)) +
            A * Real.log (X + R + 2) + 1))
    (hX : 2 * T₀ + 16 ≤ X) (hT₀ : 8 ≤ T₀) (hL : L = Real.log X) (hL1 : 1 ≤ L)
    (hDcount : (L + 1) / (2 * π) + μ * L ≤ D) (hDlow : lam * L / π ≤ D)
    (hℓ : ℓ = 3 + (2 * A + A' + 1) * π / lam)
    (hZ'count : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, z ∈ Z'.carrier ∧ |z.im - X| ≤ X / 2 ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ μ * L * (y - x) + A' * L) :
    ∃ C₀ : ℝ, |C₀| ≤ ℓ * D ∧ ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff zetaZeroConfig Z' z ≠ 0 ∧ |z.im - X| ≤ X / 2 ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀ := by
  have hX32 : 32 ≤ X := by linarith
  have hπ := Real.pi_pos
  obtain ⟨Dζ, hDζ⟩ : ∃ Dζ, Dζ = (Real.log ((X + X / 2 + 2) / (2 * Real.pi)) +
      6 / (X - X / 2 - 2)) / (2 * Real.pi) := ⟨_, rfl⟩
  obtain ⟨Cζ, hCζ⟩ : ∃ Cζ, Cζ = 3 * ((Real.log ((X + X / 2 + 2) / (2 * Real.pi)) +
      6 / (X - X / 2 - 2)) / (2 * Real.pi)) + A * Real.log (X + X / 2 + 2) + 1 := ⟨_, rfl⟩
  obtain ⟨hl0, hl1⟩ := log_count_arg_le hX32
  obtain ⟨hs0, hs1⟩ := six_div_le hX32
  obtain ⟨hk0, hk1⟩ := log_count_le hX32
  rw [← hL] at hl1 hk1
  have hDζ0 : 0 ≤ Dζ := by rw [hDζ]; positivity
  have hDζ1 : Dζ ≤ (L + 1) / (2 * π) := by
    rw [hDζ]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hμL : 0 ≤ μ * L := mul_nonneg hμ (by linarith)
  have hDζle : Dζ + μ * L ≤ D := by linarith only [hDζ1, hDcount]
  have hDζD : Dζ ≤ D := by linarith only [hDζle, hμL]
  have hCζ0 : 0 ≤ Cζ := by rw [hCζ, ← hDζ]; positivity
  refine ⟨Cζ + A' * L, ?_, fun s x y hxy hs => ?_⟩
  · rw [abs_of_nonneg (by positivity)]
    have hAlog : A * Real.log (X + X / 2 + 2) ≤ A * (2 * L) := mul_le_mul_of_nonneg_left hk1 hA
    have hCle : Cζ + A' * L ≤ 3 * D + (2 * A + A' + 1) * L := by
      rw [hCζ, ← hDζ]; linarith only [hDζD, hAlog, hL1]
    have hLD : L ≤ π / lam * D := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam0]
      have := (div_le_iff₀ hπ).mp hDlow
      linarith only [this]
    have h2 : (2 * A + A' + 1) * L ≤ (2 * A + A' + 1) * (π / lam * D) :=
      mul_le_mul_of_nonneg_left hLD (by positivity)
    rw [hℓ]
    calc Cζ + A' * L ≤ 3 * D + (2 * A + A' + 1) * (π / lam * D) := by linarith only [hCle, h2]
      _ = (3 + (2 * A + A' + 1) * π / lam) * D := by ring
  · have h := card_cluster_le (Dζ := Dζ) (Cζ := Cζ) (D' := μ * L) (C' := A' * L)
      (fun t ht => by
        have := hζ X (X / 2) (by positivity) (by linarith) x y hxy t ht
        rwa [← hCζ, ← hDζ] at this)
      (fun t ht => hZ'count t x y hxy ht) hs
    have h2 : (Dζ + μ * L) * (y - x) ≤ D * (y - x) :=
      mul_le_mul_of_nonneg_right hDζle (sub_nonneg.mpr hxy)
    linarith only [h, h2]

/-- **The budget at height `X`.** The camera inequality at height `X` with decay order
`k ≥ (c + 1) log X` is impossible once `log X` exceeds the budget. -/
theorem zeta_camera_budget {lam β L D η ε C₀ ℓ X S S'' e K c ρ q b₁ : ℝ} {k m : ℕ}
    (hX0 : 1 ≤ X) (hXL : X = Real.exp L) (hL1 : 1 ≤ L) (hD1 : 1 ≤ D) (hDup : D ≤ lam * L)
    (hC₀ℓ : |C₀| ≤ ℓ * D) (hηD : D⁻¹ ≤ η) (hε : ε = β * L / 4) (hε0 : 0 < ε)
    (hβlam : β ≤ lam) (hβ0 : 0 < β) (hℓ0 : 0 ≤ ℓ)
    (hc : c = 4 * growthRate ℓ * lam ^ 2 + 8 * floorRate ℓ * lam ^ 2) (hK : K = c + 1)
    (hkL : K * L ≤ k) (hk1 : 1 ≤ k) (hmle : (m : ℝ) ≤ (e * lam + K + 2) * L) (hmε : (m : ℝ) / ε ≤ ρ)
    (hq : q = Real.log (4 * (1 + ρ))) (hq0 : 0 ≤ q)
    (hb₁ : b₁ = 2 * q * (e * lam + K + 2) + 2 * lam + 3)
    (hLb : b₁ + Real.log S'' + 4 ≤ L) (hS0 : 0 ≤ S) (hS : S ≤ S'') (hS''1 : 1 ≤ S'')
    (hcam : (1 + X / 2) ^ (2 * k - 2) ≤
      localCameraConst (lam * L) D C₀ η ε ((4 * (1 + m / ε)) ^ m) 1 * (1 + |X|) ^ 2 * S) :
    False := by
  have hCm0 : 0 < (4 * (1 + m / ε)) ^ m := by positivity
  have hlogCm : Real.log ((4 * (1 + m / ε)) ^ m) ≤ m * q := by
    rw [Real.log_pow, hq]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith))
      (Nat.cast_nonneg _)
  have hB := localCameraConst_le (a := lam * L) (ε := ε) hD1 hC₀ℓ hηD hCm0
  have hXpos : 0 < X := by linarith
  have hΦle := camera_exponent_le (e := e) (K := K) hβlam hβ0.le (by linarith) hq0 hε rfl
    (growth_term_le (growthRate_nonneg hℓ0) hD1 hDup) (floor_term_le (floorRate_nonneg hℓ0) hD1 hDup)
    hlogCm hmle
  have hXim : (1 + |X|) ^ 2 ≤ 4 * Real.exp (2 * L) := by
    rw [abs_of_pos hXpos, show 2 * L = L + L by ring, Real.exp_add, ← hXL]
    nlinarith
  have hupper := camera_upper_bound hB hXim (by positivity) hS0 hS hS''1
  have hfinal := ((camera_lower_bound hXpos hXL hk1).trans hcam).trans hupper
  rw [Real.exp_le_exp] at hfinal
  refine camera_budget_false hL1 hK hkL (b₁ := b₁) ?_ hLb (Real.log_nonneg hS''1) hfinal
  rw [hb₁, hc]
  linarith only [hΦle]

/-- **The local camera fixes the isolated zeros of `ζ`.** For a bandwidth `λ > 1/4 + πμ/2` and
every large height `X`: a tempered mimic of `ζ` at aperture `λ log X`, of local density
`≤ μ log X` near `X`, has the multiplicity of `ζ` at every point of height `X` that is
`π/(λ log X)`-isolated in the cluster within height distance `X/2`. -/
theorem multDiff_zeta_eq_zero_of_isolated {lam μ A' S' : ℝ} (hlam : 1 / 4 + π * μ / 2 < lam)
    (hμ : 0 ≤ μ) (hA' : 0 ≤ A') :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ Z' : ZeroConfig, TemperedConfig Z' →
      (∀ f, ApertureWindow (lam * Real.log X) f → zetaZeroConfig.W f f = Z'.W f f) →
      ∑' z, ‖multDiff zetaZeroConfig Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S' →
      (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
        (∀ z ∈ s, z ∈ Z'.carrier ∧ |z.im - X| ≤ X / 2 ∧ z.im ∈ Icc x y) →
          (s.card : ℝ) ≤ μ * Real.log X * (y - x) + A' * Real.log X) →
      ∀ z₀ : ℂ, z₀.im = X →
      (∀ z, z ≠ z₀ → multDiff zetaZeroConfig Z' z ≠ 0 → |z.im - X| ≤ X / 2 →
        π / (lam * Real.log X) ≤ ‖z - z₀‖) →
      multDiff zetaZeroConfig Z' z₀ = 0 := by
  classical
  obtain ⟨T₀, A, hT₀, hA, hζ⟩ := exists_card_le_sharp_centred
  have hπ := Real.pi_gt_three
  have hlam0 : 0 < lam := by nlinarith
  -- constants independent of the height
  obtain ⟨β, hβ⟩ : ∃ β, β = lam - 1 / 4 - π * μ / 2 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hβlam : β ≤ lam := by rw [hβ]; nlinarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = 3 + (2 * A + A' + 1) * π / lam := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; positivity
  obtain ⟨e, he⟩ : ∃ e, e = 6 * slackBound ℓ * (1 + slackBound ℓ) := ⟨_, rfl⟩
  have hσ0 : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hg0 := growthRate_nonneg hℓ0
  have hf0 := floorRate_nonneg hℓ0
  obtain ⟨c, hc⟩ : ∃ c, c = 4 * growthRate ℓ * lam ^ 2 + 8 * floorRate ℓ * lam ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = c + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = 4 * (e * lam + K + 2) / β := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = Real.log (4 * (1 + ρ)) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.log_nonneg (by linarith)
  obtain ⟨S'', hS''⟩ : ∃ S'', S'' = max S' 1 := ⟨_, rfl⟩
  have hS''1 : 1 ≤ S'' := by rw [hS'']; exact le_max_right _ _
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = 2 * q * (e * lam + K + 2) + 2 * lam + 3 := ⟨_, rfl⟩
  obtain ⟨L₀, hL₀⟩ : ∃ L₀, L₀ = max (max 1 (π / lam)) (max (1 / (2 * β))
      (b₁ + Real.log S'' + 4)) := ⟨_, rfl⟩
  refine ⟨max (2 * T₀ + 16) (Real.exp L₀), ?_⟩
  intro X hX Z' hZ' hW hS hZ'count z₀ hz₀ hiso
  by_contra hc₀
  -- the height
  have hX1 : 2 * T₀ + 16 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩
  rw [← hL] at hW hZ'count hiso
  have hLL₀ : L₀ ≤ L := by
    rw [hL, ← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hX)
  rw [hL₀] at hLL₀
  have hL1 : 1 ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hLL₀
  have hLπ : π / lam ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hLL₀
  have hLβ : 1 / (2 * β) ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hLL₀
  have hLb : b₁ + Real.log S'' + 4 ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hLL₀
  have hXL : X = Real.exp L := by rw [hL, Real.exp_log hX0]
  -- the parameters of the camera
  obtain ⟨ε, hε⟩ : ∃ ε, ε = β * L / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨D, hD⟩ : ∃ D, D = (β / π + 1 / (2 * π) + μ) * L := ⟨_, rfl⟩
  have hDa : π * D / 2 + 2 * ε ≤ lam * L := by rw [hε]; exact camera_aperture_eq hβ hD
  have hDlow := camera_density_ge hμ hβ (by linarith) hD
  have hDup := camera_density_le hμ hβ hβ0 (by linarith) hD
  have hD1 : 1 ≤ D := by
    refine le_trans ?_ hDlow
    rw [le_div_iff₀ Real.pi_pos]
    have := (div_le_iff₀ hlam0).mp hLπ
    linarith only [this]
  have hD0 : 0 < D := by linarith
  obtain ⟨η, hη⟩ : ∃ η, η = π / (lam * L) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηD : D⁻¹ ≤ η := by
    rw [hη, ← inv_div]
    exact inv_anti₀ (by positivity) hDlow
  obtain ⟨C₀, hC₀ℓ, hcount⟩ := zeta_cluster_count hA hA' hμ hlam0 hζ hX1 hT₀ hL hL1
    (camera_density_count hβ0 hLβ hD) hDlow hℓ hZ'count
  -- the decay order and the bump
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈K * L⌉₊ := ⟨_, rfl⟩
  have hkL : K * L ≤ k := by rw [hk]; exact Nat.le_ceil _
  have hkle : (k : ℝ) ≤ K * L + 1 := by
    rw [hk]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : 1 ≤ k := by
    have h1 : (1 : ℝ) ≤ K * L := one_le_mul_of_one_le_of_one_le hK1 hL1
    have : (1 : ℝ) ≤ k := h1.trans hkL
    exact_mod_cast this
  obtain ⟨W, hWdef⟩ : ∃ W, W = windowExponent (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWdef, windowExponent]
    have := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
    positivity
  have hWle : W ≤ e * D := by rw [hWdef, he]; exact windowExponent_le hD1 hC₀ℓ
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈W⌉₊ + k := ⟨_, rfl⟩
  have hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + k ≤ m := by
    rw [hmdef, ← hWdef]; push_cast; linarith [Nat.le_ceil W]
  have hmle : (m : ℝ) ≤ (e * lam + K + 2) * L := by
    rw [hmdef]; push_cast
    have h1 : (⌈W⌉₊ : ℝ) ≤ W + 1 := (Nat.ceil_lt_add_one hW0).le
    have h2 : e * D ≤ e * (lam * L) := mul_le_mul_of_nonneg_left hDup he0
    have h3 : (e * lam + K + 2) * L = e * (lam * L) + K * L + 2 * L := by ring
    rw [h3]
    linarith only [h1, h2, hWle, hkle, hL1]
  have hmε : (m : ℝ) / ε ≤ ρ := by
    rw [div_le_iff₀ hε0, hρ, hε]
    have : 4 * (e * lam + K + 2) / β * (β * L / 4) = (e * lam + K + 2) * L := by
      field_simp
    rw [this]; exact hmle
  obtain ⟨b, hb, hbs, hb1, hb0, hbm⟩ := exists_explicit_bump hε0 m
  -- the camera and the budget
  have hcam := one_add_pow_le_of_isolated_cancellation_of_bump hD0 hη0 hε0 hDa hb hbs hb1 hk1 hm
    (C0 := 1) hbm (fun w => by rw [one_mul]; exact hb0 w)
    temperedConfig_zeta hZ' hW (R := X / 2) (by positivity) hc₀
    (fun z hz hcz hzR => by rw [hη]; exact hiso z hz hcz (by rwa [hz₀] at hzR))
    (fun s x y hxy hs => hcount s x y hxy (by rwa [hz₀] at hs))
  rw [hz₀] at hcam
  have hS0 : 0 ≤ ∑' z, ‖multDiff zetaZeroConfig Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    tsum_nonneg fun z => div_nonneg (norm_nonneg _)
      (by have := Complex.normSq_nonneg (gammaOf z); linarith)
  exact zeta_camera_budget (by linarith) hXL hL1 hD1 hDup hC₀ℓ hηD hε hε0 hβlam hβ0 hℓ0 hc hK hkL
    hk1 hmle hmε hq hq0 hb₁ hLb hS0 (hS.trans (by rw [hS'']; exact le_max_left _ _)) hS''1
    hcam

end GaloisForLFunctions.ZeroConfigurationGeometry
