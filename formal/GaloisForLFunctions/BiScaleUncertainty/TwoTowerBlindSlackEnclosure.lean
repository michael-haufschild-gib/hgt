import GaloisForLFunctions.BiScaleUncertainty.IncidenceGainOfTheSingleIntegerBathtub

/-!
# The blind slack on the powers of two integers: line duality and product designs

Fix integers `q₁, q₂ ≥ 2`, `ℓᵢ = log qᵢ`, and consider nonnegative combinations blind at every power
of `q₁` and every power of `q₂`. Blindness at the powers of `qᵢ` makes the spectral law uniform on
the circle `r ↦ r ℓᵢ mod 2π` (`integral_combinationSpectralDensity_mul_periodic`). The two circles
are read off one real frequency `r`: the joint phase `r ↦ (r ℓ₁, r ℓ₂)` winds densely around the
torus when `q₁, q₂` are multiplicatively independent, and the archimedean symbol `γ(r)` is a function
of `r` on that line, not of a point of the torus.

* **Line duality** (`LineCertificate.value_mul_massOf_le`). If continuous even circle observables
  satisfy `P₁(r ℓ₁) + P₂(r ℓ₂) ≤ γ(r)` for every real `r` (a *line certificate*), then
  `A(c) ≥ (⟨P₁⟩ + ⟨P₂⟩) ‖c‖²` on the blind cone. The constraint is imposed on the line only. The
  folded symbol of one tower is a certificate (`foldCertificate₁`, value `m_{q₁}`); the incidence
  gain `η(q₁, q₂)` of `IncidenceGainOfTheSingleIntegerBathtub` is a certificate correction.
* **Product designs** (`exists_blindOn_two_towers_archOnly_le`). Midpoint atoms
  `ω_a = (a + ½)π/(N ℓ₁)` and `ω'_b = (b + ½)π/(N ℓ₂)` combine into the `2N²` frequencies
  `ω_a ± ω'_b`. Their cosine sum factors, `Σ cos((ω_a ± ω'_b)t) = 2 Σ_a cos(ω_a t) Σ_b cos(ω'_b t)`,
  so it vanishes at `t = i ℓ₁` and at `t = j ℓ₂` for `i, j < 2N`; modulations of an envelope whose
  correlation vanishes beyond `2N min ℓᵢ` are blind at every power of both integers. Their symbol
  is a two-dimensional midpoint sum of `(γ(x + y) + γ(x − y))/2`, which converges to the
  **product mean** `T(q₁, q₂)`: the mean of `γ` under the convolution of the two uniform period
  laws (`productPeriodMean`).

**Theorem** (`blindSymbolSlack_two_towers_enclosure`). The exact blind symbol slack on the powers of
`q₁` and `q₂` lies in `[−T(q₁, q₂), −m_{q₁} − η(q₁, q₂)]`; every line certificate has value at most
`T(q₁, q₂)` (`LineCertificate.value_le_productPeriodMean`), and `m_{qᵢ} ≤ T(q₁, q₂)`. For `2, 3`:
`m₂ + η₂₃ ≤ T(2, 3)` with `η₂₃ > 0` (`blindSymbolSlack_two_three_enclosure`).

The upper end `T` is the product of the two single-tower optima and is not expected to be the exact
value: an admissible spectral law is any probability law on the line with uniform projections on
both circles, and the box convolution is only the one of smallest support.
-/

open MeasureTheory Set Filter Topology Complex Finsupp
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. Line certificates -/

theorem blindOn_of_subset {𝒩 𝒩' : Set ℕ} (h : 𝒩 ⊆ 𝒩') {c : WeilTestFn →₀ ℝ}
    (hc : BlindOn 𝒩' c) : BlindOn 𝒩 c := fun j hj => hc j (h hj)

/-- More blindness keeps every slack. -/
theorem BlindSymbolSlackOn.of_subset {𝒩 𝒩' : Set ℕ} (h : 𝒩 ⊆ 𝒩') {M : ℝ}
    (hM : BlindSymbolSlackOn 𝒩 M) : BlindSymbolSlackOn 𝒩' M := fun c hc hb =>
  hM c hc (blindOn_of_subset h hb)

/-- A line certificate for the powers of `q₁` and `q₂`: continuous even circle observables with
`P₁(r log q₁) + P₂(r log q₂) ≤ γ(r)` for every real frequency `r`. -/
structure LineCertificate (q₁ q₂ : ℕ) where
  P₁ : AddCircle (2 * π) → ℝ
  P₂ : AddCircle (2 * π) → ℝ
  continuous₁ : Continuous P₁
  continuous₂ : Continuous P₂
  even₁ : ∀ z, P₁ (-z) = P₁ z
  even₂ : ∀ z, P₂ (-z) = P₂ z
  le_gamma : ∀ r : ℝ, P₁ (phase (Real.log q₁) r) + P₂ (phase (Real.log q₂) r) ≤ EF.gammaBracket r

/-- The value `⟨P₁⟩ + ⟨P₂⟩` of a line certificate. -/
def LineCertificate.value {q₁ q₂ : ℕ} (C : LineCertificate q₁ q₂) : ℝ :=
  (∫ z, C.P₁ z ∂AddCircle.haarAddCircle) + ∫ z, C.P₂ z ∂AddCircle.haarAddCircle

/-- **Line duality.** A line certificate bounds the archimedean part of every nonnegative
combination blind at the powers of both integers. -/
theorem LineCertificate.value_mul_massOf_le {q₁ q₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂)
    (C : LineCertificate q₁ q₂) {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hb : BlindOn (powerNodes q₁ ∪ powerNodes q₂) c) :
    C.value * massOf c ≤ nodeArchOnly c := by
  have h₁ := integral_combinationSpectralDensity_mul_periodic hq₁ hc
    (blindOn_of_subset Set.subset_union_left hb) C.continuous₁ C.even₁
  have h₂ := integral_combinationSpectralDensity_mul_periodic hq₂ hc
    (blindOn_of_subset Set.subset_union_right hb) C.continuous₂ C.even₂
  have hint : ∀ {P : AddCircle (2 * π) → ℝ}, Continuous P → ∀ ℓ : ℝ,
      Integrable fun r => combinationSpectralDensity c r * P (phase ℓ r) := by
    intro P hP ℓ
    obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn hP.continuousOn
    exact integrable_mul_bounded (integrable_combinationSpectralDensity c)
      (hP.comp (continuous_phase _)) (C := K) fun r => by
        rw [← Real.norm_eq_abs]; exact hK _ (Set.mem_univ _)
  have hmono := integral_mono ((hint C.continuous₁ (Real.log q₁)).add
    (hint C.continuous₂ (Real.log q₂)))
    (integrable_combinationSpectralDensity_mul_gammaBracket c) fun r => by
      simp only [Pi.add_apply]
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (C.le_gamma r) (combinationSpectralDensity_nonneg hc r)
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hint C.continuous₁ _) (hint C.continuous₂ _), h₁, h₂,
    integral_combinationSpectralDensity, integral_combinationSpectralDensity_mul_gammaBracket]
    at hmono
  have hpi : 0 < 2 * π := by positivity
  rw [LineCertificate.value]
  nlinarith

/-- A line certificate is a valid blind slack on the powers of both integers. -/
theorem blindSymbolSlackOn_two_towers_of_certificate {q₁ q₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂)
    (C : LineCertificate q₁ q₂) :
    BlindSymbolSlackOn (powerNodes q₁ ∪ powerNodes q₂) (-C.value) := fun c hc hb => by
  have := C.value_mul_massOf_le hq₁ hq₂ hc hb
  linarith

/-- The folded symbol of the first tower is a line certificate. -/
def foldCertificate₁ {q₁ : ℕ} (hq₁ : 2 ≤ q₁) (q₂ : ℕ) : LineCertificate q₁ q₂ where
  P₁ := foldedSymbol (Real.log q₁)
  P₂ := fun _ => 0
  continuous₁ := continuous_foldedSymbol _
  continuous₂ := continuous_const
  even₁ := foldedSymbol_neg _
  even₂ := fun _ => rfl
  le_gamma := fun r => by
    rw [add_zero]
    exact foldedSymbol_phase_le (Real.log_pos (by exact_mod_cast hq₁)) r

/-- The folded symbol of the second tower is a line certificate. -/
def foldCertificate₂ (q₁ : ℕ) {q₂ : ℕ} (hq₂ : 2 ≤ q₂) : LineCertificate q₁ q₂ where
  P₁ := fun _ => 0
  P₂ := foldedSymbol (Real.log q₂)
  continuous₁ := continuous_const
  continuous₂ := continuous_foldedSymbol _
  even₁ := fun _ => rfl
  even₂ := foldedSymbol_neg _
  le_gamma := fun r => by
    rw [zero_add]
    exact foldedSymbol_phase_le (Real.log_pos (by exact_mod_cast hq₂)) r

theorem foldCertificate₁_value {q₁ : ℕ} (hq₁ : 2 ≤ q₁) (q₂ : ℕ) :
    (foldCertificate₁ hq₁ q₂).value = symbolPeriodMean q₁ := by
  rw [LineCertificate.value]
  simp only [foldCertificate₁, integral_zero, add_zero]
  rw [integral_foldedSymbol (Real.log_pos (by exact_mod_cast hq₁)), symbolPeriodMean]

theorem foldCertificate₂_value (q₁ : ℕ) {q₂ : ℕ} (hq₂ : 2 ≤ q₂) :
    (foldCertificate₂ q₁ hq₂).value = symbolPeriodMean q₂ := by
  rw [LineCertificate.value]
  simp only [foldCertificate₂, integral_zero, zero_add]
  rw [integral_foldedSymbol (Real.log_pos (by exact_mod_cast hq₂)), symbolPeriodMean]

/-! ### 2. The product mean and two-dimensional midpoint sums -/

/-- The pair symbol `(γ(x + y) + γ(x − y))/2`. -/
def pairSymbol (x y : ℝ) : ℝ := (EF.gammaBracket (x + y) + EF.gammaBracket (x - y)) / 2

theorem continuous_pairSymbol_left (y : ℝ) : Continuous fun x => pairSymbol x y := by
  unfold pairSymbol
  exact ((WeilHerglotz.continuous_gammaBracket.comp (continuous_id.add continuous_const)).add
    (WeilHerglotz.continuous_gammaBracket.comp (continuous_id.sub continuous_const))).div_const 2

theorem continuous_uncurry_pairSymbol :
    Continuous (Function.uncurry fun y x => pairSymbol x y) := by
  change Continuous fun p : ℝ × ℝ => pairSymbol p.2 p.1
  unfold pairSymbol
  exact ((WeilHerglotz.continuous_gammaBracket.comp (continuous_snd.add continuous_fst)).add
    (WeilHerglotz.continuous_gammaBracket.comp (continuous_snd.sub continuous_fst))).div_const 2

/-- The pair symbol oscillates little on small rectangles inside `[0, A] × [0, B]`. -/
theorem exists_pairSymbol_osc {A B ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Icc 0 A, ∀ y ∈ Icc 0 B, ∀ x' ∈ Icc 0 A, ∀ y' ∈ Icc 0 B,
      |x - x'| + |y - y'| < δ → pairSymbol x' y' ≤ pairSymbol x y + ε := by
  have huc := (isCompact_Icc (a := -(A + B)) (b := A + B)).uniformContinuousOn_of_continuous
    WeilHerglotz.continuous_gammaBracket.continuousOn
  obtain ⟨δ, hδ, hδγ⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨δ, hδ, fun x hx y hy x' hx' y' hy' hd => ?_⟩
  have mem : ∀ u ∈ Icc 0 A, ∀ v ∈ Icc 0 B, u + v ∈ Icc (-(A + B)) (A + B) ∧
      u - v ∈ Icc (-(A + B)) (A + B) := fun u hu v hv =>
    ⟨⟨by linarith [hu.1, hu.2, hv.1, hv.2], by linarith [hu.1, hu.2, hv.1, hv.2]⟩,
      ⟨by linarith [hu.1, hu.2, hv.1, hv.2], by linarith [hu.1, hu.2, hv.1, hv.2]⟩⟩
  have hd' : |x' - x| + |y' - y| < δ := by rwa [abs_sub_comm x', abs_sub_comm y']
  have d1 : dist (x' + y') (x + y) < δ := by
    rw [Real.dist_eq, show x' + y' - (x + y) = (x' - x) + (y' - y) by ring]
    exact lt_of_le_of_lt (abs_add_le _ _) hd'
  have d2 : dist (x' - y') (x - y) < δ := by
    rw [Real.dist_eq, show x' - y' - (x - y) = (x' - x) - (y' - y) by ring]
    exact lt_of_le_of_lt (abs_sub _ _) hd'
  have e1 := hδγ _ (mem x' hx' y' hy').1 _ (mem x hx y hy).1 d1
  have e2 := hδγ _ (mem x' hx' y' hy').2 _ (mem x hx y hy).2 d2
  rw [Real.dist_eq] at e1 e2
  unfold pairSymbol
  linarith [(abs_lt.mp e1).2, (abs_lt.mp e2).2]

/-- **The product mean** `T(q₁, q₂)`: the mean of `γ` under the convolution of the uniform laws on
`[−π/ℓ₁, π/ℓ₁]` and `[−π/ℓ₂, π/ℓ₂]`, written over the quarter rectangle. -/
def productPeriodMean (q₁ q₂ : ℕ) : ℝ :=
  Real.log q₂ / π * ∫ y in (0 : ℝ)..π / Real.log q₂,
    Real.log q₁ / π * ∫ x in (0 : ℝ)..π / Real.log q₁, pairSymbol x y

/-- **Midpoint sums.** If `g` oscillates by at most `ε` over half a cell, its midpoint sum with `N`
cells exceeds the integral by at most `εA`. -/
theorem midpoint_sum_le_integral {g : ℝ → ℝ} {A ε : ℝ} (hA : 0 < A) {N : ℕ} (hN : 1 ≤ N)
    (hg : ContinuousOn g (Icc 0 A))
    (hosc : ∀ x ∈ Icc 0 A, ∀ x' ∈ Icc 0 A, |x - x'| ≤ A / (2 * N) → g x' ≤ g x + ε) :
    A / N * ∑ k ∈ Finset.range N, g (((k : ℝ) + 1 / 2) * (A / N)) ≤
      (∫ x in (0 : ℝ)..A, g x) + ε * A := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨h, hh⟩ : ∃ h, h = A / N := ⟨_, rfl⟩
  rw [← hh]
  have hh0 : 0 < h := by rw [hh]; exact div_pos hA hNpos
  have hNh : (N : ℝ) * h = A := by rw [hh]; field_simp
  have hhalf : A / (2 * N) = h / 2 := by rw [hh]; field_simp
  have hcell : ∀ k ∈ Finset.range N, h * (g (((k : ℝ) + 1 / 2) * h) - ε) ≤
      ∫ x in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), g x := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hk
    have hlo : 0 ≤ (k : ℝ) * h := by positivity
    have hhi : ((k + 1 : ℕ) : ℝ) * h ≤ A := by push_cast; nlinarith
    have hle : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
    have hsub : Icc ((k : ℝ) * h) (((k + 1 : ℕ) : ℝ) * h) ⊆ Icc 0 A := Icc_subset_Icc hlo hhi
    have hmid : ((k : ℝ) + 1 / 2) * h ∈ Icc 0 A := by
      push_cast at hhi
      exact ⟨by positivity, by nlinarith⟩
    calc h * (g (((k : ℝ) + 1 / 2) * h) - ε)
        = ∫ _x in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), (g (((k : ℝ) + 1 / 2) * h) - ε) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
      _ ≤ ∫ x in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), g x := by
          refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
            ((hg.mono (by rwa [uIcc_of_le hle])).intervalIntegrable) fun x hx => ?_
          have hx' := hx
          push_cast at hx'
          have := hosc x (hsub hx) _ hmid (by
            rw [hhalf, abs_le]
            constructor <;> nlinarith [hx'.1, hx'.2])
          linarith
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) * h) (n := N) fun k hk => by
      have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
      have hle : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
      have hhi : ((k + 1 : ℕ) : ℝ) * h ≤ A := by push_cast; nlinarith
      exact (hg.mono (by
        rw [uIcc_of_le hle]; exact Icc_subset_Icc (by positivity) hhi)).intervalIntegrable
  simp only [Nat.cast_zero, zero_mul] at hadj
  rw [hNh] at hadj
  have hsum := Finset.sum_le_sum hcell
  rw [hadj, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hεA : h * ((N : ℝ) * ε) = ε * A := by rw [← hNh]; ring
  rw [mul_sub, hεA] at hsum
  linarith

/-- **Two-dimensional midpoint sums of the pair symbol** converge to its mean over the rectangle. -/
theorem productMidpoint_sum_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
      1 / (N : ℝ) ^ 2 * ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          pairSymbol (((a : ℝ) + 1 / 2) * (A / N)) (((b : ℝ) + 1 / 2) * (B / N)) ≤
        1 / (A * B) * (∫ y in (0 : ℝ)..B, ∫ x in (0 : ℝ)..A, pairSymbol x y) + ε := by
  obtain ⟨δ, hδ, hosc⟩ := exists_pairSymbol_osc (A := A) (B := B) (ε := ε / 2) (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((A + B) / δ)
  refine ⟨N₀, fun N hN hN1 => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNδ : (A + B) / δ < N := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
  have hcellA : A / (2 * N) < δ / 2 := by
    rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hδ] at hNδ; nlinarith
  have hcellB : B / (2 * N) < δ / 2 := by
    rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hδ] at hNδ; nlinarith
  have hcA : 0 ≤ A / (2 * N) := by positivity
  have hcB : 0 ≤ B / (2 * N) := by positivity
  set G : ℝ → ℝ := fun y => ∫ x in (0 : ℝ)..A, pairSymbol x y with hG
  have hpcont : ∀ y, Continuous fun x => pairSymbol x y := continuous_pairSymbol_left
  -- the grid points lie in the rectangle
  have hgrid : ∀ {C : ℝ}, 0 < C → ∀ k ∈ Finset.range N, ((k : ℝ) + 1 / 2) * (C / N) ∈ Icc 0 C := by
    intro C hC k hk
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hk
    refine ⟨by positivity, ?_⟩
    rw [show ((k : ℝ) + 1 / 2) * (C / N) = C * (((k : ℝ) + 1 / 2) / N) by ring]
    exact mul_le_of_le_one_right hC.le ((div_le_one hNpos).mpr (by linarith))
  -- inner sums
  have hinner : ∀ b ∈ Finset.range N,
      A / N * ∑ a ∈ Finset.range N, pairSymbol (((a : ℝ) + 1 / 2) * (A / N))
        (((b : ℝ) + 1 / 2) * (B / N)) ≤ G (((b : ℝ) + 1 / 2) * (B / N)) + ε / 2 * A := by
    intro b hb
    have hyb := hgrid hB b hb
    exact midpoint_sum_le_integral (g := fun x => pairSymbol x (((b : ℝ) + 1 / 2) * (B / N)))
      hA hN1 (hpcont _).continuousOn fun x hx x' hx' hxx' =>
        hosc x hx _ hyb x' hx' _ hyb (by rw [sub_self, abs_zero, add_zero]; linarith)
  -- outer sum
  have hGc : ContinuousOn G (Icc 0 B) := by
    have : Continuous G := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y x => pairSymbol x y) continuous_uncurry_pairSymbol 0 A
    exact this.continuousOn
  have houter := midpoint_sum_le_integral (g := G) hB hN1 hGc (ε := ε / 2 * A)
    fun y hy y' hy' hyy' => by
      have hle : ∫ x in (0 : ℝ)..A, pairSymbol x y' ≤
          ∫ x in (0 : ℝ)..A, (pairSymbol x y + ε / 2) :=
        intervalIntegral.integral_mono_on hA.le ((hpcont _).intervalIntegrable _ _)
          (((hpcont _).add continuous_const).intervalIntegrable _ _) fun x hx =>
            hosc x hx y hy x hx y' hy' (by rw [sub_self, abs_zero, zero_add]; linarith)
      rw [intervalIntegral.integral_add ((hpcont _).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
      simp only [hG]
      linarith
  -- combine
  set S := ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
    pairSymbol (((a : ℝ) + 1 / 2) * (A / N)) (((b : ℝ) + 1 / 2) * (B / N)) with hSdef
  have h1 : A / N * (B / N) * S = B / N * ∑ b ∈ Finset.range N, (A / N * ∑ a ∈ Finset.range N,
      pairSymbol (((a : ℝ) + 1 / 2) * (A / N)) (((b : ℝ) + 1 / 2) * (B / N))) := by
    rw [hSdef, Finset.sum_comm]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : B / N * ∑ b ∈ Finset.range N, (A / N * ∑ a ∈ Finset.range N,
      pairSymbol (((a : ℝ) + 1 / 2) * (A / N)) (((b : ℝ) + 1 / 2) * (B / N))) ≤
      B / N * ∑ b ∈ Finset.range N, G (((b : ℝ) + 1 / 2) * (B / N)) + ε / 2 * A * B := by
    have := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner) (by positivity : 0 ≤ B / N)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_add] at this
    have e : B / N * (N * (ε / 2 * A)) = ε / 2 * A * B := by field_simp
    linarith
  have htot : A / N * (B / N) * S ≤ (∫ y in (0 : ℝ)..B, G y) + ε * (A * B) := by
    linarith [h1, h2, houter]
  have hAB : 0 < A * B := mul_pos hA hB
  have hgoal : 1 / (N : ℝ) ^ 2 * S = A / N * (B / N) * S / (A * B) := by field_simp
  rw [hgoal, div_le_iff₀ hAB]
  have e2 : (1 / (A * B) * (∫ y in (0 : ℝ)..B, ∫ x in (0 : ℝ)..A, pairSymbol x y) + ε) * (A * B) =
      (∫ y in (0 : ℝ)..B, G y) + ε * (A * B) := by
    simp only [hG]; field_simp
  rw [e2]
  exact htot

/-! ### 3. Pair combinations on a finite index set -/

/-- Unit cosine/sine pairs of the envelope `f` at the frequencies `ω k`, `k ∈ s`. -/
def pairCombinationOn {ι : Type*} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (s : Finset ι) (ω : ι → ℝ) : WeilTestFn →₀ ℝ :=
  ∑ k ∈ s, (Finsupp.single (cosTest hf hfc (ω k)) 1 + Finsupp.single (sinTest hf hfc (ω k)) 1)

section PairOn

variable {ι : Type*} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
  (s : Finset ι) (ω : ι → ℝ)

theorem linearCombination_pairSumOn (φ : WeilTestFn → ℝ) (a b : ι → WeilTestFn) :
    linearCombination ℝ φ (∑ k ∈ s, (Finsupp.single (a k) (1 : ℝ) + Finsupp.single (b k) 1)) =
      ∑ k ∈ s, (φ (a k) + φ (b k)) := by
  simp only [map_sum, map_add, linearCombination_single, one_smul]

theorem pairCombinationOn_nonneg (g : WeilTestFn) : 0 ≤ pairCombinationOn hf hfc s ω g := by
  classical
  rw [pairCombinationOn, Finsupp.finsetSum_apply]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> norm_num

theorem massOf_pairCombinationOn :
    massOf (pairCombinationOn hf hfc s ω) = s.card * autocorr f 0 := by
  rw [massOf_eq_linearCombination, pairCombinationOn, linearCombination_pairSumOn]
  simp only [cosTest, sinTest, realTest, integral_norm_sq_ofReal, autocorr_cos_add_sin_zero hf hfc,
    Finset.sum_const, nsmul_eq_mul]

theorem nodeVector_pairCombinationOn (j : LogIndex) :
    nodeVector (pairCombinationOn hf hfc s ω) j =
      2 * autocorr f (Real.log (j : ℕ)) / Real.sqrt (j : ℕ) *
        ∑ k ∈ s, Real.cos (ω k * Real.log (j : ℕ)) := by
  rw [nodeVector_apply_eq_linearCombination, pairCombinationOn, linearCombination_pairSumOn,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [cosTest, sinTest, logValue_realTest]
  have h := autocorr_cosineSource_add_sineSource hf.continuous hfc (ω k) (Real.log (j : ℕ))
  linear_combination (2 / Real.sqrt (j : ℕ)) * h

theorem nodeArchOnly_pairCombinationOn_le :
    nodeArchOnly (pairCombinationOn hf hfc s ω) ≤
      autocorr f 0 * ∑ k ∈ s, EF.gammaBracket (ω k) + s.card * biScaleLevyEnergy f := by
  rw [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, pairCombinationOn, linearCombination_pairSumOn,
    linearCombination_pairSumOn, ← Finset.sum_sub_distrib, Finset.mul_sum]
  have hN : (s.card : ℝ) * biScaleLevyEnergy f = ∑ _k ∈ s, biScaleLevyEnergy f := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hN, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 := archOnly_realTest (contDiff_cosineSource hf (ω k)) (hfc.mul_right (f' :=
    fun u => Real.cos (ω k * u)))
  have h2 := archOnly_realTest (contDiff_sineSource hf (ω k)) (hfc.mul_right (f' :=
    fun u => Real.sin (ω k * u)))
  have h3 := biScaleLevyEnergy_cosine_sine_eq hf hfc (ω k)
  have h4 : EF.gammaBracket 0 * autocorr (cosineSource f (ω k)) 0 +
      EF.gammaBracket 0 * autocorr (sineSource f (ω k)) 0 =
      EF.gammaBracket 0 * autocorr f 0 := by
    rw [← mul_add, autocorr_cos_add_sin_zero hf hfc]
  have h5 : autocorr f 0 * archFrequencyCost (ω k) =
      autocorr f 0 * EF.gammaBracket (ω k) - EF.gammaBracket 0 * autocorr f 0 := by
    rw [archFrequencyCost_eq_gammaBracket_sub_zero]; ring
  have h6 := (le_abs_self _).trans (abs_archEnvelopeError_le hf hfc (ω k))
  simp only [cosTest, sinTest] at *
  linarith

end PairOn

/-! ### 4. Product designs -/

/-- The product frequencies `ω₁(a) ± ω₂(b)`. -/
def productFreq (ω₁ ω₂ : ℕ → ℝ) (k : Bool × ℕ × ℕ) : ℝ :=
  ω₁ k.2.1 + (if k.1 then ω₂ k.2.2 else -ω₂ k.2.2)

/-- The index set `{±} × [0, N) × [0, N)`. -/
def productIndex (N : ℕ) : Finset (Bool × ℕ × ℕ) :=
  Finset.univ ×ˢ (Finset.range N ×ˢ Finset.range N)

theorem card_productIndex (N : ℕ) : (productIndex N).card = 2 * N * N := by
  rw [productIndex, Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_bool,
    Finset.card_range]
  ring

/-- Sums over the product index pair the two signs. -/
theorem sum_productIndex (N : ℕ) (F : Bool × ℕ × ℕ → ℝ) :
    ∑ k ∈ productIndex N, F k = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
      (F (true, a, b) + F (false, a, b)) := by
  rw [productIndex, Finset.sum_product, Fintype.sum_bool, Finset.sum_product, Finset.sum_product,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_add_distrib]

/-- **The product cosine sum factors**: `Σ cos((ω₁(a) ± ω₂(b)) t) = 2 Σ_a cos(ω₁(a) t) Σ_b cos(ω₂(b) t)`. -/
theorem sum_cos_productFreq (ω₁ ω₂ : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    ∑ k ∈ productIndex N, Real.cos (productFreq ω₁ ω₂ k * t) =
      2 * (∑ a ∈ Finset.range N, Real.cos (ω₁ a * t)) * ∑ b ∈ Finset.range N, Real.cos (ω₂ b * t) := by
  rw [sum_productIndex, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [productFreq, if_true, Bool.false_eq_true, if_false]
  rw [add_mul, add_mul, Real.cos_add, Real.cos_add, neg_mul, Real.cos_neg, Real.sin_neg]
  ring

/-- The product symbol sum is twice the midpoint sum of the pair symbol. -/
theorem sum_gammaBracket_productFreq (ω₁ ω₂ : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ productIndex N, EF.gammaBracket (productFreq ω₁ ω₂ k) =
      2 * ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, pairSymbol (ω₁ a) (ω₂ b) := by
  rw [sum_productIndex, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [productFreq, if_true, Bool.false_eq_true, if_false, pairSymbol, ← sub_eq_add_neg]
  ring

/-- **Product designs attain the product mean.** For every `ε > 0` there is a nonnegative
combination blind at every power of `q₁` and of `q₂` with `A(c) ≤ (T(q₁, q₂) + ε) ‖c‖²`. -/
theorem exists_blindOn_two_towers_archOnly_le {q₁ q₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂) {ε : ℝ}
    (hε : 0 < ε) : ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      BlindOn (powerNodes q₁ ∪ powerNodes q₂) c ∧ 0 < massOf c ∧
      nodeArchOnly c ≤ (productPeriodMean q₁ q₂ + ε) * massOf c := by
  set ℓ₁ : ℝ := Real.log q₁ with hℓ₁def
  set ℓ₂ : ℝ := Real.log q₂ with hℓ₂def
  have hℓ₁ : 0 < ℓ₁ := Real.log_pos (by exact_mod_cast hq₁)
  have hℓ₂ : 0 < ℓ₂ := Real.log_pos (by exact_mod_cast hq₂)
  set ℓ : ℝ := min ℓ₁ ℓ₂ with hℓdef
  have hℓ : 0 < ℓ := lt_min hℓ₁ hℓ₂
  set A : ℝ := π / ℓ₁ with hAdef
  set B : ℝ := π / ℓ₂ with hBdef
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  -- envelope constants
  obtain ⟨Mb, hMb, hinc⟩ := exists_autocorr_increment_linear_bound contDiff_pairBump
    hasCompactSupport_pairBump
  have hb0 := autocorr_pairBump_zero_pos
  set E : ℝ := Mb * archWeightFirstMoment / (8 * ℓ * autocorr pairBump 0) with hEdef
  have hE : 0 ≤ E := by
    have := archWeightFirstMoment_nonneg
    positivity
  -- grid size
  obtain ⟨N₀, hN₀⟩ := productMidpoint_sum_le hA hB (ε := ε / 2) (by positivity)
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * E / ε)
  set N : ℕ := max (max N₀ 1) k with hNdef
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hEN : E / N ≤ ε / 2 := by
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast le_max_right (max N₀ 1) k
    rw [div_le_iff₀ hNpos]
    rw [div_lt_iff₀ hε] at hk
    nlinarith
  -- envelope
  set δ : ℝ := 1 / (8 * N * ℓ) with hδdef
  have hδ : 0 < δ := by positivity
  have hf := contDiff_compressedBump δ
  have hfc := hasCompactSupport_compressedBump hδ
  have hf0 : autocorr (compressedBump δ) 0 = 8 * N * ℓ * autocorr pairBump 0 := by
    rw [autocorr_compressedBump_zero hδ, hδdef]; field_simp
  have hJ : biScaleLevyEnergy (compressedBump δ) ≤ Mb * archWeightFirstMoment :=
    biScaleLevyEnergy_sourceRescale_le contDiff_pairBump hasCompactSupport_pairBump hinc hδ
  -- frequencies
  set ω₁ : ℕ → ℝ := fun a => ((a : ℝ) + 1 / 2) * (A / N) with hω₁
  set ω₂ : ℕ → ℝ := fun b => ((b : ℝ) + 1 / 2) * (B / N) with hω₂
  have hcos : ∀ {ℓ' C : ℝ}, 0 < ℓ' → C = π / ℓ' → ∀ {i : ℕ}, 1 ≤ i → i < 2 * N →
      ∑ a ∈ Finset.range N, Real.cos (((a : ℝ) + 1 / 2) * (C / N) * ((i : ℝ) * ℓ')) = 0 := by
    intro ℓ' C hℓ' hC i hi1 hiN
    have e : ∀ a : ℕ, ((a : ℝ) + 1 / 2) * (C / N) * ((i : ℝ) * ℓ') =
        ((a : ℝ) + 1 / 2) * (π * i / N) := fun a => by rw [hC]; field_simp
    simp only [e]
    exact sum_cos_midpoint_eq_zero hi1 hiN
  have hfar : ∀ {ℓ' : ℝ}, ℓ ≤ ℓ' → ∀ {i : ℕ}, 2 * N ≤ i →
      autocorr (compressedBump δ) ((i : ℝ) * ℓ') = 0 := by
    intro ℓ' hℓ' i hi
    apply autocorr_compressedBump_eq_zero hδ
    have hℓ'0 : 0 < ℓ' := hℓ.trans_le hℓ'
    rw [abs_of_nonneg (by positivity), hδdef,
      show 1 / (5 * (1 / (8 * (N : ℝ) * ℓ))) = 8 / 5 * N * ℓ by field_simp]
    have : (2 * N : ℝ) ≤ i := by exact_mod_cast hi
    nlinarith
  refine ⟨pairCombinationOn hf hfc (productIndex N) (productFreq ω₁ ω₂),
    pairCombinationOn_nonneg hf hfc _ _, fun j hj => ?_, ?_, ?_⟩
  · -- blindness at every power of both integers
    rw [nodeVector_pairCombinationOn, sum_cos_productFreq]
    rcases hj with ⟨i, hi1, hji⟩ | ⟨i, hi1, hji⟩
    · have hlog : Real.log ((j : ℕ) : ℝ) = (i : ℝ) * ℓ₁ := by
        rw [hji, Nat.cast_pow, Real.log_pow]
      rw [hlog]
      rcases lt_or_ge i (2 * N) with hiN | hiN
      · rw [show ∑ a ∈ Finset.range N, Real.cos (ω₁ a * ((i : ℝ) * ℓ₁)) = 0 from
          hcos hℓ₁ hAdef hi1 hiN]
        ring
      · rw [hfar (min_le_left _ _) hiN]; ring
    · have hlog : Real.log ((j : ℕ) : ℝ) = (i : ℝ) * ℓ₂ := by
        rw [hji, Nat.cast_pow, Real.log_pow]
      rw [hlog]
      rcases lt_or_ge i (2 * N) with hiN | hiN
      · rw [show ∑ b ∈ Finset.range N, Real.cos (ω₂ b * ((i : ℝ) * ℓ₂)) = 0 from
          hcos hℓ₂ hBdef hi1 hiN]
        ring
      · rw [hfar (min_le_right _ _) hiN]; ring
  · rw [massOf_pairCombinationOn, card_productIndex, hf0]
    positivity
  · have harch := nodeArchOnly_pairCombinationOn_le hf hfc (productIndex N) (productFreq ω₁ ω₂)
    rw [sum_gammaBracket_productFreq, card_productIndex] at harch
    rw [massOf_pairCombinationOn, card_productIndex]
    -- the midpoint sum of the pair symbol
    have hmid := hN₀ N hNN₀ hN1
    have hT : 1 / (A * B) * (∫ y in (0 : ℝ)..B, ∫ x in (0 : ℝ)..A, pairSymbol x y) =
        productPeriodMean q₁ q₂ := by
      rw [productPeriodMean, ← hℓ₁def, ← hℓ₂def, ← hAdef, ← hBdef]
      simp_rw [intervalIntegral.integral_const_mul]
      rw [hAdef, hBdef]
      field_simp
    rw [hT] at hmid
    have hS : ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, pairSymbol (ω₁ a) (ω₂ b) ≤
        (N : ℝ) ^ 2 * (productPeriodMean q₁ q₂ + ε / 2) := by
      have := (mul_le_mul_of_nonneg_left hmid (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2))
      rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
      exact this
    have hh0 : 0 ≤ autocorr (compressedBump δ) 0 := autocorr_zero_nonneg _
    have hJN : ((2 * N * N : ℕ) : ℝ) * biScaleLevyEnergy (compressedBump δ) ≤
        ((2 * N * N : ℕ) : ℝ) * (Mb * archWeightFirstMoment) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    have hEN' : Mb * archWeightFirstMoment ≤ autocorr (compressedBump δ) 0 * (ε / 2) := by
      rw [hf0]
      have : Mb * archWeightFirstMoment = 8 * N * ℓ * autocorr pairBump 0 * (E / N) := by
        rw [hEdef]; field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hEN (by positivity)
    have hSA := mul_le_mul_of_nonneg_left hS hh0
    push_cast at harch hJN ⊢
    nlinarith [mul_le_mul_of_nonneg_left hEN' (by positivity : (0 : ℝ) ≤ 2 * N * N)]

/-! ### 5. The enclosure -/

/-- **Every valid slack is at least `−T(q₁, q₂)`.** -/
theorem le_of_blindSymbolSlackOn_two_towers {q₁ q₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂) {M : ℝ}
    (h : BlindSymbolSlackOn (powerNodes q₁ ∪ powerNodes q₂) M) :
    -productPeriodMean q₁ q₂ ≤ M := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc, hb, hpos, hle⟩ := exists_blindOn_two_towers_archOnly_le hq₁ hq₂
    (ε := (-productPeriodMean q₁ q₂ - M) / 2) (by linarith)
  have := h c hc hb
  nlinarith

/-- **Every line certificate has value at most the product mean.** -/
theorem LineCertificate.value_le_productPeriodMean {q₁ q₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂)
    (C : LineCertificate q₁ q₂) : C.value ≤ productPeriodMean q₁ q₂ := by
  have := le_of_blindSymbolSlackOn_two_towers hq₁ hq₂
    (blindSymbolSlackOn_two_towers_of_certificate hq₁ hq₂ C)
  linarith

/-- Both single-tower means lie below the product mean. -/
theorem symbolPeriodMean_le_productPeriodMean {q₁ q₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂) :
    symbolPeriodMean q₁ ≤ productPeriodMean q₁ q₂ ∧ symbolPeriodMean q₂ ≤ productPeriodMean q₁ q₂ :=
  ⟨foldCertificate₁_value hq₁ q₂ ▸ (foldCertificate₁ hq₁ q₂).value_le_productPeriodMean hq₁ hq₂,
    foldCertificate₂_value q₁ hq₂ ▸ (foldCertificate₂ q₁ hq₂).value_le_productPeriodMean hq₁ hq₂⟩

/-- **The two-tower enclosure.** The blind slack on the powers of `q₁` and `q₂` is valid at
`−m_{q₁} − η(q₁, q₂)` and at no level below `−T(q₁, q₂)`; hence `m_{q₁} + η(q₁, q₂) ≤ T(q₁, q₂)`. -/
theorem blindSymbolSlack_two_towers_enclosure {q₁ q₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂) :
    BlindSymbolSlackOn (powerNodes q₁ ∪ powerNodes q₂)
        (-symbolPeriodMean q₁ - incidenceGain q₁ q₂) ∧
      (∀ M, BlindSymbolSlackOn (powerNodes q₁ ∪ powerNodes q₂) M →
        -productPeriodMean q₁ q₂ ≤ M) ∧
      symbolPeriodMean q₁ + incidenceGain q₁ q₂ ≤ productPeriodMean q₁ q₂ := by
  have hsub : insert q₂ (powerNodes q₁) ⊆ powerNodes q₁ ∪ powerNodes q₂ := by
    intro n hn
    rcases hn with rfl | hn
    · exact Or.inr ⟨1, le_rfl, (pow_one _).symm⟩
    · exact Or.inl hn
  have h₁ := (blindSymbolSlackOn_insert_of_not_mem hq₁ hq₂).of_subset hsub
  refine ⟨h₁, fun M hM => le_of_blindSymbolSlackOn_two_towers hq₁ hq₂ hM, ?_⟩
  have := le_of_blindSymbolSlackOn_two_towers hq₁ hq₂ h₁
  linarith

/-- **The primes `2` and `3`.** The joint blind slack on the powers of `2` and `3` lies in
`[−T(2, 3), −m₂ − η₂₃]` with `η₂₃ > 0`. -/
theorem blindSymbolSlack_two_three_enclosure :
    BlindSymbolSlackOn (powerNodes 2 ∪ powerNodes 3) (-symbolPeriodMean 2 - incidenceGain 2 3) ∧
      (∀ M, BlindSymbolSlackOn (powerNodes 2 ∪ powerNodes 3) M → -productPeriodMean 2 3 ≤ M) ∧
      0 < incidenceGain 2 3 ∧ symbolPeriodMean 2 < productPeriodMean 2 3 := by
  obtain ⟨h₁, h₂, h₃⟩ := blindSymbolSlack_two_towers_enclosure (q₁ := 2) (q₂ := 3) le_rfl
    (by norm_num)
  have hη := incidenceGain_two_three_pos
  exact ⟨h₁, h₂, hη, by linarith⟩

end

end GaloisForLFunctions.BiScaleUncertainty
