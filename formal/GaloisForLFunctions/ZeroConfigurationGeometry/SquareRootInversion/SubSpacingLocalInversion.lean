import GaloisForLFunctions.ZeroConfigurationGeometry.TheLocalCameraConstantIsQuasiPolynomial
import GaloisForLFunctions.ZeroConfigurationGeometry.SplineBumpsDecayAtAnExplicitRate

/-!
# Sub-spacing local inversion above half the cluster density

Let `Z, Z'` be tempered zero configurations whose signed cluster `multDiff Z Z'` near height `T`
has distinct-point local count at most `(θ / 2π) log(T / 2π) · (y − x) + A log(T / 2π)` on
`[T / 2, 3T / 2]`. At window aperture `a = λ · ½ log(T / 2π)` with `2λ > θ` (`λ > θ / 2`), every
point `z₀` in the macroscopic band `|Im z₀ − T| ≤ T / 4` that is `T^{−M}`-isolated (`M ≥ 0`) from
all other cluster points in `[T / 2, 3T / 2]` admits an isolating window pair `(F, G)` of aperture
`a` satisfying

`‖(Z.W F G − Z'.W F G) / pointImage F G z₀ − multDiff Z Z' z₀‖ ≤ 1 / 4`
(`exists_subspacing_isolating_windows`).

Consequently:
* **Exact polynomial-scale local inversion** (`multDiff_eq_zero_of_subspacing_isolated`,
  `exists_nearCollision_of_mimic_above_half_density`). If `Z.W f f = Z'.W f f` on windows of
  aperture `λ · ½ log(T / 2π)` (`λ > θ / 2`), then `Z` and `Z'` coincide with multiplicity across
  `|Im z − T| ≤ T / 4` outside near-collision clusters of polynomial diameter `< T^{−M}`.
* **Exact `o(1 / log T)` local inversion** (`multDiff_eq_zero_of_littleO_inv_log_isolated`,
  `exists_nearCollision_littleO_inv_log`). Specializing `M = 1` shows that for every `δ > 0` and
  all `T ≥ T₀(δ)`, `Z` and `Z'` coincide across `|Im z − T| ≤ T / 4` outside near-collision
  clusters of diameter `< δ / log T`.
* **Single-configuration multiplicity readout** (`exists_window_pair_reads_mult_subspacing`).
  Comparing `Z` against `emptyZeroConfig` reads the exact integer multiplicity `Z.mult z₀` (within
  `1 / 4`, hence uniquely and with `Z.W F G ≠ 0`) of every `T^{−M}`-isolated zero from a single
  window pair of aperture `λ · ½ log(T / 2π)` whenever `λ > θ / 2` (in particular at the
  square-root threshold `λ > ½` when `θ = 1`).

Proof mechanism. Removing `D⁻¹ ≤ η` via `log_inv_windowFloor_le_of_le_one` bounds
`log(windowFloor⁻¹)` at `η = T^{−M}` by `O((1 + M) u³)` in `u = log(T / 2π)`, independent of the
window decay order `k`. Choosing `k = ⌈K u²⌉` makes `(1 + T / 4)^{2k − 2} ≥ e^{2(k − 1)u}` grow
like `e^{2K u³}`, while bounding `log(4(1 + m/ε)) ≤ α · 4(1 + m/ε) + log α⁻¹` with small `α > 0`
caps `2 m log(4(1 + m/ε))` at `u³ + O_K(u²)`.
-/

open MeasureTheory Complex Set Filter Real
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-! ### The empty zero configuration -/

/-- The empty zero configuration, with empty carrier and zero Weil form. -/
def emptyZeroConfig : ZeroConfig where
  carrier := ∅
  mult := fun _ => 0
  one_le_mult := fun _ h => False.elim h
  strip := fun _ h => False.elim h
  reflect_mem := fun _ h => False.elim h
  mult_reflect := fun _ h => False.elim h
  finite_window := fun _ _ => Set.finite_empty.subset Set.inter_subset_left

theorem temperedConfig_emptyZeroConfig : TemperedConfig emptyZeroConfig := by
  haveI : IsEmpty emptyZeroConfig.carrier := ⟨fun x => x.2⟩
  exact hasSum_empty.summable

theorem W_emptyZeroConfig (f g : ℝ → ℂ) : emptyZeroConfig.W f g = 0 := by
  haveI : IsEmpty emptyZeroConfig.carrier := ⟨fun x => x.2⟩
  exact tsum_empty

theorem multDiff_emptyZeroConfig (Z : ZeroConfig) (z : ℂ) :
    multDiff Z emptyZeroConfig z = Z.carrier.indicator (fun w => (Z.mult w : ℂ)) z := by
  unfold multDiff emptyZeroConfig
  simp

/-! ### Quantitative isolating window pair without assuming mimicry -/

/-- **Quantitative local camera window pair.** Without assuming `Z` and `Z'` are mimics, any
`η`-isolated cluster point `z₀` inside height radius `R` admits aperture-`a` windows `F, G`
vanishing on all other near cluster points, with `pointImage F G z₀ ≠ 0` and tail error bounded by
`localCameraConst`. -/
theorem exists_isolating_window_pair_of_bump {a D C₀ η ε : ℝ} (hD : 0 < D)
    (hη : 0 < η) (hε : 0 < ε) (hεa : π * D / 2 + 2 * ε ≤ a) {b : ℝ → ℂ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbs : tsupport b ⊆ Icc (-ε) ε)
    (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ} (hk : 1 ≤ k)
    (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + k ≤ m) {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    {z₀ : ℂ} {R : ℝ} (hR : 0 ≤ R) (hc : multDiff Z Z' z₀ ≠ 0)
    (hiso : ∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → η ≤ ‖z - z₀‖)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀) :
    ∃ F G : ℝ → ℂ, ApertureWindow a F ∧ ApertureWindow a G ∧
      windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 ≤ ‖pointImage F G z₀‖ ∧
      pointImage F G z₀ ≠ 0 ∧
      (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → pointImage F G z = 0) ∧
      ‖(Z.W F G - Z'.W F G) / pointImage F G z₀ - multDiff Z Z' z₀‖ * (1 + R) ^ (2 * k - 2) ≤
        localCameraConst a D C₀ η ε Cm C0 * (1 + |z₀.im|) ^ 2 *
          ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) := by
  classical
  obtain ⟨h, hh_def⟩ : ∃ h, h = D⁻¹ := ⟨_, rfl⟩
  have hh : 0 < h := by rw [hh_def]; exact inv_pos.mpr hD
  have hDh : D * h = 1 := by rw [hh_def]; field_simp
  obtain ⟨L, hLs⟩ : ∃ L, L = localSlack D C₀ := ⟨_, rfl⟩
  have hL : L = (|C₀| + 1) / 2 * h + h + 1 / 2 := by rw [hLs, localSlack, hh_def]
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hr : π / (2 * h) + 2 * ε ≤ a := by
    rw [show π / (2 * h) = π * D / 2 by rw [hh_def]; field_simp]
    exact hεa
  have ha : 0 ≤ a := by nlinarith [Real.pi_pos]
  have hm' : windowExponent (2 * h) L + k ≤ m := by rw [hh_def, hLs]; exact hm
  have hCm0 : 0 ≤ Cm := by
    have h1 := hCm 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (by positivity) h1
  have hC00 : 0 ≤ C0 := by
    have h1 := hC0 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (norm_nonneg _) h1
  obtain ⟨c, hcdef⟩ : ∃ c, c = windowFloor (2 * h) L η := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = windowGrowth (2 * h) L * Cm * C0 * Real.exp ε := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; exact windowFloor_pos (by positivity) hL0 hη
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (windowGrowth_nonneg (by positivity) hL0) hCm0)
      hC00) (Real.exp_pos _).le
  have hBdef : localCameraConst a D C₀ η ε Cm C0 = M * M * Real.exp a * (5 / 4) / (c * c) := by
    rw [localCameraConst, ← hh_def, ← hLs, ← hcdef, ← hMdef]
    ring
  have hwin : ∀ {ι : Type} (lam : ι → ℂ) (τ : ι → ℤ) (P : Set ι),
      Set.InjOn τ P → (∀ i ∈ P, ‖lam i - τ i * ((2 * h : ℝ) : ℂ)‖ ≤ L) →
      (∀ i ∈ P, |(lam i).im| ≤ 1 / 2) →
      ∀ w₀ : ℂ, w₀.re = 0 → |w₀.im| ≤ 1 / 2 → (∀ i ∈ P, η ≤ ‖w₀ - lam i‖) →
      ∃ f : ℝ → ℂ, ApertureWindow a f ∧ (∀ i ∈ P, paperFT f (lam i) = 0) ∧
        c ≤ ‖paperFT f w₀‖ ∧
        ∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT f w‖ * (1 + |w.re|) ^ k ≤ M := by
    intro ι lam τ P hτ hPL hPim w₀ h1 h2 h3
    rw [hcdef, hMdef]
    exact isolating_window_of_bump (by positivity) hL0 hη hε hr hb hbs hb1 hm' hCm hC0 lam τ P
      hτ hPL hPim h1 h2 h3
  obtain ⟨X, hX⟩ : ∃ X, X = z₀.im := ⟨_, rfl⟩
  rw [← hX] at hiso hcount ⊢
  set S : Set ℂ := {z | multDiff Z Z' z ≠ 0 ∧ |z.im - X| ≤ R}
  have hcount' : ∀ (s : Finset S) (x y : ℝ), x ≤ y →
      (∀ i ∈ s, D * ((i : ℂ).im - X) ∈ Icc x y) → (s.card : ℝ) ≤ y - x + C₀ := by
    intro s x y hxy hs
    have hle := hcount (s.map (Function.Embedding.subtype _)) (x / D + X) (y / D + X)
      (by linarith [div_le_div_of_nonneg_right hxy hD.le]) fun z hz => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
        obtain ⟨h1, h2⟩ := hs i hi
        refine ⟨i.2.1, i.2.2, ?_, ?_⟩
        · simp only [Function.Embedding.subtype_apply]
          have : x / D ≤ (i : ℂ).im - X := (div_le_iff₀ hD).mpr (by linarith)
          linarith
        · simp only [Function.Embedding.subtype_apply]
          have : (i : ℂ).im - X ≤ y / D := (le_div_iff₀ hD).mpr (by linarith)
          linarith
    rw [Finset.card_map] at hle
    calc (s.card : ℝ) ≤ D * (y / D + X - (x / D + X)) + C₀ := hle
      _ = y - x + C₀ := by field_simp; ring
  obtain ⟨σ, hσ, hσd⟩ := exists_injective_near_int (fun i : S => D * ((i : ℂ).im - X)) hcount'
  have hhalf : ∀ i : S, |((i : ℂ).im - X) - ((σ i / 2 : ℤ) : ℝ) * (2 * h)| ≤ L - 1 / 2 := by
    intro i
    have hσi : |((i : ℂ).im - X) - (σ i : ℝ) * h| ≤ (|C₀| + 1) / 2 * h := by
      have e : ((i : ℂ).im - X) - (σ i : ℝ) * h = h * (D * ((i : ℂ).im - X) - σ i) := by
        rw [mul_sub, ← mul_assoc, mul_comm h D, hDh, one_mul, mul_comm]
      rw [e, abs_mul, abs_of_pos hh, mul_comm]
      refine mul_le_mul_of_nonneg_right ((hσd i).trans ?_) hh.le
      linarith [le_abs_self C₀]
    rw [hL]
    rcases Int.emod_two_eq_zero_or_one (σ i) with h0 | h1
    · have e : ((σ i / 2 : ℤ) : ℝ) * (2 * h) = (σ i : ℝ) * h := by
        have : (2 : ℤ) * (σ i / 2) = σ i := by omega
        have hc' : (2 : ℝ) * ((σ i / 2 : ℤ) : ℝ) = (σ i : ℝ) := by exact_mod_cast this
        linear_combination h * hc'
      rw [e]; linarith
    · have e : ((σ i / 2 : ℤ) : ℝ) * (2 * h) = (σ i : ℝ) * h - h := by
        have : (2 : ℤ) * (σ i / 2) + 1 = σ i := by omega
        have hc' : (2 : ℝ) * ((σ i / 2 : ℤ) : ℝ) + 1 = (σ i : ℝ) := by exact_mod_cast this
        linear_combination h * hc'
      rw [e, show ((i : ℂ).im - X) - ((σ i : ℝ) * h - h) =
        (((i : ℂ).im - X) - (σ i : ℝ) * h) + h by ring]
      exact (abs_add_le _ _).trans (by rw [abs_of_pos hh]; linarith)
  have hstrip : ∀ z, multDiff Z Z' z ≠ 0 → |z.re - 1 / 2| ≤ 1 / 2 := by
    intro z hz
    rcases mem_carrier_of_multDiff_ne_zero hz with h' | h'
    · obtain ⟨h1, h2⟩ := Z.strip _ h'
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨h1, h2⟩ := Z'.strip _ h'
      rw [abs_le]; constructor <;> linarith
  have hnorm : ∀ (w : ℂ) (t : ℝ), ‖w - t‖ ≤ |w.re - t| + |w.im| := fun w t => by
    simpa using Complex.norm_le_abs_re_add_abs_im (w - t)
  set Γ : ℂ → ℂ := fun z => gammaOf z - X with hΓ
  set Γc : ℂ → ℂ := fun z => conj (gammaOf z) - X with hΓc
  have hΓre : ∀ z, (Γ z).re = z.im - X := fun z => by simp [hΓ, gammaOf_re]
  have hΓim : ∀ z, (Γ z).im = -(z.re - 1 / 2) := fun z => by simp [hΓ, gammaOf_im]
  have hΓcre : ∀ z, (Γc z).re = z.im - X := fun z => by simp [hΓc, gammaOf_re]
  have hΓcim : ∀ z, (Γc z).im = z.re - 1 / 2 := fun z => by simp [hΓc, gammaOf_im]
  have hcast : ∀ i : S, ((σ i / 2 : ℤ) : ℂ) * ((2 * h : ℝ) : ℂ) =
      ((((σ i / 2 : ℤ) : ℝ) * (2 * h) : ℝ) : ℂ) := fun i => by push_cast; ring
  have hΓb : ∀ i : S, ‖Γ i - ((σ i / 2 : ℤ) : ℂ) * ((2 * h : ℝ) : ℂ)‖ ≤ L := fun i => by
    rw [hcast]; refine (hnorm _ _).trans ?_
    rw [hΓre, hΓim, abs_neg]; linarith [hhalf i, hstrip _ i.2.1]
  have hΓcb : ∀ i : S, ‖Γc i - ((σ i / 2 : ℤ) : ℂ) * ((2 * h : ℝ) : ℂ)‖ ≤ L := fun i => by
    rw [hcast]; refine (hnorm _ _).trans ?_
    rw [hΓcre, hΓcim]; linarith [hhalf i, hstrip _ i.2.1]
  have hinj : ∀ P : Set S, (∀ i ∈ P, ∀ j ∈ P, σ i % 2 = σ j % 2) →
      Set.InjOn (fun i => σ i / 2) P := by
    intro P hP i hi j hj e
    apply hσ
    have := hP i hi j hj
    simp only at e
    omega
  set PA : Set S := {i | σ i % 2 = 0 ∧ (i : ℂ) ≠ z₀}
  set PB : Set S := {i | σ i % 2 = 1 ∧ (i : ℂ) ≠ z₀}
  have hz₀re : (Γ z₀).re = 0 := by rw [hΓre, hX, sub_self]
  have hz₀cre : (Γc z₀).re = 0 := by rw [hΓcre, hX, sub_self]
  have hz₀im : |(Γ z₀).im| ≤ 1 / 2 := by rw [hΓim, abs_neg]; exact hstrip _ hc
  have hz₀cim : |(Γc z₀).im| ≤ 1 / 2 := by rw [hΓcim]; exact hstrip _ hc
  have hsep : ∀ i ∈ PA ∪ PB, η ≤ ‖z₀ - (i : ℂ)‖ := by
    intro i hi
    have hne : (i : ℂ) ≠ z₀ := by rcases hi with hi | hi; exacts [hi.2, hi.2]
    rw [norm_sub_rev]
    exact hiso _ hne i.2.1 i.2.2
  obtain ⟨F₁, hF₁, hF₁A, hF₁0, hF₁d⟩ := hwin (fun i : S => Γ i) (fun i => σ i / 2) PA
    (hinj PA fun i hi j hj => by rw [hi.1, hj.1]) (fun i _ => hΓb i)
    (fun i _ => by rw [hΓim, abs_neg]; exact hstrip _ i.2.1) (Γ z₀) hz₀re hz₀im
    (fun i hi => by
      rw [show Γ z₀ - Γ i = gammaOf z₀ - gammaOf i by simp [hΓ], norm_gammaOf_sub]
      exact hsep i (Or.inl hi))
  obtain ⟨G₁, hG₁, hG₁B, hG₁0, hG₁d⟩ := hwin (fun i : S => Γc i) (fun i => σ i / 2) PB
    (hinj PB fun i hi j hj => by rw [hi.1, hj.1]) (fun i _ => hΓcb i)
    (fun i _ => by rw [hΓcim]; exact hstrip _ i.2.1) (Γc z₀) hz₀cre hz₀cim
    (fun i hi => by
      rw [show Γc z₀ - Γc i = conj (gammaOf z₀ - gammaOf i) by simp [hΓc], Complex.norm_conj,
        norm_gammaOf_sub]
      exact hsep i (Or.inr hi))
  set F := localWindow X F₁ with hF
  set G := localWindow X G₁ with hG
  have hFw : ApertureWindow a F := apertureWindow_localWindow hF₁ X
  have hGw : ApertureWindow a G := apertureWindow_localWindow hG₁ X
  have hFdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT F w‖ * (1 + |w.re - X|) ^ k ≤ M * Real.exp (a * |w.im|) := fun w hw => by
    rw [hF, paperFT_localWindow]
    have := hF₁d (w - X) (by simpa using hw)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans (le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity)))
  have hGdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT G w‖ * (1 + |w.re - X|) ^ k ≤ M * Real.exp (a * |w.im|) := fun w hw => by
    rw [hG, paperFT_localWindow]
    have := hG₁d (w - X) (by simpa using hw)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans (le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity)))
  have hnear : ∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - X| ≤ R → pointImage F G z = 0 := by
    intro z hz hcz hzR
    set i : S := ⟨z, hcz, hzR⟩
    rw [pointImage, hF, hG, paperFT_localWindow, paperFT_localWindow]
    rcases Int.emod_two_eq_zero_or_one (σ i) with he | ho
    · rw [show gammaOf z - X = Γ i from rfl, hF₁A i ⟨he, hz⟩, zero_mul]
    · rw [show conj (gammaOf z) - X = Γc i from rfl, hG₁B i ⟨ho, hz⟩, map_zero, mul_zero]
  have hsee : c * c ≤ ‖pointImage F G z₀‖ := by
    rw [pointImage, hF, hG, paperFT_localWindow, paperFT_localWindow, norm_mul, Complex.norm_conj]
    exact mul_le_mul hF₁0 hG₁0 hc0.le (hc0.le.trans hF₁0)
  have hP0_ne : pointImage F G z₀ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (mul_pos hc0 hc0) hsee)
  have htot := summable_multDiff_pointImage hZ hZ' hFw.1 hFw.hasCompactSupport hGw.1
    hGw.hasCompactSupport
  have hWdiff : Z.W F G - Z'.W F G = ∑' z, multDiff Z Z' z * pointImage F G z :=
    W_sub_W_eq_tsum hZ hZ' hFw.1 hFw.hasCompactSupport hGw.1 hGw.hasCompactSupport
  have hsplit : ∀ z, multDiff Z Z' z * pointImage F G z =
      (if z = z₀ then multDiff Z Z' z₀ * pointImage F G z₀ else 0) +
        (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0) := by
    intro z
    by_cases hz : z = z₀
    · subst hz
      have : ¬ R < |z.im - X| := by rw [hX, sub_self, abs_zero]; linarith
      rw [if_pos rfl, if_neg this, add_zero]
    · rw [if_neg hz, zero_add]
      split_ifs with hfar
      · rfl
      · by_cases hcz : multDiff Z Z' z = 0
        · rw [hcz, zero_mul]
        · rw [hnear z hz hcz (not_lt.mp hfar), mul_zero]
  have hsingle : Summable fun z => if z = z₀ then multDiff Z Z' z₀ * pointImage F G z₀ else 0 :=
    (hasSum_ite_eq z₀ _).summable
  have hfarS : Summable fun z => if R < |z.im - X| then multDiff Z Z' z * pointImage F G z
      else 0 :=
    (htot.sub hsingle).congr fun z => sub_eq_of_eq_add' (hsplit z)
  rw [tsum_congr hsplit, hsingle.tsum_add hfarS, tsum_ite_eq] at hWdiff
  obtain ⟨hfs, hfle⟩ := tsum_far_multDiff_le hZ hZ' hk ha hFdec hGdec hR
  have hfnorm : ∀ z, ‖(if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ =
      farTerm (multDiff Z Z') F G X R z := fun z => by
    unfold farTerm
    split_ifs
    · rw [norm_mul]
    · rw [norm_zero]
  have hfarle : ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ ≤
      M * M * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    (norm_tsum_le_tsum_norm (hfs.congr fun z => (hfnorm z).symm)).trans
      ((tsum_congr hfnorm).le.trans hfle)
  have hquot : (Z.W F G - Z'.W F G) / pointImage F G z₀ - multDiff Z Z' z₀ =
      (∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)) /
        pointImage F G z₀ := by
    rw [hWdiff, add_div, mul_div_cancel_right₀ _ hP0_ne, add_sub_cancel_left]
  refine ⟨F, G, hFw, hGw, ?_, hP0_ne, hnear, ?_⟩
  · rw [← hh_def, ← hLs, ← hcdef, sq]; exact hsee
  · obtain ⟨Sg, hSg⟩ : ∃ Sg, Sg = ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
      ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = (1 + R) ^ (2 * k - 2) := ⟨_, rfl⟩
    have hQ0 : 0 < Q := by rw [hQ]; positivity
    rw [← hSg, ← hQ] at hfarle ⊢
    rw [hquot, norm_div]
    have hdiv_le : ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ /
        ‖pointImage F G z₀‖ ≤
        ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ / (c * c) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hc0 hc0) hsee
    have hfarQ : ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ * Q ≤
        M * M * Real.exp a * (5 / 4) * (1 + |X|) ^ 2 * Sg := by
      have h1 : ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ ≤
          (M * M * Real.exp a * (5 / 4) * (1 + |X|) ^ 2 * Sg) / Q := by
        calc _ ≤ _ := hfarle
          _ = _ := by ring
      rwa [le_div_iff₀ hQ0] at h1
    calc ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ /
          ‖pointImage F G z₀‖ * Q
        ≤ ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ /
            (c * c) * Q := mul_le_mul_of_nonneg_right hdiv_le hQ0.le
      _ = (‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ * Q) /
            (c * c) := by ring
      _ ≤ (M * M * Real.exp a * (5 / 4) * (1 + |X|) ^ 2 * Sg) / (c * c) :=
            div_le_div_of_nonneg_right hfarQ (mul_pos hc0 hc0).le
      _ = localCameraConst a D C₀ η ε Cm C0 * (1 + |X|) ^ 2 * Sg := by rw [hBdef]; ring

/-! ### Sub-spacing camera constant and cubic log-budget -/

private theorem one_add_log_le {D : ℝ} (hD : 1 ≤ D) : 1 + Real.log D ≤ D := by
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < D)
  linarith

/-- Rescaled linear upper bound for `log x`: choosing tiny `α > 0` makes the slope `α` arbitrarily
small at the cost of a constant `log α⁻¹`. -/
theorem log_le_mul_add_log_inv {x α : ℝ} (hx : 0 < x) (hα : 0 < α) :
    Real.log x ≤ α * x + Real.log α⁻¹ := by
  have h1 : Real.log (α * x) ≤ α * x - 1 := Real.log_le_sub_one_of_pos (mul_pos hα hx)
  have h2 : Real.log x = Real.log (α * x) + Real.log α⁻¹ := by
    rw [Real.log_mul hα.ne' hx.ne', Real.log_inv]
    ring
  linarith

private theorem growthRate_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : 0 ≤ growthRate ℓ := by
  have hσ : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have hnf : 0 ≤ nfRate (slackBound ℓ) := by
    unfold nfRate
    have : 0 ≤ Real.log (2 * slackBound ℓ + 9) := Real.log_nonneg (by linarith)
    positivity
  unfold growthRate
  positivity

private theorem floorRate_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : 0 ≤ floorRate ℓ := by
  have hσ : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have hnf : 0 ≤ nfRate (slackBound ℓ) := by
    unfold nfRate
    have : 0 ≤ Real.log (2 * slackBound ℓ + 9) := Real.log_nonneg (by linarith)
    positivity
  unfold floorRate
  positivity

private theorem windowGrowth_pos {H L : ℝ} (hH : 0 < H) (hL : 0 ≤ L) : 0 < windowGrowth H L := by
  have hS : 0 ≤ windowSlack H L := by rw [windowSlack]; linarith
  rw [windowGrowth, nearestConstStrip]
  exact mul_pos (mul_pos (by positivity) (Real.exp_pos _)) (Real.exp_pos _)

/-- **Unrestricted sub-spacing window floor bound.** Valid for every `0 < η` without requiring
`D⁻¹ ≤ η` or `η ≤ 1`. -/
theorem log_inv_windowFloor_subspacing_le {D C₀ ℓ η : ℝ} (hD : 1 ≤ D) (hC : |C₀| ≤ ℓ * D)
    (hη0 : 0 < η) :
    Real.log (windowFloor (2 * D⁻¹) (localSlack D C₀) η)⁻¹ ≤
      floorRate ℓ * D * (1 + Real.log D) * (1 + Real.log D + max 0 (Real.log (1 / η))) := by
  have hD0 : 0 < D := by linarith
  have hℓ0 : 0 ≤ ℓ := nonneg_of_mul_nonneg_left ((abs_nonneg C₀).trans hC) hD0
  have hf0 := floorRate_nonneg hℓ0
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hpref : 0 ≤ floorRate ℓ * D * (1 + Real.log D) := by positivity
  rcases le_or_gt η 1 with hη1 | hη1
  · refine (log_inv_windowFloor_le_of_le_one hD hC hη0 hη1).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [le_max_right 0 (Real.log (1 / η))]) hpref
  · have hηD : D⁻¹ ≤ η := (inv_le_one_of_one_le₀ hD).trans hη1.le
    refine (log_inv_windowFloor_le hD hC hηD).trans ?_
    rw [sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith [le_max_left 0 (Real.log (1 / η))]) hpref

/-- **Exponential bound on `localCameraConst` at arbitrary separation `0 < η`.** -/
theorem localCameraConst_subspacing_le {a D C₀ η ε Cm ℓ : ℝ} (hD : 1 ≤ D) (hC : |C₀| ≤ ℓ * D)
    (hη0 : 0 < η) (hCm : 0 < Cm) :
    localCameraConst a D C₀ η ε Cm 1 ≤ 5 / 4 * Real.exp (2 * (growthRate ℓ * D *
      (1 + Real.log D)) + 2 * Real.log Cm + 2 * ε + a +
      2 * (floorRate ℓ * D * (1 + Real.log D) *
        (1 + Real.log D + max 0 (Real.log (1 / η))))) := by
  have hD0 : 0 < D := by linarith
  have hL0 := localSlack_nonneg (C₀ := C₀) hD0
  obtain ⟨G, hG⟩ : ∃ G, G = windowGrowth (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = windowFloor (2 * D⁻¹) (localSlack D C₀) η := ⟨_, rfl⟩
  have hG0 : 0 < G := by rw [hG]; exact windowGrowth_pos (by positivity) hL0
  have hF0 : 0 < F := by rw [hF]; exact windowFloor_pos (by positivity) hL0 hη0
  have hGl := log_windowGrowth_le hD hC
  have hFl := log_inv_windowFloor_subspacing_le hD hC hη0
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

private theorem max_log_inv_rpow_neg_le {T u M : ℝ} (hu1 : 1 ≤ u)
    (hTu : T = 2 * π * Real.exp u) (hM : 0 ≤ M) :
    max 0 (Real.log (1 / T ^ (-M))) ≤ 8 * M * u := by
  have h2π0 : 0 < 2 * π := by positivity
  have hT0 : 0 < T := by rw [hTu]; positivity
  have hlog2π : Real.log (2 * π) ≤ 7 := by
    have := Real.log_le_sub_one_of_pos h2π0
    linarith [Real.pi_le_four]
  have hlogT : Real.log T ≤ 8 * u := by
    rw [hTu, Real.log_mul h2π0.ne' (Real.exp_pos u).ne', Real.log_exp]
    linarith
  have hinv : 1 / T ^ (-M) = T ^ M := by
    rw [one_div, Real.rpow_neg hT0.le, inv_inv]
  rw [hinv, Real.log_rpow hT0]
  exact max_le (by positivity) ((mul_le_mul_of_nonneg_left hlogT hM).trans_eq (by ring))

private theorem subspacing_lower_bound {T u : ℝ} {k : ℕ} (hTu : T = 2 * π * Real.exp u)
    (hk : 1 ≤ k) :
    Real.exp (2 * ((k : ℝ) - 1) * u) ≤ (1 + T / 4) ^ (2 * k - 2) := by
  have e1 : 2 * k - 2 = 2 * (k - 1) := by omega
  have e2 : 2 * ((k : ℝ) - 1) * u = ((2 * (k - 1) : ℕ) : ℝ) * u := by
    push_cast [hk]; ring
  have hexp : Real.exp u ≤ 1 + T / 4 := by
    rw [hTu]
    have := Real.exp_pos u
    nlinarith [Real.pi_gt_three]
  rw [e1, e2, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos u).le hexp _

private theorem subspacing_ordinate_sq_le {T u : ℝ} {z₀ : ℂ} (hu1 : 1 ≤ u)
    (hTu : T = 2 * π * Real.exp u) (hz₀ : |z₀.im - T| ≤ T / 4) :
    (1 + |z₀.im|) ^ 2 ≤ 121 * Real.exp (2 * u) := by
  have hT0 : 0 < T := by rw [hTu]; positivity
  have habs : |z₀.im| ≤ 5 * T / 4 := by
    have h1 := abs_le.mp hz₀
    rw [abs_le]
    constructor <;> linarith
  have hexp1 : 1 ≤ Real.exp u := Real.one_le_exp (by linarith)
  have hlin : 1 + |z₀.im| ≤ 11 * Real.exp u := by
    have h5T : 5 * T / 4 ≤ 10 * Real.exp u := by
      rw [hTu]
      have := Real.exp_pos u
      nlinarith [Real.pi_le_four]
    linarith
  calc (1 + |z₀.im|) ^ 2 ≤ (11 * Real.exp u) ^ 2 := pow_le_pow_left₀ (by positivity) hlin 2
    _ = 121 * (Real.exp u * Real.exp u) := by ring
    _ = 121 * Real.exp (2 * u) := by rw [← Real.exp_add, two_mul]

private theorem subspacing_camera_budget
    {lam β M ℓ c K MK ρ α q S'' T u a ε D C₀ η Sg E : ℝ} {z₀ : ℂ} {k m : ℕ}
    (hu1 : 1 ≤ u) (hTu : T = 2 * π * Real.exp u) (hM : 0 ≤ M) (_hlam0 : 0 < lam)
    (hβlam : β ≤ lam) (hℓ0 : 0 ≤ ℓ)
    (hc : c = 2 * growthRate ℓ * lam ^ 2 + 2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M))
    (hK : K = c / 2 + 2) (_hMK0 : 0 < MK) (hρ0 : 0 < ρ)
    (hα : α = 1 / (8 * MK * (1 + ρ))) (hα0 : 0 < α)
    (hq : q = max 0 (Real.log α⁻¹)) (hS''1 : 1 ≤ S'')
    (hu_bud : 2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1 ≤ u)
    (ha : a = lam * (u / 2)) (hε : ε = β * u / 8) (hε0 : 0 < ε)
    (hD1 : 1 ≤ D) (hDup : D ≤ lam * u) (hC₀ℓ : |C₀| ≤ ℓ * D)
    (hη : η = T ^ (-M)) (hη0 : 0 < η)
    (hkK : K * u ^ 2 ≤ k) (hk1 : 1 ≤ k)
    (hmle : (m : ℝ) ≤ MK * u ^ 2) (hmε : (m : ℝ) / ε ≤ ρ * u)
    (hz₀ : |z₀.im - T| ≤ T / 4) (hSg0 : 0 ≤ Sg) (hSgS'' : Sg ≤ S'')
    (htail : E * (1 + T / 4) ^ (2 * k - 2) ≤
      localCameraConst a D C₀ η ε ((4 * (1 + (m : ℝ) / ε)) ^ m) 1 * (1 + |z₀.im|) ^ 2 * Sg) :
    E ≤ 1 / 4 := by
  have hu0 : 0 < u := by linarith
  have hD0 : 0 < D := by linarith
  have hg0 := growthRate_nonneg hℓ0
  have hf0 := floorRate_nonneg hℓ0
  have hq0 : 0 ≤ q := by rw [hq]; exact le_max_left _ _
  have hlS''0 : 0 ≤ Real.log S'' := Real.log_nonneg hS''1
  obtain ⟨Cm, hCm⟩ : ∃ Cm, Cm = (4 * (1 + (m : ℝ) / ε)) ^ m := ⟨_, rfl⟩
  rw [← hCm] at htail
  have hCm0 : 0 < Cm := by rw [hCm]; positivity
  have hlogCm : 2 * Real.log Cm ≤ u ^ 3 + 2 * MK * q * u ^ 2 := by
    rw [hCm, Real.log_pow]
    have h4u : 4 * (1 + (m : ℝ) / ε) ≤ 4 * (1 + ρ) * u := by
      have : 1 + ρ * u ≤ (1 + ρ) * u := by linarith [mul_le_mul_of_nonneg_left hu1 hρ0.le]
      linarith
    have hlog1 : Real.log (4 * (1 + (m : ℝ) / ε)) ≤ Real.log (4 * (1 + ρ) * u) :=
      Real.log_le_log (by positivity) h4u
    have hlog2 := log_le_mul_add_log_inv (show 0 < 4 * (1 + ρ) * u by positivity) hα0
    have hαmul : α * (4 * (1 + ρ) * u) = u / (2 * MK) := by
      rw [hα]; field_simp; ring
    have hlog3 : Real.log (4 * (1 + (m : ℝ) / ε)) ≤ u / (2 * MK) + q := by
      have hle_q : Real.log α⁻¹ ≤ q := by rw [hq]; exact le_max_right _ _
      linarith
    have h1ge : 1 ≤ 4 * (1 + (m : ℝ) / ε) := by
      have : 0 ≤ (m : ℝ) / ε := div_nonneg (Nat.cast_nonneg m) hε0.le
      linarith
    calc 2 * ((m : ℝ) * Real.log (4 * (1 + (m : ℝ) / ε)))
        ≤ 2 * ((MK * u ^ 2) * (u / (2 * MK) + q)) := by
          have := mul_le_mul hmle hlog3 (Real.log_nonneg h1ge) (by positivity)
          linarith
      _ = u ^ 3 + 2 * MK * q * u ^ 2 := by field_simp
  have hGterm : 2 * (growthRate ℓ * D * (1 + Real.log D)) ≤ 2 * growthRate ℓ * lam ^ 2 * u ^ 3 := by
    have h1 : D * (1 + Real.log D) ≤ D ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left (one_add_log_le hD1) hD0.le
    have h2 : D ^ 2 ≤ (lam * u) ^ 2 := pow_le_pow_left₀ hD0.le hDup 2
    have h3 : (lam * u) ^ 2 ≤ lam ^ 2 * u ^ 3 := by
      have hu23 : u ^ 2 ≤ u ^ 3 := by
        have := mul_le_mul_of_nonneg_right hu1 (sq_nonneg u)
        linarith [show 1 * u ^ 2 = u ^ 2 by ring, show u * u ^ 2 = u ^ 3 by ring]
      calc (lam * u) ^ 2 = lam ^ 2 * u ^ 2 := by ring
        _ ≤ lam ^ 2 * u ^ 3 := mul_le_mul_of_nonneg_left hu23 (sq_nonneg lam)
    have h4 := mul_le_mul_of_nonneg_left ((h1.trans h2).trans h3) hg0
    linarith
  have hFterm : 2 * (floorRate ℓ * D * (1 + Real.log D) *
      (1 + Real.log D + max 0 (Real.log (1 / η)))) ≤
      2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M) * u ^ 3 := by
    have hmax := max_log_inv_rpow_neg_le hu1 hTu hM
    rw [← hη] at hmax
    have h1 : 1 + Real.log D ≤ lam * u := (one_add_log_le hD1).trans hDup
    have h2 : 1 + Real.log D + max 0 (Real.log (1 / η)) ≤ (lam + 8 * M) * u := by linarith
    have h3 : D * (1 + Real.log D) ≤ lam ^ 2 * u ^ 2 := by
      calc D * (1 + Real.log D) ≤ (lam * u) * (lam * u) :=
            mul_le_mul hDup h1 (by linarith [Real.log_nonneg hD1]) (by positivity)
        _ = lam ^ 2 * u ^ 2 := by ring
    have h4 : D * (1 + Real.log D) * (1 + Real.log D + max 0 (Real.log (1 / η))) ≤
        lam ^ 2 * (lam + 8 * M) * u ^ 3 := by
      calc D * (1 + Real.log D) * (1 + Real.log D + max 0 (Real.log (1 / η)))
          ≤ (lam ^ 2 * u ^ 2) * ((lam + 8 * M) * u) :=
            mul_le_mul h3 h2 (by linarith [Real.log_nonneg hD1, le_max_left 0 (Real.log (1 / η))])
              (by positivity)
        _ = lam ^ 2 * (lam + 8 * M) * u ^ 3 := by ring
    have h5 := mul_le_mul_of_nonneg_left h4 hf0
    linarith
  have hB := localCameraConst_subspacing_le (a := a) (ε := ε) hD1 hC₀ℓ hη0 hCm0
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = 2 * (growthRate ℓ * D * (1 + Real.log D)) +
      2 * Real.log Cm + 2 * ε + a +
      2 * (floorRate ℓ * D * (1 + Real.log D) *
        (1 + Real.log D + max 0 (Real.log (1 / η)))) := ⟨_, rfl⟩
  rw [← hΦ] at hB
  have h2εa : 2 * ε + a ≤ lam * u := by
    rw [hε, ha]
    have : β * u ≤ lam * u := mul_le_mul_of_nonneg_right hβlam hu0.le
    linarith
  have hΦle : Φ ≤ (c + 1) * u ^ 3 + 2 * MK * q * u ^ 2 + lam * u := by
    rw [hΦ, hc]
    linarith [hGterm, hFterm, hlogCm, h2εa]
  have hY := subspacing_ordinate_sq_le hu1 hTu hz₀
  have hlog605 : Real.log 605 ≤ 605 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 605)
    linarith
  have h4prod : 4 * (localCameraConst a D C₀ η ε Cm 1 * (1 + |z₀.im|) ^ 2 * Sg) ≤
      Real.exp (Φ + 2 * u + Real.log S'' + Real.log 605) := by
    calc 4 * (localCameraConst a D C₀ η ε Cm 1 * (1 + |z₀.im|) ^ 2 * Sg)
        ≤ 4 * (5 / 4 * Real.exp Φ * (121 * Real.exp (2 * u)) * S'') := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul (mul_le_mul hB hY (by positivity) (by positivity)) hSgS'' hSg0
            (by positivity)
      _ = Real.exp (Real.log 605) * Real.exp Φ * Real.exp (2 * u) * Real.exp (Real.log S'') := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 605), Real.exp_log (by linarith)]
          ring
      _ = Real.exp (Φ + 2 * u + Real.log S'' + Real.log 605) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
  have hexp_cmp : Φ + 2 * u + Real.log S'' + Real.log 605 ≤ 2 * ((k : ℝ) - 1) * u := by
    have hk_low : (c + 4) * u ^ 3 - 2 * u ≤ 2 * ((k : ℝ) - 1) * u := by
      have h1 : 2 * (K * u ^ 2 - 1) * u ≤ 2 * ((k : ℝ) - 1) * u :=
        mul_le_mul_of_nonneg_right (by linarith) hu0.le
      rw [hK] at h1
      linarith [show 2 * ((c / 2 + 2) * u ^ 2 - 1) * u = (c + 4) * u ^ 3 - 2 * u by ring]
    have hu2 : u ≤ u ^ 2 := by
      simpa [sq] using mul_le_mul_of_nonneg_right hu1 hu0.le
    have h1u2 : 1 ≤ u ^ 2 := hu1.trans hu2
    have hrem : 2 * MK * q * u ^ 2 + (lam + 4) * u + (Real.log S'' + 605) ≤ u ^ 3 := by
      have hlin1 : (lam + 4) * u ≤ (lam + 4) * u ^ 2 :=
        mul_le_mul_of_nonneg_left hu2 (by positivity)
      have hlin2 : Real.log S'' + 605 ≤ (Real.log S'' + 605) * u ^ 2 :=
        le_mul_of_one_le_right (by positivity) h1u2
      have hsum : (2 * MK * q + (lam + 4) + (Real.log S'' + 605)) * u ^ 2 ≤ u * u ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [hu_bud]) (sq_nonneg u)
      linarith [show u * u ^ 2 = u ^ 3 by ring,
        show (2 * MK * q + (lam + 4) + (Real.log S'' + 605)) * u ^ 2 =
          2 * MK * q * u ^ 2 + (lam + 4) * u ^ 2 + (Real.log S'' + 605) * u ^ 2 by ring]
    linarith [hΦle, hlog605, hk_low, hrem, pow_nonneg hu0.le 3]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (1 + T / 4) ^ (2 * k - 2) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ, hTu]; positivity
  have h4bound : 4 * (localCameraConst a D C₀ η ε Cm 1 * (1 + |z₀.im|) ^ 2 * Sg) ≤ Q := by
    rw [hQ]
    exact (h4prod.trans (Real.exp_le_exp.mpr hexp_cmp)).trans (subspacing_lower_bound hTu hk1)
  rw [← hQ] at htail
  have h4tail : 4 * E * Q ≤ 1 * Q := by
    calc 4 * E * Q = 4 * (E * Q) := by ring
      _ ≤ Q := (mul_le_mul_of_nonneg_left htail (by norm_num)).trans h4bound
      _ = 1 * Q := (one_mul Q).symm
  have h4E : 4 * E ≤ 1 := le_of_mul_le_mul_right h4tail hQ0
  linarith

/-- **Master Quantitative Sub-Spacing Window Theorem.**
For `0 ≤ θ`, `λ > θ / 2`, `0 ≤ A`, `0 ≤ S`, and `0 ≤ M`, uniformly for `T ≥ T₀`:
for any two tempered configurations `Z, Z'` whose cluster in `[T / 2, 3T / 2]` has distinct-point
local count `≤ (θ / 2π) log(T / 2π) (y − x) + A log(T / 2π)` and global tempered tail `≤ S`,
every cluster point `z₀` in `|Im z₀ − T| ≤ T / 4` that is `T^{−M}`-isolated from other cluster
points in `[T / 2, 3T / 2]` admits windows `F, G` of aperture `λ · ½ log(T / 2π)` isolating `z₀`
up to error `≤ 1 / 4`. -/
theorem exists_subspacing_isolating_windows {θ lam A S M : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (_hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 → T ^ (-M) ≤ ‖z - z₀‖) →
          ∃ F G : ℝ → ℂ,
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F ∧
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
            pointImage F G z₀ ≠ 0 ∧
            (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ T / 4 →
              pointImage F G z = 0) ∧
            ‖(Z.W F G - Z'.W F G) / pointImage F G z₀ - multDiff Z Z' z₀‖ ≤ 1 / 4 := by
  have h2π0 : 0 < 2 * π := by positivity
  have hlam0 : 0 < lam := by linarith
  obtain ⟨β, hβ⟩ : ∃ β, β = lam - θ / 2 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hβlam : β ≤ lam := by rw [hβ]; linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = 2 * π * A / lam := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; positivity
  obtain ⟨e, he⟩ : ∃ e, e = 6 * slackBound ℓ * (1 + slackBound ℓ) := ⟨_, rfl⟩
  have : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have he0 : 0 ≤ e := by rw [he]; positivity
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * growthRate ℓ * lam ^ 2 +
      2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M) := ⟨_, rfl⟩
  have : 0 ≤ growthRate ℓ := growthRate_nonneg hℓ0
  have : 0 ≤ floorRate ℓ := floorRate_nonneg hℓ0
  have : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = c / 2 + 2 := ⟨_, rfl⟩
  have hK1 : 2 ≤ K := by rw [hK]; linarith
  obtain ⟨MK, hMK⟩ : ∃ MK, MK = e * lam + K + 2 := ⟨_, rfl⟩
  have hMK0 : 0 < MK := by rw [hMK]; positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = 8 * MK / β := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨α, hα⟩ : ∃ α, α = 1 / (8 * MK * (1 + ρ)) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = max 0 (Real.log α⁻¹) := ⟨_, rfl⟩
  obtain ⟨S'', hS''⟩ : ∃ S'', S'' = max S 1 := ⟨_, rfl⟩
  have hS''1 : 1 ≤ S'' := by rw [hS'']; exact le_max_right _ _
  obtain ⟨U₀, hU₀⟩ : ∃ U₀, U₀ = max (max 1 (2 * π / lam))
      (2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1) := ⟨_, rfl⟩
  have hU₀1 : 1 ≤ U₀ := by rw [hU₀]; exact (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨2 * π * Real.exp U₀, ?_, fun T hT Z Z' hZ hZ' hStail hcount z₀ hz₀ hc_ne hiso => ?_⟩
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hU₀1) h2π0.le
  -- height scale `u = log(T / 2π)`
  have hTdiv : Real.exp U₀ ≤ T / (2 * π) := by rw [le_div_iff₀ h2π0]; linarith
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (T / (2 * π)) := ⟨_, rfl⟩
  rw [← hu] at hcount ⊢
  have huU₀ : U₀ ≤ u := by
    rw [hu, ← Real.log_exp U₀]
    exact Real.log_le_log (Real.exp_pos _) hTdiv
  rw [hU₀] at huU₀
  have hu1 : 1 ≤ u := ((le_max_left _ _).trans (le_max_left _ _)).trans huU₀
  have hu0 : 0 < u := by linarith
  have hu_lam : 2 * π / lam ≤ u := ((le_max_right _ _).trans (le_max_left _ _)).trans huU₀
  have hu_bud : 2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1 ≤ u :=
    (le_max_right _ _).trans huU₀
  have hTu : T = 2 * π * Real.exp u := by
    rw [hu, Real.exp_log (lt_of_lt_of_le (Real.exp_pos _) hTdiv)]
    field_simp
  have hT0 : 0 < T := by rw [hTu]; positivity
  -- camera parameters
  obtain ⟨a, ha⟩ : ∃ a, a = lam * (u / 2) := ⟨_, rfl⟩
  rw [← ha]
  obtain ⟨ε, hε⟩ : ∃ ε, ε = β * u / 8 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨D, hD⟩ : ∃ D, D = (θ + β) / (2 * π) * u := ⟨_, rfl⟩
  have hDa : π * D / 2 + 2 * ε ≤ a := by
    refine le_of_eq ?_
    rw [hD, hε, ha, hβ]; field_simp; ring
  have hDlow : lam / (2 * π) * u ≤ D := by
    rw [hD, hβ]
    have : lam ≤ θ + (lam - θ / 2) := by linarith
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right this h2π0.le) hu0.le
  have hDup : D ≤ lam * u := by
    rw [hD, hβ]
    have h1 : (θ + (lam - θ / 2)) / (2 * π) ≤ lam := by
      rw [div_le_iff₀ h2π0]
      have h2lam : 2 * lam ≤ lam * (2 * π) := by
        have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ 2 * π by linarith [Real.pi_gt_three])
          hlam0.le
        linarith
      linarith
    exact mul_le_mul_of_nonneg_right h1 hu0.le
  have hD1 : 1 ≤ D := by
    refine le_trans ?_ hDlow
    have h1 := (div_le_iff₀ hlam0).mp hu_lam
    rw [div_mul_eq_mul_div, le_div_iff₀ h2π0]
    linarith
  have hD0 : 0 < D := by linarith
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = A * u := ⟨_, rfl⟩
  have hC₀ℓ : |C₀| ≤ ℓ * D := by
    rw [hC₀, abs_of_nonneg (by positivity), hℓ]
    have huD : u ≤ 2 * π / lam * D := by
      calc u = 2 * π / lam * (lam / (2 * π) * u) := by field_simp
        _ ≤ 2 * π / lam * D := mul_le_mul_of_nonneg_left hDlow (by positivity)
    calc A * u ≤ A * (2 * π / lam * D) := mul_le_mul_of_nonneg_left huD hA
      _ = 2 * π * A / lam * D := by ring
  obtain ⟨η, hη⟩ : ∃ η, η = T ^ (-M) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact Real.rpow_pos_of_pos hT0 _
  -- decay order `k = ⌈K u²⌉₊` and spline order `m = ⌈W⌉₊ + k`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈K * u ^ 2⌉₊ := ⟨_, rfl⟩
  have hkK : K * u ^ 2 ≤ k := by rw [hk]; exact Nat.le_ceil _
  have hkle : (k : ℝ) ≤ K * u ^ 2 + 1 := by
    rw [hk]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : 1 ≤ k := by
    have h1 : (1 : ℝ) ≤ K * u ^ 2 :=
      one_le_mul_of_one_le_of_one_le (by linarith [hK1]) (one_le_pow₀ hu1 : 1 ≤ u ^ 2)
    exact_mod_cast h1.trans hkK
  obtain ⟨W, hWdef⟩ : ∃ W, W = windowExponent (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWdef, windowExponent]
    have := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
    positivity
  have hWle : W ≤ e * D := by rw [hWdef, he]; exact windowExponent_le hD1 hC₀ℓ
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈W⌉₊ + k := ⟨_, rfl⟩
  have hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + k ≤ m := by
    rw [hmdef, ← hWdef]; push_cast; linarith [Nat.le_ceil W]
  have hmle : (m : ℝ) ≤ MK * u ^ 2 := by
    rw [hmdef, hMK]; push_cast
    have h1 : (⌈W⌉₊ : ℝ) ≤ W + 1 := (Nat.ceil_lt_add_one hW0).le
    have h2 : e * D ≤ e * (lam * u) := mul_le_mul_of_nonneg_left hDup he0
    have hu2 : u ≤ u ^ 2 := by simpa [sq] using mul_le_mul_of_nonneg_right hu1 hu0.le
    have : 1 ≤ u ^ 2 := one_le_pow₀ hu1
    have h3 : e * (lam * u) ≤ e * lam * u ^ 2 := by
      calc e * (lam * u) = e * lam * u := by ring
        _ ≤ e * lam * u ^ 2 := mul_le_mul_of_nonneg_left hu2 (by positivity)
    linarith [hWle, hkle,
      show (e * lam + K + 2) * u ^ 2 = e * lam * u ^ 2 + K * u ^ 2 + 2 * u ^ 2 by ring]
  have hmε : (m : ℝ) / ε ≤ ρ * u := by
    rw [div_le_iff₀ hε0, hρ, hε]
    have : 8 * MK / β * u * (β * u / 8) = MK * u ^ 2 := by field_simp
    rw [this]; exact hmle
  obtain ⟨b, hb, hbs, hb1, hb0, hbm⟩ := exists_explicit_bump hε0 m
  have hsub_band : ∀ z : ℂ, |z.im - z₀.im| ≤ T / 4 → |z.im - T| ≤ T / 2 := fun z hz => by
    have h1 := abs_le.mp hz
    have h2 := abs_le.mp hz₀
    rw [abs_le]; constructor <;> linarith
  have hiso' : ∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ T / 4 → η ≤ ‖z - z₀‖ :=
    fun z hne hcz hzR => by rw [hη]; exact hiso z hne hcz (hsub_band z hzR)
  have hcount' : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ T / 4 ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀ := by
    intro s x y hxy hs
    have hc1 := hcount s x y hxy fun z hz =>
      ⟨(hs z hz).1, hsub_band z (hs z hz).2.1, (hs z hz).2.2⟩
    rw [← hC₀] at hc1
    have hDθ : θ / (2 * π) * u ≤ D := by
      rw [hD]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith [hβ0]) h2π0.le) hu0.le
    have hmul : θ / (2 * π) * u * (y - x) ≤ D * (y - x) :=
      mul_le_mul_of_nonneg_right hDθ (sub_nonneg.mpr hxy)
    linarith
  obtain ⟨F, G, hFw, hGw, _, hP0_ne, hnear, htail⟩ :=
    exists_isolating_window_pair_of_bump hD0 hη0 hε0 hDa hb hbs hb1 hk1 hm (C0 := 1) hbm
      (fun w => by rw [one_mul]; exact hb0 w) hZ hZ' (R := T / 4) (by positivity) hc_ne hiso'
      hcount'
  refine ⟨F, G, hFw, hGw, hP0_ne, hnear, ?_⟩
  have hSg0 : 0 ≤ ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    tsum_nonneg fun z => div_nonneg (norm_nonneg _)
      (by have := Complex.normSq_nonneg (gammaOf z); linarith)
  exact subspacing_camera_budget hu1 hTu hM hlam0 hβlam hℓ0 hc hK hMK0 hρ0 hα hα0 hq hS''1
    hu_bud ha hε hε0 hD1 hDup hC₀ℓ hη hη0 hkK hk1 hmle hmε hz₀ hSg0
    (hStail.trans (by rw [hS'']; exact le_max_left _ _)) htail

/-! ### Exact polynomial and `o(1 / log T)` local inversion corollaries -/

/-- **Exact polynomial-scale local inversion above `θ / 2`.**
If `Z` and `Z'` agree on diagonal windows of aperture `λ · ½ log(T / 2π)` (`λ > θ / 2`), then
every `T^{−M}`-isolated point in `|Im z₀ − T| ≤ T / 4` has `multDiff Z Z' z₀ = 0`. -/
theorem multDiff_eq_zero_of_subspacing_isolated {θ lam A S M : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 →
          (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 → T ^ (-M) ≤ ‖z - z₀‖) →
          multDiff Z Z' z₀ = 0 := by
  obtain ⟨T₀, hT₀, hwin⟩ := exists_subspacing_isolating_windows hθ hlam hA hS hM
  refine ⟨T₀, hT₀, fun T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hiso => ?_⟩
  by_contra hc
  obtain ⟨F, G, hFw, hGw, _, _, hle⟩ := hwin T hT Z Z' hZ hZ' hStail hcount z₀ hz₀ hc hiso
  rw [W_eq_of_mimic hZ hZ' hW hFw hGw, sub_self, zero_div, zero_sub, norm_neg] at hle
  linarith [one_le_norm_multDiff hc]

/-- **Polynomial near-collision localization.** Under the hypotheses of
`multDiff_eq_zero_of_subspacing_isolated`, every remaining discrepancy `multDiff Z Z' z₀ ≠ 0` in
`|Im z₀ − T| ≤ T / 4` has a distinct cluster neighbour in `[T / 2, 3T / 2]` within `< T^{−M}`. -/
theorem exists_nearCollision_of_mimic_above_half_density {θ lam A S M : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ ‖z - z₀‖ < T ^ (-M) := by
  obtain ⟨T₀, hT₀, hexact⟩ := multDiff_eq_zero_of_subspacing_isolated hθ hlam hA hS hM
  refine ⟨T₀, hT₀, fun T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hc => ?_⟩
  by_contra hall
  push Not at hall
  exact hc (hexact T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hall)

private theorem rpow_neg_one_le_div_log {T δ : ℝ} (hδ : 0 < δ) (hT3 : 3 ≤ T)
    (hTδ : 2 / δ * max 0 (Real.log (2 / δ)) ≤ T) :
    T ^ (-1 : ℝ) ≤ δ / Real.log T := by
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogle : Real.log T ≤ δ * T := by
    have h := log_le_mul_add_log_inv hT0 (show 0 < δ / 2 by positivity)
    have hinv : (δ / 2)⁻¹ = 2 / δ := by field_simp
    rw [hinv] at h
    have h1 : Real.log (2 / δ) ≤ max 0 (Real.log (2 / δ)) := le_max_right _ _
    have h2 : max 0 (Real.log (2 / δ)) ≤ δ / 2 * T := by
      calc max 0 (Real.log (2 / δ)) = δ / 2 * (2 / δ * max 0 (Real.log (2 / δ))) := by field_simp
        _ ≤ δ / 2 * T := mul_le_mul_of_nonneg_left hTδ (by positivity)
    linarith
  rw [Real.rpow_neg_one, inv_eq_one_div, div_le_div_iff₀ hT0 hlog0]
  linarith

/-- **Exact `o(1 / log T)` local inversion above `θ / 2`.**
For every `δ > 0`, uniformly for `T ≥ T₀`, `Z` and `Z'` agree at every `(δ / log T)`-isolated
point in `|Im z₀ − T| ≤ T / 4`. -/
theorem multDiff_eq_zero_of_littleO_inv_log_isolated {θ lam A S δ : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 →
          (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
            δ / Real.log T ≤ ‖z - z₀‖) →
          multDiff Z Z' z₀ = 0 := by
  obtain ⟨T₁, hT₁, hexact⟩ := multDiff_eq_zero_of_subspacing_isolated hθ hlam hA hS
    (show (0 : ℝ) ≤ 1 by norm_num)
  refine ⟨max T₁ (2 / δ * max 0 (Real.log (2 / δ))), le_trans hT₁ (le_max_left _ _),
    fun T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hiso => ?_⟩
  have hT3 : 3 ≤ T := by
    have : 2 * π * 1 ≤ 2 * π * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.one_le_exp zero_le_one) (by positivity)
    linarith [Real.pi_gt_three, (le_max_left _ _).trans hT]
  have hle := rpow_neg_one_le_div_log hδ hT3 ((le_max_right _ _).trans hT)
  exact hexact T ((le_max_left _ _).trans hT) Z Z' hZ hZ' hW hStail hcount z₀ hz₀
    fun z hne hcz hzR => hle.trans (hiso z hne hcz hzR)

/-- **`o(1 / log T)` near-collision localization.** For every `δ > 0`, uniformly for `T ≥ T₀`,
every discrepancy `multDiff Z Z' z₀ ≠ 0` in `|Im z₀ − T| ≤ T / 4` has a distinct cluster neighbour
in `[T / 2, 3T / 2]` within `< δ / log T`. -/
theorem exists_nearCollision_littleO_inv_log {θ lam A S δ : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧
            ‖z - z₀‖ < δ / Real.log T := by
  obtain ⟨T₀, hT₀, hexact⟩ := multDiff_eq_zero_of_littleO_inv_log_isolated hθ hlam hA hS hδ
  refine ⟨T₀, hT₀, fun T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hc => ?_⟩
  by_contra hall
  push Not at hall
  exact hc (hexact T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hall)

/-! ### Single-configuration multiplicity readout at `λ > θ / 2` -/

/-- **Single-configuration multiplicity readout.** Comparing `Z` against `emptyZeroConfig` shows
that a single window pair `(F, G)` of aperture `λ · ½ log(T / 2π)` (`λ > θ / 2`) determines the
exact integer multiplicity `Z.mult z₀` (within `1 / 4`, hence `Z.W F G ≠ 0`) of every
`T^{−M}`-isolated point `z₀ ∈ Z.carrier` in `|Im z₀ − T| ≤ T / 4`. -/
theorem exists_window_pair_reads_mult_subspacing {θ lam A S M : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z : ZeroConfig, TemperedConfig Z →
        ∑' z, ‖Z.carrier.indicator (fun w => (Z.mult w : ℂ)) z‖ /
          (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, z ∈ Z.carrier ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ ∈ Z.carrier, |z₀.im - T| ≤ T / 4 →
          (∀ z ∈ Z.carrier, z ≠ z₀ → |z.im - T| ≤ T / 2 → T ^ (-M) ≤ ‖z - z₀‖) →
          ∃ F G : ℝ → ℂ,
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F ∧
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
            pointImage F G z₀ ≠ 0 ∧
            Z.W F G ≠ 0 ∧
            (∀ z ∈ Z.carrier, z ≠ z₀ → |z.im - z₀.im| ≤ T / 4 → pointImage F G z = 0) ∧
            ‖Z.W F G / pointImage F G z₀ - (Z.mult z₀ : ℂ)‖ ≤ 1 / 4 := by
  obtain ⟨T₀, hT₀, hwin⟩ := exists_subspacing_isolating_windows hθ hlam hA hS hM
  refine ⟨T₀, hT₀, fun T hT Z hZ hStail hcount z₀ hz₀car hz₀ hiso => ?_⟩
  have hmd : ∀ z, multDiff Z emptyZeroConfig z ≠ 0 ↔ z ∈ Z.carrier := fun z => by
    rw [multDiff_emptyZeroConfig]
    by_cases hz : z ∈ Z.carrier
    · rw [Set.indicator_of_mem hz]
      exact ⟨fun _ => hz,
        fun _ => Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Z.one_le_mult z hz))⟩
    · rw [Set.indicator_of_notMem hz]
      exact ⟨fun h => False.elim (h rfl), fun h => False.elim (hz h)⟩
  have hStail' : ∑' z, ‖multDiff Z emptyZeroConfig z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S := by
    simpa only [multDiff_emptyZeroConfig] using hStail
  obtain ⟨F, G, hFw, hGw, hP0, hnear, hle⟩ := hwin T hT Z emptyZeroConfig hZ
    temperedConfig_emptyZeroConfig hStail'
    (fun s x y hxy hs => hcount s x y hxy fun z hz =>
      ⟨(hmd z).mp (hs z hz).1, (hs z hz).2.1, (hs z hz).2.2⟩)
    z₀ hz₀ ((hmd z₀).mpr hz₀car)
    (fun z hne hcz hzR => hiso z ((hmd z).mp hcz) hne hzR)
  rw [W_emptyZeroConfig, sub_zero, multDiff_emptyZeroConfig, Set.indicator_of_mem hz₀car] at hle
  have hW_ne : Z.W F G ≠ 0 := by
    intro h0
    rw [h0, zero_div, zero_sub, norm_neg, Complex.norm_natCast] at hle
    have h1 : (1 : ℝ) ≤ (Z.mult z₀ : ℝ) := by exact_mod_cast Z.one_le_mult z₀ hz₀car
    linarith
  exact ⟨F, G, hFw, hGw, hP0, hW_ne,
    fun z hzc hne hzR => hnear z hne ((hmd z).mpr hzc) hzR, hle⟩

end GaloisForLFunctions.ZeroConfigurationGeometry
