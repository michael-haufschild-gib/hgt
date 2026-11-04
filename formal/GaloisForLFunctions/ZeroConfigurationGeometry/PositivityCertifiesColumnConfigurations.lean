import GaloisForLFunctions.ZeroConfigurationGeometry.PositivityCertifiesIsolableTilts

/-!
# Positivity certifies column configurations

The positivity criterion of `PositivityCertifiesIsolableTilts`, extended to columns of any depth.
A vertical column `{½ + δ + i(θ + 2πk)/ℓ}` has ordinates `(θ + 2πk)/ℓ − iδ`, a complex bounded
perturbation of the lattice of spacing `2π/ℓ` with imaginary parts in `[−½, ½]`; such sets are
blinded by windows of every aperture above `π` times their density
(`exists_window_blind_to_complex_perturbed_lattice`).

* **Finite unions** (`exists_window_blind_to_complex_perturbed_lattices`). Convolving the windows of
  the single columns blinds a finite union of total density `D` at every aperture `> πD`.
* **Isolation among columns** (`exists_isolating_window_of_columns_and_finset`). In a set whose
  ordinates lie on such columns, apart from finitely many points, every point has an isolating
  window at every aperture `> πD`.
* **Positivity at one aperture** (`re_eq_half_of_re_W_nonneg_of_columns`). A configuration made of
  finitely many columns of total density `D`, plus finitely many points, lies on the critical line
  as soon as `Re W_Z(f, f) ≥ 0` for every window of one aperture `a > πD`.
* **The function-field threshold** (`re_eq_half_of_re_W_nonneg_of_curve_columns`). The zeros of the
  zeta function of a curve of genus `g` over `𝔽_q` form `2g` columns of spacing `2π/log q`, of
  total density `g log q/π`. Positivity at one aperture `a > g log q`, i.e. on windows of lag
  `2a > 2g log q`, puts them on the line. The off-line lattice shows that no aperture
  `≤ (log q)/2` suffices for one column pair (`offLineLattice_re_W_nonneg`).

So the classical lag `2g log q` at which Weil positivity decides purity for curves is the
isolation aperture `πD` of their configuration. For one column pair the exact threshold is `πD/2`
(`offLineLattice_re_W_nonneg`, `offLineLattice_separated_above_nyquist`); whether positivity
certifies every column configuration above `πD/2`, i.e. at the identification lag `g log q` for
curves, is open.
-/

open MeasureTheory Complex Set
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- **Finite unions of complex perturbed lattices.** For finitely many complex perturbations `ν_j`
of lattices `h_jℤ`, with imaginary parts in `[−½, ½]` and total density `D = Σ_j 1/h_j`, every
aperture `r > πD` has a window blind to all `ν_j k` that sees any given `z₀` off them. -/
theorem exists_window_blind_to_complex_perturbed_lattices {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (h L : ι → ℝ) (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℂ)
    (hν : ∀ j ∈ T, ∀ k : ℤ, ‖ν j k - k * h j‖ ≤ L j)
    (him : ∀ j ∈ T, ∀ k, |(ν j k).im| ≤ 1 / 2) {r : ℝ}
    (hr : π * ∑ j ∈ T, (h j)⁻¹ < r) {z₀ : ℂ} (hz₀ : ∀ j ∈ T, ∀ k, z₀ ≠ ν j k) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ j ∈ T, ∀ k, paperFT f (ν j k) = 0) ∧
      paperFT f z₀ ≠ 0 := by
  classical
  set δ := (r - π * ∑ j ∈ T, (h j)⁻¹) / (T.card + 1) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (by linarith) (by positivity)
  have key : ∀ U ⊆ T, ∃ f : ℝ → ℂ, ApertureWindow (δ + ∑ j ∈ U, (π / h j + δ)) f ∧
      (∀ j ∈ U, ∀ k, paperFT f (ν j k) = 0) ∧ paperFT f z₀ ≠ 0 := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨b, hb, -, hbs, hb1⟩ := exists_smooth_window_paperFT_eq_one hδ0 z₀
      refine ⟨b, ?_, by simp, by rw [hb1]; exact one_ne_zero⟩
      rw [Finset.sum_empty, add_zero]
      exact ⟨hb.of_le (by norm_cast), hbs⟩
    | insert j U hj ih =>
      intro hsub
      obtain ⟨f, hf, hfz, hf0⟩ := ih ((Finset.subset_insert j U).trans hsub)
      have hjT := hsub (Finset.mem_insert_self j U)
      obtain ⟨g, hg, hgz, hg0⟩ := exists_window_blind_to_complex_perturbed_lattice (hh j hjT)
        (show π / h j < π / h j + δ by linarith) (ν j) (hν j hjT) (him j hjT) (hz₀ j hjT)
      obtain ⟨hw, hwt⟩ := apertureWindow_convolution hf hg
      refine ⟨convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume, ?_, fun i hi k => ?_, ?_⟩
      · rw [Finset.sum_insert hj]
        convert hw using 1
        ring
      · rw [hwt]
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rw [hgz k, mul_zero]
        · rw [hfz i hi k, zero_mul]
      · rw [hwt]; exact mul_ne_zero hf0 hg0
  obtain ⟨f, hf, hfz, hf0⟩ := key T le_rfl
  have hap : δ + ∑ j ∈ T, (π / h j + δ) = r := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hδ]
    have hc : (T.card : ℝ) + 1 ≠ 0 := by positivity
    rw [show ∑ j ∈ T, π / h j = π * ∑ j ∈ T, (h j)⁻¹ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    field_simp
    ring
  exact ⟨f, hap ▸ hf, hfz, hf0⟩

/-- **Isolating a point from columns.** Every `z₀ ∈ ℂ` has a window of aperture `r > πD` that sees
`z₀` and is blind to every `ν_j k ≠ z₀`; indices hitting `z₀` are moved off it by one unit. -/
theorem exists_window_isolating_in_columns {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (h L : ι → ℝ) (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℂ)
    (hν : ∀ j ∈ T, ∀ k : ℤ, ‖ν j k - k * h j‖ ≤ L j)
    (him : ∀ j ∈ T, ∀ k, |(ν j k).im| ≤ 1 / 2) {r : ℝ}
    (hr : π * ∑ j ∈ T, (h j)⁻¹ < r) (z₀ : ℂ) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧
      (∀ j ∈ T, ∀ k, ν j k ≠ z₀ → paperFT f (ν j k) = 0) ∧ paperFT f z₀ ≠ 0 := by
  classical
  set ν' : ι → ℤ → ℂ := fun j k => if ν j k = z₀ then ν j k + 1 else ν j k with hν'
  have hν'b : ∀ j ∈ T, ∀ k : ℤ, ‖ν' j k - k * h j‖ ≤ L j + 1 := by
    intro j hj k
    have h0 := hν j hj k
    by_cases hk : ν j k = z₀
    · simp only [hν', if_pos hk]
      calc ‖ν j k + 1 - k * h j‖ = ‖(ν j k - k * h j) + 1‖ := by congr 1; ring
        _ ≤ ‖ν j k - k * h j‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ L j + 1 := by rw [norm_one]; linarith
    · simp only [hν', if_neg hk]; linarith
  have hν'im : ∀ j ∈ T, ∀ k, |(ν' j k).im| ≤ 1 / 2 := by
    intro j hj k
    by_cases hk : ν j k = z₀
    · simp only [hν', if_pos hk, Complex.add_im, Complex.one_im, add_zero]; exact him j hj k
    · simp only [hν', if_neg hk]; exact him j hj k
  have hz₀' : ∀ j ∈ T, ∀ k, z₀ ≠ ν' j k := by
    intro j _ k hk
    by_cases hkk : ν j k = z₀
    · simp only [hν', if_pos hkk] at hk
      rw [hkk] at hk
      have := congrArg Complex.re hk
      simp at this
    · simp only [hν', if_neg hkk] at hk
      exact hkk hk.symm
  obtain ⟨f, hf, hblind, hsee⟩ := exists_window_blind_to_complex_perturbed_lattices T h
    (fun j => L j + 1) hh ν' hν'b hν'im hr hz₀'
  refine ⟨f, hf, fun j hj k hk => ?_, hsee⟩
  have : ν' j k = ν j k := by simp only [hν', if_neg hk]
  rw [← this]
  exact hblind j hj k

/-- **Isolation among columns.** In a set `S` whose ordinates lie on finitely many columns of total
density `D`, apart from a finite set `F`, every point has a window of aperture `a > πD` that sees
it and is blind to the rest of `S`. -/
theorem exists_isolating_window_of_columns_and_finset {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (h L : ι → ℝ) (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℂ)
    (hν : ∀ j ∈ T, ∀ k : ℤ, ‖ν j k - k * h j‖ ≤ L j)
    (him : ∀ j ∈ T, ∀ k, |(ν j k).im| ≤ 1 / 2) {a : ℝ} (ha : π * ∑ j ∈ T, (h j)⁻¹ < a)
    (F : Finset ℂ) {S : Set ℂ} (hS : ∀ z ∈ S, (∃ j ∈ T, ∃ k : ℤ, gammaOf z = ν j k) ∨ z ∈ F)
    (z₀ : ℂ) :
    ∃ f : ℝ → ℂ, ApertureWindow a f ∧ (∀ z ∈ S, z ≠ z₀ → paperFT f (gammaOf z) = 0) ∧
      paperFT f (gammaOf z₀) ≠ 0 := by
  classical
  set δ := (a - π * ∑ j ∈ T, (h j)⁻¹) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨f₁, hf₁, hf₁lat, hf₁0⟩ := exists_window_isolating_in_columns T h L hh ν hν him
    (r := a - δ) (by rw [hδ]; linarith) (gammaOf z₀)
  obtain ⟨g, hg, hgF, hg0⟩ := exists_window_vanishing_on_finset hδ0
    ((F.image gammaOf).erase (gammaOf z₀)) (Finset.notMem_erase _ _)
  obtain ⟨hw, hwt⟩ := apertureWindow_convolution hf₁ hg
  refine ⟨_, by rwa [sub_add_cancel] at hw, fun z hzS hz => ?_,
    by rw [hwt]; exact mul_ne_zero hf₁0 hg0⟩
  rw [hwt]
  rcases hS z hzS with ⟨j, hj, k, hk⟩ | hF
  · rw [hk, hf₁lat j hj k (by rw [← hk]; exact fun h' => hz (gammaOf_injective h')), zero_mul]
  · rw [hgF _ (Finset.mem_erase.mpr ⟨fun h' => hz (gammaOf_injective h'),
      Finset.mem_image_of_mem _ hF⟩), mul_zero]

/-- **Positivity at one aperture puts a column configuration on the line.** -/
theorem re_eq_half_of_re_W_nonneg_of_columns {ι : Type*} [DecidableEq ι] {Z : ZeroConfig}
    (T : Finset ι) (h L : ι → ℝ) (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℂ)
    (hν : ∀ j ∈ T, ∀ k : ℤ, ‖ν j k - k * h j‖ ≤ L j)
    (him : ∀ j ∈ T, ∀ k, |(ν j k).im| ≤ 1 / 2) {a : ℝ} (ha : π * ∑ j ∈ T, (h j)⁻¹ < a)
    (F : Finset ℂ) (hS : ∀ z ∈ Z.carrier, (∃ j ∈ T, ∃ k : ℤ, gammaOf z = ν j k) ∨ z ∈ F)
    (hpos : ∀ f, ApertureWindow a f → 0 ≤ (Z.W f f).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := fun _ hρ =>
  re_eq_half_of_re_W_nonneg hpos hρ fun z₀ _ =>
    exists_isolating_window_of_columns_and_finset T h L hh ν hν him ha F hS z₀

/-- **The function-field threshold.** A configuration whose ordinates lie on `2g` columns
`(θ_j + 2πk)/log q − iδ_j`, `|δ_j| ≤ ½`, `q > 1` — the zeros of the zeta function of a curve of
genus `g` over `𝔽_q` — lies on the critical line as soon as `Re W_Z(f, f) ≥ 0` for every window of
one aperture `a > g log q`. -/
theorem re_eq_half_of_re_W_nonneg_of_curve_columns {Z : ZeroConfig} {g : ℕ} {q : ℝ} (hq : 1 < q)
    (θ δ : Fin (2 * g) → ℝ) (hδ : ∀ j, |δ j| ≤ 1 / 2)
    (hS : ∀ z ∈ Z.carrier, ∃ j : Fin (2 * g), ∃ k : ℤ,
      gammaOf z = (((θ j + 2 * π * k) / Real.log q : ℝ) : ℂ) - I * δ j)
    {a : ℝ} (ha : g * Real.log q < a) (hpos : ∀ f, ApertureWindow a f → 0 ≤ (Z.W f f).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  classical
  have hl : 0 < Real.log q := Real.log_pos hq
  set ν : Fin (2 * g) → ℤ → ℂ := fun j k =>
    (((θ j + 2 * π * k) / Real.log q : ℝ) : ℂ) - I * δ j with hνdef
  have hν : ∀ j ∈ (Finset.univ : Finset (Fin (2 * g))), ∀ k : ℤ,
      ‖ν j k - k * ((2 * π / Real.log q : ℝ) : ℂ)‖ ≤ |θ j| / Real.log q + 1 / 2 := by
    intro j _ k
    have e : ν j k - k * ((2 * π / Real.log q : ℝ) : ℂ) =
        ((θ j / Real.log q : ℝ) : ℂ) - I * δ j := by
      simp only [hνdef]; push_cast; field_simp; ring
    rw [e]
    calc ‖((θ j / Real.log q : ℝ) : ℂ) - I * δ j‖
        ≤ ‖((θ j / Real.log q : ℝ) : ℂ)‖ + ‖I * δ j‖ := norm_sub_le _ _
      _ = |θ j| / Real.log q + |δ j| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hl, norm_mul,
            Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |θ j| / Real.log q + 1 / 2 := by linarith [hδ j]
  have him : ∀ j ∈ (Finset.univ : Finset (Fin (2 * g))), ∀ k, |(ν j k).im| ≤ 1 / 2 := by
    intro j _ k
    simp only [hνdef, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_sub, zero_add, abs_neg]
    exact hδ j
  have hsum : π * ∑ j ∈ (Finset.univ : Finset (Fin (2 * g))), (2 * π / Real.log q)⁻¹ =
      g * Real.log q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  refine re_eq_half_of_re_W_nonneg_of_columns Finset.univ (fun _ => 2 * π / Real.log q)
    (fun j => |θ j| / Real.log q + 1 / 2) (fun _ _ => by positivity) ν hν him
    (by rw [hsum]; exact ha) ∅ (fun z hz => ?_) hpos
  obtain ⟨j, k, hk⟩ := hS z hz
  exact Or.inl ⟨j, Finset.mem_univ _, k, hk⟩

end GaloisForLFunctions.ZeroConfigurationGeometry
