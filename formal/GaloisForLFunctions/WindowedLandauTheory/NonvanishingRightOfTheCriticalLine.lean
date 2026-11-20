import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.WindowedCesaroBoundsForceZeroFreeHalfPlanes

/-!
# Nonvanishing right of the critical line from windowed Cesàro bounds

The outer reductions of the windowed route, each unconditional:

* `riemannHypothesis_of_zeta_windows`: if for every `ε > 0` the functional `G_ζ` satisfies
  `G_ζ(y) ≤ C y^{1/2+ε}` on windows `[Y, Y^{1+δ}]` with arbitrarily large `Y`, then RH.
* `zeroFree_of_windowed_family_all_eps`: the same for a fixed family `G_ζ + Σ w_i Re G_{χ_i}` gives
  `ζ(s) ≠ 0` and `L(s, χ_i) ≠ 0` on `Re s > 1/2`.
* `LFunction_ne_zero_of_primitive`: nonvanishing of `ζ` and of all primitive nonprincipal
  `L`-functions on `Re s > θ ≥ 0` gives it for every Dirichlet `L`-function, since
  `L(s, χ) = L(s, χ*) ∏_{p | N}(1 - χ*(p)p^{-s})` and the Euler factors do not vanish for `Re s > 0`.
* `LFunction_ne_zero_of_windows`: windows for `G_ζ` and, around every primitive nonprincipal
  character, windows for a family containing it give `L(s, χ) ≠ 0` on `Re s > 1/2` for every
  Dirichlet character (`χ ≠ 1` or `s ≠ 1`).
-/

open Set Complex

namespace WindowedLandauTheory

noncomputable section

/-- **RH from windows.** If for every `ε > 0` there are `δ > 0` and `C` with `G_ζ(y) ≤ C y^{1/2+ε}` for
all `y ∈ [Y, Y^{1+δ}]` and arbitrarily large `Y`, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_zeta_windows
    (h : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)),
      zetaCesaroFunctional y ≤ C * y ^ (1 / 2 + ε)) :
    RiemannHypothesis := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro s hs
  obtain ⟨δ, hδ, C, hwin⟩ := h ((s.re - 1 / 2) / 2) (by linarith)
  have hfam : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)),
      familyCesaroFunctional (N := fun _ : Empty => 1) (fun i : Empty => i.elim)
        (fun i : Empty => i.elim) y ≤ C * y ^ (1 / 2 + (s.re - 1 / 2) / 2) := by
    intro Y₀
    obtain ⟨Y, hY, hYw⟩ := hwin Y₀
    refine ⟨Y, hY, fun y hy => ?_⟩
    simpa [familyCesaroFunctional] using hYw y hy
  exact (zeroFree_of_windowed_cesaro_bound (χ := fun i : Empty => i.elim) (fun i => i.elim)
    (fun i : Empty => i.elim) (fun i => i.elim) (by linarith) hδ hfam s (by linarith)).1

/-- **A fixed family with windows at every exponent above `1/2`.** Then `ζ` and every `L(·, χ_i)`
are zero-free on `Re s > 1/2`. -/
theorem zeroFree_of_windowed_family_all_eps {ι : Type*} [Fintype ι] {N : ι → ℕ}
    [∀ i, NeZero (N i)] {χ : (i : ι) → DirichletCharacter ℂ (N i)} (hχ : ∀ i, χ i ≠ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (h : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)),
      familyCesaroFunctional χ w y ≤ C * y ^ (1 / 2 + ε)) :
    ∀ s : ℂ, 1 / 2 < s.re →
      riemannZeta s ≠ 0 ∧ ∀ i, DirichletCharacter.LFunction (χ i) s ≠ 0 := by
  intro s hs
  obtain ⟨δ, hδ, C, hwin⟩ := h ((s.re - 1 / 2) / 2) (by linarith)
  exact zeroFree_of_windowed_cesaro_bound hχ w hw (by linarith) hδ hwin s (by linarith)

/-! ## A family around a given character -/

/-- Levels of a family with one extra member of level `N₀`. -/
def extendedLevel {ι : Type*} (N₀ : ℕ) (N : ι → ℕ) : Option ι → ℕ
  | none => N₀
  | some i => N i

instance extendedLevel.neZero {ι : Type*} (N₀ : ℕ) [NeZero N₀] (N : ι → ℕ)
    [∀ i, NeZero (N i)] (j : Option ι) : NeZero (extendedLevel N₀ N j) := by
  cases j with
  | none => exact (inferInstance : NeZero N₀)
  | some i => exact (inferInstance : NeZero (N i))

/-- The family `χ_i` together with the extra member `χ₀`. -/
def extendedFamily {ι : Type*} {N₀ : ℕ} {N : ι → ℕ} (χ₀ : DirichletCharacter ℂ N₀)
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) :
    (j : Option ι) → DirichletCharacter ℂ (extendedLevel N₀ N j)
  | none => χ₀
  | some i => χ i

/-- The weights `w_i` together with `w₀` for the extra member. -/
def extendedWeight {ι : Type*} (w₀ : ℝ) (w : ι → ℝ) : Option ι → ℝ
  | none => w₀
  | some i => w i

theorem familyCesaroFunctional_extended {ι : Type*} [Fintype ι] {N₀ : ℕ} [NeZero N₀]
    {N : ι → ℕ} [∀ i, NeZero (N i)] (χ₀ : DirichletCharacter ℂ N₀)
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w₀ : ℝ) (w : ι → ℝ) (y : ℝ) :
    familyCesaroFunctional (extendedFamily χ₀ χ) (extendedWeight w₀ w) y =
      familyCesaroFunctional χ w y + w₀ * (charCesaroFunctional χ₀ y).re := by
  simp only [familyCesaroFunctional, Fintype.sum_option, extendedWeight, extendedFamily]
  ring

/-- `χ₀` admits windowed families at exponent `θ`: some family of nonprincipal characters with
positive weights, together with `χ₀` at a positive weight, has
`G_ζ + w₀ Re G_{χ₀} + Σ w_i Re G_{χ_i} ≤ C y^{θ+ε}` on windows `[Y, Y^{1+δ}]` with arbitrarily
large `Y`, for every `ε > 0`. -/
def HasWindowedFamily {N₀ : ℕ} [NeZero N₀] (χ₀ : DirichletCharacter ℂ N₀) (θ : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (N : ι → ℕ) (_ : ∀ i, NeZero (N i))
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (_ : ∀ i, χ i ≠ 1) (w : ι → ℝ)
    (_ : ∀ i, 0 < w i) (w₀ : ℝ) (_ : 0 < w₀),
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)),
      familyCesaroFunctional χ w y + w₀ * (charCesaroFunctional χ₀ y).re ≤ C * y ^ (θ + ε)

/-- A nonprincipal character with windowed families at exponent `1/2` has a zero-free
`L`-function on `Re s > 1/2`, and so has `ζ`. -/
theorem LFunction_ne_zero_of_hasWindowedFamily {N₀ : ℕ} [NeZero N₀]
    {χ₀ : DirichletCharacter ℂ N₀} (hχ₀ : χ₀ ≠ 1) (h : HasWindowedFamily χ₀ (1 / 2)) :
    ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction χ₀ s ≠ 0 := by
  obtain ⟨ι, _, N, _, χ, hχ, w, hw, w₀, hw₀, hwin⟩ := h
  have hχ' : ∀ j, extendedFamily χ₀ χ j ≠ 1 := by
    rintro (_ | i)
    · exact hχ₀
    · exact hχ i
  have hw' : ∀ j, 0 < extendedWeight w₀ w j := by
    rintro (_ | i)
    · exact hw₀
    · exact hw i
  have hwin' : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)),
      familyCesaroFunctional (extendedFamily χ₀ χ) (extendedWeight w₀ w) y ≤
        C * y ^ (1 / 2 + ε) := by
    intro ε hε
    obtain ⟨δ, hδ, C, hYw⟩ := hwin ε hε
    refine ⟨δ, hδ, C, fun Y₀ => ?_⟩
    obtain ⟨Y, hY, hy⟩ := hYw Y₀
    exact ⟨Y, hY, fun y hyY => by
      rw [familyCesaroFunctional_extended]
      exact hy y hyY⟩
  intro s hs
  obtain ⟨hζ, hL⟩ := zeroFree_of_windowed_family_all_eps hχ' (extendedWeight w₀ w) hw' hwin' s hs
  exact ⟨hζ, hL none⟩

/-- **Reduction to primitive characters.** If `ζ` and every primitive nonprincipal `L`-function are
zero-free on `Re s > θ` with `θ ≥ 0`, then so is every Dirichlet `L`-function (away from the pole
of the principal ones): `L(s, χ) = L(s, χ*) ∏_{p | N}(1 - χ*(p) p^{-s})` with `|χ*(p) p^{-s}| < 1`. -/
theorem LFunction_ne_zero_of_primitive {θ : ℝ} (hθ : 0 ≤ θ)
    (hζ : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0)
    (hprim : ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), ψ.IsPrimitive → ψ ≠ 1 →
      ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ s ≠ 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : θ < s.re)
    (h1 : χ ≠ 1 ∨ s ≠ 1) : DirichletCharacter.LFunction χ s ≠ 0 := by
  have hs0 : 0 < s.re := lt_of_le_of_lt hθ hs
  -- the Euler factors at the primes of the level do not vanish
  have heuler : ∀ (M : ℕ) (ψ : DirichletCharacter ℂ M),
      ∏ p ∈ N.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s)) ≠ 0 := by
    intro M ψ
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hp1 : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
    have hlt : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
      calc ‖ψ p‖ * (p : ℝ) ^ (-s.re) ≤ 1 * (p : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one ψ _)
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ < 1 := by
            rw [one_mul]
            exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp1) (by linarith)
    intro h
    have h' : ψ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
    rw [h', norm_one] at hlt
    exact lt_irrefl _ hlt
  by_cases hχ1 : χ = 1
  · -- the principal character: `L(s, 1_N) = ζ(s) ∏_{p | N}(1 - p^{-s})`
    subst hχ1
    have hs1 : s ≠ 1 := h1.resolve_left fun h => h rfl
    have e := DirichletCharacter.LFunction_changeLevel (one_dvd N) (1 : DirichletCharacter ℂ 1)
      (Or.inr hs1)
    rw [map_one, DirichletCharacter.LFunction_modOne_eq] at e
    rw [e]
    exact mul_ne_zero (hζ s hs) (heuler 1 1)
  · haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero (NeZero.ne N)⟩
    have hψ1 : χ.primitiveCharacter ≠ 1 := by
      intro h
      apply hχ1
      rw [← χ.changeLevel_primitiveCharacter, h, map_one]
    have e := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
      (Or.inl hψ1)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at e
    rw [e]
    exact mul_ne_zero (hprim _ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hψ1 s hs)
      (heuler _ _)

/-- **Every Dirichlet `L`-function is zero-free right of the critical line**, given windows for
`G_ζ` and windowed families around every primitive nonprincipal character. -/
theorem LFunction_ne_zero_of_windows
    (hζ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)),
      zetaCesaroFunctional y ≤ C * y ^ (1 / 2 + ε))
    (hfam : ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), ψ.IsPrimitive → ψ ≠ 1 →
      HasWindowedFamily ψ (1 / 2))
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 / 2 < s.re)
    (h1 : χ ≠ 1 ∨ s ≠ 1) : DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_primitive (θ := 1 / 2) (by norm_num)
    (RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp
      (riemannHypothesis_of_zeta_windows hζ))
    (fun M hM ψ hprim hψ t ht => (LFunction_ne_zero_of_hasWindowedFamily hψ
      (hfam M ψ hprim hψ) t ht).2) χ hs h1

end

end WindowedLandauTheory
