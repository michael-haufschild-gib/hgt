import GaloisForLFunctions.SquareRootThreshold.OnLineSamplingAtTheNyquistAperture

/-!
# Crystallization hides off-line zeros: visibility is not monotone

Adding on-line zeros can only help Weil positivity, since each contributes `|h_f(γ)|² ≥ 0`. One
might expect the converse for off-line zeros: more off-line zeros, more visibility. This is false.

**Non-monotonicity** (`exists_offLine_superset_hiding`). Let `Z` be the off-line lattice
`{½ ± δ + 2πij/L}` (one pair per period `2π/L`) and `Z'` the uniform two-point crystal obtained by
adding its half-step translate `{½ ± δ + 2πi(j + ½)/L}` at the same depth. Then `Z ⊆ Z'`, all zeros
of `Z'` are off the line, and at every aperture `a ∈ (L/2, L]`

* `Z` is visible (`twoMode_visible`: its first lag mode `2cosh(δL)` exceeds the diagonal `2`);
* `Z'` is invisible (`uniform_crystal_hides`: the crystal hides up to its Nyquist aperture `L`).

So positivity is a collective property of the configuration: off-line zeros can mask each other
when they complete a crystal, and the visibility of a configuration says nothing about the
visibility of its sub-configurations.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The single-pair pattern: offsets `0`, one pair per period. -/
def singlePairTheta : Fin 1 → ℝ := fun _ => 0

/-- The two-point crystal: offsets `0` and `½`. -/
def halfStepTheta : Fin 2 → ℝ := ![0, 1 / 2]

theorem singlePairTheta_distinct :
    ∀ r r' : Fin 1, ∀ j j' : ℤ, singlePairTheta r + j = singlePairTheta r' + j' →
      r = r' ∧ j = j' := by
  intro r r' j j' h
  refine ⟨Subsingleton.elim _ _, ?_⟩
  simp only [singlePairTheta, zero_add] at h
  exact_mod_cast h

theorem halfStepTheta_distinct :
    ∀ r r' : Fin 2, ∀ j j' : ℤ, halfStepTheta r + j = halfStepTheta r' + j' →
      r = r' ∧ j = j' := by
  have hnot : ∀ j j' : ℤ, (j : ℝ) ≠ 1 / 2 + j' := by
    intro j j' h
    have h2 : (2 : ℝ) * (j - j') = 1 := by linarith
    have : (2 * (j - j') : ℤ) = 1 := by exact_mod_cast h2
    omega
  intro r r' j j' h
  fin_cases r <;> fin_cases r' <;> simp only [halfStepTheta, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one] at h ⊢
  · exact ⟨trivial, by exact_mod_cast (by linarith : (j : ℝ) = j')⟩
  · exact absurd (by linarith : (j : ℝ) = 1 / 2 + j') (hnot j j')
  · exact absurd (by linarith : (j' : ℝ) = 1 / 2 + j) (hnot j' j)
  · exact ⟨trivial, by exact_mod_cast (by linarith : (j : ℝ) = j')⟩

theorem halfStepTheta_crystal :
    ∀ r r' : Fin 2, ∃ k : ℤ, (2 : ℕ) * halfStepTheta r - (2 : ℕ) * halfStepTheta r' = k := by
  intro r r'
  fin_cases r <;> fin_cases r' <;>
    simp only [halfStepTheta, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.mk_one, Nat.cast_ofNat]
  · exact ⟨0, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- **A two-mode visibility criterion.** A lag-lattice configuration with `|D(1)| > Re D(0)` is
visible at every aperture `a ∈ (ℓ/2, ℓ]`. -/
theorem twoMode_visible (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) (D : ℤ → ℂ)
    (hD : ∀ m, D (-m) = conj (D m))
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    (h1 : (D 0).re < ‖D 1‖) {a : ℝ} (ha1 : ℓ / 2 < a) (ha2 : a ≤ ℓ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ (Z.W f f).re < 0 := by
  have ha0 : 0 < a := lt_trans (by positivity) ha1
  have hn : ⌈2 * a / ℓ⌉₊ = 2 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor
    · rw [lt_div_iff₀ hℓ]; push_cast; linarith
    · rw [div_le_iff₀ hℓ]; push_cast; linarith
  by_contra hcon
  push Not at hcon
  have hT := (weil_nonneg_iff_toeplitz_of_lagFormula Z hℓ D hW ha0).mp hcon
  rw [hn] at hT
  have := norm_le_of_toeplitzForm_nonneg hD hT (m := 1) le_rfl (by norm_num)
  exact absurd this (not_le.mpr (by exact_mod_cast h1))

/-- **Crystallization hides off-line zeros.** For every depth `δ ∈ (0, ½]` and density `L > 0`
there are configurations `Z ⊆ Z'` with only off-line zeros, every zero simple, such that at every
aperture `a ∈ (L/2, L]` the smaller configuration `Z` is visible and the larger `Z'` is
invisible. -/
theorem exists_offLine_superset_hiding {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∃ Z Z' : ZeroConfig, Z.carrier ⊆ Z'.carrier ∧ (∀ ρ ∈ Z'.carrier, ρ.re ≠ 1 / 2) ∧
      (∀ ρ, Z.mult ρ = 1) ∧ (∀ ρ, Z'.mult ρ = 1) ∧
      ∀ a : ℝ, L / 2 < a → a ≤ L →
        (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ (Z.W f f).re < 0) ∧
        ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z'.W f f).re := by
  set Z := patternConfig hL (scaledOffset L singlePairTheta) (fun _ => δ) (fun _ => hδ)
    (fun _ => hδ') with hZ
  set Z' := patternConfig hL (scaledOffset L halfStepTheta) (fun _ => δ) (fun _ => hδ)
    (fun _ => hδ') with hZ'
  refine ⟨Z, Z', ?_, ?_, fun _ => rfl, fun _ => rfl, fun a ha1 ha2 => ⟨?_, ?_⟩⟩
  · -- the single lattice is the first half of the crystal
    have hoff : scaledOffset L singlePairTheta 0 = scaledOffset L halfStepTheta 0 := by
      simp [scaledOffset, singlePairTheta, halfStepTheta]
    rintro _ (⟨⟨r, j⟩, rfl⟩ | ⟨⟨r, j⟩, rfl⟩)
    · refine Or.inl ⟨(0, j), ?_⟩
      simp only [Fin.fin_one_eq_zero r]
      rw [hoff]
    · refine Or.inr ⟨(0, j), ?_⟩
      simp only [Fin.fin_one_eq_zero r]
      rw [hoff]
  · rintro _ (⟨⟨r, j⟩, rfl⟩ | ⟨⟨r, j⟩, rfl⟩) <;> simp only [patternPoint] <;> intro h <;>
      linarith
  · refine twoMode_visible Z hL (patternSymbol L (scaledOffset L singlePairTheta) fun _ => δ)
      (patternSymbol_neg L _ _)
      (fun _ hf hfc => W_patternConfig hL _ _ _ _
        (scaledOffset_injective hL singlePairTheta_distinct) hf hfc) ?_ ha1 ha2
    rw [patternSymbol_zero, show (2 * ((1 : ℕ) : ℂ)).re = 2 by simp,
      show ((1 : ℤ) : ℤ) = ((1 : ℕ) : ℤ) from rfl, patternSymbol_uniform hL]
    simp only [Nat.cast_one, one_mul, Fin.sum_univ_one, pow_one]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hz : ‖phasePoint singlePairTheta 0‖ = 1 := by
      simp [phasePoint, singlePairTheta]
    rw [hz, mul_one]
    have := Real.one_lt_cosh.mpr (mul_ne_zero hδ.ne' hL.ne')
    linarith
  · intro f hf hfs
    exact uniform_crystal_hides halfStepTheta (fun _ => δ) (fun _ => hδ) (fun _ => hδ')
      halfStepTheta_distinct (fun _ _ => rfl) halfStepTheta_crystal hL
      (lt_trans (by positivity) ha1) (by push_cast; linarith) hf hfs

end GaloisForLFunctions.SquareRootThreshold
