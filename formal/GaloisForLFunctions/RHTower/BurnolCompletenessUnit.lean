import GaloisForLFunctions.RHTower.BurnolQuotientGrowth
import GaloisForLFunctions.RHTower.MellinRealVanishing
import GaloisForLFunctions.RHTower.BurnolCompletenessLarge
import GaloisForLFunctions.RHTower.EntireAutomorphism
import GaloisForLFunctions.HTGeometry.PrincipalPartPolynomial

/-!
# Completeness of the evaluators at the critical aperture `a = 1`

Burnol proves Proposition 6.1 for `a ≥ 1` with Krein's theorem: the quotient `θ = M(f)/ζ` is
entire and of bounded characteristic in the two half-planes `Re s ≥ 2` and `Re s ≤ −1`, hence of
finite exponential type; the type is computed by the growth along the real axis, which is `≤ 0`,
and the Paley--Wiener theorem finishes.

Here the same conclusion is reached **without any Nevanlinna theory**:

* `θ` is bounded on `Re s ≥ 2` and on `Re s ≤ −1` (`BurnolQuotientGrowth`);
* `θ` is polynomially bounded on the heights of Proposition 5.1, so the maximum modulus principle
  on the rectangles `[−1,2] × [−T_n,T_n]` makes it polynomially bounded on the whole plane;
* an entire function of polynomial growth is a polynomial;
* `M(f)(σ) → 0` as `σ → +∞` (`MellinRealVanishing`), so that polynomial is `0`.

## Main results

* `zero_le_meromorphicOrderAt_burnolQuotient_extendedMellin`
* `eq_zero_of_zeta_dvd_extendedMellin_one_le` — **Proposition 6.1 for every `a ≥ 1`.**
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

/-! ## Divisibility at every point of the plane -/

/-- The order of `ζ` never exceeds the order of the continued Mellin transform: at the trivial
zeros because the functional-equation factor `χ` vanishes there, at `s = 1` because the transform
has at worst a simple pole, at `s = 0` because the numerator vanishes, and at the nontrivial zeros
by hypothesis. -/
theorem meromorphicOrderAt_riemannZeta_le_extendedMellin (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation a c d f) ρ)
    (z : ℂ) :
    meromorphicOrderAt riemannZeta z
      ≤ meromorphicOrderAt (extendedMellinContinuation a c d f) z := by
  by_cases h1 : z = 1
  · subst h1
    rw [GaloisForLFunctions.meromorphicOrderAt_riemannZeta_one]
    exact neg_one_le_meromorphicOrderAt_extendedMellinContinuation_one ha hev hc hd
  by_cases hζ : riemannZeta z = 0
  · rcases riemannZeta_zero_trivial_or_mem_strip hζ with ⟨n, hn⟩ | ⟨hlo, hhi⟩
    · have hk : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
      have hz : z = -(2 * (((n + 1 : ℕ) : ℂ))) := by rw [hn]; push_cast; ring
      rw [hz, meromorphicOrderAt_riemannZeta_trivial hk]
      exact one_le_meromorphicOrderAt_extendedMellinContinuation_trivial ha hev hc hd hk
    · exact hdvd z hζ hlo hhi
  · have hzord : meromorphicOrderAt riemannZeta z = ((0 : ℤ) : WithTop ℤ) := by
      have hana : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z (by simpa using h1)
      rw [hana.meromorphicOrderAt_eq, hana.analyticOrderAt_eq_zero.2 hζ]
      simp
    rw [hzord]
    by_cases h0 : z = 0
    · rw [h0]
      exact zero_le_meromorphicOrderAt_extendedMellinContinuation_zero ha hev hc hd
    · have := meromorphicOrderAt_nonneg_of_analyticAt
        (analyticAt_extendedMellinContinuation_of_ne ha hev hc hd h0 h1)
      simpa using this

/-- **The quotient by `ζ` is regular everywhere.** -/
theorem zero_le_meromorphicOrderAt_burnolQuotient_extendedMellin (ha : 0 < a)
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation a c d f) ρ)
    (z : ℂ) :
    0 ≤ meromorphicOrderAt (burnolQuotient (extendedMellinContinuation a c d f)) z := by
  have hmero : MeromorphicAt (extendedMellinContinuation a c d f) z :=
    meromorphicAt_extendedMellinContinuation ha hev hc hd z
  have hle := meromorphicOrderAt_riemannZeta_le_extendedMellin ha hev hc hd hdvd z
  rw [meromorphicOrderAt_burnolQuotient hmero]
  induction hx : meromorphicOrderAt riemannZeta z with
  | top =>
      rw [hx] at hle
      rw [top_le_iff.1 hle]
      simp
  | coe n =>
      rw [hx] at hle
      exact withTop_sub_nonneg_of_le hle

/-! ## Proposition 6.1 for every aperture `a ≥ 1` -/

/-- **Proposition 6.1 for every `a ≥ 1`**, the critical aperture `a = 1` included.  A vector of
`L_b` whose continued Mellin transform is divisible by `ζ` at every nontrivial zero is zero: the
evaluators are complete. -/
theorem eq_zero_of_zeta_dvd_extendedMellin_one_le {b : ℝ} (hb : 1 ≤ b) {g : SoninL2} {c d : ℂ}
    (hev : g ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary g : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (g : ℝ → ℂ) t = d)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation b c d g) ρ) :
    g = 0 := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hord := zero_le_meromorphicOrderAt_burnolQuotient_extendedMellin hb0 hev hc hd hdvd
  have hmall := meromorphicAt_extendedMellin_all hb0 hev hc hd
  obtain ⟨Mc, D, _hMc0, hgrow⟩ := exists_polyGrowth_burnolQuotientNF hb hev hc hd hord
  have hdiffθ : Differentiable ℂ (burnolQuotientNF (extendedMellinContinuation b c d g)) :=
    differentiable_burnolQuotientNF hmall hord
  obtain ⟨p, hp⟩ := exists_polynomial_of_polyGrowth hdiffθ hgrow
  -- the polynomial tends to zero along the real axis
  have hlim : Tendsto (fun σ : ℝ => p.eval ((σ : ℝ) : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm'
      (a := fun σ : ℝ => 4 * ‖extendedMellinContinuation b c d g ((σ : ℝ) : ℂ)‖) ?_ ?_
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ
      have hre : (((σ : ℝ) : ℂ)).re = σ := by simp
      have hs2 : (2 : ℝ) ≤ (((σ : ℝ) : ℂ)).re := by rw [hre]; linarith
      have hζne : riemannZeta ((σ : ℝ) : ℂ) ≠ 0 := by
        have h := norm_riemannZeta_ge_of_two_le_re (s := ((σ : ℝ) : ℂ)) hs2
        intro hzero
        rw [hzero] at h
        simp at h
        linarith
      have hs1 : ((σ : ℝ) : ℂ) ≠ 1 := by
        intro h; rw [h] at hre; simp at hre; linarith
      have hs0 : ((σ : ℝ) : ℂ) ≠ 0 := by
        intro h; rw [h] at hre; simp at hre; linarith
      have hana : AnalyticAt ℂ (burnolQuotient (extendedMellinContinuation b c d g))
          ((σ : ℝ) : ℂ) :=
        analyticAt_burnolQuotient
          (analyticAt_extendedMellinContinuation_of_ne hb0 hev hc hd hs0 hs1) hζne hs1
      have hval := burnolQuotientNF_eq_of_analyticAt hmall hana
      rw [← hp ((σ : ℝ) : ℂ), hval, burnolQuotient, norm_mul]
      have h4 : ‖(riemannZeta ((σ : ℝ) : ℂ))⁻¹‖ ≤ 4 := norm_zeta_inv_le_of_two_le_re hs2
      nlinarith [norm_nonneg (extendedMellinContinuation b c d g ((σ : ℝ) : ℂ)),
        norm_nonneg ((riemannZeta ((σ : ℝ) : ℂ))⁻¹)]
    · have h := tendsto_extendedMellinContinuation_real_atTop hb hev hc hd
      have hn : Tendsto
          (fun σ : ℝ => ‖extendedMellinContinuation b c d g ((σ : ℝ) : ℂ)‖) atTop (𝓝 0) := by
        simpa using h.norm
      simpa using hn.const_mul (4 : ℝ)
  have hp0 : p = 0 := polynomial_eq_zero_of_tendsto_zero hlim
  have hθ0 : ∀ s : ℂ, burnolQuotientNF (extendedMellinContinuation b c d g) s = 0 := by
    intro s
    rw [hp s, hp0, Polynomial.eval_zero]
  -- so the transform vanishes wherever `ζ` does not
  have hMzero : ∀ s : ℂ, riemannZeta s ≠ 0 → s ≠ 1 → s ≠ 0 →
      extendedMellinContinuation b c d g s = 0 := by
    intro s hζ h1 h0
    have hana : AnalyticAt ℂ (burnolQuotient (extendedMellinContinuation b c d g)) s :=
      analyticAt_burnolQuotient
        (analyticAt_extendedMellinContinuation_of_ne hb0 hev hc hd h0 h1) hζ h1
    have hval := burnolQuotientNF_eq_of_analyticAt hmall hana
    rw [hθ0 s, burnolQuotient] at hval
    rcases mul_eq_zero.1 hval.symm with h' | h'
    · exact h'
    · exact absurd (inv_eq_zero.1 h') hζ
  -- vanishing near a good point forces the entire numerator to vanish
  obtain ⟨Z₀, hZ₀1, hZ₀2, hZ₀ne⟩ := exists_good_point
  have hZ₀0 : Z₀ ≠ 0 := by
    intro h; rw [h] at hZ₀1; norm_num at hZ₀1
  have hZ₀one : Z₀ ≠ 1 := by
    intro h; rw [h] at hZ₀2; norm_num at hZ₀2
  have hnear : ∀ᶠ Z in 𝓝 Z₀, extendedMellinContinuation b c d g Z = 0 := by
    have hζ : ∀ᶠ Z in 𝓝 Z₀, riemannZeta Z ≠ 0 :=
      ((differentiableAt_riemannZeta hZ₀one).continuousAt).eventually_ne hZ₀ne
    have h0 : ∀ᶠ Z in 𝓝 Z₀, Z ≠ 0 :=
      ContinuousAt.eventually_ne (g := fun z : ℂ => z) continuousAt_id hZ₀0
    have h1 : ∀ᶠ Z in 𝓝 Z₀, Z ≠ 1 :=
      ContinuousAt.eventually_ne (g := fun z : ℂ => z) continuousAt_id hZ₀one
    filter_upwards [hζ, h0, h1] with Z hζZ hZ0 hZ1
    exact hMzero Z hζZ hZ1 hZ0
  have hnum : ∀ s : ℂ, extendedMellinNumerator b c d g s = 0 :=
    extendedMellinNumerator_eq_zero_of_eventually hb0 hev hc hd hnear hZ₀0 hZ₀one
  refine eq_zero_of_extendedMellinContinuation_eq_zero hb0 hev hc hd ?_
  intro s _ _
  rw [extendedMellinContinuation, hnum s, zero_div]

end

end RHTower
