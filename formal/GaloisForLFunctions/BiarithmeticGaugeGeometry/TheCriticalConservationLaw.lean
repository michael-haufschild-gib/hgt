import GaloisForLFunctions.BiarithmeticGaugeGeometry.TheBoundaryCapacityOfDeformationsOfPowersOfZeta
import GaloisForLFunctions.MultiplicativePositivityGeometry.SummableBochner

/-!
# The Critical Conservation Law

The Abel–Gram law makes the divisor jump `r(t) = ord_{x₀+it} Λ₀ − ord_{x₀+it} Λ` of a positive
deformation an even positive-definite function on the discrete group `ℝ`. When only finitely many
heights move, positive definiteness is a family of trigonometric inequalities.

* **Finite-support Bochner inequality (`cos_sum_nonneg_of_finite_support`).** If `φ : ℝ → ℝ` is even
  positive definite and vanishes off `{0} ∪ ±Z` for a finite set `Z` of positive reals, then
  `φ(0) + 2 Σ_{z ∈ Z} φ(z) cos(θ z) ≥ 0` for every `θ ∈ ℝ`. The Gram form on the Følner sets
  `{Σ n_z z : 0 ≤ n_z < N}` counts each difference `z` about `|F_N|` times, so the normalized Gram
  form tends to `φ(0) + 2 Σ φ(z)`; twisting by `cos(θ ·)` gives the other inequalities.
* **Line conservation (`jump_cos_sum_nonneg_of_rel`).** Under the Landau–Wronskian relation on
  `Re z > x₀`, if the divisors of `Λ` and `Λ₀` differ on the line `Re z = x₀` only at heights in
  `{0} ∪ ±Z`, then `r(0) + 2 Σ_{z ∈ Z} r(z) cos(θ z) ≥ 0` for all `θ`.
* **Critical conservation (`centralDrop_ge_two_mul_created_sub_destroyed`).** For a positive
  deformation of `ζ_γ` without off-critical zeros at ordinate `γ` that moves finitely many critical
  zeros, the central drop pays for every created critical zero twice:
  `ord_{½} Λ_γ − ord_{½} Λ ≥ 2 Σ_{t ∈ Z} (ord_{½+it} Λ − ord_{½+it} Λ_γ)`.
-/

open Complex Filter Topology Set MeasureTheory Finset
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity StripBochnerWeilForcing MultiplicativePositivityGeometry
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace)

/-- **Finite-support Gram inequality.** If `φ` is even, has nonnegative unit Gram sums over every
finite set, and vanishes off `{0} ∪ ±Z` (`Z` a finite set of positive reals), then
`0 ≤ φ(0) + 2 Σ_{z ∈ Z} φ(z)`. -/
theorem nonneg_of_finite_support_gram {φ : ℝ → ℝ} (heven : ∀ u, φ (-u) = φ u)
    (hgram : ∀ F : Finset ℝ, 0 ≤ ∑ x ∈ F, ∑ y ∈ F, φ (x - y)) {Z : Finset ℝ}
    (hZ : ∀ z ∈ Z, 0 < z) (hsupp : ∀ u, u ≠ 0 → u ∉ Z → -u ∉ Z → φ u = 0) :
    0 ≤ φ 0 + 2 * ∑ z ∈ Z, φ z := by
  classical
  set A : ℝ := ∑ z ∈ Z, |φ z| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun z _ => abs_nonneg _
  -- the Gram sum over a Følner set splits into the diagonal and the shifts by `±z`
  have hsplit : ∀ F : Finset ℝ, ∑ x ∈ F, ∑ y ∈ F, φ (x - y) =
      (F.card : ℝ) * φ 0 + 2 * ∑ z ∈ Z, φ z * ((F.filter fun y => y + z ∈ F).card : ℝ) := by
    intro F
    have hpt : ∀ x y : ℝ, φ (x - y) = (if x = y then φ 0 else 0) +
        (if x - y ∈ Z then φ (x - y) else 0) + (if y - x ∈ Z then φ (y - x) else 0) := by
      intro x y
      by_cases hxy : x = y
      · subst hxy
        have h0 : (0 : ℝ) ∉ Z := fun h => lt_irrefl 0 (hZ 0 h)
        simp [h0]
      · rw [if_neg hxy]
        by_cases h1 : x - y ∈ Z
        · have h2 : y - x ∉ Z := fun h => by
            have := hZ _ h
            have := hZ _ h1
            linarith
          rw [if_pos h1, if_neg h2]
          simp
        · rw [if_neg h1]
          by_cases h2 : y - x ∈ Z
          · rw [if_pos h2, show y - x = -(x - y) by ring, heven]
            simp
          · rw [if_neg h2, hsupp (x - y) (sub_ne_zero.mpr hxy) h1 (by rwa [neg_sub])]
            simp
    have hdiag : ∑ x ∈ F, ∑ y ∈ F, (if x = y then φ 0 else 0) = (F.card : ℝ) * φ 0 := by
      rw [Finset.sum_congr rfl fun x hx => by rw [Finset.sum_ite_eq, if_pos hx],
        Finset.sum_const, nsmul_eq_mul]
    have h1 := sum_sum_ite_mem F Z φ
    have h2 : ∑ x ∈ F, ∑ y ∈ F, (if y - x ∈ Z then φ (y - x) else 0) =
        ∑ z ∈ Z, φ z * ((F.filter fun y => y + z ∈ F).card : ℝ) := by
      rw [Finset.sum_comm]
      exact sum_sum_ite_mem F Z φ
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hpt x y]
    simp only [Finset.sum_add_distrib]
    rw [hdiag, h1, h2]
    ring
  by_contra hcon
  push Not at hcon
  set S : ℝ := φ 0 + 2 * ∑ z ∈ Z, φ z with hS
  set ε : ℝ := -S / (2 * (A + 1)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by positivity)
  obtain ⟨N, hN1, hN⟩ := exists_folner_step Z hε0
  set F := folnerSet Z N with hF
  have hFpos : (0 : ℝ) < F.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_folnerSet Z hN1⟩
  -- each shift count lies within `ε |F|` of `|F|`
  have hcnt : ∀ z ∈ Z, φ z * ((F.filter fun y => y + z ∈ F).card : ℝ) ≤
      φ z * F.card + |φ z| * (ε * F.card) := by
    intro z hz
    have hlo := card_shift_mem_ge (N := N) hz
    have hhi : ((F.filter fun y => y + z ∈ F).card : ℝ) ≤ F.card := by
      exact_mod_cast Finset.card_filter_le _ _
    have hdev : |((F.filter fun y => y + z ∈ F).card : ℝ) - F.card| ≤ ε * F.card := by
      rw [abs_le]; constructor <;> linarith
    have := abs_le.mp ((abs_mul (φ z) (((F.filter fun y => y + z ∈ F).card : ℝ) - F.card)).le.trans
      (mul_le_mul_of_nonneg_left hdev (abs_nonneg _)))
    nlinarith [this.2]
  have hsum : ∑ z ∈ Z, φ z * ((F.filter fun y => y + z ∈ F).card : ℝ) ≤
      F.card * ∑ z ∈ Z, φ z + ε * F.card * A := by
    calc _ ≤ ∑ z ∈ Z, (φ z * F.card + |φ z| * (ε * F.card)) := Finset.sum_le_sum hcnt
      _ = F.card * ∑ z ∈ Z, φ z + ε * F.card * A := by
        rw [Finset.sum_add_distrib, hA, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> exact Finset.sum_congr rfl fun z _ => by ring
  have hg := hgram F
  rw [hsplit F] at hg
  have hkey : 0 ≤ (F.card : ℝ) * (S + 2 * ε * A) := by nlinarith
  have hpos := (mul_nonneg_iff_of_pos_left hFpos).mp hkey
  have hεA : 2 * ε * A < -S := by
    rw [hε]
    have hA1 : 0 < A + 1 := by linarith
    rw [show 2 * (-S / (2 * (A + 1))) * A = -S * (A / (A + 1)) by field_simp]
    have : A / (A + 1) < 1 := (div_lt_one hA1).mpr (by linarith)
    nlinarith
  linarith

/-- **Finite-support Bochner inequality.** An even positive-definite `φ : ℝ → ℝ` vanishing off
`{0} ∪ ±Z` has a nonnegative cosine sum: `φ(0) + 2 Σ_{z ∈ Z} φ(z) cos(θ z) ≥ 0` for all `θ`. -/
theorem cos_sum_nonneg_of_finite_support {φ : ℝ → ℝ} (hφ : IsEvenPosDef φ) {Z : Finset ℝ}
    (hZ : ∀ z ∈ Z, 0 < z) (hsupp : ∀ u, u ≠ 0 → u ∉ Z → -u ∉ Z → φ u = 0) (θ : ℝ) :
    0 ≤ φ 0 + 2 * ∑ z ∈ Z, φ z * Real.cos (θ * z) := by
  have h := nonneg_of_finite_support_gram (φ := fun u => φ u * Real.cos (θ * u))
    (fun u => by simp only [hφ.even, mul_neg, Real.cos_neg])
    (fun F => by simpa using hφ.sum_sum_cos_nonneg (AddMonoidHom.mulLeft θ) F) hZ
    (fun u hu h1 h2 => by simp [hsupp u hu h1 h2])
  simpa using h

/-- **Line conservation law.** Under the Landau–Wronskian relation on `Re z > x₀` (Abel-negligible
perturbation, integrable kernel), if the divisors of `Λ` and `Λ₀` on the line `Re z = x₀` differ only
at heights in `{0} ∪ ±Z`, then the jump `r(t) = ord_{x₀+it} Λ₀ − ord_{x₀+it} Λ` satisfies
`r(0) + 2 Σ_{z ∈ Z} r(z) cos(θ z) ≥ 0` for every `θ`. -/
theorem jump_cos_sum_nonneg_of_rel {Λ Λ₀ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hΛ₀ : Differentiable ℂ Λ₀) (htop : ∀ z, analyticOrderAt Λ z ≠ ⊤)
    (htop₀ : ∀ z, analyticOrderAt Λ₀ z ≠ ⊤) {ν : Measure ℝ} {E : ℂ → ℂ} {x₀ : ℝ}
    (hrel : ∀ z : ℂ, x₀ < z.re → Λ z ≠ 0 → Λ₀ z ≠ 0 →
      logDeriv Λ₀ z - logDeriv Λ z = complexLaplace ν z + E z)
    (hEt : ∀ t : ℝ, Tendsto (fun σ : ℝ => ((σ - x₀ : ℝ) : ℂ) * E ((σ : ℂ) + (t : ℂ) * I))
      (𝓝[>] x₀) (𝓝 0))
    (hint : ∀ z : ℂ, x₀ < z.re →
      Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (ν.restrict (Ioi (0 : ℝ))))
    {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z)
    (hsupp : ∀ t : ℝ, t ≠ 0 → t ∉ Z → -t ∉ Z →
      analyticOrderAt Λ ((x₀ : ℂ) + (t : ℂ) * I) = analyticOrderAt Λ₀ ((x₀ : ℂ) + (t : ℂ) * I))
    (θ : ℝ) :
    0 ≤ (((analyticOrderAt Λ₀ (x₀ : ℂ)).toNat : ℝ) - (analyticOrderAt Λ (x₀ : ℂ)).toNat) +
      2 * ∑ z ∈ Z, (((analyticOrderAt Λ₀ ((x₀ : ℂ) + (z : ℂ) * I)).toNat : ℝ) -
        (analyticOrderAt Λ ((x₀ : ℂ) + (z : ℂ) * I)).toNat) * Real.cos (θ * z) := by
  have hD := jump_isEvenPosDef_of_rel hΛ hΛ₀ htop htop₀ hrel hEt hint
  have h := cos_sum_nonneg_of_finite_support hD hZ (fun u hu h1 h2 => by
    simp only [hsupp u hu h1 h2, sub_self]) θ
  simpa using h

/-- **Critical conservation law.** If `ξ` has no off-critical zero at ordinate `γ` and a perturbed
positive deformation of `ζ_γ` moves critical zeros only at heights in `{0} ∪ ±Z`, then for every
`θ`, `ord_{½} Λ_γ − ord_{½} Λ + 2 Σ_{t ∈ Z} (ord_{½+it} Λ_γ − ord_{½+it} Λ) cos(θ t) ≥ 0`; at `θ = 0`
the central drop is at least twice the net number of created critical zeros above the axis. -/
theorem centralDrop_ge_two_mul_created_sub_destroyed {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ} (hσE : σE < 1 / 2)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ)
    {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z)
    (hsupp : ∀ t : ℝ, t ≠ 0 → t ∉ Z → -t ∉ Z →
      analyticOrderAt Λ (1 / 2 + (t : ℂ) * I) =
        analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2 + (t : ℂ) * I))
    (θ : ℝ) :
    0 ≤ (((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat : ℝ) -
        (analyticOrderAt Λ (1 / 2)).toNat) +
      2 * ∑ z ∈ Z, (((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ)
          (1 / 2 + (z : ℂ) * I)).toNat : ℝ) -
        (analyticOrderAt Λ (1 / 2 + (z : ℂ) * I)).toNat) * Real.cos (θ * z) := by
  have hD := criticalJump_isEvenPosDef hoff hHC hconv hσE hE hagree
  have h := cos_sum_nonneg_of_finite_support hD hZ (fun u hu h1 h2 => by
    simp only [hsupp u hu h1 h2, sub_self]) θ
  simpa using h

end GaloisForLFunctions.BiarithmeticGaugeGeometry
