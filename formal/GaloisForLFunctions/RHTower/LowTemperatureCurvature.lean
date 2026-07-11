import GaloisForLFunctions.RHTower.FisherCurvatureMoment
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Universal two-level law for low-temperature Fisher curvature

For a countable positive Boltzmann spectrum, the first energy controls every rescaled moment and
the first two distinct energies control the rescaled Fisher determinant.  This file proves those
two assertions directly by Tannery's theorem.  It also isolates the resulting curvature exponent
`2 * E₁ - E₂`, giving the sharp divergent / finite / vanishing trichotomy.

The domination assumptions are deliberately stated at the level needed by Tannery.  They separate
the universal two-level mechanism from the arithmetic estimates used to verify it for the Euler
prime-power spectrum.
-/

noncomputable section

open Filter Topology

namespace RHTower

/-- A ground-state-rescaled Boltzmann moment summand. -/
def lowTemperatureMomentTerm {ι : Type*} (c E : ι → ℝ) (E₁ : ℝ) (m : ℕ)
    (β : ℝ) (i : ι) : ℝ :=
  c i * E i ^ m * Real.exp (-β * (E i - E₁))

/-- The first-two-level-rescaled ordered-pair dispersion summand. -/
def lowTemperaturePairTerm {ι : Type*} (c E : ι → ℝ) (E₁ E₂ : ℝ)
    (β : ℝ) (z : ι × ι) : ℝ :=
  c z.1 * c z.2 * E z.1 ^ 2 * E z.2 ^ 2 * (E z.1 - E z.2) ^ 2 *
    Real.exp (-β * ((E z.1 + E z.2) - (E₁ + E₂)))

private theorem tendsto_exp_neg_mul_atTop {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun β : ℝ => Real.exp (-β * δ)) atTop (𝓝 0) := by
  have hlin : Tendsto (fun β : ℝ => β * (-δ)) atTop atBot := by
    simpa [mul_comm] using
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.mpr hδ))
  convert Real.tendsto_exp_atBot.comp hlin using 1
  funext β
  congr 1
  ring

/-- Tannery selection of the unique ground state.  After rescaling by the ground energy, every
countable Boltzmann moment converges to the contribution of that single state. -/
theorem lowTemperatureMoment_tendsto
    {ι : Type*} [DecidableEq ι]
    (c E : ι → ℝ) (i₁ : ι) (E₁ : ℝ) (m : ℕ) (bound : ι → ℝ)
    (hbottom : ∀ i, E₁ ≤ E i)
    (hunique : ∀ i, E i = E₁ ↔ i = i₁)
    (hsum : Summable bound)
    (hbound : ∀ᶠ β : ℝ in atTop,
      ∀ i, ‖lowTemperatureMomentTerm c E E₁ m β i‖ ≤ bound i) :
    Tendsto (fun β : ℝ => ∑' i, lowTemperatureMomentTerm c E E₁ m β i)
      atTop (𝓝 (c i₁ * E₁ ^ m)) := by
  let g : ι → ℝ := fun i => if i = i₁ then c i₁ * E₁ ^ m else 0
  have hpoint : ∀ i, Tendsto (fun β : ℝ => lowTemperatureMomentTerm c E E₁ m β i)
      atTop (𝓝 (g i)) := by
    intro i
    by_cases hi : i = i₁
    · subst i
      have hEi : E i₁ = E₁ := (hunique i₁).2 rfl
      simp [lowTemperatureMomentTerm, g, hEi]
    · have hgap : 0 < E i - E₁ := by
        have hne : E i ≠ E₁ := fun h => hi ((hunique i).1 h)
        exact sub_pos.mpr (lt_of_le_of_ne (hbottom i) (Ne.symm hne))
      have hexp := tendsto_exp_neg_mul_atTop hgap
      have hmul := hexp.const_mul (c i * E i ^ m)
      simpa [lowTemperatureMomentTerm, g, hi] using hmul
  have h := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  simpa [g] using h

/-- The universal leading coefficient of the first-two-level Fisher determinant. -/
def lowTemperatureDetLeading (c₁ c₂ E₁ E₂ : ℝ) : ℝ :=
  c₁ * c₂ * E₁ ^ 2 * E₂ ^ 2 * (E₂ - E₁) ^ 2

/-- Tannery selection of the two ordered ground/first-excited pairs.  The factor `1 / 2` is the
factor in the exact pairwise-dispersion identity for `M₂ M₄ - M₃²`. -/
theorem lowTemperaturePairDispersion_tendsto
    {ι : Type*} [DecidableEq ι]
    (c E : ι → ℝ) (i₁ i₂ : ι) (E₁ E₂ : ℝ) (bound : ι × ι → ℝ)
    (h12 : E₁ < E₂)
    (hfirst : ∀ i, E i = E₁ ↔ i = i₁)
    (hsecondLower : ∀ i, i ≠ i₁ → E₂ ≤ E i)
    (hsecond : ∀ i, E i = E₂ ↔ i = i₂)
    (hsum : Summable bound)
    (hbound : ∀ᶠ β : ℝ in atTop,
      ∀ z, ‖lowTemperaturePairTerm c E E₁ E₂ β z‖ ≤ bound z) :
    Tendsto (fun β : ℝ => (2 : ℝ)⁻¹ *
        ∑' z, lowTemperaturePairTerm c E E₁ E₂ β z)
      atTop (𝓝 (lowTemperatureDetLeading (c i₁) (c i₂) E₁ E₂)) := by
  have hi12 : i₁ ≠ i₂ := by
    intro h
    subst i₂
    have hE1 : E i₁ = E₁ := (hfirst i₁).2 rfl
    have hE2 : E i₁ = E₂ := (hsecond i₁).2 rfl
    linarith
  let K : ℝ := lowTemperatureDetLeading (c i₁) (c i₂) E₁ E₂
  let g : ι × ι → ℝ := fun z =>
    if z = (i₁, i₂) then K else if z = (i₂, i₁) then K else 0
  have hpoint : ∀ z, Tendsto (fun β : ℝ => lowTemperaturePairTerm c E E₁ E₂ β z)
      atTop (𝓝 (g z)) := by
    rintro ⟨i, j⟩
    by_cases hij : (i, j) = (i₁, i₂)
    · have hi : i = i₁ := congrArg Prod.fst hij
      have hj : j = i₂ := congrArg Prod.snd hij
      subst i
      subst j
      have hE1 : E i₁ = E₁ := (hfirst i₁).2 rfl
      have hE2 : E i₂ = E₂ := (hsecond i₂).2 rfl
      have heqfun :
          (fun β : ℝ => lowTemperaturePairTerm c E E₁ E₂ β (i₁, i₂)) =
            fun _ => K := by
        funext β
        simp only [lowTemperaturePairTerm, Prod.fst, Prod.snd, hE1, hE2, sub_self,
          neg_zero, zero_mul, Real.exp_zero, mul_one]
        dsimp [K, lowTemperatureDetLeading]
        simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
        ring
      rw [heqfun]
      simp [g]
    · by_cases hji : (i, j) = (i₂, i₁)
      · have hi : i = i₂ := congrArg Prod.fst hji
        have hj : j = i₁ := congrArg Prod.snd hji
        subst i
        subst j
        have hE1 : E i₁ = E₁ := (hfirst i₁).2 rfl
        have hE2 : E i₂ = E₂ := (hsecond i₂).2 rfl
        have heqfun :
            (fun β : ℝ => lowTemperaturePairTerm c E E₁ E₂ β (i₂, i₁)) =
              fun _ => K := by
          funext β
          simp only [lowTemperaturePairTerm, Prod.fst, Prod.snd, hE1, hE2, sub_self,
            neg_zero, zero_mul, Real.exp_zero, mul_one]
          dsimp [K, lowTemperatureDetLeading]
          rw [show -β * ((E₂ + E₁) - (E₁ + E₂)) = 0 by ring, Real.exp_zero]
          ring
        rw [heqfun]
        simp [g, hi12, hi12.symm]
      · by_cases heq : i = j
        · subst j
          simp [lowTemperaturePairTerm, g, hij, hji]
        · have hgap : 0 < (E i + E j) - (E₁ + E₂) := by
            by_cases hi : i = i₁
            · subst i
              have hj1 : j ≠ i₁ := fun hj => heq hj.symm
              have hj2 : j ≠ i₂ := by
                intro hj
                apply hij
                simp [hj]
              have hE1 : E i₁ = E₁ := (hfirst i₁).2 rfl
              have hEj : E₂ < E j :=
                lt_of_le_of_ne (hsecondLower j hj1)
                  (fun h => hj2 ((hsecond j).1 h.symm))
              linarith
            · by_cases hj : j = i₁
              · subst j
                have hi2 : i ≠ i₂ := by
                  intro hi2
                  apply hji
                  simp [hi2]
                have hE1 : E i₁ = E₁ := (hfirst i₁).2 rfl
                have hEi : E₂ < E i :=
                  lt_of_le_of_ne (hsecondLower i hi)
                    (fun h => hi2 ((hsecond i).1 h.symm))
                linarith
              · have hEi : E₂ ≤ E i := hsecondLower i hi
                have hEj : E₂ ≤ E j := hsecondLower j hj
                linarith
          have hexp := tendsto_exp_neg_mul_atTop hgap
          have hmul := hexp.const_mul
            (c i * c j * E i ^ 2 * E j ^ 2 * (E i - E j) ^ 2)
          simpa [lowTemperaturePairTerm, g, hij, hji] using hmul
  have htsum := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  have hsumg : (∑' z, g z) = 2 * K := by
    have hpairs : (i₁, i₂) ≠ (i₂, i₁) := by
      intro h
      exact hi12 (congrArg Prod.fst h)
    have hg : g = fun z =>
        (if z = (i₁, i₂) then K else 0) + (if z = (i₂, i₁) then K else 0) := by
      funext z
      by_cases h1 : z = (i₁, i₂)
      · subst z
        simp [g, hpairs]
      · by_cases h2 : z = (i₂, i₁)
        · subst z
          simp [g, hpairs, h1]
        · simp [g, h1, h2]
    rw [hg]
    have hleft : HasSum (fun z : ι × ι => if z = (i₁, i₂) then K else 0) K :=
      hasSum_ite_eq (i₁, i₂) K
    have hright : HasSum (fun z : ι × ι => if z = (i₂, i₁) then K else 0) K :=
      hasSum_ite_eq (i₂, i₁) K
    simpa [two_mul] using (hleft.add hright).tsum_eq
  have hc : Tendsto (fun _ : ℝ => (2 : ℝ)⁻¹) atTop (𝓝 (2 : ℝ)⁻¹) :=
    tendsto_const_nhds
  have hscaled := hc.mul htsum
  rw [hsumg] at hscaled
  convert hscaled using 1 <;> norm_num [K] <;> ring

/-- The curvature coefficient is the quotient of the determinant coefficient by the cube of the
ground-state second-moment coefficient. -/
theorem lowTemperatureCurvatureCoefficient_tendsto
    (M D : ℝ → ℝ) (A B : ℝ)
    (hM : Tendsto M atTop (𝓝 A)) (hD : Tendsto D atTop (𝓝 B)) (hA : A ≠ 0) :
    Tendsto (fun β => -(D β) / (M β) ^ 3) atTop (𝓝 (-B / A ^ 3)) := by
  exact hD.neg.div (hM.pow 3) (pow_ne_zero 3 hA)

/-- Normal form of the low-temperature scalar-curvature profile. -/
def lowTemperatureCurvatureProfile (K δ β : ℝ) : ℝ :=
  -K * Real.exp (β * δ)

/-- If `E₂ < 2 E₁`, the negative scalar curvature diverges to `-∞`. -/
theorem lowTemperatureCurvatureProfile_tendsto_atBot
    {K E₁ E₂ : ℝ} (hK : 0 < K) (hgap : E₂ < 2 * E₁) :
    Tendsto (lowTemperatureCurvatureProfile K (2 * E₁ - E₂)) atTop atBot := by
  have hexp : Tendsto (fun β : ℝ => Real.exp (β * (2 * E₁ - E₂))) atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (by simpa [mul_comm] using
        (tendsto_id.const_mul_atTop (sub_pos.mpr hgap)))
  have hmul : Tendsto
      (fun β : ℝ => (-K) * Real.exp (β * (2 * E₁ - E₂))) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (f := fun β : ℝ =>
      Real.exp (β * (2 * E₁ - E₂))) (r := -K) (neg_lt_zero.mpr hK)).2 hexp
  exact hmul

/-- If `E₂ = 2 E₁`, the scalar curvature tends to the finite negative constant `-K`. -/
theorem lowTemperatureCurvatureProfile_critical
    (K E₁ E₂ : ℝ) (hgap : E₂ = 2 * E₁) :
    lowTemperatureCurvatureProfile K (2 * E₁ - E₂) = fun _ => -K := by
  funext β
  simp [lowTemperatureCurvatureProfile, hgap]

/-- If `2 E₁ < E₂`, the scalar curvature vanishes from below. -/
theorem lowTemperatureCurvatureProfile_tendsto_zero
    (K E₁ E₂ : ℝ) (hgap : 2 * E₁ < E₂) :
    Tendsto (lowTemperatureCurvatureProfile K (2 * E₁ - E₂)) atTop (𝓝 0) := by
  have hδ : 0 < E₂ - 2 * E₁ := sub_pos.mpr hgap
  have hexp := tendsto_exp_neg_mul_atTop hδ
  have hmul := hexp.const_mul (-K)
  have hmul' : Tendsto (fun x : ℝ => -K * Real.exp (-x * (E₂ - 2 * E₁)))
      atTop (𝓝 0) := by simpa using hmul
  convert hmul' using 1
  funext β
  dsimp [lowTemperatureCurvatureProfile]
  congr 1
  ring

end RHTower
