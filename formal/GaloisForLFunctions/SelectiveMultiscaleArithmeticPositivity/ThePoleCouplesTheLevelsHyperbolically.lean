import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleHyperplaneIsTheHarmonicHyperplane

/-!
# The pole couples the levels hyperbolically

Weil's form is `W = M + 2AB`, with `M` the Markov form and `A(f) = ∫ f e^{−u/2}`,
`B(f) = ∫ f e^{u/2}` the pole moments. Translation by `s` multiplies them by `e^{∓s/2}`. So the
pole part of the coupling between two copies of one generator, as between two dyadic levels, is
exact:

* **The cosh law** (`polePairing_shift`): the pole pairing of `f(· − s)` and `f(· − t)` is
  `2A(f)B(f) cosh((t − s)/2)`. Between dyadic levels `j, k` it grows like `2^{|k − j|/2}`
  (`exp_abs_mul_le_abs_polePairing_shift`). It vanishes for all pairs of levels iff `A(f)B(f) = 0`
  (`polePairing_shift_eq_zero_iff`). Pole couplings are therefore never summable level costs
  unless they vanish.
* **Orbit moments** (`poleMomentA_levelOrbit`, `poleMomentB_levelOrbit`): for
  `F = Σ_j c_j f(· − s_j)`, `A(F) = A(f) Σ_j c_j e^{−s_j/2}` and `B(F) = B(f) Σ_j c_j e^{s_j/2}`.
  The pole term of `W(F)` is the rank-two form
  `2A(f)B(f) (Σ_j c_j e^{−s_j/2})(Σ_j c_j e^{s_j/2})` (`weilQuad_levelOrbit_eq`).
* **Hyperbolic signature** (`exists_poleMomentA_levelOrbit_eq_zero`,
  `poleQuad_twoLevels_neg`): any two orbit coefficient vectors have a nontrivial combination
  with `A(F) = 0`, so the pole term is negative on at most one direction of coefficients. Two
  distinct shifts of a generator with `A(f)B(f) ≠ 0` span a plane where the pole term takes both
  signs: it is a hyperbolic plane.
* **The dyadic harmonic hyperplane** (`poleMomentA_levelOrbit_eq_zero_iff`): if `A(f) ≠ 0`, the
  orbit lies on the pole hyperplane iff `Σ_j c_j e^{−s_j/2} = 0`. At the dyadic shifts
  `s_j = j log 2` this is `Σ_j c_j 2^{−j/2} = 0`, the harmonic hyperplane of the atoms at `2^j`.

So the one negative pole direction across levels is removed by one linear condition, and on the
pole hyperplane the pole couplings between levels vanish identically.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

/-- The left pole moment `A(f) = ∫ f e^{−u/2}`. -/
def poleMomentA (f : ℝ → ℝ) : ℝ := ∫ u, f u * Real.exp (-(u / 2))

/-- The right pole moment `B(f) = ∫ f e^{u/2}`. -/
def poleMomentB (f : ℝ → ℝ) : ℝ := ∫ u, f u * Real.exp (u / 2)

/-- The polarized pole term: `W(f, g) = M(f, g) + A(f)B(g) + A(g)B(f)`. -/
def polePairing (f g : ℝ → ℝ) : ℝ := poleMomentA f * poleMomentB g + poleMomentA g * poleMomentB f

theorem poleMomentA_shift (f : ℝ → ℝ) (t : ℝ) :
    poleMomentA (fun u => f (u - t)) = Real.exp (-(t / 2)) * poleMomentA f := by
  have h := integral_shift_mul_exp f t (-2⁻¹)
  have e : ∀ u : ℝ, -2⁻¹ * u = -(u / 2) := fun u => by ring
  simp only [e] at h
  exact h

theorem poleMomentB_shift (f : ℝ → ℝ) (t : ℝ) :
    poleMomentB (fun u => f (u - t)) = Real.exp (t / 2) * poleMomentB f := by
  have h := integral_shift_mul_exp f t 2⁻¹
  have e : ∀ u : ℝ, 2⁻¹ * u = u / 2 := fun u => by ring
  simp only [e] at h
  exact h

/-- **The cosh law**: the pole pairing of two copies of a generator is
`2A(f)B(f) cosh((t − s)/2)`. -/
theorem polePairing_shift (f : ℝ → ℝ) (s t : ℝ) :
    polePairing (fun u => f (u - s)) (fun u => f (u - t)) =
      2 * poleMomentA f * poleMomentB f * Real.cosh ((t - s) / 2) := by
  rw [polePairing, poleMomentA_shift, poleMomentB_shift, poleMomentA_shift, poleMomentB_shift,
    Real.cosh_eq]
  have h1 : Real.exp (-(s / 2)) * Real.exp (t / 2) = Real.exp ((t - s) / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-(t / 2)) * Real.exp (s / 2) = Real.exp (-((t - s) / 2)) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination (poleMomentA f * poleMomentB f) * h1 + (poleMomentA f * poleMomentB f) * h2

theorem exp_abs_le_two_mul_cosh (y : ℝ) : Real.exp |y| ≤ 2 * Real.cosh y := by
  rw [Real.cosh_eq]
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-y)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_pos y]

/-- **Pole couplings grow geometrically with the level distance**:
`|A(f)B(f)| e^{|t − s|/2} ≤ |pole pairing|`; at dyadic levels this is `2^{|k − j|/2}`. -/
theorem exp_abs_mul_le_abs_polePairing_shift (f : ℝ → ℝ) (s t : ℝ) :
    |poleMomentA f * poleMomentB f| * Real.exp (|t - s| / 2) ≤
      |polePairing (fun u => f (u - s)) (fun u => f (u - t))| := by
  rw [polePairing_shift, show 2 * poleMomentA f * poleMomentB f * Real.cosh ((t - s) / 2) =
      (poleMomentA f * poleMomentB f) * (2 * Real.cosh ((t - s) / 2)) by ring,
    abs_mul (poleMomentA f * poleMomentB f), abs_of_pos (by positivity : 0 < 2 * Real.cosh ((t - s) / 2))]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := exp_abs_le_two_mul_cosh ((t - s) / 2)
  rwa [abs_div, abs_two] at h

/-- The pole couplings between all pairs of copies vanish iff `A(f)B(f) = 0`. -/
theorem polePairing_shift_eq_zero_iff (f : ℝ → ℝ) :
    (∀ s t : ℝ, polePairing (fun u => f (u - s)) (fun u => f (u - t)) = 0) ↔
      poleMomentA f * poleMomentB f = 0 := by
  constructor
  · intro h
    have h0 := h 0 0
    rw [polePairing_shift, sub_self, zero_div, Real.cosh_zero] at h0
    linarith
  · intro h s t
    rw [polePairing_shift, mul_assoc 2, h]
    ring

/-- A **level orbit** `F = Σ_j c_j f(· − s_j)`: copies of one generator at the shifts `s_j`. -/
def levelOrbit {ι : Type*} (S : Finset ι) (c s : ι → ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u => ∑ j ∈ S, c j * f (u - s j)

theorem integrable_const_mul_shift_mul {f e : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (he : Continuous e) (c t : ℝ) :
    Integrable (fun u => c * f (u - t) * e u) := by
  have hK : HasCompactSupport (fun u => f (u - t)) := hfc.comp_homeomorph (Homeomorph.subRight t)
  have hK' : HasCompactSupport (fun u => c * f (u - t) * e u) :=
    (hK.mul_left (f := fun _ => c)).mul_right
  exact ((continuous_const.mul (hf.comp (continuous_sub_right t))).mul
    he).integrable_of_hasCompactSupport hK'

/-- Integrating a level orbit against a continuous weight sums the shifted integrals. -/
theorem integral_levelOrbit_mul {ι : Type*} (S : Finset ι) (c s : ι → ℝ) {f e : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (he : Continuous e) :
    ∫ u, levelOrbit S c s f u * e u = ∑ j ∈ S, c j * ∫ u, f (u - s j) * e u := by
  unfold levelOrbit
  simp_rw [sum_mul]
  rw [integral_finsetSum _ fun j _ => integrable_const_mul_shift_mul hf hfc he (c j) (s j)]
  refine sum_congr rfl fun j _ => ?_
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

/-- `A(F) = A(f) Σ_j c_j e^{−s_j/2}`. -/
theorem poleMomentA_levelOrbit {ι : Type*} (S : Finset ι) (c s : ι → ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    poleMomentA (levelOrbit S c s f) = poleMomentA f * ∑ j ∈ S, c j * Real.exp (-(s j / 2)) := by
  rw [poleMomentA, integral_levelOrbit_mul S c s hf hfc (by fun_prop), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have h := poleMomentA_shift f (s j)
  rw [poleMomentA, poleMomentA] at h
  rw [h, poleMomentA]
  ring

/-- `B(F) = B(f) Σ_j c_j e^{s_j/2}`. -/
theorem poleMomentB_levelOrbit {ι : Type*} (S : Finset ι) (c s : ι → ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    poleMomentB (levelOrbit S c s f) = poleMomentB f * ∑ j ∈ S, c j * Real.exp (s j / 2) := by
  rw [poleMomentB, integral_levelOrbit_mul S c s hf hfc (by fun_prop), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have h := poleMomentB_shift f (s j)
  rw [poleMomentB, poleMomentB] at h
  rw [h, poleMomentB]
  ring

theorem contDiff_levelOrbit {ι : Type*} (S : Finset ι) (c s : ι → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (levelOrbit S c s f) := by
  unfold levelOrbit
  exact ContDiff.sum fun j _ => contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_levelOrbit {ι : Type*} (S : Finset ι) (c s : ι → ℝ) {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) : HasCompactSupport (levelOrbit S c s f) := by
  classical
  unfold levelOrbit
  induction S using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact HasCompactSupport.zero
  | insert j S hj ih =>
    simp_rw [sum_insert hj]
    have hK : HasCompactSupport (fun u => c j * f (u - s j)) :=
      (hfc.comp_homeomorph (Homeomorph.subRight (s j))).mul_left (f := fun _ => c j)
    exact hK.add ih

/-- **Weil's form on a level orbit**: the pole term is the rank-two form
`2A(f)B(f) (Σ_j c_j e^{−s_j/2})(Σ_j c_j e^{s_j/2})`. -/
theorem weilQuad_levelOrbit_eq {ι : Type*} (S : Finset ι) (c s : ι → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    weilQuad (levelOrbit S c s f) =
      RHTower.markovEnergy (fun u => (levelOrbit S c s f u : ℂ)) +
        2 * poleMomentA f * poleMomentB f *
          ((∑ j ∈ S, c j * Real.exp (-(s j / 2))) * ∑ j ∈ S, c j * Real.exp (s j / 2)) := by
  rw [weilQuad_eq_markov_add_pole (contDiff_levelOrbit S c s hf)
    (hasCompactSupport_levelOrbit S c s hfc)]
  have hA := poleMomentA_levelOrbit S c s hf.continuous hfc
  have hB := poleMomentB_levelOrbit S c s hf.continuous hfc
  rw [poleMomentA] at hA
  rw [poleMomentB] at hB
  rw [hA, hB]
  ring

/-- **At most one negative pole direction**: any two orbit coefficient vectors have a nontrivial
combination on the pole hyperplane, where the pole term vanishes. -/
theorem exists_poleMomentA_levelOrbit_eq_zero {ι : Type*} (S : Finset ι) (s : ι → ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (c d : ι → ℝ) :
    ∃ σ τ : ℝ, (σ ≠ 0 ∨ τ ≠ 0) ∧ poleMomentA (levelOrbit S (σ • c + τ • d) s f) = 0 := by
  set L : (ι → ℝ) → ℝ := fun c => ∑ j ∈ S, c j * Real.exp (-(s j / 2))
  have hL : ∀ σ τ : ℝ, L (σ • c + τ • d) = σ * L c + τ * L d := fun σ τ => by
    simp only [L, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, mul_sum]
    exact congrArg₂ _ (sum_congr rfl fun _ _ => by ring) (sum_congr rfl fun _ _ => by ring)
  by_cases h : L c = 0 ∧ L d = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    rw [poleMomentA_levelOrbit S _ s hf hfc]
    change poleMomentA f * L _ = 0
    rw [hL, h.1, h.2]
    ring
  · refine ⟨L d, -L c, ?_, ?_⟩
    · rw [not_and_or] at h
      rcases h with h | h
      · exact Or.inr (neg_ne_zero.mpr h)
      · exact Or.inl h
    · rw [poleMomentA_levelOrbit S _ s hf hfc]
      change poleMomentA f * L _ = 0
      rw [hL]
      ring

/-- **The two-level pole plane is hyperbolic**: for distinct shifts `s ≠ t` the pole term of the
coefficients `(1, −1)` is negative, `(e^{−s/2} − e^{−t/2})(e^{s/2} − e^{t/2}) < 0`, while that of
`(1, 0)` is `1`. So with `A(f)B(f) ≠ 0` the pole term takes both signs on the plane of two copies. -/
theorem poleQuad_twoLevels_neg {s t : ℝ} (hst : s ≠ t) :
    (Real.exp (-(s / 2)) - Real.exp (-(t / 2))) * (Real.exp (s / 2) - Real.exp (t / 2)) < 0 := by
  rcases lt_or_gt_of_ne hst with h | h
  · have h1 : Real.exp (-(t / 2)) < Real.exp (-(s / 2)) := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp (s / 2) < Real.exp (t / 2) := Real.exp_lt_exp.mpr (by linarith)
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  · have h1 : Real.exp (-(s / 2)) < Real.exp (-(t / 2)) := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp (t / 2) < Real.exp (s / 2) := Real.exp_lt_exp.mpr (by linarith)
    exact mul_neg_of_neg_of_pos (by linarith) (by linarith)

/-- The pole terms of the two-level orbits `f(· − s)` and `f(· − s) − f(· − t)` have opposite
signs whenever `A(f)B(f) ≠ 0` and `s ≠ t`. -/
theorem poleTerm_twoLevels_opposite {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hAB : poleMomentA f * poleMomentB f ≠ 0) {s t : ℝ} (hst : s ≠ t) :
    (poleMomentA (levelOrbit univ ![1, 0] ![s, t] f) *
        poleMomentB (levelOrbit univ ![1, 0] ![s, t] f)) *
      (poleMomentA (levelOrbit univ ![1, -1] ![s, t] f) *
        poleMomentB (levelOrbit univ ![1, -1] ![s, t] f)) < 0 := by
  simp only [poleMomentA_levelOrbit _ _ _ hf hfc, poleMomentB_levelOrbit _ _ _ hf hfc,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hneg := poleQuad_twoLevels_neg hst
  have hpos : 0 < (poleMomentA f * poleMomentB f) ^ 2 := by positivity
  have hexp : Real.exp (-(s / 2)) * Real.exp (s / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have key : poleMomentA f * (1 * Real.exp (-(s / 2)) + 0 * Real.exp (-(t / 2))) *
        (poleMomentB f * (1 * Real.exp (s / 2) + 0 * Real.exp (t / 2))) *
      (poleMomentA f * (1 * Real.exp (-(s / 2)) + -1 * Real.exp (-(t / 2))) *
        (poleMomentB f * (1 * Real.exp (s / 2) + -1 * Real.exp (t / 2)))) =
      (poleMomentA f * poleMomentB f) ^ 2 *
        ((Real.exp (-(s / 2)) - Real.exp (-(t / 2))) * (Real.exp (s / 2) - Real.exp (t / 2))) := by
    linear_combination (poleMomentA f * poleMomentB f) ^ 2 *
      ((Real.exp (-(s / 2)) - Real.exp (-(t / 2))) * (Real.exp (s / 2) - Real.exp (t / 2))) * hexp
  rw [key]
  exact mul_neg_of_pos_of_neg hpos hneg

/-- **The dyadic harmonic hyperplane**: if `A(f) ≠ 0`, a level orbit lies on the pole hyperplane
iff `Σ_j c_j e^{−s_j/2} = 0`. -/
theorem poleMomentA_levelOrbit_eq_zero_iff {ι : Type*} (S : Finset ι) (c s : ι → ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hA : poleMomentA f ≠ 0) :
    poleMomentA (levelOrbit S c s f) = 0 ↔ ∑ j ∈ S, c j * Real.exp (-(s j / 2)) = 0 := by
  rw [poleMomentA_levelOrbit S c s hf hfc, mul_eq_zero, or_iff_right hA]

/-- At the dyadic shifts `s_j = j log 2` the weights are `e^{−s_j/2} = 1/√(2^j)`, the harmonic
weights of the atoms at `2^j`. -/
theorem exp_neg_half_dyadic (j : ℕ) :
    Real.exp (-((j * Real.log 2) / 2)) = 1 / Real.sqrt (2 ^ j) := by
  have h := exp_neg_half_log_eq (n := 2 ^ j) (Nat.one_le_two_pow)
  rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at h

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
