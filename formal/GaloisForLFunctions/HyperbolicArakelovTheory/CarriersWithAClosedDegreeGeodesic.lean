import GaloisForLFunctions.HyperbolicArakelovTheory.CarriersOfBoundedGeometry

/-!
# Carriers with a closed degree geodesic

`TheDilationLimitOfATwistedCarrier` treats carriers that see the end `∞` of the degree geodesic as a
point of discontinuity. The opposite situation is a group `Γ ⊂ SL₂(ℂ)` containing a loxodromic
element `D = diag(a, a⁻¹)`, `‖a‖ > 1`, whose axis is the degree geodesic: `D` dilates the geodesic by
`Q = ‖a‖²` and rotates about it (`h3Act_diag`), `∞` is a limit point, the degree geodesic closes up
to a closed geodesic of `Γ\ℍ³`, and the endpoint Eisenstein series diverges. Such carriers still
cannot carry the torsion: their geometry along the degree pairs is bounded, and
`CarriersOfBoundedGeometry` applies.

**Domination by the Poincaré series** (`greenOfCosh_imageCosh_le_poincare`,
`summable_greenOfCosh_imageCosh`). With `o = z_1` and the Poincaré weight
`P(γ) = e^{−d(o, γo)/2}` (`poincareWeight`), the triangle inequality gives
`e^{−d(z_t, γz_u)/2} ≤ e^{(|log t| + |log u|)/2} P(γ)`; under a gap `cosh d ≥ 1 + h` the Green
function is `≤ C(h) e^{−d/2}`. A pair `(z_t, z_u)` that no image hits has such a gap
(`exists_gap`), since only finitely many `γ` have `d(o, γo) ≤ R` (`finite_near`).

**A resonance-free prime** (`exists_prime_nonsingular_of_diag`). If `γz_p = z_1`, then
`g = D^{−j}γ^{−1}`, `j = ⌊log_Q p⌋`, moves `z_1` to `z_{p/Q^j}` in the segment `[z_1, z_Q)`. The pair
`(g, j)` determines `p`, only finitely many `g` occur, and `1/p ≤ Q^{−j}`; so the resonant primes have
`Σ 1/p < ∞`, while `Σ_p 1/p = ∞`.

**Bounded geometry along the closed geodesic** (`imageCosh_diag_conj`, `imageCosh_le_sq_mul`,
`not_carrierSum_eq_torsion_of_loxodromic`). Conjugation by `D^j` permutes `Γ∖{1}` and
`cosh d(z_{Q^j t}, γz_{Q^j u}) = cosh d(z_t, D^{−j}γD^j z_u)`. For `M_j = ⌈Q^j⌉` the pair
`(M_j, pM_j)` is the image of `(T_j, pT_j)` with `T_j = M_j/Q^j → 1`, and scaling by `T_j` divides
`cosh d` by at most `T_j²`; so the gap at `(1, p)` survives and the Green majorant at `(M_j, pM_j)`
is uniformly bounded. Every twisted carrier of `Γ` with weights `‖w‖ ≤ 1`, in particular every unitary
character, fails to carry the torsion kernel.
-/

open Filter Topology Set
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ ArithmeticEffectivityTheory

/-! ## Domination by the Poincaré series -/

/-- The base point `z_1` of the degree geodesic. -/
abbrev basePoint : H3 := degPoint 1 one_pos

/-- The Poincaré weight `e^{−d(z_1, γz_1)/2}` at `s = ½`. -/
def poincareWeight (g : SL2C) : ℝ := Real.exp (-(h3Dist basePoint (h3Act g basePoint)) / 2)

theorem poincareWeight_nonneg (g : SL2C) : 0 ≤ poincareWeight g := (Real.exp_pos _).le

theorem degPoint_eq {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (h : t = s) : degPoint t ht = degPoint s hs := by
  subst h; rfl

/-- Away from `cosh d = 1` the Green function is `O(X^{−1/2})`. -/
theorem greenOfCosh_le_inv_sqrt {h X : ℝ} (hh : 0 < h) (hX : 1 + h ≤ X) :
    greenOfCosh X ≤ (4 / 3 + Real.sqrt 2 * greenOfCosh (1 + h)) * (Real.sqrt X)⁻¹ := by
  have hg0 := greenOfCosh_nonneg (show (1 : ℝ) ≤ 1 + h by linarith)
  have hX0 : 0 ≤ (Real.sqrt X)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg X)
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rcases le_total X 2 with hX2 | hX2
  · have h1 : greenOfCosh X ≤ greenOfCosh (1 + h) := greenOfCosh_anti (by linarith) hX
    have h2 : (Real.sqrt 2)⁻¹ ≤ (Real.sqrt X)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt hX2)
    have h3 : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have h4 : greenOfCosh (1 + h) ≤ Real.sqrt 2 * greenOfCosh (1 + h) * (Real.sqrt X)⁻¹ := by
      calc greenOfCosh (1 + h) = Real.sqrt 2 * greenOfCosh (1 + h) * (Real.sqrt 2)⁻¹ := by
            rw [mul_comm (Real.sqrt 2), mul_assoc, h3, mul_one]
        _ ≤ Real.sqrt 2 * greenOfCosh (1 + h) * (Real.sqrt X)⁻¹ :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hs2 hg0)
    nlinarith
  · have := greenOfCosh_le hX2
    nlinarith [mul_nonneg (mul_nonneg hs2 hg0) hX0]

/-- `X^{−1/2} ≤ √2·e^{−arcosh(X)/2}`, since `e^{arcosh X} ≤ 2X`. -/
theorem inv_sqrt_le_exp_arcosh {X : ℝ} (hX : 1 ≤ X) :
    (Real.sqrt X)⁻¹ ≤ Real.sqrt 2 * Real.exp (-(Real.arcosh X) / 2) := by
  have hX0 : 0 < X := by linarith
  have hE : Real.exp (Real.arcosh X) ≤ 2 * X := by
    rw [Real.exp_arcosh hX]
    have h3 : Real.sqrt (X ^ 2 - 1) ≤ Real.sqrt (X ^ 2) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_sq hX0.le] at h3
    linarith
  have hexp : Real.exp (-(Real.arcosh X) / 2) = (Real.sqrt (Real.exp (Real.arcosh X)))⁻¹ := by
    rw [show -(Real.arcosh X) / 2 = -(Real.arcosh X / 2) by ring, Real.exp_neg, Real.exp_half]
  rw [hexp]
  have h1 : (Real.sqrt (2 * X))⁻¹ ≤ (Real.sqrt (Real.exp (Real.arcosh X)))⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr (Real.exp_pos _)) (Real.sqrt_le_sqrt hE)
  have h2 : (Real.sqrt X)⁻¹ = Real.sqrt 2 * (Real.sqrt (2 * X))⁻¹ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul]
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 2)

/-- **The triangle inequality against the base point.**
`e^{−d(z_t, γz_u)/2} ≤ e^{(|log t| + |log u|)/2}·P(γ)`. -/
theorem exp_neg_half_dist_le (g : SL2C) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    Real.exp (-(Real.arcosh (imageCosh g t u)) / 2) ≤
      Real.exp ((|Real.log t| + |Real.log u|) / 2) * poincareWeight g := by
  rw [← h3Dist_degPoint_h3Act g ht hu, poincareWeight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := h3Dist_triangle basePoint (degPoint t ht) (h3Act g basePoint)
  have h2 := h3Dist_triangle (degPoint t ht) (h3Act g (degPoint u hu)) (h3Act g basePoint)
  have h3 : h3Dist basePoint (degPoint t ht) = |Real.log t| := by
    rw [h3Dist_degPoint, Real.log_one, sub_zero]
  have h4 : h3Dist (h3Act g (degPoint u hu)) (h3Act g basePoint) = |Real.log u| := by
    rw [h3Dist_h3Act, h3Dist_degPoint, Real.log_one, zero_sub, abs_neg]
  linarith

/-- **Domination.** Under a gap `cosh d ≥ 1 + h`, `2πG_{1/2}(d(z_t, γz_u)) ≤ C·P(γ)`. -/
theorem greenOfCosh_imageCosh_le_poincare (g : SL2C) {t u h : ℝ} (ht : 0 < t) (hu : 0 < u)
    (hh : 0 < h) (hX : 1 + h ≤ imageCosh g t u) :
    greenOfCosh (imageCosh g t u) ≤
      (4 / 3 + Real.sqrt 2 * greenOfCosh (1 + h)) * Real.sqrt 2 *
        Real.exp ((|Real.log t| + |Real.log u|) / 2) * poincareWeight g := by
  have hX1 : 1 ≤ imageCosh g t u := by linarith
  have hK : 0 ≤ 4 / 3 + Real.sqrt 2 * greenOfCosh (1 + h) :=
    by have := greenOfCosh_nonneg (show (1 : ℝ) ≤ 1 + h by linarith); positivity
  calc greenOfCosh (imageCosh g t u)
      ≤ (4 / 3 + Real.sqrt 2 * greenOfCosh (1 + h)) * (Real.sqrt (imageCosh g t u))⁻¹ :=
        greenOfCosh_le_inv_sqrt hh hX
    _ ≤ (4 / 3 + Real.sqrt 2 * greenOfCosh (1 + h)) *
          (Real.sqrt 2 * Real.exp (-(Real.arcosh (imageCosh g t u)) / 2)) :=
        mul_le_mul_of_nonneg_left (inv_sqrt_le_exp_arcosh hX1) hK
    _ ≤ (4 / 3 + Real.sqrt 2 * greenOfCosh (1 + h)) *
          (Real.sqrt 2 * (Real.exp ((|Real.log t| + |Real.log u|) / 2) * poincareWeight g)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (exp_neg_half_dist_le g ht hu)
          (Real.sqrt_nonneg 2)) hK
    _ = _ := by ring

/-- Only finitely many elements move the base point by at most `R`. -/
theorem finite_near {ι : Type*} {γ : ι → SL2C} (hP : Summable fun i => poincareWeight (γ i))
    (R : ℝ) : {i | h3Dist basePoint (h3Act (γ i) basePoint) ≤ R}.Finite := by
  have hpos : 0 < Real.exp (-R / 2) := Real.exp_pos _
  have hfin : {i | ¬ poincareWeight (γ i) < Real.exp (-R / 2)}.Finite := by
    have h2 := hP.tendsto_cofinite_zero.eventually (gt_mem_nhds hpos)
    simpa [Filter.eventually_cofinite] using h2
  refine hfin.subset fun i hi => ?_
  simp only [mem_setOf_eq, not_lt, poincareWeight] at hi ⊢
  exact Real.exp_le_exp.mpr (by linarith)

theorem exists_pos_le_of_finset {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 < f a) : ∃ h, 0 < h ∧ ∀ a ∈ s, h ≤ f a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨h, hh, hle⟩ := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    refine ⟨min h (f a), lt_min hh (hf a (Finset.mem_insert_self a s)), fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hle b hb)

theorem three_halves_le_cosh_one : 5 / 4 ≤ Real.cosh 1 := by
  rw [Real.cosh_eq]
  have h1 : (2.5 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : 0 < Real.exp (-1) := Real.exp_pos _
  linarith

/-- **A nonsingular pair has a gap.** If no image of `z_u` hits `z_t`, then `cosh d ≥ 1 + h` for
every image, with one `h > 0`. -/
theorem exists_gap {ι : Type*} {γ : ι → SL2C} (hP : Summable fun i => poincareWeight (γ i))
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (hsing : ∀ i, 1 < imageCosh (γ i) t u) :
    ∃ h, 0 < h ∧ ∀ i, 1 + h ≤ imageCosh (γ i) t u := by
  set R := |Real.log t| + |Real.log u| + 1 with hR
  have hN := finite_near hP R
  obtain ⟨h₁, hh₁, hle⟩ := exists_pos_le_of_finset hN.toFinset (fun i => imageCosh (γ i) t u - 1)
    fun i _ => by linarith [hsing i]
  refine ⟨min h₁ (1 / 4), lt_min hh₁ (by norm_num), fun i => ?_⟩
  by_cases hi : i ∈ hN.toFinset
  · have := hle i hi
    linarith [min_le_left h₁ (1 / 4)]
  · simp only [Set.Finite.mem_toFinset, mem_setOf_eq, not_le] at hi
    -- far image: `d(z_t, γz_u) ≥ 1`
    have h1 := h3Dist_triangle basePoint (degPoint t ht) (h3Act (γ i) basePoint)
    have h2 := h3Dist_triangle (degPoint t ht) (h3Act (γ i) (degPoint u hu))
      (h3Act (γ i) basePoint)
    have h3 : h3Dist basePoint (degPoint t ht) = |Real.log t| := by
      rw [h3Dist_degPoint, Real.log_one, sub_zero]
    have h4 : h3Dist (h3Act (γ i) (degPoint u hu)) (h3Act (γ i) basePoint) = |Real.log u| := by
      rw [h3Dist_h3Act, h3Dist_degPoint, Real.log_one, zero_sub, abs_neg]
    have hd : 1 ≤ h3Dist (degPoint t ht) (h3Act (γ i) (degPoint u hu)) := by linarith
    have hc : Real.cosh 1 ≤ imageCosh (γ i) t u := by
      rw [← h3Cosh_degPoint_h3Act (γ i) ht hu, ← cosh_h3Dist, Real.cosh_le_cosh,
        abs_of_pos one_pos, abs_of_nonneg (h3Dist_nonneg _ _)]
      exact hd
    linarith [three_halves_le_cosh_one, min_le_right h₁ (1 / 4)]

/-- **The Green majorant converges at every nonsingular pair** of a carrier whose Poincaré
series converges at `½`. -/
theorem summable_greenOfCosh_imageCosh {ι : Type*} {γ : ι → SL2C}
    (hP : Summable fun i => poincareWeight (γ i)) {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (hsing : ∀ i, 1 < imageCosh (γ i) t u) :
    Summable fun i => greenOfCosh (imageCosh (γ i) t u) := by
  obtain ⟨h, hh, hgap⟩ := exists_gap hP ht hu hsing
  refine Summable.of_nonneg_of_le (fun i => greenOfCosh_nonneg (one_le_imageCosh _ ht hu))
    (fun i => greenOfCosh_imageCosh_le_poincare (γ i) ht hu hh (hgap i)) (hP.mul_left _)

/-! ## Loxodromic elements along the degree geodesic -/

/-- `diag(a, a⁻¹)` maps `z_t` to `z_{‖a‖²t}`: the dilation by `‖a‖²` along the degree geodesic,
composed with a rotation about it. -/
theorem h3Act_diag {a : ℂ} (ha : a ≠ 0) {t : ℝ} (ht : 0 < t) :
    h3Act (diagSL2 a ha) (degPoint t ht) =
      degPoint (‖a‖ ^ 2 * t) (mul_pos (pow_pos (norm_pos_iff.mpr ha) 2) ht) := by
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hden : h3Denom (diagSL2 a ha) (degPoint t ht) = (‖a‖ ^ 2)⁻¹ := by
    simp [h3Denom, diagSL2, degPoint, norm_inv, inv_pow]
  ext
  · simp [h3Act, diagSL2, degPoint]
  · rw [h3Act_t, hden]
    simp only [degPoint]
    field_simp

theorem h3Act_diag_pow {a : ℂ} (ha : a ≠ 0) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    h3Act (diagSL2 a ha ^ j) (degPoint t ht) =
      degPoint ((‖a‖ ^ 2) ^ j * t)
        (mul_pos (pow_pos (pow_pos (norm_pos_iff.mpr ha) 2) j) ht) := by
  induction j generalizing t with
  | zero => rw [pow_zero, h3Act_one]; exact degPoint_eq _ _ (by ring)
  | succ j ih =>
    rw [pow_succ, h3Act_mul, h3Act_diag ha ht, ih]
    exact degPoint_eq _ _ (by ring)

theorem h3Act_inv_diag_pow {a : ℂ} (ha : a ≠ 0) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    h3Act (diagSL2 a ha ^ j)⁻¹ (degPoint t ht) =
      degPoint (t / (‖a‖ ^ 2) ^ j)
        (div_pos ht (pow_pos (pow_pos (norm_pos_iff.mpr ha) 2) j)) := by
  have hQ : 0 < (‖a‖ ^ 2) ^ j := pow_pos (pow_pos (norm_pos_iff.mpr ha) 2) j
  have h := h3Act_diag_pow ha (div_pos ht hQ) j
  rw [degPoint_eq (t := (‖a‖ ^ 2) ^ j * (t / (‖a‖ ^ 2) ^ j)) (s := t) _ ht
    (by rw [mul_comm]; exact div_mul_cancel₀ t hQ.ne')] at h
  rw [← h, ← h3Act_mul, inv_mul_cancel, h3Act_one]

/-- **Invariance under the loxodromic.** With `Q = ‖a‖²` and `D = diag(a, a⁻¹)`,
`cosh d(z_{Q^j t}, γz_{Q^j u}) = cosh d(z_t, D^{−j}γD^j z_u)`. -/
theorem imageCosh_diag_conj (g : SL2C) {a : ℂ} (ha : a ≠ 0) {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (j : ℕ) :
    imageCosh g ((‖a‖ ^ 2) ^ j * t) ((‖a‖ ^ 2) ^ j * u) =
      imageCosh ((diagSL2 a ha ^ j)⁻¹ * g * diagSL2 a ha ^ j) t u := by
  have hQ : 0 < (‖a‖ ^ 2) ^ j := pow_pos (pow_pos (norm_pos_iff.mpr ha) 2) j
  rw [← h3Cosh_degPoint_h3Act g (mul_pos hQ ht) (mul_pos hQ hu),
    ← h3Cosh_degPoint_h3Act _ ht hu, ← h3Act_diag_pow ha ht, ← h3Act_diag_pow ha hu,
    h3Act_mul, h3Act_mul, ← h3Cosh_h3Act (diagSL2 a ha ^ j)⁻¹, ← h3Act_mul, inv_mul_cancel,
    h3Act_one]

/-- Scaling a pair by `t ≥ 1` along the geodesic divides `cosh d` by at most `t²`. -/
theorem imageCosh_le_sq_mul (g : SL2C) {t p : ℝ} (ht : 1 ≤ t) (hp : 0 < p) :
    imageCosh g 1 p ≤ t ^ 2 * imageCosh g t (t * p) := by
  have ht0 : 0 < t := by linarith
  have e : t ^ 2 * imageCosh g t (t * p) - imageCosh g 1 p =
      (‖g.1 0 0‖ ^ 2 * p ^ 2 * (t ^ 2 - 1) + ‖g.1 1 0‖ ^ 2 * p ^ 2 * (t ^ 4 - 1) +
        ‖g.1 1 1‖ ^ 2 * (t ^ 2 - 1)) / (2 * p) := by
    unfold imageCosh; field_simp; ring
  have h2 : 0 ≤ t ^ 2 - 1 := by nlinarith
  have h4 : 0 ≤ t ^ 4 - 1 := by nlinarith [sq_nonneg (t ^ 2)]
  have : 0 ≤ (‖g.1 0 0‖ ^ 2 * p ^ 2 * (t ^ 2 - 1) + ‖g.1 1 0‖ ^ 2 * p ^ 2 * (t ^ 4 - 1) +
      ‖g.1 1 1‖ ^ 2 * (t ^ 2 - 1)) / (2 * p) :=
    div_nonneg (add_nonneg (add_nonneg (mul_nonneg (by positivity) h2)
      (mul_nonneg (by positivity) h4)) (mul_nonneg (by positivity) h2)) (by positivity)
  linarith

/-! ## Groups whose degree geodesic is an axis -/

/-- The non-identity elements of a subgroup of `SL₂(ℂ)`. -/
abbrev Nontriv (Γ : Subgroup SL2C) := {g : SL2C // g ∈ Γ ∧ g ≠ 1}

/-- Conjugation by an element of `Γ` permutes `Γ∖{1}`. -/
def conjEquiv (Γ : Subgroup SL2C) {D : SL2C} (hD : D ∈ Γ) : Nontriv Γ ≃ Nontriv Γ where
  toFun g := ⟨D⁻¹ * g.1 * D, Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hD) g.2.1) hD, fun h => g.2.2 (by
    calc g.1 = D * (D⁻¹ * g.1 * D) * D⁻¹ := by group
      _ = 1 := by rw [h]; group)⟩
  invFun g := ⟨D * g.1 * D⁻¹, Γ.mul_mem (Γ.mul_mem hD g.2.1) (Γ.inv_mem hD), fun h => g.2.2 (by
    calc g.1 = D⁻¹ * (D * g.1 * D⁻¹) * D := by group
      _ = 1 := by rw [h]; group)⟩
  left_inv g := Subtype.ext (by simp only; group)
  right_inv g := Subtype.ext (by simp only; group)

/-- **Resonance-free primes exist.** If `Γ` contains `D = diag(a, a⁻¹)`, `‖a‖ > 1`, and its
Poincaré series converges at `½`, some prime `p` has `γz_p ≠ z_1` for every `γ ∈ Γ∖{1}`. A bad
prime gives `g = D^{−j}γ^{−1}` with `gz_1 = z_{p/Q^j}` in the segment `[z_1, z_Q)`; the pairs
`(g, j)` determine `p`, the `g` form a finite set, and `1/p ≤ Q^{−j}`, so the bad primes have
`Σ 1/p < ∞`, while `Σ_p 1/p = ∞`. -/
theorem exists_prime_nonsingular_of_diag {Γ : Subgroup SL2C} {a : ℂ} (ha : a ≠ 0)
    (ha1 : 1 < ‖a‖) (hD : diagSL2 a ha ∈ Γ)
    (hP : Summable fun i : Nontriv Γ => poincareWeight i.1) :
    ∃ p : ℕ, p.Prime ∧ ∀ i : Nontriv Γ, 1 < imageCosh i.1 1 p := by
  by_contra hcon
  push Not at hcon
  set Q := ‖a‖ ^ 2 with hQ
  have hQ1 : 1 < Q := by rw [hQ]; nlinarith
  have hQ0 : 0 < Q := by linarith
  have hlQ : 0 < Real.log Q := Real.log_pos hQ1
  set D := diagSL2 a ha with hDdef
  have hbad : ∀ p : Nat.Primes, ∃ i : Nontriv Γ, imageCosh i.1 1 ((p : ℕ) : ℝ) = 1 := fun p => by
    obtain ⟨i, hi⟩ := hcon p p.2
    exact ⟨i, le_antisymm hi (one_le_imageCosh i.1 one_pos (by exact_mod_cast p.2.pos))⟩
  choose φ hφ using hbad
  set jj : Nat.Primes → ℕ := fun p => ⌊Real.log ((p : ℕ) : ℝ) / Real.log Q⌋₊ with hjj
  have hbounds : ∀ p : Nat.Primes,
      Q ^ jj p ≤ ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) < Q * Q ^ jj p := by
    intro p
    have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have hlp : 0 ≤ Real.log ((p : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
    have h1 : (jj p : ℝ) ≤ Real.log ((p : ℕ) : ℝ) / Real.log Q := Nat.floor_le (by positivity)
    have h2 : Real.log ((p : ℕ) : ℝ) / Real.log Q < jj p + 1 := Nat.lt_floor_add_one _
    rw [le_div_iff₀ hlQ] at h1
    rw [div_lt_iff₀ hlQ] at h2
    constructor
    · rw [← Real.exp_log (pow_pos hQ0 _), ← Real.exp_log hp0, Real.log_pow]
      exact Real.exp_le_exp.mpr h1
    · rw [← pow_succ', ← Real.exp_log (pow_pos hQ0 _), ← Real.exp_log hp0, Real.log_pow]
      exact Real.exp_lt_exp.mpr (by push_cast; linarith)
  set f : Nat.Primes → SL2C := fun p => (D ^ jj p)⁻¹ * (φ p).1⁻¹ with hfdef
  have hf : ∀ p : Nat.Primes, h3Act (f p) basePoint =
      degPoint (((p : ℕ) : ℝ) / Q ^ jj p)
        (div_pos (by exact_mod_cast p.2.pos) (pow_pos hQ0 _)) := by
    intro p
    have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have h1 : h3Act (φ p).1 (degPoint _ hp0) = basePoint := by
      have := hφ p
      rw [← h3Cosh_degPoint_h3Act (φ p).1 one_pos hp0] at this
      exact ((h3Cosh_eq_one_iff _ _).mp this).symm
    have h2 : h3Act (φ p).1⁻¹ basePoint = degPoint _ hp0 := by
      rw [← h1, ← h3Act_mul, inv_mul_cancel, h3Act_one]
    rw [hfdef, h3Act_mul, h2, h3Act_inv_diag_pow ha hp0]
  set F := {g : SL2C | g ∈ Γ ∧ h3Dist basePoint (h3Act g basePoint) ≤ Real.log Q} with hF
  have hFfin : F.Finite := by
    refine (((finite_near hP (Real.log Q)).image Subtype.val).insert 1).subset ?_
    rintro g ⟨hg, hd⟩
    by_cases h1 : g = 1
    · exact Or.inl h1
    · exact Or.inr ⟨⟨g, hg, h1⟩, hd, rfl⟩
  haveI : Finite F := hFfin.to_subtype
  have hmem : ∀ p : Nat.Primes, f p ∈ F := by
    intro p
    obtain ⟨hlo, hhi⟩ := hbounds p
    have hqj := pow_pos hQ0 (jj p)
    have hlo' : (1 : ℝ) ≤ ((p : ℕ) : ℝ) / Q ^ jj p := by rw [le_div_iff₀ hqj, one_mul]; exact hlo
    have hhi' : ((p : ℕ) : ℝ) / Q ^ jj p < Q := by rw [div_lt_iff₀ hqj]; exact hhi
    refine ⟨Γ.mul_mem (Γ.inv_mem (Γ.pow_mem hD _)) (Γ.inv_mem (φ p).2.1), ?_⟩
    rw [hf p, h3Dist_degPoint, Real.log_one, sub_zero, abs_of_nonneg (Real.log_nonneg hlo')]
    exact (Real.log_lt_log (by linarith) hhi').le
  set ψ : Nat.Primes → F × ℕ := fun p => (⟨f p, hmem p⟩, jj p) with hψ
  have hinj : Function.Injective ψ := by
    intro p p' h
    simp only [hψ, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨hfp, hj⟩ := h
    have h1 := hf p
    have h2 := hf p'
    rw [hfp] at h1
    have ht := congrArg H3.t (h1.symm.trans h2)
    simp only [degPoint] at ht
    rw [hj] at ht
    have hq := pow_pos hQ0 (jj p')
    have : ((p : ℕ) : ℝ) = ((p' : ℕ) : ℝ) := by
      field_simp at ht; linarith
    exact Subtype.ext (by exact_mod_cast this)
  have hsumF : Summable fun x : F × ℕ => (1 : ℝ) * (Q⁻¹) ^ x.2 :=
    Summable.mul_of_nonneg (f := fun _ : F => (1 : ℝ)) (g := fun n : ℕ => (Q⁻¹) ^ n)
      Summable.of_finite (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hQ1))
      (fun _ => zero_le_one) (fun n => by positivity)
  have hsumP : Summable fun p : Nat.Primes => (1 / (p : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
      (hsumF.comp_injective hinj)
    simp only [Function.comp, hψ, one_mul]
    rw [inv_pow, one_div]
    exact inv_anti₀ (pow_pos hQ0 _) (hbounds p).1
  exact Nat.Primes.not_summable_one_div hsumP

/-- **No carrier of a group whose degree geodesic is the axis of a loxodromic element carries
the torsion** (B118′.2 at limit points on a closed geodesic). Let `Γ ⊂ SL₂(ℂ)` contain
`diag(a, a⁻¹)` with `‖a‖ > 1` and have convergent Poincaré series at `½`. For every weight
`‖w‖ ≤ 1` on `Γ∖{1}` and every `κ ≠ 0`,
`Σ_{γ≠1} w(γ)·2πG_{1/2}(d(z_m, γz_n)) = κ·Λ(n/m)(n/m)^{−1/2}` fails. -/
theorem not_carrierSum_eq_torsion_of_loxodromic {Γ : Subgroup SL2C} {a : ℂ} (ha : a ≠ 0)
    (ha1 : 1 < ‖a‖) (hD : diagSL2 a ha ∈ Γ)
    (hP : Summable fun i : Nontriv Γ => poincareWeight i.1) {w : Nontriv Γ → ℂ}
    (hw : ∀ i, ‖w i‖ ≤ 1) {κ : ℂ} (hκ : κ ≠ 0) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      carrierSum (fun i : Nontriv Γ => i.1) w m n = κ * (weilPrimeKernel m n : ℂ) := by
  set Q := ‖a‖ ^ 2 with hQ
  have hQ1 : 1 < Q := by rw [hQ]; nlinarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨p, hp, hns⟩ := exists_prime_nonsingular_of_diag ha ha1 hD hP
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨h, hh, hgap⟩ := exists_gap hP one_pos hp0 hns
  set h' := min h 1 with hh'
  have hh'0 : 0 < h' := lt_min hh one_pos
  -- the degrees `M_j = ⌈Q^j⌉` and their reduced positions `T_j = M_j/Q^j → 1`
  set M : ℕ → ℕ := fun j => ⌈Q ^ j⌉₊ with hMdef
  set T : ℕ → ℝ := fun j => (M j : ℝ) / Q ^ j with hTdef
  have hT1 : ∀ j, 1 ≤ T j := fun j => by
    rw [hTdef, le_div_iff₀ (pow_pos hQ0 j), one_mul]; exact Nat.le_ceil _
  have hTlt : ∀ j, T j ≤ 1 + (Q⁻¹) ^ j := fun j => by
    rw [hTdef, div_le_iff₀ (pow_pos hQ0 j), add_mul, one_mul, inv_pow,
      inv_mul_cancel₀ (pow_pos hQ0 j).ne']
    exact (Nat.ceil_lt_add_one (pow_pos hQ0 j).le).le
  have hTlim : Tendsto T atTop (𝓝 1) := by
    have hg : Tendsto (fun j : ℕ => 1 + (Q⁻¹) ^ j) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ hQ1))
    rw [add_zero] at hg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg hT1 hTlt
  have hev : ∀ᶠ j in atTop, T j ^ 2 * (1 + h' / 2) ≤ 1 + h' ∧ T j ≤ 2 := by
    have h1 : Tendsto (fun j => T j ^ 2 * (1 + h' / 2)) atTop (𝓝 (1 ^ 2 * (1 + h' / 2))) :=
      (hTlim.pow 2).mul_const _
    rw [one_pow, one_mul] at h1
    exact (h1.eventually (ge_mem_nhds (by linarith))).and
      (hTlim.eventually (ge_mem_nhds (by norm_num)))
  set K := (4 / 3 + Real.sqrt 2 * greenOfCosh (1 + h' / 2)) * Real.sqrt 2 *
    Real.exp ((Real.log 2 + Real.log (2 * p)) / 2) with hK
  set S := ∑' i : Nontriv Γ, poincareWeight i.1 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun i => poincareWeight_nonneg _
  have hK0 : 0 ≤ K := by
    have := greenOfCosh_nonneg (show (1 : ℝ) ≤ 1 + h' / 2 by linarith)
    positivity
  have hbg : ∀ j, T j ^ 2 * (1 + h' / 2) ≤ 1 + h' ∧ T j ≤ 2 →
      BoundedGeometryAt (fun i : Nontriv Γ => i.1) p (K * S + 1) (M j) := by
    rintro j ⟨hT2, hT2'⟩
    set e := conjEquiv Γ (Γ.pow_mem hD j)
    have hTpos : 0 < T j := by linarith [hT1 j]
    have hMj : (M j : ℝ) = Q ^ j * T j := by
      rw [hTdef]; field_simp
    have hterm : ∀ i : Nontriv Γ, imageCosh i.1 (M j) (p * M j) =
        imageCosh (e i).1 (T j) (T j * p) := by
      intro i
      rw [hMj, show (p : ℝ) * (Q ^ j * T j) = Q ^ j * (T j * p) by ring]
      exact imageCosh_diag_conj i.1 ha hTpos (mul_pos hTpos hp0) j
    have hgap' : ∀ i : Nontriv Γ, 1 + h' / 2 ≤ imageCosh i.1 (T j) (T j * p) := by
      intro i
      have h1 := imageCosh_le_sq_mul i.1 (hT1 j) hp0
      have h2 : 1 + h' ≤ imageCosh i.1 1 p := le_trans (by linarith [min_le_left h 1]) (hgap i)
      have hT0 : 0 < T j ^ 2 := by positivity
      nlinarith
    have hdom : ∀ i : Nontriv Γ, greenOfCosh (imageCosh i.1 (T j) (T j * p)) ≤
        K * poincareWeight i.1 := by
      intro i
      refine (greenOfCosh_imageCosh_le_poincare i.1 hTpos (mul_pos hTpos hp0)
        (by linarith) (hgap' i)).trans ?_
      have hlogT : |Real.log (T j)| ≤ Real.log 2 := by
        rw [abs_of_nonneg (Real.log_nonneg (hT1 j))]
        exact Real.log_le_log hTpos hT2'
      have hlogTp : |Real.log (T j * p)| ≤ Real.log (2 * p) := by
        rw [abs_of_nonneg (Real.log_nonneg (by nlinarith [hT1 j, (show (1:ℝ) ≤ p by
          exact_mod_cast hp.one_lt.le)]))]
        exact Real.log_le_log (mul_pos hTpos hp0) (by nlinarith)
      have hc : 0 ≤ (4 / 3 + Real.sqrt 2 * greenOfCosh (1 + h' / 2)) * Real.sqrt 2 := by
        have := greenOfCosh_nonneg (show (1 : ℝ) ≤ 1 + h' / 2 by linarith)
        positivity
      rw [hK]
      gcongr
      exact poincareWeight_nonneg _
    have hsum : Summable fun i : Nontriv Γ => greenOfCosh (imageCosh i.1 (T j) (T j * p)) :=
      Summable.of_nonneg_of_le (fun i => greenOfCosh_nonneg
        (one_le_imageCosh _ hTpos (mul_pos hTpos hp0))) hdom (hP.mul_left K)
    set f : Nontriv Γ → ℝ := fun i => greenOfCosh (imageCosh i.1 (T j) (T j * p)) with hf
    have hcomp : (fun i : Nontriv Γ => greenOfCosh (imageCosh i.1 (M j) (p * M j))) = f ∘ e := by
      funext i
      simp only [Function.comp, hf]
      rw [hterm i]
    refine ⟨fun i => by rw [hterm i]; linarith [hgap' (e i)], ?_, ?_⟩
    · rw [hcomp]; exact e.summable_iff.mpr hsum
    · rw [hcomp]
      have h2 : ∑' i, (f ∘ e) i = ∑' i, f i := e.tsum_eq f
      rw [h2]
      have h3 : ∑' i, f i ≤ ∑' i : Nontriv Γ, K * poincareWeight i.1 :=
        Summable.tsum_le_tsum hdom hsum (hP.mul_left K)
      rw [tsum_mul_left] at h3
      linarith
  have hfreq : ∃ᶠ N : ℕ in atTop, BoundedGeometryAt (fun i : Nontriv Γ => i.1) p (K * S + 1) N := by
    rw [frequently_atTop]
    intro N
    have hQj : Tendsto (fun j : ℕ => Q ^ j) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hQ1
    obtain ⟨j, hj1, hj2⟩ := (hev.and (hQj.eventually_ge_atTop (N : ℝ))).exists
    refine ⟨M j, ?_, hbg j hj1⟩
    have : (N : ℝ) ≤ M j := hj2.trans (Nat.le_ceil _)
    exact_mod_cast this
  exact not_carrierSum_eq_torsion_of_boundedGeometry hw hκ hp (by positivity) hfreq

end GaloisForLFunctions.HyperbolicArakelovTheory
