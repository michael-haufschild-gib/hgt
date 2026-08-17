import GaloisForLFunctions.HTGeometry.StaticOrbitBandwidth

/-!
# Extracting an exact spectral phase from an approximate shortcut

A unitary within `ε` of a static orbit has diagonal entries within `ε` of the orbit phases, so the
entries are nonzero and their normalizations are honest circle points within `2ε` of the orbit
phases.  A chord of length `c` between circle points subtends an arc of at most `2 arcsin(c/2)`, so
the extracted phases are within `2 arcsin ε` of the orbit phases in circular distance.

The circular triangle inequality then transfers the orbit winding across every pair of levels to the
extracted phases, up to `4 arcsin ε`, and dividing by the level separation bounds the bandwidth of
the extracted centralizer element from below -- with no division by a minimum gap anywhere.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

/-! ## More circular-distance geometry -/

/-- The circular distance never exceeds `π`. -/
theorem circDist_le_pi (a b : ℝ) : circDist a b ≤ Real.pi := by
  have hpi := two_pi_pos
  have hne : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
  set x : ℝ := a - b with hx
  have e1 : x - 2 * Real.pi * (round (x / (2 * Real.pi)) : ℝ)
      = 2 * Real.pi * (x / (2 * Real.pi) - (round (x / (2 * Real.pi)) : ℝ)) := by
    field_simp
  have hhalf : |x / (2 * Real.pi) - (round (x / (2 * Real.pi)) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  rw [circDist, phaseGap, ← hx, e1, abs_mul (2 * Real.pi), abs_of_pos hpi]
  nlinarith [hhalf, Real.pi_pos]

/-- **The circular triangle inequality.** -/
theorem circDist_triangle (a b c : ℝ) : circDist a c ≤ circDist a b + circDist b c := by
  have h := circDist_add_le a b b c
  have heq : circDist (a + b) (b + c) = circDist a c := by
    rw [add_comm b c, circDist_add_const]
  rwa [heq] at h

/-- The circular distance is a difference read at the origin. -/
theorem circDist_sub_zero (a b : ℝ) : circDist (a - b) 0 = circDist a b := by
  have h := circDist_add_const (a - b) 0 b
  simpa using h.symm

/-! ## Chord and arc -/

/-- The squared chord between two unit phases. -/
theorem normSq_expI_sub (φ ψ : ℝ) :
    ‖Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((ψ : ℂ) * Complex.I)‖ ^ 2
      = 2 - 2 * Real.cos (φ - ψ) := by
  have hφ : Complex.exp ((φ : ℂ) * Complex.I)
      = ((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hψ : Complex.exp ((ψ : ℂ) * Complex.I)
      = ((Real.cos ψ : ℝ) : ℂ) + ((Real.sin ψ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [← Complex.normSq_eq_norm_sq, hφ, hψ]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq φ, Real.sin_sq_add_cos_sq ψ]

/-- The chord depends only on the circular distance. -/
theorem cos_sub_eq_cos_circDist (φ ψ : ℝ) : Real.cos (φ - ψ) = Real.cos (circDist φ ψ) := by
  obtain ⟨k, hk⟩ := exists_int_phaseGap φ ψ
  have hshift : φ - ψ = phaseGap φ ψ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hk]
    push_cast
    ring
  rw [hshift, Real.cos_add_int_mul_two_pi, circDist, Real.cos_abs]

/-- **Chord to arc.**  A chord of length at most `c` subtends an arc of at most `2 arcsin(c/2)`. -/
theorem circDist_le_two_arcsin {φ ψ c : ℝ} (hc0 : 0 ≤ c)
    (h : ‖Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((ψ : ℂ) * Complex.I)‖ ≤ c) :
    circDist φ ψ ≤ 2 * Real.arcsin (c / 2) := by
  set d : ℝ := circDist φ ψ with hd
  have hd0 : 0 ≤ d := circDist_nonneg φ ψ
  have hdpi : d ≤ Real.pi := circDist_le_pi φ ψ
  have hchord : 2 - 2 * Real.cos d
      ≤ c ^ 2 := by
    have hsq := normSq_expI_sub φ ψ
    rw [cos_sub_eq_cos_circDist] at hsq
    have hnn : (0 : ℝ) ≤ ‖Complex.exp ((φ : ℂ) * Complex.I)
        - Complex.exp ((ψ : ℂ) * Complex.I)‖ := norm_nonneg _
    nlinarith [hsq, h, hnn, hc0]
  have hdouble : ∀ x : ℝ, Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    intro x
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hhalf : Real.cos d = 1 - 2 * Real.sin (d / 2) ^ 2 := by
    have hx := hdouble (d / 2)
    rwa [show 2 * (d / 2) = d from by ring] at hx
  have hsin0 : 0 ≤ Real.sin (d / 2) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) ?_
    linarith [Real.pi_pos]
  have hsq : 4 * Real.sin (d / 2) ^ 2 ≤ c ^ 2 := by nlinarith [hchord, hhalf]
  have hsinle : Real.sin (d / 2) ≤ c / 2 := by
    nlinarith [hsq, hsin0, hc0, sq_nonneg (Real.sin (d / 2) + c / 2)]
  have hrange1 : -(Real.pi / 2) ≤ d / 2 := by linarith [Real.pi_pos]
  have hrange2 : d / 2 ≤ Real.pi / 2 := by linarith
  have harc : d / 2 ≤ Real.arcsin (c / 2) := by
    have := Real.arcsin_le_arcsin hsinle
    rwa [Real.arcsin_sin hrange1 hrange2] at this
  linarith

/-! ## Normalizing a diagonal entry -/

/-- The circle point carrying the phase of a nonzero complex number. -/
private noncomputable def phaseNormalize (a : ℂ) : ℂ := a / (‖a‖ : ℂ)

private theorem norm_phaseNormalize {a : ℂ} (ha : a ≠ 0) : ‖phaseNormalize a‖ = 1 := by
  have hne : (‖a‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr ha
  rw [phaseNormalize, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg a), div_self hne]

theorem norm_phaseNormalize_sub_self {a : ℂ} (ha : a ≠ 0) :
    ‖phaseNormalize a - a‖ = |1 - ‖a‖| := by
  have hne : (‖a‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr ha
  have hfac : phaseNormalize a - a = ((1 / ‖a‖ - 1 : ℝ) : ℂ) * a := by
    rw [phaseNormalize]
    push_cast
    field_simp
  rw [hfac, norm_mul, Complex.norm_real,
    show (1 / ‖a‖ - 1 : ℝ) = (1 - ‖a‖) / ‖a‖ from by field_simp,
    Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg a)]
  field_simp

/-- **`(20)`: a near-unit entry is bounded away from zero.** -/
theorem one_sub_le_norm_of_close {a u : ℂ} (hu : ‖u‖ = 1) {ε : ℝ} (h : ‖a - u‖ ≤ ε) :
    1 - ε ≤ ‖a‖ := by
  have htri : ‖u‖ - ‖a‖ ≤ ‖a - u‖ := by
    have := norm_sub_norm_le u a
    rwa [norm_sub_rev] at this
  rw [hu] at htri
  linarith

/-- **`(21)`: the normalized entry stays within `2ε` of the orbit phase.** -/
private theorem norm_phaseNormalize_sub_le {a u : ℂ} (hu : ‖u‖ = 1) (ha : a ≠ 0) {ε : ℝ}
    (h : ‖a - u‖ ≤ ε) : ‖phaseNormalize a - u‖ ≤ 2 * ε := by
  have hgap : |1 - ‖a‖| ≤ ε := by
    have h1 : |‖u‖ - ‖a‖| ≤ ‖u - a‖ := abs_norm_sub_norm_le u a
    rw [hu, norm_sub_rev] at h1
    linarith [h1, h]
  have hsplit : ‖phaseNormalize a - u‖ ≤ ‖phaseNormalize a - a‖ + ‖a - u‖ := by
    have h0 : phaseNormalize a - u = (phaseNormalize a - a) + (a - u) := by ring
    rw [h0]
    exact norm_add_le _ _
  rw [norm_phaseNormalize_sub_self ha] at hsplit
  linarith

/-! ## The extracted winding -/

/-- **`(23)`: the orbit winding survives extraction, up to `4 arcsin ε`.** -/
theorem circDist_extracted_ge {φ ψ θ χ : ℝ} {α : ℝ}
    (hφ : circDist φ θ ≤ α) (hψ : circDist ψ χ ≤ α) :
    circDist θ χ - 2 * α ≤ circDist φ ψ := by
  have h1 : circDist θ χ ≤ circDist θ φ + circDist φ χ := circDist_triangle _ _ _
  have h2 : circDist φ χ ≤ circDist φ ψ + circDist ψ χ := circDist_triangle _ _ _
  have h3 : circDist θ φ = circDist φ θ := circDist_comm _ _
  linarith [h1, h2, h3, hφ, hψ]

/-- **`(19)`: the extracted centralizer element has bandwidth at least the resolved winding rate.**
Stated across an arbitrary level pair, so no minimum gap is used. -/
theorem pair_ratio_le_of_lip {p : ℝ → ℝ} {L : ℝ} (hLip : ∀ x y, |p x - p y| ≤ L * |x - y|)
    {θ E : ℕ → ℝ} {n : ℕ} (hlift : IsPhaseLift θ E n p) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (hlt : E j < E i) :
    circDist (θ i) (θ j) / (E i - E j) ≤ L := by
  have hpos : 0 < E i - E j := by linarith
  have h := circDist_le_of_lip hLip hlift hi hj
  rw [abs_of_pos hpos] at h
  exact (div_le_iff₀ hpos).mpr h

/-! ## The resolved spectral scale -/

/-- **`(25)`: on a resolved pair the extracted phase keeps half the orbit rate.**  If the pair
separation `Δ` satisfies `8α ≤ |t|Δ ≤ π`, then the extracted winding across it is at least
`|t|Δ/2`. -/
theorem extracted_ratio_ge_half {t Δ α : ℝ} (hΔ : 0 < Δ)
    (h8 : 8 * α ≤ |t| * Δ) (hpi : |t| * Δ ≤ Real.pi)
    {φ ψ θ χ : ℝ} (hθχ : θ - χ = t * Δ)
    (hφ : circDist φ θ ≤ 2 * α) (hψ : circDist ψ χ ≤ 2 * α) :
    |t| / 2 ≤ circDist φ ψ / Δ := by
  have habs : |θ - χ| = |t| * Δ := by
    rw [hθχ, abs_mul, abs_of_pos hΔ]
  have hres : circDist θ χ = |t| * Δ := by
    rw [circDist_eq_abs_of_le_pi (by rw [habs]; exact hpi), habs]
  have hext := circDist_extracted_ge hφ hψ
  rw [hres] at hext
  have hlow : |t| * Δ / 2 ≤ circDist φ ψ := by linarith
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hΔ]
  linarith [hlow]

/-- A quadratic carrier is Lipschitz with constant `2|c|R` on a spectrum inside `[-R, R]`. -/
theorem quadratic_carrier_lip {c R : ℝ} {x y : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |c * x ^ 2 - c * y ^ 2| ≤ 2 * |c| * R * |x - y| := by
  have hfac : c * x ^ 2 - c * y ^ 2 = c * (x - y) * (x + y) := by ring
  have hsum : |x + y| ≤ 2 * R := by
    calc |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ 2 * R := by linarith
  calc |c * x ^ 2 - c * y ^ 2| = |c| * |x - y| * |x + y| := by
        rw [hfac, abs_mul, abs_mul]
    _ ≤ |c| * |x - y| * (2 * R) := by
        refine mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * |c| * R * |x - y| := by ring


/-! ## The operator layer of `(18)` and `(17)` -/

section OperatorLayer

open _root_.Matrix

/-- **A diagonal operator moves no vector further than its largest entry.**  This is the operator
norm of a difference diagonal in the spectral decomposition, in the form the Loewner and Lipschitz
estimates consume. -/
theorem diagonal_mulVec_norm_le {d : Type*} [Fintype d] [DecidableEq d] (ζ : d → ℂ) {c : ℝ}
    (hc : ∀ l, ‖ζ l‖ ≤ c) (v : d → ℂ) :
    ∑ l, ‖(Matrix.diagonal ζ *ᵥ v) l‖ ^ 2 ≤ c ^ 2 * ∑ l, ‖v l‖ ^ 2 := by
  have hstep : ∀ l, ‖(Matrix.diagonal ζ *ᵥ v) l‖ ^ 2 ≤ c ^ 2 * ‖v l‖ ^ 2 := by
    intro l
    rw [Matrix.mulVec_diagonal, norm_mul, mul_pow]
    have hcl := hc l
    have hnn : (0 : ℝ) ≤ ‖ζ l‖ := norm_nonneg _
    have hsq : ‖ζ l‖ ^ 2 ≤ c ^ 2 := by nlinarith [hcl, hnn]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  calc ∑ l, ‖(Matrix.diagonal ζ *ᵥ v) l‖ ^ 2 ≤ ∑ l, c ^ 2 * ‖v l‖ ^ 2 :=
        Finset.sum_le_sum fun l _ => hstep l
    _ = c ^ 2 * ∑ l, ‖v l‖ ^ 2 := (Finset.mul_sum _ _ _).symm

end OperatorLayer

/-- **`(17)` does not see the eigenvector phase.**  Rescaling a unit eigenvector by a unit scalar
leaves the diagonal entry unchanged. -/
theorem diagonalEntry_phase_invariant {lam a : ℂ} (hlam : ‖lam‖ = 1) :
    (starRingEnd ℂ) lam * a * lam = a := by
  have hns : Complex.normSq lam = 1 := by
    rw [Complex.normSq_eq_norm_sq, hlam]
    norm_num
  have hconj : (starRingEnd ℂ) lam * lam = 1 := by
    rw [mul_comm, Complex.mul_conj, hns]
    norm_num
  calc (starRingEnd ℂ) lam * a * lam = ((starRingEnd ℂ) lam * lam) * a := by ring
    _ = a := by rw [hconj, one_mul]

end GaloisForLFunctions.HTGeometry
