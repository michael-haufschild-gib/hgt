import GaloisForLFunctions.HTGeometry.FDNLS.Conservation

/-!
# The anti-continuum limit and its Bogoliubov spectrum

Zhong--Malomed--Yan, arXiv:2407.12441, Section II E, equations (40) and (41).

At `C = 0` the lattice sites decouple, and the stationary equation (26) at the normalised frequency
`ω = -1` becomes the single-site condition `(|v|² - 1) v = 0` of equation (40): every site carries
either no amplitude or a unimodular one.  Linearising about such a configuration decouples the
Bogoliubov--de Gennes system into `2 × 2` blocks, one per site, and equation (41) records their
spectra: an excited site (`v = ±1`) contributes a *nilpotent* block, hence a pair of zero
eigenvalues joined by a Jordan chain, while an empty site (`v = 0`) contributes `λ = ± i`.

## Main results

* `antiContinuum_amplitude` — **equation (40)**: `(|v|² - 1)v = 0 ↔ v = 0 ∨ |v| = 1`.
* `antiContinuum_amplitude_phase` — the nonzero solutions are exactly the phases `e^{iθ}`.
* `IsACMode` — **equation (41)**.
* `acMode_excited_eigenvalue_eq_zero` — an excited site admits only `λ = 0`.
* `acMode_excited_kernel`, `acMode_excited_jordan` — the zero eigenvalue at an excited site really
  comes in a pair: the block is nilpotent with a length-two Jordan chain.
* `acMode_empty_eigenvalue` — an empty site admits exactly `λ = ± i`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-! ## Equation (40): the decoupled amplitude equation -/

/-- **Equation (40).**  In the anti-continuum limit the sites decouple and each amplitude solves
`(|v|² - 1) v = 0`; the solutions are `v = 0` and the unimodular numbers. -/
theorem antiContinuum_amplitude (v : ℂ) :
    ((‖v‖ ^ 2 - 1 : ℝ) : ℂ) * v = 0 ↔ v = 0 ∨ ‖v‖ = 1 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · right
      have : ‖v‖ ^ 2 - 1 = 0 := by exact_mod_cast h1
      have hv : ‖v‖ ^ 2 = 1 := by linarith
      nlinarith [norm_nonneg v]
    · exact Or.inl h2
  · rintro (rfl | h)
    · rw [mul_zero]
    · rw [h]
      norm_num

/-- The nonzero anti-continuum amplitudes are exactly the phases `e^{iθ}`, with `θ` free at each
site. -/
theorem antiContinuum_amplitude_phase {v : ℂ} (hv : ‖v‖ = 1) :
    ∃ θ : ℝ, v = Complex.exp ((θ : ℂ) * Complex.I) := by
  refine ⟨v.arg, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I v
  rw [hv] at h
  simpa using h.symm

/-! ## Equation (41): the anti-continuum Bogoliubov blocks -/

/-- **Equation (41).**  The single-site Bogoliubov--de Gennes system in the anti-continuum limit,
at the normalised frequency `ω = -1`, for a real limit amplitude `v`. -/
def IsACMode (v : ℝ) (a b lam : ℂ) : Prop :=
  ((1 - 2 * v ^ 2 : ℝ) : ℂ) * a - ((v ^ 2 : ℝ) : ℂ) * b = Complex.I * lam * a
    ∧ ((v ^ 2 : ℝ) : ℂ) * a - ((1 - 2 * v ^ 2 : ℝ) : ℂ) * b = Complex.I * lam * b

/-- **An excited site admits only the zero eigenvalue.**  The `2 × 2` block at a site with `v = ±1`
has vanishing trace *and* vanishing determinant, so it is nilpotent. -/
theorem acMode_excited_eigenvalue_eq_zero {v : ℝ} (hv : v ^ 2 = 1) {a b lam : ℂ}
    (h : IsACMode v a b lam) (hab : ¬(a = 0 ∧ b = 0)) : lam = 0 := by
  obtain ⟨h1, h2⟩ := h
  rw [hv] at h1 h2
  norm_num at h1 h2
  -- `h1 : -a - b = I lam a`,  `h2 : a + b = I lam b`  (up to normalisation)
  have hsum : Complex.I * lam * (a + b) = 0 := by
    have : Complex.I * lam * a + Complex.I * lam * b = 0 := by
      rw [← h1, ← h2]; ring
    rw [mul_add]
    exact this
  rcases mul_eq_zero.mp hsum with hIlam | hab0
  · rcases mul_eq_zero.mp hIlam with hI | hlam
    · exact absurd hI Complex.I_ne_zero
    · exact hlam
  · -- `b = -a`; then the first equation forces `I lam a = 0`
    have hb : b = -a := by linear_combination hab0
    have ha : a ≠ 0 := by
      intro ha0
      exact hab ⟨ha0, by rw [hb, ha0, neg_zero]⟩
    have : Complex.I * lam * a = 0 := by
      rw [← h1, hb]; ring
    rcases mul_eq_zero.mp this with hIlam | ha0
    · rcases mul_eq_zero.mp hIlam with hI | hlam
      · exact absurd hI Complex.I_ne_zero
      · exact hlam
    · exact absurd ha0 ha

/-- The zero mode of an excited block. -/
theorem acMode_excited_kernel {v : ℝ} (hv : v ^ 2 = 1) : IsACMode v 1 (-1) 0 := by
  constructor <;> · rw [hv]; norm_num

/-- The excited block is a genuine Jordan block: its zero mode `(1, -1)` is the image of another
vector, so the zero eigenvalue occurs in a *pair*, exactly as the paper records. -/
theorem acMode_excited_jordan {v : ℝ} (hv : v ^ 2 = 1) :
    ((1 - 2 * v ^ 2 : ℝ) : ℂ) * (-1) - ((v ^ 2 : ℝ) : ℂ) * 0 = 1
      ∧ ((v ^ 2 : ℝ) : ℂ) * (-1) - ((1 - 2 * v ^ 2 : ℝ) : ℂ) * 0 = -1 := by
  rw [hv]
  norm_num

/-- Solving `i λ = c` for `λ`. -/
theorem eq_neg_I_mul_of_I_mul_eq {lam c : ℂ} (h : Complex.I * lam = c) :
    lam = -(Complex.I * c) := by
  have h2 : -Complex.I * (Complex.I * lam) = -Complex.I * c := by rw [h]
  rw [← mul_assoc, neg_mul, Complex.I_mul_I] at h2
  simpa using h2

/-- **An empty site admits exactly the eigenvalues `λ = ± i`.**  Its `2 × 2` block is
`diag(1, -1)`. -/
theorem acMode_empty_eigenvalue {a b lam : ℂ} (h : IsACMode 0 a b lam)
    (hab : ¬(a = 0 ∧ b = 0)) : lam = -Complex.I ∨ lam = Complex.I := by
  obtain ⟨h1, h2⟩ := h
  norm_num at h1 h2
  by_cases ha : a = 0
  · right
    have hb : b ≠ 0 := fun hb0 => hab ⟨ha, hb0⟩
    have hfac : (Complex.I * lam + 1) * b = 0 := by linear_combination -h2
    have hI : Complex.I * lam = -1 := by
      rcases mul_eq_zero.mp hfac with hz | hz
      · linear_combination hz
      · exact absurd hz hb
    rw [eq_neg_I_mul_of_I_mul_eq hI]
    ring
  · left
    have hfac : (Complex.I * lam - 1) * a = 0 := by linear_combination -h1
    have hI : Complex.I * lam = 1 := by
      rcases mul_eq_zero.mp hfac with hz | hz
      · linear_combination hz
      · exact absurd hz ha
    rw [eq_neg_I_mul_of_I_mul_eq hI]
    ring

/-- Both eigenvalues `± i` are attained at an empty site. -/
theorem acMode_empty_modes :
    IsACMode 0 1 0 (-Complex.I) ∧ IsACMode 0 0 1 Complex.I := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp

end GaloisForLFunctions.HTGeometry.FDNLS
