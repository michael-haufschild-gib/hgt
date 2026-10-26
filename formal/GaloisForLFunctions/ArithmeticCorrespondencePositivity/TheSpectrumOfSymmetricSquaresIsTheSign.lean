import GaloisForLFunctions.ArithmeticCorrespondencePositivity.KernelCountsAreBlindToComplexQuartets
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheLocalGeometryOfAReflectionPair

/-!
# The spectrum of symmetric squares is the sign

For a ring element `f = P(F)` of a curve, the symmetric square `f f′ = P(F) P(q/F)` acts on `H¹`
with eigenvalues `P(α_i) P(q/α_i)`. Three invariants of `f f′` carry three different amounts of
information.

* **Its kernel count is a square** (`prod_symSquareEig_eq_sq`): `deg(f f′) = (Π_i P(α_i))²` because
  the functional equation permutes the eigenvalues. It is nonnegative on every datum and sees
  nothing.
* **Kernel counts of `f`** see the real off-line pairs and miss the complex quartets
  (`KernelCountsAreBlindToComplexQuartets`).
* **The spectrum of `f f′` is the sign** (`symSquare_spectrum_nonneg_iff_unitary`). Every eigenvalue
  `(α_i − c)(q/α_i − c)` of `(F − c)(F − c)′`, `c ∈ ℝ`, is a nonnegative real iff the datum is
  unitary. Linear elements suffice: a non-unitary non-real `α` makes `α + q/α` non-real, a real
  off-line pair makes the value at `c = (α + q/α)/2` negative. The complex fake has the non-real
  eigenvalue `17 − 6i` at `c = 1` (`complexFake_symSquareEig_one`); the golden datum has `−1` at
  `c = 2` (`goldenDatum_symSquareEig_two`).
* **The local criterion** (`symSquare_local_nonneg_iff`). For a symbol `β ≠ 0`, the numbers
  `(β − c)(β⁻¹ − c)`, `c ∈ ℝ`, are all nonnegative reals iff `|β| = 1`; for the Hecke symbol
  `β = p^{ρ − ½}` this is `Re ρ = ½` at one prime, with no resonant exception
  (`symSquare_heckeSymbol_nonneg_iff`).

So the positivity Weil's argument supplies is pointwise positivity of the spectrum of symmetric
squares — the spectral form of the positivity of the Rosati involution. Counting kernels sees only
products of that spectrum, and products of a reflection-symmetric spectrum are squares or pair
conjugates. Over `ℤ` this pointwise positivity is the critical line itself; an arithmetic
substitute must produce it without reading the spectrum.
-/

open Complex Polynomial Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri

/-! ### The core lemma -/

/-- **Core lemma.** If `α α' = q > 0` and every `(α − c)(α' − c)`, `c ∈ ℝ`, is a nonnegative real,
then `|α|² = q`: a non-real `α` with `|α|² ≠ q` makes `α + α'` non-real, a real pair `α ≠ α'` is
negative at the midpoint. -/
theorem normSq_eq_of_symSquare_nonneg {α α' : ℂ} {q : ℝ} (hq : 0 < q) (hprod : α * α' = q)
    (h : ∀ c : ℝ, ∃ r : ℝ, 0 ≤ r ∧ (α - c) * (α' - c) = r) : Complex.normSq α = q := by
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_mul] at hprod; exact (Complex.ofReal_ne_zero.mpr hq.ne') hprod.symm
  have hα' : α' = q / α := by rw [eq_div_iff hα0, mul_comm, hprod]
  obtain ⟨r1, -, h1⟩ := h 1
  obtain ⟨r0, -, h0⟩ := h 0
  have him : α.im + α'.im = 0 := by
    have e : (α - ((1 : ℝ) : ℂ)) * (α' - ((1 : ℝ) : ℂ)) =
        (α - ((0 : ℝ) : ℂ)) * (α' - ((0 : ℝ) : ℂ)) - (α + α') + 1 := by push_cast; ring
    have := congrArg Complex.im e
    rw [h1, h0] at this
    simp only [Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.one_im] at this
    linarith
  have hnorm : (Complex.normSq α : ℂ) * α' = q * conj α := by
    rw [hα', ← Complex.mul_conj]; field_simp
  have himn : Complex.normSq α * α'.im = -(q * α.im) := by
    have := congrArg Complex.im hnorm
    simpa [Complex.mul_im] using this
  rcases eq_or_ne α.im 0 with hy | hy
  · have hy' : α'.im = 0 := by linarith
    obtain ⟨r, hr, hrv⟩ := h ((α.re + α'.re) / 2)
    have hval : (α - (((α.re + α'.re) / 2 : ℝ) : ℂ)) * (α' - (((α.re + α'.re) / 2 : ℝ) : ℂ)) =
        ((-(α.re - α'.re) ^ 2 / 4 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hy, hy'] <;> ring
    rw [hval] at hrv
    have h2 := Complex.ofReal_injective hrv
    have heq : α.re = α'.re := by nlinarith [sq_nonneg (α.re - α'.re)]
    have hprod' : α.re * α'.re = q := by
      have := congrArg Complex.re hprod
      simpa [Complex.mul_re, hy, hy'] using this
    rw [Complex.normSq_apply, hy, mul_zero, add_zero]
    nth_rewrite 2 [heq]
    exact hprod'
  · have h3 : α'.im = -α.im := by linarith
    rw [h3] at himn
    have : (Complex.normSq α - q) * α.im = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_right hy
    linarith

section CurveData

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The eigenvalue `(α_i − c)(q/α_i − c)` of the symmetric square `(F − c)(F − c)′`. -/
def symSquareEig (c : ℝ) (i : ι) : ℂ :=
  (eigenvalue D i - c) * (eigenvalue D (D.fePerm i) - c)

theorem eigenvalue_mul_fePerm (i : ι) : eigenvalue D i * eigenvalue D (D.fePerm i) = D.q := by
  rw [eigenvalue, eigenvalue, mul_mul_mul_comm, mul_comm (D.β i), D.β_fePerm, mul_one,
    ← Complex.ofReal_mul, ← pow_two, D.sqrtq_sq]

/-- **The kernel count of a symmetric square is a square.** -/
theorem prod_symSquareEig_eq_sq (c : ℝ) :
    ∏ i, symSquareEig D c i = (∏ i, (eigenvalue D i - c)) ^ 2 := by
  rw [pow_two]
  simp only [symSquareEig, prod_mul_distrib]
  rw [Equiv.prod_comp D.fePerm (fun i => eigenvalue D i - c)]

theorem normSq_eigenvalue (i : ι) :
    Complex.normSq (eigenvalue D i) = D.q * ‖D.β i‖ ^ 2 := by
  rw [Complex.normSq_eq_norm_sq, eigenvalue, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg D.sqrtq_pos.le, mul_pow, D.sqrtq_sq]

/-- **The spectrum of symmetric squares is the sign.** All eigenvalues of `(F − c)(F − c)′`,
`c ∈ ℝ`, are nonnegative reals iff the datum is unitary. -/
theorem symSquare_spectrum_nonneg_iff_unitary :
    (∀ (c : ℝ) (i : ι), ∃ r : ℝ, 0 ≤ r ∧ symSquareEig D c i = r) ↔ ∀ i, ‖D.β i‖ = 1 := by
  have hqpos : (0 : ℝ) < D.q := by linarith [D.one_lt_q]
  constructor
  · intro h i
    have hn := normSq_eq_of_symSquare_nonneg hqpos (eigenvalue_mul_fePerm D i) fun c => h c i
    rw [normSq_eigenvalue] at hn
    have : ‖D.β i‖ ^ 2 = 1 := mul_left_cancel₀ hqpos.ne' (by rw [hn, mul_one])
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  · intro hU c i
    have h0 : D.β i ≠ 0 := by
      intro h0; have := hU i; rw [h0, norm_zero] at this; norm_num at this
    have hfe : D.β (D.fePerm i) = conj (D.β i) := by
      have h1 : D.β (D.fePerm i) = (D.β i)⁻¹ := eq_inv_of_mul_eq_one_left (D.β_fePerm i)
      rw [h1, Complex.inv_def, Complex.normSq_eq_norm_sq, hU i]; simp
    refine ⟨Complex.normSq (eigenvalue D i - c), Complex.normSq_nonneg _, ?_⟩
    rw [symSquareEig, eigenvalue, eigenvalue, hfe, ← Complex.mul_conj]
    simp [map_sub, map_mul, Complex.conj_ofReal]

end CurveData

/-! ### Calibration -/

/-- **The complex fake has a non-real symmetric-square eigenvalue**: `(8i − 1)(−2i − 1) = 17 − 6i`. -/
theorem complexFake_symSquareEig_one : symSquareEig complexFake 1 0 = 17 - 6 * I := by
  have hfe : complexFake.fePerm 0 = 3 := rfl
  rw [symSquareEig, hfe, complexFake_eigenvalue]
  simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- **The golden datum has a negative symmetric-square eigenvalue**: `(√5φ − 2)(√5φ⁻¹ − 2) = −1`. -/
theorem goldenDatum_symSquareEig_two : symSquareEig goldenDatum 2 0 = -1 := by
  have hfe : goldenDatum.fePerm 0 = 1 := rfl
  have h := goldenDatum_detDeg_two_sub_X
  rw [detDeg, Fin.prod_univ_two] at h
  simp only [map_sub, aeval_C, aeval_X] at h
  rw [symSquareEig, hfe]
  have e : (eigenvalue goldenDatum 0 - ((2 : ℝ) : ℂ)) * (eigenvalue goldenDatum 1 - ((2 : ℝ) : ℂ)) =
      ((algebraMap ℝ ℂ) 2 - eigenvalue goldenDatum 0) * ((algebraMap ℝ ℂ) 2 - eigenvalue goldenDatum 1) := by
    simp; ring
  rw [e, h]

/-! ### The local criterion -/

/-- **Local criterion.** For `β ≠ 0`, every `(β − c)(β⁻¹ − c)`, `c ∈ ℝ`, is a nonnegative real iff
`|β| = 1`. -/
theorem symSquare_local_nonneg_iff {β : ℂ} (hβ : β ≠ 0) :
    (∀ c : ℝ, ∃ r : ℝ, 0 ≤ r ∧ (β - c) * (β⁻¹ - c) = r) ↔ ‖β‖ = 1 := by
  constructor
  · intro h
    have hprod : β * β⁻¹ = ((1 : ℝ) : ℂ) := by rw [mul_inv_cancel₀ hβ, Complex.ofReal_one]
    have hn := normSq_eq_of_symSquare_nonneg one_pos hprod h
    rw [Complex.normSq_eq_norm_sq] at hn
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hn
  · intro hn c
    have hinv : β⁻¹ = conj β := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
    refine ⟨Complex.normSq (β - c), Complex.normSq_nonneg _, ?_⟩
    rw [hinv, ← Complex.mul_conj]
    simp [map_sub, Complex.conj_ofReal]

/-- **At one prime the local criterion is the critical line**, with no resonant exception. -/
theorem symSquare_heckeSymbol_nonneg_iff {p : ℝ} (hp : 1 < p) (ρ : ℂ) :
    (∀ c : ℝ, ∃ r : ℝ, 0 ≤ r ∧
      (heckeSymbol p ρ - c) * ((heckeSymbol p ρ)⁻¹ - c) = r) ↔ ρ.re = 1 / 2 := by
  rw [symSquare_local_nonneg_iff (heckeSymbol_ne_zero p ρ), norm_heckeSymbol_eq_one_iff hp]

/-- **RH as pointwise positivity of symmetric squares at one prime.** For any `p > 1`, RH holds
iff at every nontrivial zero `ρ` of `ζ` all numbers `(p^{ρ−½} − c)(p^{½−ρ} − c)`, `c ∈ ℝ`, are
nonnegative reals. -/
theorem riemannHypothesis_iff_symSquare_heckeSymbol_nonneg {p : ℝ} (hp : 1 < p) :
    RiemannHypothesis ↔ ∀ ρ : ℂ, riemannZeta ρ = 0 → (¬∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 →
      ∀ c : ℝ, ∃ r : ℝ, 0 ≤ r ∧ (heckeSymbol p ρ - c) * ((heckeSymbol p ρ)⁻¹ - c) = r := by
  constructor
  · intro hRH ρ hz htriv h1
    exact (symSquare_heckeSymbol_nonneg_iff hp ρ).mpr (hRH ρ hz htriv h1)
  · intro h ρ hz htriv h1
    exact (symSquare_heckeSymbol_nonneg_iff hp ρ).mp (h ρ hz htriv h1)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
