import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquareOfTheSourceThetaUnfolds

/-!
# The cube frequencies of the theta square factor out

The coefficients of the projected cubic theta function at unramified frequencies are supported on
`gen(A) gen(B)³` with `A` squarefree, and there (MMD, `rationalSourceResidualFourierCoefficient_squarefree_cube`)

`T(gen(A) gen(B)³) = \overline{C} |gen B| (9/gen A)₃ \overline{G̃(gen A)}`,   `C = rationalSourceThetaScalar ≠ 0`.

* `thetaSquarefreePart_mul_cube`, `thetaCubePart_mul_cube`: for squarefree `A`, the ideal `A B³`
  determines `A` and `B` (prime counts `a + 3b` with `a ≤ 1`); so `(A, B) ↦ A B³` is injective.
* `sourceCoefficient_sq`: `T(gen(A) gen(B)³)² = \overline{C}² N(B) σ(A)`, with the unimodular weight
  `σ(A) = ((9/gen A)₃ \overline{G̃(gen A)})²` (`norm_thetaSquareWeight`).
* `thetaSquareDirichlet_eq` (**the cube frequencies factor out**): for `Re w > 1`,

  `Σ_I N(I)^{−w} T(gen I)² = \overline{C}² Z₀(3w − 1) Σ_{A squarefree} N(A)^{−w} σ(A)`,

  `Z₀` the unramified zeta function, sums over unramified ideals. The cube frequencies `B³` are
  principal (`T(h b³) = |b| T(h)`) and contribute `Z₀(3w − 1)`, which has its pole at `w = 2/3`. The
  squarefree factor `S(w) = Σ_A N(A)^{−w} σ(A)` is a finite-order twist of `Σ_A γ₂(A)² N(A)^{−w}`, the
  series of the long columns of `CoherenceTheoryOfReciprocityFamilies`.
-/

noncomputable section

open MeasureTheory UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi

/-! ### Unique decomposition `I = A B³` -/

theorem count_mul_cube {A B : Ideal O} (hA : A ≠ 0) (hB : B ≠ 0) (P : Ideal O) :
    (normalizedFactors (A * B ^ 3)).count P =
      (normalizedFactors A).count P + 3 * (normalizedFactors B).count P := by
  rw [normalizedFactors_mul hA (pow_ne_zero 3 hB), normalizedFactors_pow, Multiset.count_add,
    Multiset.count_nsmul]

theorem count_le_one_of_squarefree {A : Ideal O} (hA : Squarefree A) (P : Ideal O) :
    (normalizedFactors A).count P ≤ 1 :=
  Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hA.ne_zero).mp hA) P

/-- `thetaSquarefreePart (A B³) = A` for squarefree `A`. -/
theorem thetaSquarefreePart_mul_cube {A B : Ideal O} (hA : Squarefree A) (hB : B ≠ 0) :
    thetaSquarefreePart (A * B ^ 3) = A := by
  have hA0 : A ≠ 0 := hA.ne_zero
  have hset : (primeSupport (A * B ^ 3)).filter
      (fun P => (normalizedFactors (A * B ^ 3)).count P % 3 = 1) = primeSupport A := by
    ext P
    simp only [Finset.mem_filter, primeSupport, Multiset.mem_toFinset, count_mul_cube hA0 hB P]
    have hle := count_le_one_of_squarefree hA P
    constructor
    · rintro ⟨-, h1⟩
      apply Multiset.count_pos.mp
      omega
    · intro hP
      have hpos := Multiset.count_pos.mpr hP
      refine ⟨Multiset.count_pos.mp ?_, by omega⟩
      rw [count_mul_cube hA0 hB P]
      omega
  rw [thetaSquarefreePart, hset, squarefree_support_product_self hA]

/-- `thetaCubePart (A B³) = B` for squarefree `A`. -/
theorem thetaCubePart_mul_cube {A B : Ideal O} (hA : Squarefree A) (hB : B ≠ 0) :
    thetaCubePart (A * B ^ 3) = B := by
  have hA0 : A ≠ 0 := hA.ne_zero
  have hexp : ∀ P, (normalizedFactors (A * B ^ 3)).count P / 3 = (normalizedFactors B).count P := by
    intro P
    rw [count_mul_cube hA0 hB P]
    have := count_le_one_of_squarefree hA P
    omega
  have hsub : primeSupport B ⊆ primeSupport (A * B ^ 3) := by
    intro P hP
    simp only [primeSupport, Multiset.mem_toFinset] at hP ⊢
    apply Multiset.count_pos.mp
    rw [count_mul_cube hA0 hB P]
    have := Multiset.count_pos.mpr hP
    omega
  rw [thetaCubePart]
  simp_rw [hexp]
  rw [← Finset.prod_subset hsub (fun P _ hP => by
    simp only [primeSupport, Multiset.mem_toFinset] at hP
    rw [Multiset.count_eq_zero.mpr hP, pow_zero])]
  rw [primeSupport, ← Finset.prod_multiset_count (normalizedFactors B)]
  exact Ideal.prod_normalizedFactors_eq_self hB

/-- `(A, B) ↦ A B³` is injective on squarefree `A` and nonzero `B`. -/
theorem mul_cube_injective {A₁ B₁ A₂ B₂ : Ideal O} (hA₁ : Squarefree A₁) (hA₂ : Squarefree A₂)
    (hB₁ : B₁ ≠ 0) (hB₂ : B₂ ≠ 0) (h : A₁ * B₁ ^ 3 = A₂ * B₂ ^ 3) : A₁ = A₂ ∧ B₁ = B₂ := by
  constructor
  · rw [← thetaSquarefreePart_mul_cube hA₁ hB₁, h, thetaSquarefreePart_mul_cube hA₂ hB₂]
  · rw [← thetaCubePart_mul_cube hA₁ hB₁, h, thetaCubePart_mul_cube hA₂ hB₂]

/-! ### The coefficients on squarefree times cube -/

/-- The unimodular weight `σ(A) = ((9/gen A)₃ \overline{G̃(gen A)})²`. -/
def thetaSquareWeight (A : Ideal O) : ℂ :=
  (ringComplex (symbol 9 (primaryIdealGenerator A)) *
    star (normalizedCubicUnitGauss (primaryIdealGenerator A))) ^ 2

theorem norm_thetaSquareWeight (A : Ideal O) (hA : primaryIdealGenerator A ≠ 0) (hsq : Squarefree A) :
    ‖thetaSquareWeight A‖ = 1 := by
  have hp := (primaryIdealGenerator_spec A hA).2
  have hc3 : IsCoprime (3 : O) (primaryIdealGenerator A) := by
    simpa only [Units.val_one, pow_zero, mul_one] using ramified_primary_coprime (1 : Oˣ) 0 _ hp
  have hc9 : IsCoprime (9 : O) (primaryIdealGenerator A) := by
    convert hc3.mul_left hc3 using 1
    norm_num
  rw [thetaSquareWeight, norm_pow, norm_mul, norm_star, symbol_norm_one _ _ hp hc9,
    normalizedCubicUnitGauss_squarefree_norm A hA hsq]
  norm_num

/-- `T(gen(A) gen(B)³)² = \overline{C}² |gen B|² σ(A)`. -/
theorem sourceCoefficient_sq (A B : Ideal O) (hA : primaryIdealGenerator A ≠ 0)
    (hB : primaryIdealGenerator B ≠ 0) (hsq : Squarefree A) :
    rationalSourceResidualFourierCoefficient (primaryIdealGenerator A * primaryIdealGenerator B ^ 3) ^ 2 =
      star rationalSourceThetaScalar ^ 2 * ((‖ringComplex (primaryIdealGenerator B)‖ : ℂ) ^ 2) *
        thetaSquareWeight A := by
  have h := congrArg star (rationalSourceResidualFourierCoefficient_squarefree_cube A B hA hB hsq)
  rw [star_star] at h
  rw [h, thetaSquareWeight]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-! ### The Dirichlet series -/

/-- `N(B)^{−(3w−1)} = N(B) (N(B)^{−w})³` on good ideals, as weights. -/
theorem normWeight_shift (w : ℂ) (B : Ideal O) (hB : primaryIdealGenerator B ≠ 0) :
    unramifiedNormWeight (3 * w - 1) B =
      (‖ringComplex (primaryIdealGenerator B)‖ : ℂ) ^ 2 * unramifiedNormWeight w B ^ 3 := by
  have hN : ((‖ringComplex (primaryIdealGenerator B)‖ : ℂ)) ^ 2 = (Ideal.absNorm B : ℂ) := by
    have := primaryIdealGenerator_norm_sq B hB
    exact_mod_cast this
  have hB0 : (Ideal.absNorm B : ℂ) ≠ 0 := by
    rw [← hN]
    exact pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.mpr (ringComplex_ne_zero hB))
  rw [unramifiedNormWeight_of_good _ _ hB, unramifiedNormWeight_of_good _ _ hB, hN,
    show -(3 * w - 1) = 1 + (3 : ℕ) * (-w) by push_cast; ring, Complex.cpow_add _ _ hB0,
    Complex.cpow_one, Complex.cpow_nat_mul]

/-- The admissible pairs `(B, A)`: `A` squarefree, both unramified. -/
def admissiblePairs : Set (Ideal O × Ideal O) :=
  {p | Squarefree p.2 ∧ primaryIdealGenerator p.2 ≠ 0 ∧ primaryIdealGenerator p.1 ≠ 0}

/-- **The cube frequencies factor out.** For `Re w > 1`,
`Σ_I N(I)^{−w} T(gen I)² = \overline{C}² Z₀(3w − 1) Σ_{A squarefree} N(A)^{−w} σ(A)`. -/
theorem thetaSquareDirichlet_eq (w : ℂ) (hw : 1 < w.re) :
    ∑' I : Ideal O, unramifiedNormWeight w I *
        rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2 =
      star rationalSourceThetaScalar ^ 2 * unramifiedIdealZeta (3 * w - 1) *
        ∑' A : Ideal O, (if Squarefree A then unramifiedNormWeight w A * thetaSquareWeight A else 0) := by
  set f : Ideal O → ℂ := fun I => unramifiedNormWeight w I *
    rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2 with hf
  set x : Ideal O → ℂ := fun B => unramifiedNormWeight (3 * w - 1) B with hx
  set y : Ideal O → ℂ := fun A =>
    if Squarefree A then unramifiedNormWeight w A * thetaSquareWeight A else 0 with hy
  have hw3 : 1 < (3 * w - 1).re := by
    have : (3 * w - 1).re = 3 * w.re - 1 := by simp
    rw [this]
    linarith
  have hxs : Summable (fun B => ‖x B‖) := unramifiedNormWeight_summable_norm _ hw3
  have hys : Summable (fun A => ‖y A‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun A => ?_)
      (unramifiedNormWeight_summable_norm w hw)
    simp only [hy]
    split_ifs with hsq
    · by_cases hA : primaryIdealGenerator A = 0
      · rw [unramifiedNormWeight_of_bad w A hA, zero_mul, norm_zero]
      · rw [norm_mul, norm_thetaSquareWeight A hA hsq, mul_one]
    · rw [norm_zero]
      exact norm_nonneg _
  -- the pair terms
  have hpair : ∀ p : Ideal O × Ideal O, star rationalSourceThetaScalar ^ 2 * (x p.1 * y p.2) =
      admissiblePairs.indicator (fun p => f (p.2 * p.1 ^ 3)) p := by
    rintro ⟨B, A⟩
    by_cases hp : (B, A) ∈ admissiblePairs
    · obtain ⟨hsq, hA, hB⟩ := hp
      rw [Set.indicator_of_mem (show (B, A) ∈ admissiblePairs from ⟨hsq, hA, hB⟩)]
      simp only [hf, hx, hy, if_pos hsq]
      rw [map_mul, map_pow, primaryIdealGenerator_mul, primaryIdealGenerator_pow,
        sourceCoefficient_sq A B hA hB hsq, normWeight_shift w B hB]
      ring
    · rw [Set.indicator_of_notMem hp]
      simp only [admissiblePairs, Set.mem_setOf_eq, not_and_or] at hp
      simp only [hx, hy]
      rcases hp with hsq | hA | hB
      · rw [if_neg hsq, mul_zero, mul_zero]
      · push Not at hA
        by_cases hsq : Squarefree A
        · rw [if_pos hsq, unramifiedNormWeight_of_bad w A hA, zero_mul, mul_zero, mul_zero]
        · rw [if_neg hsq, mul_zero, mul_zero]
      · push Not at hB
        rw [unramifiedNormWeight_of_bad _ B hB, zero_mul, mul_zero]
  -- reindexing the support of `f` by the admissible pairs
  have hinj : Function.Injective (fun p : admissiblePairs => p.1.2 * p.1.1 ^ 3) := by
    rintro ⟨⟨B₁, A₁⟩, hsq₁, hA₁, hB₁⟩ ⟨⟨B₂, A₂⟩, hsq₂, hA₂, hB₂⟩ h
    obtain ⟨hA, hB⟩ := mul_cube_injective hsq₁ hsq₂ (primaryIdealGenerator_ne_zero_ideal B₁ hB₁)
      (primaryIdealGenerator_ne_zero_ideal B₂ hB₂) h
    subst hA hB
    rfl
  have hsupp : Function.support f ⊆ Set.range (fun p : admissiblePairs => p.1.2 * p.1.1 ^ 3) := by
    intro I hI
    have hI' : f I ≠ 0 := hI
    simp only [hf] at hI'
    have hg : primaryIdealGenerator I ≠ 0 := by
      intro hz
      exact hI' (by rw [unramifiedNormWeight_of_bad w I hz, zero_mul])
    have hT : rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ≠ 0 := by
      intro hz
      exact hI' (by rw [hz]; ring)
    obtain ⟨A, B, hsq, hA, hB, hAB⟩ := (sourceFourier_squarefree_cube_support_iff I hg).mp hT
    exact ⟨⟨(B, A), hsq, hA, hB⟩, hAB⟩
  calc ∑' I : Ideal O, f I
      = ∑' p : admissiblePairs, f (p.1.2 * p.1.1 ^ 3) := (hinj.tsum_eq hsupp).symm
    _ = ∑' p : Ideal O × Ideal O, admissiblePairs.indicator (fun p => f (p.2 * p.1 ^ 3)) p :=
        tsum_subtype admissiblePairs (fun p => f (p.2 * p.1 ^ 3))
    _ = ∑' p : Ideal O × Ideal O, star rationalSourceThetaScalar ^ 2 * (x p.1 * y p.2) :=
        tsum_congr fun p => (hpair p).symm
    _ = star rationalSourceThetaScalar ^ 2 * ((∑' B, x B) * ∑' A, y A) := by
        rw [tsum_mul_left, tsum_mul_tsum_of_summable_norm hxs hys]
    _ = _ := by
        simp only [hx, unramifiedIdealZeta]
        ring

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
