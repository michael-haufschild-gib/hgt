import GaloisForLFunctions.FamilyContinuationTheory.ThePoissonCoefficientIsMultiplicativeUpToReciprocity

/-!
# The theta coefficient cancels the pair phases

The cubic-theta probe attaches to an index `A = cn³` (`c` squarefree) the theta coefficient
`γ₂(c) G(A)`, with `γ₂(c) = |c|⁻¹ Σ_{v mod c} χ_c(v)² ψ_c(v)` (`thetaGauss`) and
`G(A) = χ_A(4) Γ(A)` (`thetaPhase`), and to the pair `(s, A)` the fixed bicharacter `R(A, s)`.
The corrected coefficient

`K(s, c, n; H) = R(cn³, s) γ₂(c) G(cn³) F(s, cn³; H)`   (`correctedCoeff`)

is multiplicative (`correctedCoeff_mul`): for primary data prime to `2` with
`(s₁c₁n₁, s₂c₂n₂) = 1`,

`K(s₁s₂, c₁c₂, n₁n₂; H) = K(s₁, c₁, n₁; H) K(s₂, c₂, n₂; H)`.

The Poisson coefficient leaves the phase `r(A₁, s₂) r(A₂, s₁) χ_{A₁}(A₂) χ_{A₂}(A₁)`
(`poissonCoeff_mul_reciprocity`); `R` is a bicharacter, `γ₂` contributes `(χ_{c₁}(c₂) χ_{c₂}(c₁))²`
(`thetaGauss_mul`) and `G` contributes `r(A₁, A₂)` (`thetaPhase_mul`). Reciprocity reduces the
remaining phase to `χ_{c₁}(c₂)⁶ = 1` (`pairPhase_eq_one`): the cube indices of `A` drop out because
every coprime sextic symbol is a sixth root of unity (`sexticSymbol_pow_six`).
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-! ### Powers of the sextic symbol -/

theorem sexticSymbol_cube_numerator (x d : O) :
    sexticSymbol (x ^ 3) d = sexticSymbol x d ^ 3 := by
  rw [show x ^ 3 = x * x * x by ring, sexticSymbol_mul_numerator, sexticSymbol_mul_numerator]
  ring

theorem sexticSymbol_cube_denominator (x n : O) :
    sexticSymbol x (n ^ 3) = sexticSymbol x n ^ 3 := by
  rw [show n ^ 3 = n * n * n by ring, sexticSymbol_mul_denominator, sexticSymbol_mul_denominator]
  ring

/-- A coprime sextic symbol is a sixth root of unity. -/
theorem sexticSymbol_pow_six {x a : O} (ha : lambda ^ 2 ∣ a - 1) (ha2 : IsCoprime a 2)
    (hxa : IsCoprime x a) : sexticSymbol x a ^ 6 = 1 := by
  have hc := CubicJacobi.symbol_cube_of_isCoprime x a ha hxa
  have hq := quadSymbol_sq (primary_ne_zero a ha) ha2 hxa
  unfold sexticSymbol
  calc (ringComplex (CubicJacobi.symbol x a) ^ 2 * quadSymbol x a) ^ 6 =
      ringComplex (CubicJacobi.symbol x a ^ 3) ^ 4 * (quadSymbol x a ^ 2) ^ 3 := by
        rw [map_pow]; ring
    _ = 1 := by rw [hc, hq, map_one]; norm_num

/-! ### The theta coefficient -/

/-- `γ₂(c) = |c|⁻¹ Σ_{v mod c} χ_c(v)² ψ_c(v)`. -/
def thetaGauss (c : O) [NeZero c] : ℂ := sexticGaussPow 2 c 1 / (‖ringComplex c‖ : ℂ)

/-- `G(c) = χ_c(4) Γ(c)`. -/
def thetaPhase (c : O) : ℂ := sexticSymbol 4 c * fixedDualAverage c

/-- **CRT for `γ₂`.** For coprime `c₁, c₂`: `γ₂(c₁c₂) = (χ_{c₁}(c₂) χ_{c₂}(c₁))² γ₂(c₁) γ₂(c₂)`. -/
theorem thetaGauss_mul (c₁ c₂ : O) [NeZero c₁] [NeZero c₂] (h : IsCoprime c₁ c₂) :
    thetaGauss (c₁ * c₂) =
      (sexticSymbol c₂ c₁ * sexticSymbol c₁ c₂) ^ 2 * thetaGauss c₁ * thetaGauss c₂ := by
  unfold thetaGauss
  rw [sexticGaussPow_mul 2 c₁ c₂ h, map_mul, norm_mul, Complex.ofReal_mul]
  have h1 : (‖ringComplex c₁‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr fun h => NeZero.ne c₁ (ringComplex_injective
      (by rw [h, map_zero]))
  have h2 : (‖ringComplex c₂‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr fun h => NeZero.ne c₂ (ringComplex_injective
      (by rw [h, map_zero]))
  field_simp

/-- **The quadratic refinement.** For odd `v, w`: `G(vw) = G(v) G(w) r(v, w)`. -/
theorem thetaPhase_mul {v w : O} (hv : v ∉ Ideal.span {(2 : O)}) (hw : w ∉ Ideal.span {(2 : O)}) :
    thetaPhase (v * w) = thetaPhase v * thetaPhase w * quadraticPhase v w := by
  unfold thetaPhase quadraticPhase
  rw [sexticSymbol_mul_denominator]
  have h1 := gamma_ne_zero hv
  have h2 := gamma_ne_zero hw
  field_simp

/-! ### The pair phases -/

theorem primary_mul {a b : O} (ha : lambda ^ 2 ∣ a - 1) (hb : lambda ^ 2 ∣ b - 1) :
    lambda ^ 2 ∣ a * b - 1 := by
  have h : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left ha b) hb

theorem primary_pow {a : O} (ha : lambda ^ 2 ∣ a - 1) (k : ℕ) : lambda ^ 2 ∣ a ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ a k]; exact primary_mul ih ha

/-- **The pair phase is trivial.** With `A_i = c_i n_i³`, primary data prime to `2` and
`(c₁n₁, c₂n₂) = 1`: `(χ_{c₁}(c₂) χ_{c₂}(c₁))² r(A₁, A₂) χ_{A₁}(A₂) χ_{A₂}(A₁) = 1`. -/
theorem pairPhase_eq_one {c₁ n₁ c₂ n₂ : O} (hc₁ : lambda ^ 2 ∣ c₁ - 1) (hn₁ : lambda ^ 2 ∣ n₁ - 1)
    (hc₂ : lambda ^ 2 ∣ c₂ - 1) (hn₂ : lambda ^ 2 ∣ n₂ - 1) (hc₁2 : IsCoprime c₁ 2)
    (hn₁2 : IsCoprime n₁ 2) (hc₂2 : IsCoprime c₂ 2) (hn₂2 : IsCoprime n₂ 2)
    (h : IsCoprime (c₁ * n₁) (c₂ * n₂)) :
    (sexticSymbol c₂ c₁ * sexticSymbol c₁ c₂) ^ 2 * quadraticPhase (c₁ * n₁ ^ 3) (c₂ * n₂ ^ 3) *
        sexticSymbol (c₂ * n₂ ^ 3) (c₁ * n₁ ^ 3) * sexticSymbol (c₁ * n₁ ^ 3) (c₂ * n₂ ^ 3) = 1 := by
  have hl := h.of_isCoprime_of_dvd_left (dvd_mul_right c₁ n₁)
  have hl' := h.of_isCoprime_of_dvd_left (dvd_mul_left n₁ c₁)
  have hcc : IsCoprime c₁ c₂ := hl.of_isCoprime_of_dvd_right (dvd_mul_right c₂ n₂)
  have hcn : IsCoprime c₁ n₂ := hl.of_isCoprime_of_dvd_right (dvd_mul_left n₂ c₂)
  have hnc : IsCoprime n₁ c₂ := hl'.of_isCoprime_of_dvd_right (dvd_mul_right c₂ n₂)
  have hnn : IsCoprime n₁ n₂ := hl'.of_isCoprime_of_dvd_right (dvd_mul_left n₂ c₂)
  have hA₁ := primary_mul hc₁ (primary_pow hn₁ 3)
  have hA₂ := primary_mul hc₂ (primary_pow hn₂ 3)
  have hA₁2 : IsCoprime (c₁ * n₁ ^ 3) 2 := hc₁2.mul_left (hn₁2.pow_left)
  have hA₂2 : IsCoprime (c₂ * n₂ ^ 3) 2 := hc₂2.mul_left (hn₂2.pow_left)
  have hAA : IsCoprime (c₁ * n₁ ^ 3) (c₂ * n₂ ^ 3) :=
    (hcc.mul_right hcn.pow_right).mul_left ((hnc.mul_right hnn.pow_right).pow_left)
  -- reciprocity for `c₁, c₂` and for `A₁, A₂`
  rw [sexticSymbol_reciprocity hc₁ hc₂ hc₁2 hc₂2 hcc,
    sexticSymbol_reciprocity hA₁ hA₂ hA₁2 hA₂2 hAA]
  -- expand `χ_{A₁}(A₂)` over the factors
  rw [sexticSymbol_mul_numerator, sexticSymbol_mul_denominator, sexticSymbol_mul_denominator,
    sexticSymbol_cube_numerator, sexticSymbol_cube_numerator, sexticSymbol_cube_denominator,
    sexticSymbol_cube_denominator]
  have hrc := quadraticPhase_sq (not_mem_two_of_isCoprime hc₁2) (not_mem_two_of_isCoprime hc₂2)
  have hrA := quadraticPhase_sq (not_mem_two_of_isCoprime hA₁2) (not_mem_two_of_isCoprime hA₂2)
  have hX := sexticSymbol_pow_six hc₁ hc₁2 hcc.symm
  have hY := sexticSymbol_pow_six hn₁ hn₁2 hnc.symm
  have hZ := sexticSymbol_pow_six hc₁ hc₁2 hcn.symm
  have hW := sexticSymbol_pow_six hn₁ hn₁2 hnn.symm
  calc _ = quadraticPhase c₁ c₂ ^ 2 * quadraticPhase (c₁ * n₁ ^ 3) (c₂ * n₂ ^ 3) ^ 2 *
        sexticSymbol c₂ c₁ ^ 6 * sexticSymbol c₂ n₁ ^ 6 * sexticSymbol n₂ c₁ ^ 6 *
          (sexticSymbol n₂ n₁ ^ 6) ^ 3 := by ring
    _ = 1 := by rw [hrc, hrA, hX, hY, hZ, hW]; norm_num

/-! ### The corrected coefficient -/

/-- The corrected coefficient `K(s, c, n; H) = R(A, s) γ₂(c) G(A) F(s, A; H)`, `A = cn³`. -/
def correctedCoeff (s c n : O) [NeZero s] [NeZero c] [NeZero n] (H : O) : ℂ :=
  quadraticPhase (c * n ^ 3) s * (thetaGauss c * thetaPhase (c * n ^ 3)) *
    poissonCoeff s (c * n ^ 3) H

theorem poissonCoeff_congr_index (s : O) [NeZero s] {A A' : O} [NeZero A] [NeZero A'] (h : A = A')
    (H : O) : poissonCoeff s A H = poissonCoeff s A' H := by
  subst h
  rfl

theorem quadraticPhase_mul_right {c d e : O} (hc : c ∉ Ideal.span {(2 : O)})
    (hd : d ∉ Ideal.span {(2 : O)}) (he : e ∉ Ideal.span {(2 : O)}) :
    quadraticPhase c (d * e) = quadraticPhase c d * quadraticPhase c e := by
  rw [quadraticPhase_comm, quadraticPhase_mul_left hd he hc, quadraticPhase_comm d,
    quadraticPhase_comm e]

/-- **The corrected coefficient is multiplicative.** For primary data prime to `2` with
`(s₁c₁n₁, s₂c₂n₂) = 1`: `K(s₁s₂, c₁c₂, n₁n₂; H) = K(s₁, c₁, n₁; H) K(s₂, c₂, n₂; H)`. -/
theorem correctedCoeff_mul {s₁ s₂ c₁ c₂ n₁ n₂ : O} [NeZero s₁] [NeZero s₂] [NeZero c₁]
    [NeZero c₂] [NeZero n₁] [NeZero n₂] (hs₁ : lambda ^ 2 ∣ s₁ - 1) (hs₂ : lambda ^ 2 ∣ s₂ - 1)
    (hc₁ : lambda ^ 2 ∣ c₁ - 1) (hc₂ : lambda ^ 2 ∣ c₂ - 1) (hn₁ : lambda ^ 2 ∣ n₁ - 1)
    (hn₂ : lambda ^ 2 ∣ n₂ - 1) (hs₁2 : IsCoprime s₁ 2) (hs₂2 : IsCoprime s₂ 2)
    (hc₁2 : IsCoprime c₁ 2) (hc₂2 : IsCoprime c₂ 2) (hn₁2 : IsCoprime n₁ 2)
    (hn₂2 : IsCoprime n₂ 2) (h : IsCoprime (s₁ * c₁ * n₁) (s₂ * c₂ * n₂)) (H : O) :
    correctedCoeff (s₁ * s₂) (c₁ * c₂) (n₁ * n₂) H =
      correctedCoeff s₁ c₁ n₁ H * correctedCoeff s₂ c₂ n₂ H := by
  -- coprimality of the factors
  have hl := h.of_isCoprime_of_dvd_left (dvd_mul_right (s₁ * c₁) n₁)
  have hl₁ := hl.of_isCoprime_of_dvd_left (dvd_mul_right s₁ c₁)
  have hl₂ := hl.of_isCoprime_of_dvd_left (dvd_mul_left c₁ s₁)
  have hl₃ := h.of_isCoprime_of_dvd_left (dvd_mul_left n₁ (s₁ * c₁))
  have hcn : IsCoprime (c₁ * n₁) (c₂ * n₂) :=
    (hl₂.mul_left hl₃).of_isCoprime_of_dvd_right (by
      rw [show s₂ * c₂ * n₂ = s₂ * (c₂ * n₂) by ring]; exact dvd_mul_left _ _)
  have hcc : IsCoprime c₁ c₂ := hl₂.of_isCoprime_of_dvd_right (by
    rw [show s₂ * c₂ * n₂ = c₂ * (s₂ * n₂) by ring]; exact dvd_mul_right _ _)
  -- the indices
  have hA₁ := primary_mul hc₁ (primary_pow hn₁ 3)
  have hA₂ := primary_mul hc₂ (primary_pow hn₂ 3)
  have hA₁2 : IsCoprime (c₁ * n₁ ^ 3) 2 := hc₁2.mul_left hn₁2.pow_left
  have hA₂2 : IsCoprime (c₂ * n₂ ^ 3) 2 := hc₂2.mul_left hn₂2.pow_left
  have hM : IsCoprime (s₁ * (c₁ * n₁ ^ 3)) (s₂ * (c₂ * n₂ ^ 3)) := by
    have h3 := h.pow (m := 3) (n := 3)
    refine (h3.of_isCoprime_of_dvd_left ?_).of_isCoprime_of_dvd_right ?_
    · exact ⟨s₁ ^ 2 * c₁ ^ 2, by ring⟩
    · exact ⟨s₂ ^ 2 * c₂ ^ 2, by ring⟩
  have hodd := fun {x : O} (hx : IsCoprime x 2) => not_mem_two_of_isCoprime hx
  have hA : c₁ * c₂ * (n₁ * n₂) ^ 3 = c₁ * n₁ ^ 3 * (c₂ * n₂ ^ 3) := by ring
  unfold correctedCoeff
  rw [poissonCoeff_congr_index (s₁ * s₂) hA H, hA,
    poissonCoeff_mul_reciprocity hs₁ hs₂ hA₁ hA₂ hs₁2 hs₂2 hA₁2 hA₂2 hM H,
    thetaGauss_mul c₁ c₂ hcc, thetaPhase_mul (hodd hA₁2) (hodd hA₂2),
    quadraticPhase_mul_left (hodd hA₁2) (hodd hA₂2) (hodd (hs₁2.mul_left hs₂2)),
    quadraticPhase_mul_right (hodd hA₁2) (hodd hs₁2) (hodd hs₂2),
    quadraticPhase_mul_right (hodd hA₂2) (hodd hs₁2) (hodd hs₂2)]
  have hP := pairPhase_eq_one hc₁ hn₁ hc₂ hn₂ hc₁2 hn₁2 hc₂2 hn₂2 hcn
  have h12 := quadraticPhase_sq (hodd hA₁2) (hodd hs₂2)
  have h21 := quadraticPhase_sq (hodd hA₂2) (hodd hs₁2)
  set RHS := quadraticPhase (c₁ * n₁ ^ 3) s₁ * (thetaGauss c₁ * thetaPhase (c₁ * n₁ ^ 3)) *
    poissonCoeff s₁ (c₁ * n₁ ^ 3) H * (quadraticPhase (c₂ * n₂ ^ 3) s₂ *
      (thetaGauss c₂ * thetaPhase (c₂ * n₂ ^ 3)) * poissonCoeff s₂ (c₂ * n₂ ^ 3) H)
  linear_combination RHS * quadraticPhase (c₁ * n₁ ^ 3) s₂ ^ 2 *
      quadraticPhase (c₂ * n₂ ^ 3) s₁ ^ 2 * hP +
    RHS * quadraticPhase (c₁ * n₁ ^ 3) s₂ ^ 2 * h21 + RHS * h12

end GaloisForLFunctions.FamilyContinuationTheory
