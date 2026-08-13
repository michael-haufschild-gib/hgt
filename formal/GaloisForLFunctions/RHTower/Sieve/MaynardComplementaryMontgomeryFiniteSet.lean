import GaloisForLFunctions.RHTower.Sieve.MaynardMontgomeryFiniteSet

/-!
# Complementary Montgomery without amplitude coloring

A large product does not require either factor to be uniformly large.  If

`V ≤ |F(λ)| |G(λ)|`

on a finite separated set, summing the product lower bound and applying Cauchy--Schwarz gives

`(|S| V)² ≤ (∑ |F(λ)|²) (∑ |G(λ)|²)`.

This is the literal form of complementary Montgomery needed by Route T.  It retains both halves
of a Heath--Brown product and avoids discretizing their continuously varying local amplitudes.
-/

noncomputable section
namespace RHTower.Sieve

open Finset

/-- **Finite complementary Cauchy count.**  Pointwise largeness of a product, together with two
independent mean-square bounds, controls the square of the point count. -/
theorem finset_card_mul_productFloor_sq_le
    {S : Finset ℕ} {f g : ℕ → ℝ} {V A B : ℝ}
    (hV : 0 ≤ V)
    (hlarge : ∀ r ∈ S, V ≤ f r * g r)
    (hA : ∑ r ∈ S, (f r) ^ 2 ≤ A)
    (hB : ∑ r ∈ S, (g r) ^ 2 ≤ B) :
    (((S.card : ℝ) * V) ^ 2) ≤ A * B := by
  have hcount : (S.card : ℝ) * V ≤ ∑ r ∈ S, f r * g r := by
    calc
      (S.card : ℝ) * V = ∑ _r ∈ S, V := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ S, f r * g r := Finset.sum_le_sum hlarge
  have hcount0 : 0 ≤ (S.card : ℝ) * V := mul_nonneg (by positivity) hV
  have hsquares : ((S.card : ℝ) * V) ^ 2 ≤
      (∑ r ∈ S, f r * g r) ^ 2 :=
    pow_le_pow_left₀ hcount0 hcount 2
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq S f g
  have hsumF0 : 0 ≤ ∑ r ∈ S, (f r) ^ 2 :=
    Finset.sum_nonneg fun r _hr => sq_nonneg (f r)
  have hsumG0 : 0 ≤ ∑ r ∈ S, (g r) ^ 2 :=
    Finset.sum_nonneg fun r _hr => sq_nonneg (g r)
  have hA0 : 0 ≤ A := hsumF0.trans hA
  calc
    ((S.card : ℝ) * V) ^ 2 ≤
        (∑ r ∈ S, f r * g r) ^ 2 := hsquares
    _ ≤ (∑ r ∈ S, (f r) ^ 2) * ∑ r ∈ S, (g r) ^ 2 := hcauchy
    _ ≤ A * B := mul_le_mul hA hB hsumG0 hA0

/-- Complementary Cauchy count for two Dirichlet polynomials, from arbitrary mean-square
bounds.  No separate lower threshold for either factor is assumed. -/
theorem card_mul_dirPoly_productFloor_sq_le_of_bounds
    (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    {S : Finset ℕ} {lam : ℕ → ℝ} {V A B : ℝ}
    (hV : 0 ≤ V)
    (hlarge : ∀ r ∈ S,
      V ≤ ‖dirPoly N a (lam r)‖ * ‖dirPoly M b (lam r)‖)
    (hA : ∑ r ∈ S, ‖dirPoly N a (lam r)‖ ^ 2 ≤ A)
    (hB : ∑ r ∈ S, ‖dirPoly M b (lam r)‖ ^ 2 ≤ B) :
    (((S.card : ℝ) * V) ^ 2) ≤ A * B := by
  exact finset_card_mul_productFloor_sq_le hV
    hlarge hA hB

/-- **Complementary finite-set Montgomery theorem.**  The two mean-value estimates are applied
directly to a common separated set.  Product largeness is retained pointwise, so no amplitude
bins and no union bound over factor thresholds occur. -/
theorem complementary_dirPoly_montgomery_finset
    (N M : ℕ) (hN : 2 ≤ N) (hM : 2 ≤ M)
    (a : Fin N → ℂ) (b : Fin M → ℂ)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hlarge : ∀ r ∈ S,
      V ≤ ‖dirPoly N a (lam r)‖ * ‖dirPoly M b (lam r)‖) :
    (((S.card : ℝ) * V) ^ 2) ≤
      ((T + 4 * (N : ℝ) * (1 + Real.log N)) *
          (1 / delta + 2 * Real.log N) * ∑ n : Fin N, ‖a n‖ ^ 2) *
        ((T + 4 * (M : ℝ) * (1 + Real.log M)) *
          (1 / delta + 2 * Real.log M) * ∑ m : Fin M, ‖b m‖ ^ 2) := by
  exact card_mul_dirPoly_productFloor_sq_le_of_bounds N M a b hV hlarge
    (largeValues_dirPoly_finset N hN a hdelta hT hgap hband)
    (largeValues_dirPoly_finset M hM b hdelta hT hgap hband)

/-- Mean-square form of literal grouped-factor Montgomery on an arbitrary color fibre.  Unlike
the count theorem, this keeps the full square sum so it can be paired with a complementary group. -/
theorem meanSquare_heathBrown_grouped_finset
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {sigma G : ℝ} (hsigma : 0 ≤ sigma)
    (henergy : ∑ j : Fin (groupedDyadicUpper q),
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 ≤ G)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T) :
    ∑ r ∈ S,
        ‖∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖ ^ 2 ≤
      (T + 4 * (groupedDyadicUpper q : ℝ) *
          (1 + Real.log (groupedDyadicUpper q))) *
        (1 / delta + 2 * Real.log (groupedDyadicUpper q)) *
        (((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G) := by
  let F : ι → ArithmeticFunction ℝ := fun i => heathBrownFactorBase L X (kind i)
  let b : Fin (groupedDyadicUpper q) → ℂ :=
    sigmaWeightedCoeff (groupedDyadicUpper q) (groupedDyadicCoeffVector F q) sigma
  let a : Fin (groupedDyadicUpper q) → ℂ := fun j => (starRingEnd ℂ) (b j)
  have hpoint : ∀ r : ℕ,
      ‖dirPoly (groupedDyadicUpper q) a (lam r)‖ =
        ‖∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖ := by
    intro r
    rw [show dirPoly (groupedDyadicUpper q) a (lam r) =
      (starRingEnd ℂ) (dirPoly (groupedDyadicUpper q) b (-lam r)) by
        exact dirPoly_conj_neg (groupedDyadicUpper q) b (lam r)]
    rw [RCLike.norm_conj]
    rw [show dirPoly (groupedDyadicUpper q) b (-lam r) =
      ∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I) by
      exact dirPoly_groupedDyadicCoeffVector_eq_product F q sigma (lam r)]
  have hbase := largeValues_dirPoly_finset (groupedDyadicUpper q)
    (two_le_groupedDyadicUpper q) a hdelta hT hgap hband
  have hnorm : ∑ j : Fin (groupedDyadicUpper q), ‖a j‖ ^ 2 =
      ∑ j : Fin (groupedDyadicUpper q), ‖b j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [RCLike.norm_conj]
  have hsum :
      (∑ r ∈ S,
        ‖∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖ ^ 2) =
      ∑ r ∈ S, ‖dirPoly (groupedDyadicUpper q) a (lam r)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [hpoint r]
  rw [hsum]
  rw [hnorm] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (sum_normSq_sigmaWeighted_grouped_le F q hsigma henergy) (by positivity))

/-- **Literal complementary grouped-factor Montgomery.**  Two disjoint grouped products may vary
arbitrarily in relative amplitude across the fibre.  Their pointwise product threshold and their
two coefficient energies alone give the squared count bound. -/
theorem complementary_heathBrown_grouped_montgomery_finset
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (L X : ℕ)
    (kind₁ : ι → HeathBrownFactorKind) (q₁ : ι → ℕ)
    (kind₂ : κ → HeathBrownFactorKind) (q₂ : κ → ℕ)
    {sigma G₁ G₂ : ℝ} (hsigma : 0 ≤ sigma)
    (henergy₁ : ∑ j : Fin (groupedDyadicUpper q₁),
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind₁ i)) q₁ j‖ ^ 2 ≤ G₁)
    (henergy₂ : ∑ j : Fin (groupedDyadicUpper q₂),
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind₂ i)) q₂ j‖ ^ 2 ≤ G₂)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hlarge : ∀ r ∈ S, V ≤
      ‖∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind₁ i)) (q₁ i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖ *
      ‖∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind₂ i)) (q₂ i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖) :
    (((S.card : ℝ) * V) ^ 2) ≤
      ((T + 4 * (groupedDyadicUpper q₁ : ℝ) *
          (1 + Real.log (groupedDyadicUpper q₁))) *
        (1 / delta + 2 * Real.log (groupedDyadicUpper q₁)) *
        (((groupedDyadicLower q₁ : ℝ) ^ (-sigma)) ^ 2 * G₁)) *
      ((T + 4 * (groupedDyadicUpper q₂ : ℝ) *
          (1 + Real.log (groupedDyadicUpper q₂))) *
        (1 / delta + 2 * Real.log (groupedDyadicUpper q₂)) *
        (((groupedDyadicLower q₂ : ℝ) ^ (-sigma)) ^ 2 * G₂)) := by
  exact finset_card_mul_productFloor_sq_le hV hlarge
    (meanSquare_heathBrown_grouped_finset L X kind₁ q₁ hsigma henergy₁
      hdelta hT hgap hband)
    (meanSquare_heathBrown_grouped_finset L X kind₂ q₂ hsigma henergy₂
      hdelta hT hgap hband)

/-- Receiver extraction from a complementary squared count.  This is the exact cancellation
behind Route T's first alternative: the Perron abscissa disappears from the quotient. -/
theorem complementary_count_sq_to_first_alternative
    {R C x sigma c : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hcount : (R * x ^ (sigma - c)) ^ 2 ≤
      (C * x ^ (1 - c)) ^ 2) :
    R ≤ C * x ^ (1 - sigma) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hleft0 : 0 ≤ R * x ^ (sigma - c) :=
    mul_nonneg hR (Real.rpow_nonneg hx0.le _)
  have hright0 : 0 ≤ C * x ^ (1 - c) :=
    mul_nonneg hC (Real.rpow_nonneg hx0.le _)
  have hroot : R * x ^ (sigma - c) ≤ C * x ^ (1 - c) :=
    le_of_pow_le_pow_left₀ (by norm_num) hright0 hcount
  have hpow : 0 < x ^ (sigma - c) := Real.rpow_pos_of_pos hx0 _
  have hfactor : C * x ^ (1 - c) =
      (C * x ^ (1 - sigma)) * x ^ (sigma - c) := by
    rw [show (1 : ℝ) - c = (1 - sigma) + (sigma - c) by ring,
      Real.rpow_add hx0]
    ring
  rw [hfactor] at hroot
  exact (mul_le_mul_iff_of_pos_right hpow).mp hroot

/-- Receiver extraction when both complementary mean squares are height-dominated.  The Perron
abscissa again cancels, leaving the balanced exponent `1/2 - sigma`. -/
theorem complementary_count_sq_to_height_alternative
    {R C T x sigma c : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hx : 1 ≤ x)
    (hcount : (R * x ^ (sigma - c)) ^ 2 ≤
      (C * T * x ^ (1 / 2 - c)) ^ 2) :
    R ≤ C * T * x ^ (1 / 2 - sigma) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hright0 : 0 ≤ C * T * x ^ (1 / 2 - c) :=
    mul_nonneg (mul_nonneg hC hT) (Real.rpow_nonneg hx0.le _)
  have hroot : R * x ^ (sigma - c) ≤ C * T * x ^ (1 / 2 - c) :=
    le_of_pow_le_pow_left₀ (by norm_num) hright0 hcount
  have hpow : 0 < x ^ (sigma - c) := Real.rpow_pos_of_pos hx0 _
  have hfactor : C * T * x ^ (1 / 2 - c) =
      (C * T * x ^ (1 / 2 - sigma)) * x ^ (sigma - c) := by
    rw [show (1 / 2 : ℝ) - c = (1 / 2 - sigma) + (sigma - c) by ring,
      Real.rpow_add hx0]
    ring
  rw [hfactor] at hroot
  exact (mul_le_mul_iff_of_pos_right hpow).mp hroot

/-- The balanced height exponent lies inside Route T's second alternative throughout the overlap
band.  A multiplicative analytic cost `C` is retained for later reserve absorption. -/
theorem complementary_count_sq_to_routeT_second
    {R C T x sigma c nu : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hx : 1 ≤ x)
    (hsigma : sigma ≤ 1 / 2 + nu)
    (hcount : (R * x ^ (sigma - c)) ^ 2 ≤
      (C * T * x ^ (1 / 2 - c)) ^ 2) :
    R ≤ C * (T * x ^ (1 + nu - 2 * sigma)) := by
  have hbalanced := complementary_count_sq_to_height_alternative
    hC hT hx hcount
  have hexp : 1 / 2 - sigma ≤ 1 + nu - 2 * sigma := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hx hexp
  calc
    R ≤ C * T * x ^ (1 / 2 - sigma) := hbalanced
    _ ≤ C * T * x ^ (1 + nu - 2 * sigma) := by
      gcongr
    _ = C * (T * x ^ (1 + nu - 2 * sigma)) := by ring

end RHTower.Sieve
