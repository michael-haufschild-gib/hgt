import GaloisForLFunctions.RHTower.Sieve.MaynardRStarFirstAlternative

/-!
# Route-T coverage from global additive-energy bounds

For the deficit-matched moment parameter, Maynard's full high-amplitude case split collapses to
two global Heath--Brown additive-energy exponents.  Below the transition, a global `R*` bound is
the third alternative.  Above it, diagonal energy turns the same bound into the first alternative.
Together with the trivial low-amplitude count and endpoint exclusion, this removes all
complementary-Montgomery length geometry from the Route-T receiver.
-/

noncomputable section

namespace RHTower.Sieve

/-- Heath--Brown's global additive-energy exponent below amplitude `3/4`. -/
def maynardHB3Exponent (sigma : ℝ) : ℝ := (15 - 16 * sigma) / 2

/-- Heath--Brown's global additive-energy exponent above amplitude `3/4`. -/
def maynardHB4Exponent (sigma : ℝ) : ℝ :=
  12 * (1 - sigma) / (4 * sigma - 1)

/-- Heath--Brown's global count exponent above amplitude `25/28`. -/
def maynardHB2CountExponent (sigma : ℝ) : ℝ :=
  4 * (1 - sigma) / (4 * sigma - 1)

/-- Montgomery's global count exponent below amplitude `3/4`. -/
def maynardMontgomeryCountExponent (sigma : ℝ) : ℝ :=
  3 * (1 - sigma) / (2 - sigma)

/-- The narrow interval between the trivial-count threshold and `3/4` is covered by the lower
global additive-energy exponent. -/
theorem routeT_HB3_exponent_le_third_alternative
    {mu sigma : ℝ}
    (hmu : 4 / 3 ≤ mu)
    (hsigmaLo : (1 + routeTGapMomentNu) / 2 ≤ sigma)
    (hsigmaHi : sigma ≤ 3 / 4) :
    maynardHB3Exponent sigma ≤
      1 + mu * (3 + routeTGapMomentNu - 4 * sigma) := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : maynardLongGlobalAmplitudeDeficit < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hb : 0 ≤ 3 + routeTGapMomentNu - 4 * sigma := by
    dsimp only [routeTGapMomentNu]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hmu hb
  dsimp only [maynardHB3Exponent, routeTGapMomentNu]
  dsimp only [routeTGapMomentNu] at hsigmaLo hmul
  nlinarith

/-- The thin interval not covered by the trivial count is far inside Montgomery's global count
range.  Its exponent is already smaller than Route-T alternative (ii). -/
theorem routeT_montgomery_exponent_le_second_alternative
    {mu sigma : ℝ}
    (hmuHi : mu ≤ 19 / 9)
    (hsigmaLo : (1 + routeTGapMomentNu) / 2 ≤ sigma)
    (hsigmaHi : sigma ≤ 3 / 4) :
    maynardMontgomeryCountExponent sigma ≤
      1 + mu * (1 + routeTGapMomentNu - 2 * sigma) := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let q : ℝ := 1 + routeTGapMomentNu - 2 * sigma
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hden : 0 < 2 - sigma := by linarith
  have hsigmaFiveSevenths : 5 / 7 ≤ sigma := by
    dsimp only [routeTGapMomentNu] at hsigmaLo
    linarith [maynardLongGlobalAmplitudeDeficit_lt_one_hundredth]
  have hmont : maynardMontgomeryCountExponent sigma ≤ 2 / 3 := by
    dsimp only [maynardMontgomeryCountExponent]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hqnonpos : q ≤ 0 := by
    dsimp only [q]
    linarith
  have hqlower : -d / 2 ≤ q := by
    dsimp only [q, d, routeTGapMomentNu]
    linarith
  have hmuq : (19 / 9 : ℝ) * q ≤ mu * q :=
    mul_le_mul_of_nonpos_right hmuHi hqnonpos
  have hqscaled : -(19 / 18 : ℝ) * d ≤ (19 / 9 : ℝ) * q := by
    nlinarith
  dsimp only [q] at hmuq
  nlinarith

/-- Above `3/4` and below the fixed endpoint, the upper global additive-energy exponent always
lands in one of the two useful regions: it either square-roots to the first alternative or is
already no larger than the third-alternative exponent. -/
theorem routeT_HB4_exponent_first_or_third
    {mu sigma : ℝ}
    (hmuLo : 4 / 3 ≤ mu)
    (hsigmaLo : 3 / 4 ≤ sigma)
    (hsigmaHi : sigma ≤ 1 - maynardLongGlobalAmplitudeDeficit) :
    maynardHB4Exponent sigma ≤ 2 * mu * (1 - sigma) ∨
      maynardHB4Exponent sigma ≤
        1 + mu * (3 + routeTGapMomentNu - 4 * sigma) := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let den : ℝ := 4 * sigma - 1
  let delta : ℝ := 1 - sigma
  let b : ℝ := 7 / 2 - d / 2 - 4 * sigma
  have hd : 0 < d := by
    exact maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < 1 / 100 := by
    exact maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hden : 0 < den := by
    dsimp only [den]
    linarith
  have hdelta : 0 ≤ delta := by
    dsimp only [delta, d] at hsigmaHi ⊢
    linarith [maynardLongGlobalAmplitudeDeficit_pos]
  have hd_delta : d ≤ delta := by
    dsimp only [delta, d] at hsigmaHi ⊢
    linarith
  have hdelta_quarter : delta ≤ 1 / 4 := by
    dsimp only [delta]
    linarith
  have htarget :
      3 + routeTGapMomentNu - 4 * sigma = b := by
    dsimp only [b, d, routeTGapMomentNu]
    ring
  rw [htarget]
  change 12 * delta / den ≤ 2 * mu * delta ∨
    12 * delta / den ≤ 1 + mu * b
  by_cases hmuLarge : 6 / den ≤ mu
  · left
    have hmuLarge' : 6 ≤ mu * den := (div_le_iff₀ hden).mp hmuLarge
    have hscaled : (2 * delta) * 6 ≤ (2 * delta) * (mu * den) :=
      mul_le_mul_of_nonneg_left hmuLarge' (mul_nonneg (by norm_num) hdelta)
    apply (div_le_iff₀ hden).2
    nlinarith
  · right
    have hmuSmall : mu < 6 / den := lt_of_not_ge hmuLarge
    by_cases hb : 0 ≤ b
    · have hmuProduct := mul_le_mul_of_nonneg_right hmuLo hb
      have hquad : 0 ≤ delta * (1 / 4 - delta) :=
        mul_nonneg hdelta (sub_nonneg.mpr hdelta_quarter)
      have hddelta : 0 ≤ d * delta := mul_nonneg hd.le hdelta
      have hbase : 12 * delta / den ≤ 1 + (4 / 3 : ℝ) * b := by
        apply (div_le_iff₀ hden).2
        dsimp only [den, delta, b] at hquad hddelta ⊢
        nlinarith
      exact hbase.trans (by linarith)
    · have hbneg : b < 0 := lt_of_not_ge hb
      have hmuProduct :=
        mul_le_mul_of_nonpos_right (le_of_lt hmuSmall) hbneg.le
      have hbase : 12 * delta / den ≤ 1 + (6 / den) * b := by
        apply (div_le_iff₀ hden).2
        have hdenne : den ≠ 0 := hden.ne'
        field_simp [hdenne]
        dsimp only [den, delta, b] at hd_delta ⊢
        nlinarith
      exact hbase.trans (by linarith)

/-- The stronger count formulation: the upper global count exponent either is already the first
alternative, or its universal cube `R* ≤ R^3` is the third alternative. -/
theorem routeT_HB2_exponent_first_or_cube_third
    {mu sigma : ℝ}
    (hmuLo : 4 / 3 ≤ mu)
    (hsigmaLo : 3 / 4 ≤ sigma)
    (hsigmaHi : sigma ≤ 1) :
    maynardHB2CountExponent sigma ≤ mu * (1 - sigma) ∨
      3 * maynardHB2CountExponent sigma ≤
        1 + mu * (3 + routeTGapMomentNu - 4 * sigma) := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let den : ℝ := 4 * sigma - 1
  let delta : ℝ := 1 - sigma
  let b : ℝ := 7 / 2 - d / 2 - 4 * sigma
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hden : 0 < den := by
    dsimp only [den]
    linarith
  have hdelta : 0 ≤ delta := by
    dsimp only [delta] at hsigmaHi ⊢
    linarith
  have hdelta_quarter : delta ≤ 1 / 4 := by
    dsimp only [delta]
    linarith
  have htarget : 3 + routeTGapMomentNu - 4 * sigma = b := by
    dsimp only [b, d, routeTGapMomentNu]
    ring
  rw [htarget]
  change 4 * delta / den ≤ mu * delta ∨
    3 * (4 * delta / den) ≤ 1 + mu * b
  have hcube : 3 * (4 * delta / den) = 12 * delta / den := by ring
  rw [hcube]
  by_cases hmuLarge : 4 / den ≤ mu
  · left
    have hmuLarge' : 4 ≤ mu * den := (div_le_iff₀ hden).mp hmuLarge
    have hscaled : delta * 4 ≤ delta * (mu * den) :=
      mul_le_mul_of_nonneg_left hmuLarge' hdelta
    apply (div_le_iff₀ hden).2
    nlinarith
  · right
    have hmuSmall : mu < 4 / den := lt_of_not_ge hmuLarge
    by_cases hb : 0 ≤ b
    · have hmuProduct := mul_le_mul_of_nonneg_right hmuLo hb
      have hquad : 0 ≤ delta * (1 / 4 - delta) :=
        mul_nonneg hdelta (sub_nonneg.mpr hdelta_quarter)
      have hddelta : 0 ≤ d * delta := mul_nonneg hd.le hdelta
      have hbase : 12 * delta / den ≤ 1 + (4 / 3 : ℝ) * b := by
        apply (div_le_iff₀ hden).2
        dsimp only [den, delta, b] at hquad hddelta ⊢
        nlinarith
      exact hbase.trans (by linarith)
    · have hbneg : b < 0 := lt_of_not_ge hb
      have hmuProduct :=
        mul_le_mul_of_nonpos_right (le_of_lt hmuSmall) hbneg.le
      have hbase : 12 * delta / den ≤ 1 + (4 / den) * b := by
        apply (div_le_iff₀ hden).2
        have hdenne : den ≠ 0 := hden.ne'
        field_simp [hdenne]
        dsimp only [den, delta, b] at hdsmall ⊢
        nlinarith
      exact hbase.trans (by linarith)

/-- Below the trivial-count threshold, cardinality at most height is already Maynard's second
alternative. -/
theorem routeT_trivial_count_second_alternative
    {R T x sigma : ℝ}
    (hT : 0 ≤ T) (hx : 1 ≤ x) (hR : R ≤ T)
    (hsigma : sigma ≤ (1 + routeTGapMomentNu) / 2) :
    R ≤ T * x ^ (1 + routeTGapMomentNu - 2 * sigma) := by
  have hexp : 0 ≤ 1 + routeTGapMomentNu - 2 * sigma := by linarith
  have hone : 1 ≤ x ^ (1 + routeTGapMomentNu - 2 * sigma) :=
    Real.one_le_rpow hx hexp
  exact hR.trans (by nlinarith)

/-- Receiver-facing three-way alternative. -/
def IsRouteTMaynardTripleAlternative
    (R Rstar T x sigma : ℝ) : Prop :=
  R ≤ x ^ (1 - sigma) ∨
    R ≤ T * x ^ (1 + routeTGapMomentNu - 2 * sigma) ∨
      Rstar ≤ T * x ^ (3 + routeTGapMomentNu - 4 * sigma)

theorem routeT_height_scale_identity
    {T x mu e : ℝ} (hT : 1 ≤ T) (hx : x = T ^ mu) :
    T * x ^ e = T ^ (1 + mu * e) := by
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  calc
    T * x ^ e = T * (T ^ mu) ^ e := by rw [hx]
    _ = T * T ^ (mu * e) := by rw [← Real.rpow_mul hT0]
    _ = T ^ (1 : ℝ) * T ^ (mu * e) := by rw [Real.rpow_one]
    _ = T ^ (1 + mu * e) := (Real.rpow_add hTpos 1 (mu * e)).symm

/-- Convert an additive-energy height exponent directly to Maynard's third alternative. -/
theorem routeT_third_alternative_of_height_exponent
    {Rstar T x mu sigma e : ℝ}
    (hT : 1 ≤ T) (hx : x = T ^ mu)
    (hRstar : Rstar ≤ T ^ e)
    (hexp : e ≤ 1 + mu * (3 + routeTGapMomentNu - 4 * sigma)) :
    Rstar ≤ T * x ^ (3 + routeTGapMomentNu - 4 * sigma) := by
  rw [routeT_height_scale_identity hT hx]
  exact hRstar.trans (Real.rpow_le_rpow_of_exponent_le hT hexp)

/-- Convert a count height exponent directly to Maynard's second alternative. -/
theorem routeT_second_alternative_of_height_exponent
    {R T x mu sigma e : ℝ}
    (hT : 1 ≤ T) (hx : x = T ^ mu)
    (hR : R ≤ T ^ e)
    (hexp : e ≤ 1 + mu * (1 + routeTGapMomentNu - 2 * sigma)) :
    R ≤ T * x ^ (1 + routeTGapMomentNu - 2 * sigma) := by
  rw [routeT_height_scale_identity hT hx]
  exact hR.trans (Real.rpow_le_rpow_of_exponent_le hT hexp)

/-- Convert an additive-energy height exponent to the first alternative using only the diagonal
`R^2 ≤ R*`. -/
theorem routeT_first_alternative_of_rstar_height_exponent
    {R Rstar T x mu sigma e : ℝ}
    (hT : 1 ≤ T) (hx : x = T ^ mu) (hx1 : 1 ≤ x)
    (hdiag : R ^ 2 ≤ Rstar) (hRstar : Rstar ≤ T ^ e)
    (hexp : e ≤ 2 * mu * (1 - sigma)) :
    R ≤ x ^ (1 - sigma) := by
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
  have hsq : R ^ 2 ≤ (x ^ (1 - sigma)) ^ 2 := by
    calc
      R ^ 2 ≤ Rstar := hdiag
      _ ≤ T ^ e := hRstar
      _ ≤ T ^ (2 * mu * (1 - sigma)) :=
        Real.rpow_le_rpow_of_exponent_le hT hexp
      _ = x ^ (2 * (1 - sigma)) := by
        rw [hx, show 2 * mu * (1 - sigma) = mu * (2 * (1 - sigma)) by ring,
          Real.rpow_mul hT0]
      _ = (x ^ (1 - sigma)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
        norm_num
        congr 1
        ring
  exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hx0 _) hsq

/-- A direct count height exponent converts to the first alternative at ambient scale. -/
theorem routeT_first_alternative_of_count_height_exponent
    {R T x mu sigma e : ℝ}
    (hT : 1 ≤ T) (hx : x = T ^ mu)
    (hR : R ≤ T ^ e) (hexp : e ≤ mu * (1 - sigma)) :
    R ≤ x ^ (1 - sigma) := by
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  calc
    R ≤ T ^ e := hR
    _ ≤ T ^ (mu * (1 - sigma)) :=
      Real.rpow_le_rpow_of_exponent_le hT hexp
    _ = x ^ (1 - sigma) := by rw [hx, Real.rpow_mul hT0]

/-- Cubing a count estimate and using `R* ≤ R^3` produces the third alternative. -/
theorem routeT_third_alternative_of_count_cube
    {R Rstar T x mu sigma e : ℝ}
    (hR0 : 0 ≤ R) (hT : 1 ≤ T) (hx : x = T ^ mu)
    (hRstarCube : Rstar ≤ R ^ 3) (hR : R ≤ T ^ e)
    (hexp : 3 * e ≤ 1 + mu * (3 + routeTGapMomentNu - 4 * sigma)) :
    Rstar ≤ T * x ^ (3 + routeTGapMomentNu - 4 * sigma) := by
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hpow : R ^ 3 ≤ (T ^ e) ^ 3 :=
    pow_le_pow_left₀ hR0 hR 3
  have hcube : (T ^ e) ^ 3 = T ^ (3 * e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]
    norm_num
    congr 1
    ring
  rw [routeT_height_scale_identity hT hx]
  exact hRstarCube.trans (hpow.trans_eq hcube) |>.trans
    (Real.rpow_le_rpow_of_exponent_le hT hexp)

/-- **Complete algebraic coverage.**  Once the two global Heath--Brown `R*` height bounds are
available, only endpoint first-alternative input remains.  No factor-length case split or
complementary Montgomery hypothesis occurs. -/
theorem routeT_triple_alternative_of_global_rstar
    {R Rstar T x mu sigma : ℝ}
    (hT : 1 ≤ T) (hx : x = T ^ mu) (hx1 : 1 ≤ x)
    (hmuLo : 4 / 3 ≤ mu)
    (hRheight : R ≤ T) (hdiag : R ^ 2 ≤ Rstar)
    (hHB3 : Rstar ≤ T ^ maynardHB3Exponent sigma)
    (hHB4 : Rstar ≤ T ^ maynardHB4Exponent sigma)
    (hendpoint : 1 - maynardLongGlobalAmplitudeDeficit < sigma →
      R ≤ x ^ (1 - sigma)) :
    IsRouteTMaynardTripleAlternative R Rstar T x sigma := by
  by_cases hlow : sigma ≤ (1 + routeTGapMomentNu) / 2
  · exact Or.inr (Or.inl
      (routeT_trivial_count_second_alternative
        (le_trans (by norm_num) hT) hx1 hRheight hlow))
  have hlow' : (1 + routeTGapMomentNu) / 2 ≤ sigma := le_of_not_ge hlow
  by_cases hthree : sigma ≤ 3 / 4
  · right
    right
    exact routeT_third_alternative_of_height_exponent hT hx hHB3
      (routeT_HB3_exponent_le_third_alternative hmuLo hlow' hthree)
  have hthree' : 3 / 4 ≤ sigma := le_of_not_ge hthree
  by_cases hend : sigma ≤ 1 - maynardLongGlobalAmplitudeDeficit
  · rcases routeT_HB4_exponent_first_or_third hmuLo hthree' hend with
      hfirst | hthird
    · exact Or.inl
        (routeT_first_alternative_of_rstar_height_exponent
          hT hx hx1 hdiag hHB4 hfirst)
    · exact Or.inr (Or.inr
        (routeT_third_alternative_of_height_exponent hT hx hHB4 hthird))
  · exact Or.inl (hendpoint (lt_of_not_ge hend))

/-- Stronger capstone: above `3/4`, only the global Heath--Brown count exponent and the universal
energy cube are needed.  Genuine `R*` analysis remains confined to the thin interval between the
trivial threshold and `3/4`. -/
theorem routeT_triple_alternative_of_global_count
    {R Rstar T x mu sigma : ℝ}
    (hR0 : 0 ≤ R) (hT : 1 ≤ T) (hx : x = T ^ mu) (hx1 : 1 ≤ x)
    (hmuLo : 4 / 3 ≤ mu)
    (hRheight : R ≤ T) (hRstarCube : Rstar ≤ R ^ 3)
    (hHB3 : Rstar ≤ T ^ maynardHB3Exponent sigma)
    (hHB2 : R ≤ T ^ maynardHB2CountExponent sigma)
    (hendpoint : 1 - maynardLongGlobalAmplitudeDeficit < sigma →
      R ≤ x ^ (1 - sigma)) :
    IsRouteTMaynardTripleAlternative R Rstar T x sigma := by
  by_cases hlow : sigma ≤ (1 + routeTGapMomentNu) / 2
  · exact Or.inr (Or.inl
      (routeT_trivial_count_second_alternative
        (le_trans (by norm_num) hT) hx1 hRheight hlow))
  have hlow' : (1 + routeTGapMomentNu) / 2 ≤ sigma := le_of_not_ge hlow
  by_cases hthree : sigma ≤ 3 / 4
  · exact Or.inr (Or.inr
      (routeT_third_alternative_of_height_exponent hT hx hHB3
        (routeT_HB3_exponent_le_third_alternative hmuLo hlow' hthree)))
  have hthree' : 3 / 4 ≤ sigma := le_of_not_ge hthree
  by_cases hsigmaOne : sigma ≤ 1
  · rcases routeT_HB2_exponent_first_or_cube_third hmuLo hthree' hsigmaOne with
      hfirst | hthird
    · exact Or.inl
        (routeT_first_alternative_of_count_height_exponent hT hx hHB2 hfirst)
    · exact Or.inr (Or.inr
        (routeT_third_alternative_of_count_cube
          hR0 hT hx hRstarCube hHB2 hthird))
  · exact Or.inl (hendpoint (by
      have hd := maynardLongGlobalAmplitudeDeficit_pos
      linarith [lt_of_not_ge hsigmaOne]))

/-- **Minimal count-only coverage.**  Global Montgomery below `3/4`, global Heath--Brown count
above `3/4`, universal `R* ≤ R^3`, and Route-T endpoint exclusion imply the complete receiver
alternative.  No nontrivial upper estimate for `R*` remains. -/
theorem routeT_triple_alternative_of_global_count_only
    {R Rstar T x mu sigma : ℝ}
    (hR0 : 0 ≤ R) (hT : 1 ≤ T) (hx : x = T ^ mu) (hx1 : 1 ≤ x)
    (hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 19 / 9)
    (hRheight : R ≤ T) (hRstarCube : Rstar ≤ R ^ 3)
    (hMont : R ≤ T ^ maynardMontgomeryCountExponent sigma)
    (hHB2 : R ≤ T ^ maynardHB2CountExponent sigma)
    (hendpoint : 1 - maynardLongGlobalAmplitudeDeficit < sigma →
      R ≤ x ^ (1 - sigma)) :
    IsRouteTMaynardTripleAlternative R Rstar T x sigma := by
  by_cases hlow : sigma ≤ (1 + routeTGapMomentNu) / 2
  · exact Or.inr (Or.inl
      (routeT_trivial_count_second_alternative
        (le_trans (by norm_num) hT) hx1 hRheight hlow))
  have hlow' : (1 + routeTGapMomentNu) / 2 ≤ sigma := le_of_not_ge hlow
  by_cases hthree : sigma ≤ 3 / 4
  · exact Or.inr (Or.inl
      (routeT_second_alternative_of_height_exponent hT hx hMont
        (routeT_montgomery_exponent_le_second_alternative hmuHi hlow' hthree)))
  have hthree' : 3 / 4 ≤ sigma := le_of_not_ge hthree
  by_cases hsigmaOne : sigma ≤ 1
  · rcases routeT_HB2_exponent_first_or_cube_third hmuLo hthree' hsigmaOne with
      hfirst | hthird
    · exact Or.inl
        (routeT_first_alternative_of_count_height_exponent hT hx hHB2 hfirst)
    · exact Or.inr (Or.inr
        (routeT_third_alternative_of_count_cube
          hR0 hT hx hRstarCube hHB2 hthird))
  · exact Or.inl (hendpoint (by
      have hd := maynardLongGlobalAmplitudeDeficit_pos
      linarith [lt_of_not_ge hsigmaOne]))

end RHTower.Sieve
