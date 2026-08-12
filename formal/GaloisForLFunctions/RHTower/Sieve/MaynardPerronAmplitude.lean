import GaloisForLFunctions.RHTower.Sieve.MaynardFibreCount

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-! Scratch: separate Perron abscissa from Maynard amplitude exponent. -/

theorem weighted_huxley_term_eq_amplitude
    {D G c delta H : ℝ} (hD : 0 < D) (hdelta : 0 < delta) :
    ((D ^ (-c)) ^ 2 * G) * (D + (12 * Real.pi * D / delta) * H) =
      G * (1 + (12 * Real.pi / delta) * H) * D ^ (1 - 2 * c) := by
  have hweight : (D ^ (-c)) ^ 2 * D = D ^ (1 - 2 * c) := by
    have hsquare : (D ^ (-c)) ^ 2 = D ^ (-2 * c) := by
      calc
        (D ^ (-c)) ^ 2 = Real.rpow (D ^ (-c)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = D ^ ((-c) * 2) := (Real.rpow_mul hD.le _ _).symm
        _ = D ^ (-2 * c) := by congr 1; ring
    rw [hsquare]
    calc
      D ^ (-2 * c) * D = D ^ (-2 * c) * D ^ (1 : ℝ) := by simp
      _ = D ^ (-2 * c + 1) := (Real.rpow_add hD _ _).symm
      _ = D ^ (1 - 2 * c) := by congr 1; ring
  have hfactor : D + (12 * Real.pi * D / delta) * H =
      D * (1 + (12 * Real.pi / delta) * H) := by field_simp
  rw [hfactor]
  calc
    (D ^ (-c)) ^ 2 * G * (D * (1 + (12 * Real.pi / delta) * H)) =
      G * ((D ^ (-c)) ^ 2 * D) * (1 + (12 * Real.pi / delta) * H) := by ring
    _ = G * D ^ (1 - 2 * c) * (1 + (12 * Real.pi / delta) * H) := by rw [hweight]
    _ = G * (1 + (12 * Real.pi / delta) * H) * D ^ (1 - 2 * c) := by ring

theorem weighted_huxley_absorption_at_amplitude
    {ι : Type*} [Fintype ι] (D : ι → ℕ) (B : ι → ℝ)
    {Y c alpha Graw Bmax : ℝ}
    (hY : 0 < Y) (hc : 0 ≤ c)
    (hD : ∀ r, Y ≤ (D r : ℝ))
    (hGraw : 0 ≤ Graw) (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Bmax)
    (hscale : 2 * (Fintype.card ι : ℝ) ^ 2 * Graw * Bmax ≤ Y ^ (2 * alpha)) :
    (Fintype.card ι : ℝ) *
        ∑ r : ι, ((((D r : ℝ) ^ (-c)) ^ 2 * Graw) * B r) ≤
      (Y ^ (alpha - c)) ^ 2 / 2 := by
  have hweight : ∀ r, (D r : ℝ) ^ (-c) ≤ Y ^ (-c) := by
    intro r
    have hDr : 0 < (D r : ℝ) := hY.trans_le (hD r)
    rw [Real.rpow_neg hDr.le, Real.rpow_neg hY.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hDr c)
      (Real.rpow_pos_of_pos hY c)).2
        (Real.rpow_le_rpow hY.le (hD r) hc)
  have hterm : ∀ r,
      (((D r : ℝ) ^ (-c)) ^ 2 * Graw) * B r ≤
        (Y ^ (-c)) ^ 2 * Graw * Bmax := by
    intro r
    have hDpow0 : 0 ≤ (D r : ℝ) ^ (-c) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hYpow0 : 0 ≤ Y ^ (-c) := Real.rpow_nonneg hY.le _
    have hsquare : ((D r : ℝ) ^ (-c)) ^ 2 ≤ (Y ^ (-c)) ^ 2 :=
      pow_le_pow_left₀ hDpow0 (hweight r) 2
    have hcoeff : ((D r : ℝ) ^ (-c)) ^ 2 * Graw ≤
        (Y ^ (-c)) ^ 2 * Graw :=
      mul_le_mul_of_nonneg_right hsquare hGraw
    calc
      (((D r : ℝ) ^ (-c)) ^ 2 * Graw) * B r
          ≤ ((Y ^ (-c)) ^ 2 * Graw) * B r :=
            mul_le_mul_of_nonneg_right hcoeff (hB r).1
      _ ≤ (Y ^ (-c)) ^ 2 * Graw * Bmax :=
            mul_le_mul_of_nonneg_left (hB r).2 (mul_nonneg (sq_nonneg _) hGraw)
  have hsum :
      ∑ r : ι, ((((D r : ℝ) ^ (-c)) ^ 2 * Graw) * B r) ≤
        (Fintype.card ι : ℝ) * ((Y ^ (-c)) ^ 2 * Graw * Bmax) := by
    calc
      ∑ r : ι, ((((D r : ℝ) ^ (-c)) ^ 2 * Graw) * B r)
          ≤ ∑ _r : ι, ((Y ^ (-c)) ^ 2 * Graw * Bmax) :=
            Finset.sum_le_sum fun r _hr => hterm r
      _ = (Fintype.card ι : ℝ) * ((Y ^ (-c)) ^ 2 * Graw * Bmax) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard0 : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hsumScaled := mul_le_mul_of_nonneg_left hsum hcard0
  have hscale' :
      (Fintype.card ι : ℝ) ^ 2 * Graw * Bmax ≤ Y ^ (2 * alpha) / 2 := by
    linarith
  have hweight0 : 0 ≤ (Y ^ (-c)) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hscale' hweight0
  have hthreshold :
      (Y ^ (alpha - c)) ^ 2 = Y ^ (2 * alpha) * (Y ^ (-c)) ^ 2 := by
    have hsquare (a : ℝ) : (Y ^ a) ^ 2 = Y ^ (2 * a) := by
      calc
        (Y ^ a) ^ 2 = Real.rpow (Y ^ a) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Y ^ (a * 2) := (Real.rpow_mul hY.le _ _).symm
        _ = Y ^ (2 * a) := by congr 1; ring
    rw [hsquare, hsquare]
    rw [show 2 * (alpha - c) = 2 * alpha + (-2 * c) by ring,
      Real.rpow_add hY]
    congr 1
    ring
  calc
    (Fintype.card ι : ℝ) *
        ∑ r : ι, ((((D r : ℝ) ^ (-c)) ^ 2 * Graw) * B r)
        ≤ (Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ) * ((Y ^ (-c)) ^ 2 * Graw * Bmax)) :=
            hsumScaled
    _ = (Y ^ (-c)) ^ 2 *
        ((Fintype.card ι : ℝ) ^ 2 * Graw * Bmax) := by ring
    _ ≤ (Y ^ (-c)) ^ 2 * (Y ^ (2 * alpha) / 2) := hscaled
    _ = (Y ^ (alpha - c)) ^ 2 / 2 := by rw [hthreshold]; ring

theorem exists_maynardEligibleSelection_raise_at_exponent
    (L X k : ℕ) {T0 t e mu : ℝ}
    (hT0 : 1 < T0) (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120)
    (label : HeathBrownSelectionLabel L X k)
    (S : Finset ℕ) (hSne : S.Nonempty) (s : ℕ → ℂ)
    (hselection : ∀ r ∈ S,
      IsHeathBrownEligibleSelection L X k
        (T0 := T0) (t := t) (e := e) (s r) label) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 51 ∧
      T0 ^ (9 / 16 : ℝ) ≤
        ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) ∧
      (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
        T0 ^ (1367 / 2160 : ℝ) ∧
      ∀ r ∈ S,
        (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) ≤
          ‖(∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i))) (s r)) ^ ell‖ := by
  obtain ⟨r0, hr0⟩ := hSne
  have hsel0 := hselection r0 hr0
  rcases hsel0 with ⟨_helig, _hune, halower, haupper, _hcard, hAlength, _hlarge⟩
  let beta : ℝ := ∑ i ∈ label.2,
    dyadicLogExponent T0
      (heathBrownBoxFactorExponent label.1.a label.1.b label.1.q i)
  have hbeta_lo : mu / 120 ≤ beta := by simpa [beta, ht] using halower
  have hbeta_hi : beta ≤ 4 * mu / 120 := by
    rw [ht] at haupper
    dsimp [beta]
    linarith
  obtain ⟨hbetaWindow_lo, hbetaWindow_hi⟩ :=
    maynard_greedy_grouped_factor_exponent_window hmu_lo hmu_hi hbeta_lo hbeta_hi
  let A : ℝ := (groupedDyadicLower (heathBrownSelectedExponent label) : ℝ)
  have hAeq : A = T0 ^ beta := by simpa [A, beta] using hAlength
  obtain ⟨ell, hell51, hYlo, hYhi⟩ :=
    exists_maynard_greedy_raised_length hT0.le hAeq hbetaWindow_lo hbetaWindow_hi
  have hell : 0 < ell := by
    by_contra hn
    have hell0 : ell = 0 := Nat.eq_zero_of_not_pos hn
    subst ell
    norm_num at hYlo
    have hgt : (1 : ℝ) < T0 ^ (9 / 16 : ℝ) :=
      Real.one_lt_rpow hT0 (by norm_num)
    linarith
  refine ⟨ell, hell, hell51, ?_, ?_, ?_⟩
  · simpa [A, Nat.cast_pow] using hYlo
  · simpa [A, Nat.cast_pow] using hYhi
  · intro r hr
    have hsel := hselection r hr
    rcases hsel with ⟨_helig, _hune, _halower, _hupper, _hcard, _hlength, hlarge⟩
    have hbase : A ^ e ≤
        ‖∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i))) (s r)‖ := by
      simpa [A] using hlarge
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity : 0 ≤ A) _)
      hbase ell
    have hrewrite :
        (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) =
          (A ^ e) ^ ell := by
      calc
        (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) =
            A ^ ((ell : ℝ) * e) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast,
            ← Real.rpow_mul (by positivity : 0 ≤ A)]
        _ = A ^ (e * (ell : ℝ)) := by ring_nf
        _ = (A ^ e) ^ (ell : ℝ) := by
          rw [Real.rpow_mul (by positivity : 0 ≤ A)]
        _ = (A ^ e) ^ ell := Real.rpow_natCast _ _
    calc
      (((groupedDyadicLower (heathBrownSelectedExponent label) ^ ell : ℕ) : ℝ) ^ e) =
          (A ^ e) ^ ell := hrewrite
      _ ≤ ‖∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i))) (s r)‖ ^ ell := hpow
      _ = ‖(∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i))) (s r)) ^ ell‖ := by
        rw [norm_pow]

/-- Correct Huxley interface: `c` is the fixed Perron abscissa and `alpha` is the
Maynard magnitude exponent. -/
theorem huxley_heathBrown_grouped_large_values_finset_at_amplitude
    {ι : Type*} [Fintype ι] (L X ell K : ℕ)
    (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {c alpha : ℝ} (hc : 0 ≤ c)
    (Graw : ℝ) (hGraw : 0 ≤ Graw)
    (henergy : ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
      ‖convPow (groupedDyadicUpper q) ell
        (groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2 ≤ Graw)
    {S : Finset ℕ} (hS : S ⊆ Finset.range K)
    {lam : ℕ → ℝ} {delta T : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T)
    (hheight : T ≤ 8 * Real.pi *
      ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ 2)
    (hlarge : ∀ r ∈ S,
      ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ (alpha - c) ≤
        ‖(∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((c : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖)
    (hscale :
      2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) ^ 2 * Graw *
          (1 + 256 * (Real.sqrt T +
            8 * Real.sqrt
              ((((groupedDyadicUpper q) ^ ell : ℕ) : ℝ)))) ≤
        ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ (2 * alpha)) :
    (S.card : ℝ) *
        (((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ (alpha - c)) ^ 2 ≤
      2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
        ∑ r : Fin (Fintype.card ι * ell + 1),
          ((((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) ^
              (-c)) ^ 2 * Graw *
            (((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) +
              (12 * Real.pi *
                ((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) /
                  delta) *
                ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))) := by
  let A : ℕ := groupedDyadicLower q
  let D : Fin (Fintype.card ι * ell + 1) → ℕ :=
    fun r => A ^ ell * 2 ^ (r : ℕ)
  have hA : 1 ≤ A := one_le_groupedDyadicLower q
  have hD1 : ∀ r, 1 ≤ D r := by
    intro r
    dsimp [D]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero ell (by omega)) (pow_ne_zero (r : ℕ) (by norm_num)))
  have hU : ∀ r : Fin (Fintype.card ι * ell + 1),
      0 < maynardHuxleyU (D r) := by
    intro r
    exact maynardHuxleyU_pos (hD1 r)
  have hnear : ∀ r : Fin (Fintype.card ι * ell + 1),
      3 * maynardHuxleyU (D r) ≤ 4 * Real.pi * (D r : ℝ) := by
    intro r
    exact maynardHuxleyU_near
  have hY_D : ∀ r : Fin (Fintype.card ι * ell + 1),
      ((((A ^ ell : ℕ) : ℝ)) ≤ (D r : ℝ)) := by
    intro r
    dsimp [D]
    exact_mod_cast Nat.le_mul_of_pos_right (A ^ ell) (pow_pos (by omega) _)
  have hlamT : ∀ r : Fin (Fintype.card ι * ell + 1),
      logDyadicLambda (D r) T ≤ 1 := by
    intro r
    apply logDyadicLambda_le_one_of_height_le (hD1 r)
    have hsquare : ((((A ^ ell : ℕ) : ℝ)) ^ 2) ≤ ((D r : ℝ) ^ 2) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY_D r) 2
    exact hheight.trans (mul_le_mul_of_nonneg_left hsquare (by positivity))
  have hB : ∀ r : Fin (Fintype.card ι * ell + 1),
      logDyadicSecondEnvelope (D r) (maynardHuxleyU (D r)) T ≤
        maynardHuxleyB (D r) T := by
    intro r
    exact logDyadicSecondEnvelope_le_maynardHuxleyB (D r) T
  have hB1 : ∀ r : Fin (Fintype.card ι * ell + 1),
      1 ≤ maynardHuxleyB (D r) T := by
    intro r
    exact one_le_maynardHuxleyB (D r) T
  have hscale' :
      2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) ^ 2 * Graw *
          (1 + 256 * (Real.sqrt T +
            8 * Real.sqrt
              (((((groupedDyadicLower q) * 2 ^ Fintype.card ι) ^ ell : ℕ) : ℝ)))) ≤
        ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ (2 * alpha) := by
    rw [← groupedDyadicUpper_eq_lower_mul_twoPow q]
    exact hscale
  have hBmax : ∀ r : Fin (Fintype.card ι * ell + 1),
      0 ≤ maynardHuxleyB (D r) T ∧
      maynardHuxleyB (D r) T ≤
        1 + 256 * (Real.sqrt T +
          8 * Real.sqrt
            (((((groupedDyadicLower q) * 2 ^ Fintype.card ι) ^ ell : ℕ) : ℝ))) := by
    intro r
    constructor
    · exact (one_le_maynardHuxleyB (D r) T).trans' (by norm_num)
    · have hDupper : D r ≤ ((groupedDyadicLower q) * 2 ^ Fintype.card ι) ^ ell := by
        dsimp [D, A]
        rw [mul_pow, ← pow_mul]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hbase := maynardHuxleyB_le (hD1 r) hT
      have hsqrt : Real.sqrt (D r : ℝ) ≤
          Real.sqrt (((((groupedDyadicLower q) * 2 ^ Fintype.card ι) ^ ell : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hDupper)
      exact hbase.trans (by gcongr)
  have hYpos : 0 < (((A ^ ell : ℕ) : ℝ)) := by positivity
  have habsorb : ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
      ∑ r : Fin (Fintype.card ι * ell + 1),
        ((((D r : ℝ) ^ (-c)) ^ 2 * Graw) * maynardHuxleyB (D r) T) ≤
      ((((A ^ ell : ℕ) : ℝ)) ^ (alpha - c)) ^ 2 / 2 := by
    simpa only [Fintype.card_fin] using
      (weighted_huxley_absorption_at_amplitude D
        (fun r => maynardHuxleyB (D r) T) hYpos hc hY_D hGraw hBmax
          (by simpa [A] using hscale'))
  simpa [A, D] using
    huxley_heathBrown_grouped_large_values_finset_weighted
      L X ell K kind q hc Graw henergy
      (fun r => maynardHuxleyU (D r))
      (fun r => maynardHuxleyB (D r) T) hS hdelta
      (Real.rpow_pos_of_pos hYpos _) hU hgap hnear hlamT hB hB1
      hdiam hlarge habsorb

theorem huxley_maynardEligibleSelection_fibre_at_amplitude
    (L X k K : ℕ) {T0 t e mu c alpha delta : ℝ}
    (hT0 : 1 < T0) (hc : 0 ≤ c)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (he : e = alpha - c)
    (label : HeathBrownSelectionLabel L X k)
    (S : Finset ℕ) (hSne : S.Nonempty) (hS : S ⊆ Finset.range K)
    (lam : ℕ → ℝ) (hdelta : 0 < delta)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T0)
    (hselection : ∀ r ∈ S,
      IsHeathBrownEligibleSelection L X k
        (T0 := T0) (t := t) (e := e)
        ((c : ℂ) + (lam r : ℝ) * Complex.I) label)
    (hscale : ∀ ell : ℕ, 0 < ell → ell ≤ 51 →
      T0 ^ (9 / 16 : ℝ) ≤
        ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) →
      2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) ^ 2 *
          heathBrownSelectedRaisedEnergy label ell *
          (1 + 256 * (Real.sqrt T0 +
            8 * Real.sqrt
              ((((groupedDyadicUpper (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ≤
        ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) ^
          (2 * alpha)) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 51 ∧
      T0 ^ (9 / 16 : ℝ) ≤
        ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) ∧
      (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
        T0 ^ (1367 / 2160 : ℝ) ∧
      (S.card : ℝ) *
          (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
            (alpha - c)) ^ 2) ≤
        2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) *
          ∑ r : Fin (Fintype.card (HeathBrownSelectedFactor label) * ell + 1),
            ((((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-c)) ^ 2 *
              heathBrownSelectedRaisedEnergy label ell *
              (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                  2 ^ (r : ℕ) : ℕ) : ℝ)) +
                (12 * Real.pi *
                  ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                    2 ^ (r : ℕ) : ℕ) : ℝ)) / delta) *
                  ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))) := by
  obtain ⟨ell, hell, hell51, hYlo, hYhi, hlarge⟩ :=
    exists_maynardEligibleSelection_raise_at_exponent L X k hT0 hmu_lo hmu_hi ht
      label S hSne (fun r => (c : ℂ) + (lam r : ℝ) * Complex.I)
      (by simpa [he] using hselection)
  refine ⟨ell, hell, hell51, hYlo, hYhi, ?_⟩
  apply huxley_heathBrown_grouped_large_values_finset_at_amplitude
    (c := c) (alpha := alpha) (S := S) (lam := lam) (delta := delta) (T := T0)
    L X ell K (heathBrownSelectedKind label) (heathBrownSelectedExponent label)
    hc (heathBrownSelectedRaisedEnergy label ell)
    (heathBrownSelectedRaisedEnergy_nonneg label ell)
  · exact le_rfl
  · exact hS
  · exact hdelta
  · linarith
  · exact hgap
  · exact hdiam
  · exact maynard_huxley_square_height_of_raise hT0 hYlo
  · simpa [he] using hlarge
  · exact hscale ell hell hell51 hYlo

/-- Correct fibre count.  Dependence on `c` cancels, while Maynard amplitude `alpha`
survives as exponent `81/40 - 2*alpha`. -/
theorem card_le_of_huxley_at_amplitude
    {L X K : ℕ} {T0 c alpha delta : ℝ}
    (hT0 : 1 < T0) (hc : 1 / 2 ≤ c) (halpha : alpha ≤ 1)
    (hdelta : 0 < delta)
    (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ)
    (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (hYlo : T0 ^ (9 / 16 : ℝ) ≤
      ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ))
    (hYhi : (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
      T0 ^ (1367 / 2160 : ℝ))
    (hHuxley :
      (S.card : ℝ) *
          (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
            (alpha - c)) ^ 2) ≤
        2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) *
          ∑ r : Fin (Fintype.card (HeathBrownSelectedFactor label) * ell + 1),
            ((((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-c)) ^ 2 *
              heathBrownSelectedRaisedEnergy label ell *
              (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                  2 ^ (r : ℕ) : ℕ) : ℝ)) +
                (12 * Real.pi *
                  ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                    2 ^ (r : ℕ) : ℕ) : ℝ)) / delta) *
                  ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)))) :
    (S.card : ℝ) ≤
      2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant *
        maynardHarmonicFactor K delta *
          T0 ^ ((1367 / 2160 : ℝ) * (81 / 40 - 2 * alpha)) := by
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  let Q : ℕ := w * ell + 1
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let G : ℝ := heathBrownSelectedRaisedEnergy label ell
  let H : ℝ := ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)
  let HF : ℝ := maynardHarmonicFactor K delta
  have hT0pos : 0 < T0 := by linarith
  have hY1 : 1 ≤ Y := by
    have hTpow1 : 1 ≤ T0 ^ (9 / 16 : ℝ) :=
      Real.one_le_rpow hT0.le (by norm_num)
    exact hTpow1.trans (by simpa [Y, A] using hYlo)
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hw : w ≤ 120 := card_heathBrownSelectedFactor_sixty_le label
  have hQ : Q ≤ 6121 := by
    dsimp [Q]
    calc
      w * ell + 1 ≤ 120 * 51 + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul hw hell51) 1
      _ = 6121 := by norm_num
  have hQcast : (Q : ℝ) ≤ 6121 := by exact_mod_cast hQ
  have hG0 : 0 ≤ G := heathBrownSelectedRaisedEnergy_nonneg label ell
  have hG : G ≤ maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) := by
    simpa [G, heathBrownSelectedRaisedEnergy, Y, A, Nat.cast_pow] using
      (sum_normSq_convPow_heathBrownGrouped_le_subcritical hw ell hell hell51
        L X (heathBrownSelectedKind label) (heathBrownSelectedExponent label))
  have hHFpos : 0 < HF := maynardHarmonicFactor_pos K hdelta
  have hexp : 1 - 2 * c ≤ 0 := by linarith
  let term : Fin Q → ℝ := fun r =>
    (((((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-c)) ^ 2 * G) *
      (((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) +
        (12 * Real.pi * ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) / delta) * H)
  have hterm : ∀ r : Fin Q,
      term r ≤ maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
          Y ^ (1 - 2 * c) := by
    intro r
    let D : ℝ := (((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ))
    have htwo : 1 ≤ (2 ^ (r : ℕ) : ℕ) :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have hDlower : Y ≤ D := by
      dsimp [D, Y]
      exact_mod_cast (by simpa using Nat.mul_le_mul_left (A ^ ell) htwo)
    have hDpos : 0 < D := hYpos.trans_le hDlower
    have hDpow : D ^ (1 - 2 * c) ≤ Y ^ (1 - 2 * c) :=
      Real.rpow_le_rpow_of_nonpos hYpos hDlower hexp
    have hGD : G * D ^ (1 - 2 * c) ≤
        (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ)) * Y ^ (1 - 2 * c) :=
      mul_le_mul hG hDpow (Real.rpow_nonneg hDpos.le _)
        (mul_nonneg maynardUniformEnergyConstant_pos.le
          (Real.rpow_nonneg hYpos.le _))
    have hscaled := mul_le_mul_of_nonneg_right hGD hHFpos.le
    have htermEq : term r = G * HF * D ^ (1 - 2 * c) := by
      dsimp [term, D, HF, H, maynardHarmonicFactor]
      exact weighted_huxley_term_eq_amplitude (D := D) (G := G) (c := c)
        (delta := delta) (H := ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))
        (by positivity) hdelta
    rw [htermEq]
    calc
      G * HF * D ^ (1 - 2 * c) = G * D ^ (1 - 2 * c) * HF := by ring
      _ ≤ maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) *
          Y ^ (1 - 2 * c) * HF := hscaled
      _ = maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
          Y ^ (1 - 2 * c) := by ring
  have hsum :
      (∑ r : Fin Q, term r) ≤
        (Q : ℝ) * (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
          Y ^ (1 - 2 * c)) := by
    calc
      (∑ r : Fin Q, term r) ≤
          ∑ _r : Fin Q,
            (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
              Y ^ (1 - 2 * c)) := Finset.sum_le_sum fun r _ => hterm r
      _ = (Q : ℝ) * (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
          Y ^ (1 - 2 * c)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  let p : ℝ := 81 / 40 - 2 * alpha
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hpower : Y ^ (41 / 40 : ℝ) * Y ^ (1 - 2 * c) =
      Y ^ p * (Y ^ (alpha - c)) ^ 2 := by
    have hsquare : (Y ^ (alpha - c)) ^ 2 = Y ^ (2 * (alpha - c)) := by
      calc
        (Y ^ (alpha - c)) ^ 2 = Real.rpow (Y ^ (alpha - c)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Y ^ ((alpha - c) * 2) := (Real.rpow_mul hYpos.le _ _).symm
        _ = Y ^ (2 * (alpha - c)) := by congr 1; ring
    rw [hsquare, ← Real.rpow_add hYpos, ← Real.rpow_add hYpos]
    congr 1
    dsimp [p]
    ring
  have hHuxley' : (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 ≤
      2 * (Q : ℝ) * ∑ r : Fin Q, term r := by
    simpa [term, A, Y, G, H, Q, w, div_mul_eq_mul_div] using hHuxley
  have hQ0 : 0 ≤ (Q : ℝ) := Nat.cast_nonneg _
  have hupper := hHuxley'.trans
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hQ0))
  have hQsq : (Q : ℝ) ^ 2 ≤ (6121 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hQ0 hQcast 2
  have hrest0 : 0 ≤ maynardUniformEnergyConstant * HF *
      (Y ^ (41 / 40 : ℝ) * Y ^ (1 - 2 * c)) := by
    exact mul_nonneg
      (mul_nonneg maynardUniformEnergyConstant_pos.le hHFpos.le)
      (mul_nonneg (Real.rpow_nonneg hYpos.le _) (Real.rpow_nonneg hYpos.le _))
  have hreplaceQ :
      2 * (Q : ℝ) * ((Q : ℝ) *
        (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
          Y ^ (1 - 2 * c))) ≤
      2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF *
        (Y ^ p * (Y ^ (alpha - c)) ^ 2) := by
    rw [← hpower]
    calc
      2 * (Q : ℝ) * ((Q : ℝ) *
          (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
            Y ^ (1 - 2 * c))) =
        2 * (Q : ℝ) ^ 2 * (maynardUniformEnergyConstant * HF *
          (Y ^ (41 / 40 : ℝ) * Y ^ (1 - 2 * c))) := by ring
      _ ≤ 2 * (6121 : ℝ) ^ 2 * (maynardUniformEnergyConstant * HF *
          (Y ^ (41 / 40 : ℝ) * Y ^ (1 - 2 * c))) := by gcongr
      _ = _ := by ring
  have hmaster : (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 ≤
      2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF *
        (Y ^ p * (Y ^ (alpha - c)) ^ 2) := hupper.trans hreplaceQ
  have hthreshold : 0 < (Y ^ (alpha - c)) ^ 2 := by positivity
  have hcard : (S.card : ℝ) ≤
      2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF * Y ^ p := by
    have hmaster' : (Y ^ (alpha - c)) ^ 2 * (S.card : ℝ) ≤
        (Y ^ (alpha - c)) ^ 2 *
          (2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF * Y ^ p) := by
      calc
        (Y ^ (alpha - c)) ^ 2 * (S.card : ℝ) =
            (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 := by ring
        _ ≤ 2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF *
            (Y ^ p * (Y ^ (alpha - c)) ^ 2) := hmaster
        _ = (Y ^ (alpha - c)) ^ 2 *
            (2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF * Y ^ p) := by ring
    exact (mul_le_mul_iff_right₀ hthreshold).mp hmaster'
  have hYheight : Y ^ p ≤ T0 ^ ((1367 / 2160 : ℝ) * p) := by
    have hYhi' : Y ≤ T0 ^ (1367 / 2160 : ℝ) := by
      simpa [Y, A, Nat.cast_pow] using hYhi
    have hp' := Real.rpow_le_rpow hYpos.le hYhi' hp
    calc
      Y ^ p ≤ (T0 ^ (1367 / 2160 : ℝ)) ^ p := hp'
      _ = T0 ^ ((1367 / 2160 : ℝ) * p) := by
        rw [← Real.rpow_mul hT0pos.le]
  have hconst0 : 0 ≤
      2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        maynardUniformEnergyConstant_pos.le)
      hHFpos.le
  simpa [HF, p] using hcard.trans (mul_le_mul_of_nonneg_left hYheight hconst0)

end RHTower.Sieve
