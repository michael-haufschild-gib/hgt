import GaloisForLFunctions.RHTower.Sieve.HuxleyLogPhase
import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicPointwise
import GaloisForLFunctions.RHTower.Sieve.MaynardLongFactorAbsorption

/-!
# Kuzmin--Landau saving for over-height Heath--Brown factors

The first-derivative regime gives a full height saving, rather than the tiny fixed deficit from
an arbitrary high derivative.  This module first proves uniform prefix control on a dyadic
logarithmic phase, then inserts the Perron weight by Abel summation.  It is the analytic mechanism
which rules out a selected zeta/log factor longer than the ordinate height.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Real

/-- Kuzmin--Landau uniformly on every nonempty prefix of a dyadic logarithmic block. -/
theorem norm_logPhase_dyadic_prefix_le_kuzminLandau
    (t : ℝ) (ht : 0 < t) (N L : ℕ) (hN : 1 ≤ N)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (htN : 3 * t ≤ 4 * Real.pi * (N : ℝ)) :
    ‖∑ j ∈ Finset.range L,
        Complex.exp (((2 * Real.pi * logPhase t ((N : ℝ) + j) : ℝ) : ℂ) * Complex.I)‖
      ≤ 6 * Real.pi * (N : ℝ) / t + 1 := by
  let delta : ℝ := t / (4 * Real.pi * (N : ℝ))
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hspan : (N : ℝ) + ((L - 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have hsub : L - 1 ≤ N := (Nat.sub_le L 1).trans hLN
    have hsubR : ((L - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsub
    linarith
  have hderiv : ∀ x ∈ Set.Icc (N : ℝ) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      HasDerivAt (logPhase t) (logPhaseChain t 1 x) x := by
    intro x hx
    exact logPhaseChain_hasDerivAt t 0 (lt_of_lt_of_le hNR hx.1)
  have hmono : MonotoneOn (logPhaseChain t 1)
      (Set.Icc (N : ℝ) ((N : ℝ) + ((L - 1 : ℕ) : ℝ))) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := lt_of_lt_of_le hNR hx.1
    have hy0 : 0 < y := lt_of_lt_of_le hNR hy.1
    have hinv : y⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 hxy
    simp only [logPhaseChain]
    norm_num
    have hc : 0 ≤ t / (2 * Real.pi) := by positivity
    nlinarith
  have hlo : ∀ x ∈ Set.Icc (N : ℝ) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      ((-1 : ℤ) : ℝ) + delta ≤ logPhaseChain t 1 x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hNR hx.1
    have hinv : x⁻¹ ≤ ((N : ℝ))⁻¹ := inv_anti₀ hNR hx.1
    simp only [logPhaseChain]
    norm_num
    dsimp [delta]
    have hden : 0 < 4 * Real.pi * (N : ℝ) := by positivity
    have h3delta : 3 * delta ≤ 1 := by
      dsimp [delta]
      have hq := (div_le_one hden).2 (by simpa [mul_assoc] using htN)
      have heqdiv : 3 * (t / (4 * Real.pi * (N : ℝ))) =
          3 * t / (4 * Real.pi * (N : ℝ)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [heqdiv]
      exact hq
    have hc : 0 ≤ t / (2 * Real.pi) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hinv hc
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
    have heq : t / (2 * Real.pi) * ((N : ℝ))⁻¹ = 2 * delta := by
      dsimp [delta]
      field_simp [hNne, Real.pi_ne_zero]
      ring
    rw [heq] at hmul
    change delta + t / (2 * Real.pi) * x⁻¹ ≤ 1
    linarith
  have hhi : ∀ x ∈ Set.Icc (N : ℝ) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      logPhaseChain t 1 x ≤ ((-1 : ℤ) : ℝ) + 1 - delta := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hNR hx.1
    have hx2N : x ≤ 2 * (N : ℝ) := hx.2.trans hspan
    have hinv : (2 * (N : ℝ))⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 hx2N
    simp only [logPhaseChain]
    norm_num
    dsimp [delta]
    have hc : 0 ≤ t / (2 * Real.pi) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hinv hc
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
    field_simp [hNne]
    nlinarith
  have hmain := kuzminLandau_interval (logPhase t) (logPhaseChain t 1) (N : ℝ)
    (L - 1) (-1) hdelta hderiv hmono hlo hhi
  rw [Nat.sub_add_cancel hL] at hmain
  convert hmain using 1 <;> dsimp [delta]
  field_simp
  <;> ring

/-- Pure Dirichlet phase prefixes inherit the Kuzmin--Landau bound. -/
theorem norm_dirichletPhase_Ico_le_kuzminLandau
    (t : ℝ) (ht : 0 < t) (N M : ℕ) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (htN : 3 * t ≤ 4 * Real.pi * (N : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
      6 * Real.pi * (N : ℝ) / t + 1 := by
  by_cases hEq : M = N
  · subst M
    simp
    positivity
  · have hL : 1 ≤ M - N := by omega
    have hLN : M - N ≤ N := by omega
    rw [Finset.sum_Ico_eq_sum_range]
    have hphase := norm_logPhase_dyadic_prefix_le_kuzminLandau
      t ht N (M - N) hN hL hLN htN
    have hterm : ∀ j ∈ Finset.range (M - N),
        (((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))) =
          Complex.exp (((2 * Real.pi * logPhase t ((N : ℝ) + j) : ℝ) : ℂ) *
            Complex.I) := by
      intro j hj
      have hNj : 1 ≤ N + j := hN.trans (Nat.le_add_right N j)
      rw [natCast_cpow_neg_I_mul t (N + j) hNj]
      congr 3
      push_cast
      ring
    simpa only [Finset.sum_congr rfl hterm] using hphase

/-- **Perron-weighted Kuzmin--Landau dyadic block.** -/
theorem norm_dirichletBlock_sigma_le_kuzminLandau
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (t : ℝ) (ht : 0 < t) (N M : ℕ) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (htN : 3 * t ≤ 4 * Real.pi * (N : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M,
        (n : ℂ) ^ (-(sigma : ℂ) - Complex.I * (t : ℂ))‖ ≤
      (6 * Real.pi * (N : ℝ) / t + 1) * (N : ℝ) ^ (-sigma) := by
  apply dirichlet_block_sigma_bound hsigma t N M hN hNM
  intro m hNm hmM
  exact norm_dirichletPhase_Ico_le_kuzminLandau t ht N m hN hNm
    (hmM.trans hM) htN

/-- Logarithmic coefficient version, with only the terminal logarithmic weight. -/
theorem norm_dirichletBlock_log_sigma_le_kuzminLandau
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (t : ℝ) (ht : 0 < t) (N M : ℕ) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (htN : 3 * t ≤ 4 * Real.pi * (N : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M, (Real.log (n : ℝ) : ℂ) *
        (n : ℂ) ^ (-(sigma : ℂ) - Complex.I * (t : ℂ))‖ ≤
      2 * ((6 * Real.pi * (N : ℝ) / t + 1) * (N : ℝ) ^ (-sigma)) *
        Real.log (M : ℝ) := by
  apply dirichlet_block_log_sigma_bound t N M hN hNM
  intro m hNm hmM
  exact norm_dirichletBlock_sigma_le_kuzminLandau hsigma t ht N m hN hNm
    (hmM.trans hM) htN

/-- Literal zeta factor in the Kuzmin--Landau regime. -/
theorem norm_LSeries_zetaDyadicBlock_le_kuzminLandau
    {X q : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X)
    {sigma t : ℝ} (hsigma : 0 ≤ sigma) (ht : 0 < t)
    (htN : 3 * t ≤ 4 * Real.pi * ((2 ^ q : ℕ) : ℝ)) :
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
        ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (6 * Real.pi * ((2 ^ q : ℕ) : ℝ) / t + 1) *
        ((2 ^ q : ℕ) : ℝ) ^ (-sigma) := by
  rw [LSeries_zetaDyadicBlock_eq_sum_Ico]
  apply norm_dirichletBlock_sigma_le_kuzminLandau hsigma t ht
  · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero q (by norm_num))
  · exact pow_le_heathBrownDyadicFactorTop hX hq
  · calc
      heathBrownDyadicFactorTop X q ≤ 2 ^ (q + 1) := min_le_right _ _
      _ = 2 * 2 ^ q := by rw [pow_succ]; ring
  · exact htN

/-- Literal logarithmic factor in the Kuzmin--Landau regime. -/
theorem norm_LSeries_logDyadicBlock_le_kuzminLandau
    {X q : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X)
    {sigma t : ℝ} (hsigma : 0 ≤ sigma) (ht : 0 < t)
    (htN : 3 * t ≤ 4 * Real.pi * ((2 ^ q : ℕ) : ℝ)) :
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
        ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * ((6 * Real.pi * ((2 ^ q : ℕ) : ℝ) / t + 1) *
        ((2 ^ q : ℕ) : ℝ) ^ (-sigma)) *
          Real.log (heathBrownDyadicFactorTop X q : ℝ) := by
  rw [LSeries_logDyadicBlock_eq_sum_Ico]
  apply norm_dirichletBlock_log_sigma_le_kuzminLandau hsigma t ht
  · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero q (by norm_num))
  · exact pow_le_heathBrownDyadicFactorTop hX hq
  · calc
      heathBrownDyadicFactorTop X q ≤ 2 ^ (q + 1) := min_le_right _ _
      _ = 2 * 2 ^ q := by rw [pow_succ]; ring
  · exact htN

/-- A dyadic lower edge above the height lies uniformly in the first-derivative regime throughout
the ordinate band `[T,2T]`. -/
theorem kuzminLandau_regime_of_over_height
    {T t N : ℝ} (hT : 0 < T) (ht : t ≤ 2 * T) (hN : T ≤ N) :
    3 * t ≤ 4 * Real.pi * N := by
  have hpi := Real.pi_gt_three
  calc
    3 * t ≤ 6 * T := by linarith
    _ ≤ 6 * N := mul_le_mul_of_nonneg_left hN (by norm_num)
    _ ≤ 4 * Real.pi * N := by nlinarith

/-- The reciprocal-frequency envelope above the height has one full factor `N/T`. -/
theorem kuzminLandau_envelope_le_over_height
    {T t N : ℝ} (hT : 0 < T) (hTt : T ≤ t) (hTN : T ≤ N) :
    6 * Real.pi * N / t + 1 ≤ (6 * Real.pi + 1) * N / T := by
  have ht : 0 < t := hT.trans_le hTt
  have hN : 0 < N := hT.trans_le hTN
  have hinv : t⁻¹ ≤ T⁻¹ := (inv_le_inv₀ ht hT).2 hTt
  have hratio : N / t ≤ N / T := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hN.le
  have hone : 1 ≤ N / T := (le_div_iff₀ hT).2 (by simpa using hTN)
  calc
    6 * Real.pi * N / t + 1 = 6 * Real.pi * (N / t) + 1 := by ring
    _ ≤ 6 * Real.pi * (N / T) + N / T :=
      add_le_add (mul_le_mul_of_nonneg_left hratio (by positivity)) hone
    _ = (6 * Real.pi + 1) * N / T := by ring

/-- Zeta block bound with the full explicit height saving. -/
theorem norm_LSeries_zetaDyadicBlock_le_over_height
    {X q : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X)
    {T sigma t : ℝ} (hT : 0 < T) (hsigma : 0 ≤ sigma)
    (hTt : T ≤ t) (htupper : t ≤ 2 * T)
    (hTN : T ≤ ((2 ^ q : ℕ) : ℝ)) :
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
        ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (6 * Real.pi + 1) / T *
        ((2 ^ q : ℕ) : ℝ) ^ (1 - sigma) := by
  let N : ℝ := ((2 ^ q : ℕ) : ℝ)
  have ht : 0 < t := hT.trans_le hTt
  have hreg : 3 * t ≤ 4 * Real.pi * N :=
    kuzminLandau_regime_of_over_height hT htupper hTN
  have hraw := norm_LSeries_zetaDyadicBlock_le_kuzminLandau
    hX hq hsigma ht (by simpa [N] using hreg)
  have hpref := kuzminLandau_envelope_le_over_height hT hTt hTN
  have hNpos : 0 < N := hT.trans_le hTN
  have hweight0 : 0 ≤ N ^ (-sigma) := Real.rpow_nonneg hNpos.le _
  have hscaled := mul_le_mul_of_nonneg_right hpref hweight0
  have hrpow : N * N ^ (-sigma) = N ^ (1 - sigma) := by
    calc
      N * N ^ (-sigma) = N ^ (1 : ℝ) * N ^ (-sigma) := by rw [Real.rpow_one]
      _ = N ^ ((1 : ℝ) + (-sigma)) := (Real.rpow_add hNpos _ _).symm
      _ = N ^ (1 - sigma) := by ring
  calc
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
        ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (6 * Real.pi * N / t + 1) * N ^ (-sigma) := by simpa [N] using hraw
    _ ≤ ((6 * Real.pi + 1) * N / T) * N ^ (-sigma) := hscaled
    _ = (6 * Real.pi + 1) / T * N ^ (1 - sigma) := by
      rw [← hrpow]
      ring
    _ = _ := by rfl

/-- Logarithmic block bound with the same full height saving and one polylog envelope. -/
theorem norm_LSeries_logDyadicBlock_le_over_height
    {X q : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X)
    {T sigma t : ℝ} (hT : 0 < T) (hsigma : 0 ≤ sigma)
    (hTt : T ≤ t) (htupper : t ≤ 2 * T)
    (hTN : T ≤ ((2 ^ q : ℕ) : ℝ)) :
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
        ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X / T *
        ((2 ^ q : ℕ) : ℝ) ^ (1 - sigma) := by
  let N : ℝ := ((2 ^ q : ℕ) : ℝ)
  have ht : 0 < t := hT.trans_le hTt
  have hreg : 3 * t ≤ 4 * Real.pi * N :=
    kuzminLandau_regime_of_over_height hT htupper hTN
  have hraw := norm_LSeries_logDyadicBlock_le_kuzminLandau
    hX hq hsigma ht (by simpa [N] using hreg)
  have hpref := kuzminLandau_envelope_le_over_height hT hTt hTN
  have hNpos : 0 < N := hT.trans_le hTN
  have hweight0 : 0 ≤ N ^ (-sigma) := Real.rpow_nonneg hNpos.le _
  have hscaled := mul_le_mul_of_nonneg_right hpref hweight0
  have hrpow : N * N ^ (-sigma) = N ^ (1 - sigma) := by
    calc
      N * N ^ (-sigma) = N ^ (1 : ℝ) * N ^ (-sigma) := by rw [Real.rpow_one]
      _ = N ^ ((1 : ℝ) + (-sigma)) := (Real.rpow_add hNpos _ _).symm
      _ = N ^ (1 - sigma) := by ring
  have hlog := log_heathBrownDyadicFactorTop_le_polylogEnvelope
    (X := X) (q := q) hX
  have hlog0 : 0 ≤ Real.log (heathBrownDyadicFactorTop X q : ℝ) := by
    have htop : 1 ≤ heathBrownDyadicFactorTop X q :=
      (Nat.one_le_pow q 2 (by norm_num)).trans (pow_le_heathBrownDyadicFactorTop hX hq)
    exact Real.log_nonneg (by exact_mod_cast htop)
  have hmain :
      2 * ((6 * Real.pi * N / t + 1) * N ^ (-sigma)) *
          Real.log (heathBrownDyadicFactorTop X q : ℝ) ≤
        2 * (((6 * Real.pi + 1) * N / T) * N ^ (-sigma)) *
          maynardLongPolylogEnvelope X := by
    have htwo := mul_le_mul_of_nonneg_left hscaled (by norm_num : (0 : ℝ) ≤ 2)
    exact mul_le_mul htwo hlog hlog0 (by positivity)
  calc
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
        ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        2 * ((6 * Real.pi * N / t + 1) * N ^ (-sigma)) *
          Real.log (heathBrownDyadicFactorTop X q : ℝ) := by simpa [N] using hraw
    _ ≤ 2 * (((6 * Real.pi + 1) * N / T) * N ^ (-sigma)) *
          maynardLongPolylogEnvelope X := hmain
    _ = 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X / T *
          N ^ (1 - sigma) := by
      rw [← hrpow]
      ring
    _ = _ := by rfl

end RHTower.Sieve
