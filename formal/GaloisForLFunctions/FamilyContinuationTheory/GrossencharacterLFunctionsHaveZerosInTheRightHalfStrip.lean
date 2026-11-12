import GaloisForLFunctions.FamilyContinuationTheory.HarmonicGaussianPoissonGivesGrossencharacterContinuation
import GaloisForLFunctions.HeckeLFunctions.NonquadraticCharactersDoNotVanishOnTheLineReOne
import GaloisForLFunctions.HTGeometry.GammaLogGrowth
import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticRigidity

/-!
# Grossencharacter `L`-Functions Have Infinitely Many Zeros in the Right Half-Strip

For every modulus `𝔪` of `K = ℚ(ω)`, every ray class character `ψ : HeckeCharacter 𝔪`, and every
positive sextic weight `k ≥ 1`, the primitive Grossencharacter `L`-function
`grossenLFunction 𝔪 ψ k` satisfies:

1. **Unconditional nonvanishing on `Re w ≥ 1`:** `grossenLFunction 𝔪 ψ k w ≠ 0` for all `Re w ≥ 1`.
   On `Re w > 1` this follows from the convergent Euler product; on the boundary `Re w = 1` it
   follows from the `3-4-1` Euler-logarithm inequality applied to `heckeL 𝔪 1` together with the
   `𝔪`-imprimitive Grossencharacter `L`-functions at `(ψ, k)` and `(ψ², 2k)`. Because `2k ≥ 2 ≥ 1`,
   the `(ψ², 2k)` factor is holomorphic across `Re w = 1` even when `ψ² = 1`.
2. **Infinitely many zeros in `1/2 ≤ Re w < 1` with unbounded ordinates:** `grossenCompletedL 𝔪 ψ k`
   is entire of order one (hence subquadratic) and grows superlinearly along the positive real ray
   via `Γ(w + 3k)`, so Hadamard subquadratic rigidity yields infinitely many zeros. Nonvanishing on
   `Re w ≥ 1` and the functional equation `w ↔ 1 - conj w` confine all zeros to `0 < Re w < 1` and
   fold them `2`-to-`1` into `1/2 ≤ Re w < 1`. Compactness of closed balls forces their imaginary
   parts to be unbounded.
3. **Analytic continuation and zero obstruction of the cubic probe correction:** the continued probe
   correction `continuedProbeCorrection 𝔪 η S` continues `fullPrincipalCorrection` (`Re s > 2/3`)
   and `probeCorrection` (`Re s ≥ 7/8`) holomorphically to all of `Re s > 1/2`, is nonvanishing on
   `Re s ≥ 2/3`, vanishes on `Re s > 1/2` if and only if `L(6s - 3, ψ₆ χ_{𝔣(η⁶)}) = 0`, has
   infinitely many zeros in `7/12 ≤ Re s < 2/3` with unbounded ordinates, and therefore admits **no**
   holomorphic nonvanishing continuation to `Re s > σ₀` for any `σ₀ < 7/12`.
-/

noncomputable section

open Complex Filter Topology Set NumberField IsDedekindDomain
open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-! ### Euler logarithm, nonvanishing on `Re w > 1`, and uniform two-sided bounds on `Re w ≥ 2` -/

theorem grossenEulerDenominator_ne_zero (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {w : ℂ} (hw : 1 < w.re) (v : HeightOneSpectrum O) :
    1 - grossenPrimeTerm 𝔪 ψ k w v ≠ 0 := by
  have hlt := norm_grossenPrimeTerm_lt_one 𝔪 ψ k hw v
  intro h0
  have htri := norm_sub_norm_le (1 : ℂ) (grossenPrimeTerm 𝔪 ψ k w v)
  rw [h0, norm_zero, norm_one] at htri
  linarith

theorem summable_grossenEulerLog (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {w : ℂ} (hw : 1 < w.re) :
    Summable fun v : HeightOneSpectrum O => -Complex.log (1 - grossenPrimeTerm 𝔪 ψ k w v) :=
  (summable_norm_grossenPrimeTerm 𝔪 ψ k hw).of_norm.clog_one_sub.neg

theorem exp_tsum_grossenEulerLog (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ} (hk : 1 ≤ k)
    {w : ℂ} (hw : 1 < w.re) :
    cexp (∑' v : HeightOneSpectrum O, -Complex.log (1 - grossenPrimeTerm 𝔪 ψ k w v)) =
      grossenLFunction 𝔪 ψ k w := by
  have h := (summable_grossenEulerLog 𝔪 ψ k hw).hasSum.cexp
  simp only [Function.comp_def, Complex.exp_neg,
    Complex.exp_log (grossenEulerDenominator_ne_zero 𝔪 ψ k hw _)] at h
  rw [grossenLFunction_eq_tsum_ideals 𝔪 ψ hk hw]
  exact h.unique (hasProd_grossenEulerProduct 𝔪 ψ k hw)

/-- `grossenLFunction 𝔪 ψ k` is nonvanishing on the open half-plane `Re w > 1` (`k ≥ 1`). -/
theorem grossenLFunction_ne_zero_of_one_lt_re (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    grossenLFunction 𝔪 ψ k w ≠ 0 := by
  rw [← exp_tsum_grossenEulerLog 𝔪 ψ hk hw]
  exact Complex.exp_ne_zero _

/-- Uniform positive lower bound and uniform upper bound for `‖grossenLFunction 𝔪 ψ k w‖` on
`Re w ≥ 2` (`k ≥ 1`). -/
theorem exists_pos_le_and_le_norm_grossenLFunction (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ c M : ℝ, 0 < c ∧ ∀ w : ℂ, 2 ≤ w.re →
      c ≤ ‖grossenLFunction 𝔪 ψ k w‖ ∧ ‖grossenLFunction 𝔪 ψ k w‖ ≤ M := by
  have hmaj : Summable fun v : HeightOneSpectrum O =>
      (3 / 2 : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)) :=
    (numberField_summable_finitePlace_absNorm_rpow (K := K) one_lt_two).mul_left (3 / 2)
  set B : ℝ := ∑' v : HeightOneSpectrum O,
    (3 / 2 : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ))
  refine ⟨Real.exp (-B), Real.exp B, Real.exp_pos _, fun w hw => ?_⟩
  have hw1 : 1 < w.re := by linarith
  have hterm_le : ∀ v : HeightOneSpectrum O,
      ‖-Complex.log (1 - grossenPrimeTerm 𝔪 ψ k w v)‖ ≤
        (3 / 2 : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)) := by
    intro v
    have hv2 := ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
    have hv2r : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast hv2
    have hnorm_u : ‖grossenPrimeTerm 𝔪 ψ k w v‖ ≤
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)) :=
      (norm_grossenPrimeTerm_le 𝔪 ψ k w v).trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
    have hhalf : ‖-grossenPrimeTerm 𝔪 ψ k w v‖ ≤ 1 / 2 := by
      rw [norm_neg]
      refine hnorm_u.trans ?_
      calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ))
          ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hlog := Complex.norm_log_one_add_half_le_self hhalf
    rw [← sub_eq_add_neg, norm_neg] at hlog
    rw [norm_neg]
    exact hlog.trans (mul_le_mul_of_nonneg_left hnorm_u (by norm_num))
  have hsum_norm : Summable fun v : HeightOneSpectrum O =>
      ‖-Complex.log (1 - grossenPrimeTerm 𝔪 ψ k w v)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hmaj
  have hnorm_tsum : ‖∑' v : HeightOneSpectrum O,
      -Complex.log (1 - grossenPrimeTerm 𝔪 ψ k w v)‖ ≤ B :=
    (norm_tsum_le_tsum_norm hsum_norm).trans (hsum_norm.tsum_le_tsum hterm_le hmaj)
  have habs_re : |(∑' v : HeightOneSpectrum O,
      -Complex.log (1 - grossenPrimeTerm 𝔪 ψ k w v)).re| ≤ B :=
    (Complex.abs_re_le_norm _).trans hnorm_tsum
  rw [← exp_tsum_grossenEulerLog 𝔪 ψ hk hw1, Complex.norm_exp]
  exact ⟨Real.exp_le_exp.mpr (neg_le_of_abs_le habs_re),
    Real.exp_le_exp.mpr (le_of_abs_le habs_re)⟩

theorem exists_norm_grossenLFunction_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ M : ℝ, ∀ w : ℂ, 2 ≤ w.re → ‖grossenLFunction 𝔪 ψ k w‖ ≤ M := by
  obtain ⟨_, M, _, h⟩ := exists_pos_le_and_le_norm_grossenLFunction 𝔪 ψ hk
  exact ⟨M, fun w hw => (h w hw).2⟩

/-! ### Unconditional `3-4-1` nonvanishing on the line `Re w = 1` -/

private def grossenModulusPrimeTerm (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (w : ℂ)
    (v : HeightOneSpectrum O) : ℂ :=
  idealPsiSix v.asIdeal ^ k * heckeValue 𝔪 ψ v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)

private theorem norm_grossenModulusPrimeTerm_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (w : ℂ) (v : HeightOneSpectrum O) :
    ‖grossenModulusPrimeTerm 𝔪 ψ k w v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-w.re) := by
  have hv0 : 0 < Ideal.absNorm v.asIdeal :=
    lt_of_lt_of_le zero_lt_two (ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot)
  have hcoeff : ‖idealPsiSix v.asIdeal ^ k * heckeValue 𝔪 ψ v.asIdeal‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_idealPsiSix_le_one _))
      (norm_nonneg _) (norm_heckeValue_le_one 𝔪 ψ _)
  rw [grossenModulusPrimeTerm, norm_mul, Complex.norm_natCast_cpow_of_pos hv0, neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hcoeff

private theorem summable_grossenModulusEulerLog (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {w : ℂ} (hw : 1 < w.re) :
    Summable fun v : HeightOneSpectrum O =>
      -Complex.log (1 - grossenModulusPrimeTerm 𝔪 ψ k w v) := by
  have hsum : Summable fun v : HeightOneSpectrum O => ‖grossenModulusPrimeTerm 𝔪 ψ k w v‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_)
      (numberField_summable_finitePlace_norm_cpow (K := K) hw)
    have hv0 : 0 < Ideal.absNorm v.asIdeal :=
      lt_of_lt_of_le zero_lt_two (ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot)
    rw [Complex.norm_natCast_cpow_of_pos hv0, neg_re]
    exact norm_grossenModulusPrimeTerm_le 𝔪 ψ k w v
  exact hsum.of_norm.clog_one_sub.neg

/-- Continuation of the `𝔪`-imprimitive Grossencharacter Euler product across `Re w = 1`. -/
private def grossenModulusLCont (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (w : ℂ) : ℂ :=
  grossenLFunction 𝔪 ψ k w * grossenDeletedFactors 𝔪 ψ k ∅ w

private theorem differentiableAt_grossenModulusLCont (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : -(3 * (k : ℝ)) < w.re) :
    DifferentiableAt ℂ (grossenModulusLCont 𝔪 ψ k) w :=
  ((differentiableOn_grossenLFunction 𝔪 ψ hk).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds hw)).mul
    (differentiable_grossenDeletedFactors 𝔪 ψ k ∅ w)

private theorem exp_tsum_grossenModulusEulerLog (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    cexp (∑' v : HeightOneSpectrum O, -Complex.log (1 - grossenModulusPrimeTerm 𝔪 ψ k w v)) =
      grossenModulusLCont 𝔪 ψ k w := by
  have hden : ∀ v : HeightOneSpectrum O, 1 - grossenModulusPrimeTerm 𝔪 ψ k w v ≠ 0 := by
    intro v h0
    have hv2 := ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
    have hlt : ‖grossenModulusPrimeTerm 𝔪 ψ k w v‖ < 1 :=
      (norm_grossenModulusPrimeTerm_le 𝔪 ψ k w v).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast lt_of_lt_of_le one_lt_two hv2)
          (by linarith))
    have htri := norm_sub_norm_le (1 : ℂ) (grossenModulusPrimeTerm 𝔪 ψ k w v)
    rw [h0, norm_zero, norm_one] at htri
    linarith
  have h := (summable_grossenModulusEulerLog 𝔪 ψ k hw).hasSum.cexp.tprod_eq
  simp only [Function.comp_def, Complex.exp_neg, Complex.exp_log (hden _)] at h
  rw [← h, grossenModulusLCont, ← grossenEulerProductModS_eq_mul_deletedFactors 𝔪 ψ hk ∅ hw]
  unfold grossenEulerProductModS
  rw [← (Subtype.val_injective (p := fun v : HeightOneSpectrum O =>
    v ∉ (∅ : Finset (HeightOneSpectrum O)))).tprod_eq
      (fun v _ => ⟨⟨v, Finset.notMem_empty v⟩, rfl⟩)]
  refine tprod_congr fun u => ?_
  unfold grossenModulusPrimeTerm primeNorm
  rw [Complex.ofReal_natCast]

private theorem three_four_one_log_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-Complex.log (1 - a)).re + 4 * (-Complex.log (1 - a * z)).re +
      (-Complex.log (1 - a * z ^ 2)).re := by
  have h0 : ‖(a : ℂ)‖ < 1 := by simpa only [Complex.norm_of_nonneg ha] using ha1
  have h1 : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have h2 : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  have H := ((hasSum_re (hasSum_taylorSeries_neg_log h0)).mul_left 3).add
    ((hasSum_re (hasSum_taylorSeries_neg_log h1)).mul_left 4) |>.add
    (hasSum_re (hasSum_taylorSeries_neg_log h2))
  rw [← H.tsum_eq]
  refine tsum_nonneg fun n => ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im,
    zero_mul, sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

private theorem grossenModulusEulerLog_three_four_one_nonneg (𝔪 : Modulus K)
    (ψ : HeckeCharacter 𝔪) (k : ℕ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (v : HeightOneSpectrum O) :
    0 ≤ 3 * (-Complex.log (1 - heckePrimeTerm 𝔪 1 σ v)).re +
      4 * (-Complex.log (1 - grossenModulusPrimeTerm 𝔪 ψ k (σ + I * t) v)).re +
      (-Complex.log (1 - grossenModulusPrimeTerm 𝔪 (ψ ^ 2) (2 * k) (σ + 2 * I * t) v)).re := by
  have hn : 1 < Ideal.absNorm v.asIdeal :=
    lt_of_lt_of_le one_lt_two (ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot)
  have hn0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 :=
    by exact_mod_cast (lt_trans Nat.zero_lt_one hn).ne'
  by_cases hm : idealUnit v.ne_bot ∈ idealGroup 𝔪
  · set z : ℂ := idealPsiSix v.asIdeal ^ k * ψ (rayClass 𝔪 ⟨_, hm⟩)
    have hz : ‖z‖ = 1 := by
      rw [norm_mul, norm_pow, norm_idealPsiSix_prime, one_pow, one_mul, norm_char_eq_one]
    have ha : (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn)
        (neg_neg_of_pos (lt_trans zero_lt_one hσ))
    have hz' : ‖z * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(I * t))‖ = 1 := by
      rw [norm_mul, hz, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos
        (by exact_mod_cast lt_trans Nat.zero_lt_one hn)]
      simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im,
        mul_zero, sub_self, neg_zero, Real.rpow_zero, one_mul]
    have hsq_z : idealPsiSix v.asIdeal ^ (2 * k) * (ψ (rayClass 𝔪 ⟨_, hm⟩) : ℂ) ^ 2 = z ^ 2 := by
      dsimp only [z]
      rw [mul_pow, ← pow_mul, mul_comm k 2]
    simp only [heckePrimeTerm, grossenModulusPrimeTerm, heckeValue_sq,
      heckeValue_of_mem 𝔪 1 v.ne_bot hm, heckeValue_of_mem 𝔪 ψ v.ne_bot hm,
      MonoidHom.one_apply, Units.val_one, one_mul, hsq_z]
    convert three_four_one_log_nonneg (by positivity) ha hz' using 6
    · simp only [ofReal_cpow (Nat.cast_nonneg _) (-σ), ofReal_natCast, ofReal_neg]
    · congr 2
      rw [neg_add, cpow_add _ _ hn0, ← ofReal_neg,
        ofReal_cpow (Nat.cast_nonneg _) (-σ), ofReal_natCast]
      ring
    · rw [neg_add, cpow_add _ _ hn0, ← ofReal_neg,
        ofReal_cpow (Nat.cast_nonneg _) (-σ), ofReal_natCast,
        show -(2 * I * t) = (2 : ℕ) * -(I * t) by ring,
        cpow_nat_mul, mul_pow]
      ring
  · have hbad : ¬ ∃ hI : v.asIdeal ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪 := fun ⟨_, h⟩ => hm h
    simp only [heckePrimeTerm, grossenModulusPrimeTerm, heckeValue_of_not_mem 𝔪 _ hbad,
      mul_zero, zero_mul, sub_zero, Complex.log_one, neg_zero, zero_re, add_zero, le_refl]

private theorem one_le_norm_grossenModulus_three_four_one (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖heckeL 𝔪 1 σ ^ 3 * grossenModulusLCont 𝔪 ψ k (σ + I * t) ^ 4 *
      grossenModulusLCont 𝔪 (ψ ^ 2) (2 * k) (σ + 2 * I * t)‖ := by
  have hk2 : 1 ≤ 2 * k := by omega
  have h0 : 1 < (σ : ℂ).re := hσ
  have h1 : 1 < (σ + I * t : ℂ).re := by simpa using hσ
  have h2 : 1 < (σ + 2 * I * t : ℂ).re := by simpa using hσ
  have H0 := summable_heckeEulerLog 𝔪 1 h0
  have H1 := summable_grossenModulusEulerLog 𝔪 ψ k h1
  have H2 := summable_grossenModulusEulerLog 𝔪 (ψ ^ 2) (2 * k) h2
  have S0 := (hasSum_re H0.hasSum).summable.mul_left 3
  have S1 := (hasSum_re H1.hasSum).summable.mul_left 4
  have S2 := (hasSum_re H2.hasSum).summable
  rw [← exp_tsum_heckeEulerLog 𝔪 1 h0, ← exp_tsum_grossenModulusEulerLog 𝔪 ψ hk h1,
    ← exp_tsum_grossenModulusEulerLog 𝔪 (ψ ^ 2) hk2 h2]
  simp only [← Complex.exp_nat_mul, Nat.cast_ofNat, ← Complex.exp_add, Complex.norm_exp,
    add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H0, re_tsum H1, re_tsum H2, ← tsum_mul_left, ← tsum_mul_left,
    ← S0.tsum_add S1, ← (S0.add S1).tsum_add S2]
  exact tsum_nonneg (grossenModulusEulerLog_three_four_one_nonneg 𝔪 ψ k hσ t)

/-- **Unconditional nonvanishing on `Re w = 1`:** for every `k ≥ 1`, modulus `𝔪`, ray class
character `ψ`, and real height `t`, `grossenLFunction 𝔪 ψ k (1 + I * t) ≠ 0`. -/
theorem grossenLFunction_line_one_ne_zero (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) (t : ℝ) :
    grossenLFunction 𝔪 ψ k (1 + I * t) ≠ 0 := by
  intro hzero
  have hzero' : grossenModulusLCont 𝔪 ψ k (1 + I * t) = 0 := by
    simp [grossenModulusLCont, hzero]
  have hk2 : 1 ≤ 2 * k := by omega
  have hc : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [ofReal_one] using
      (continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hc' : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    change (σ : ℂ) ≠ 1
    exact_mod_cast (show 1 < σ from hσ).ne'
  have hdiff1 : DifferentiableAt ℂ (fun s : ℂ => grossenModulusLCont 𝔪 ψ k (s + I * t)) 1 := by
    have hre : -(3 * (k : ℝ)) < (1 + I * t : ℂ).re := by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero]
      linarith
    exact (differentiableAt_grossenModulusLCont 𝔪 ψ hk hre).comp 1
      (differentiableAt_id.add_const _)
  have hquot : Tendsto (fun σ : ℝ => grossenModulusLCont 𝔪 ψ k (σ + I * t) / ((σ : ℂ) - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (deriv (fun s : ℂ => grossenModulusLCont 𝔪 ψ k (s + I * t)) 1)) :=
    (HTGeometry.tendsto_div_sub_of_hasDerivAt_eq_zero hdiff1 hzero').comp hc'
  have hsq : Tendsto (fun σ : ℝ => grossenModulusLCont 𝔪 (ψ ^ 2) (2 * k) (σ + 2 * I * t))
      (𝓝[>] (1 : ℝ)) (𝓝 (grossenModulusLCont 𝔪 (ψ ^ 2) (2 * k) (1 + 2 * I * t))) := by
    have hre2 : -(3 * ((2 * k : ℕ) : ℝ)) < (1 + 2 * I * t : ℂ).re := by
      have hk0 : (0 : ℝ) ≤ (2 * k : ℕ) := Nat.cast_nonneg _
      simp only [add_re, one_re, mul_re, re_ofNat, I_re, zero_mul, im_ofNat, I_im, mul_one,
        sub_zero, ofReal_re, ofReal_im, mul_zero, add_zero]
      linarith
    exact (differentiableAt_grossenModulusLCont 𝔪 (ψ ^ 2) hk2 hre2).continuousAt.tendsto.comp
      (hc.add_const (2 * I * t))
  have hsub : Tendsto (fun σ : ℝ => (σ : ℂ) - 1) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa only [sub_self] using hc.sub_const 1
  have hprod := (((tendsto_sub_one_mul_heckeL_one (𝔪 := 𝔪)).pow 3).mul
    (hquot.pow 4)).mul hsq |>.mul hsub
  simp only [mul_zero] at hprod
  have hlim : Tendsto (fun σ : ℝ =>
      heckeL 𝔪 1 σ ^ 3 * grossenModulusLCont 𝔪 ψ k (σ + I * t) ^ 4 *
        grossenModulusLCont 𝔪 (ψ ^ 2) (2 * k) (σ + 2 * I * t))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hs : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show 1 < σ from hσ).ne')
    field_simp [hs]
  have hge : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      1 ≤ ‖heckeL 𝔪 1 σ ^ 3 * grossenModulusLCont 𝔪 ψ k (σ + I * t) ^ 4 *
        grossenModulusLCont 𝔪 (ψ ^ 2) (2 * k) (σ + 2 * I * t)‖ := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact one_le_norm_grossenModulus_three_four_one 𝔪 ψ hk (show 1 < σ from hσ) t
  have hcontr : (1 : ℝ) ≤ 0 := by simpa only [norm_zero] using ge_of_tendsto hlim.norm hge
  exact (not_le_of_gt zero_lt_one) hcontr

/-- **Unconditional nonvanishing on `Re w ≥ 1`:** for every `k ≥ 1`, modulus `𝔪`, and ray class
character `ψ`, `grossenLFunction 𝔪 ψ k w ≠ 0` throughout `{w : ℂ | 1 ≤ w.re}`. -/
theorem grossenLFunction_ne_zero_of_one_le_re (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) {w : ℂ} (hw : 1 ≤ w.re) :
    grossenLFunction 𝔪 ψ k w ≠ 0 := by
  rcases hw.eq_or_lt with hw | hw
  · have hw_eq : w = 1 + I * w.im := by
      apply Complex.ext
      · simpa using hw.symm
      · simp
    rw [hw_eq]
    exact grossenLFunction_line_one_ne_zero 𝔪 ψ hk w.im
  · exact grossenLFunction_ne_zero_of_one_lt_re 𝔪 ψ hk hw

theorem grossenCompletedL_ne_zero_of_one_le_re (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) {w : ℂ} (hw : 1 ≤ w.re) :
    grossenCompletedL 𝔪 ψ k w ≠ 0 := by
  have hw' : -(3 * (k : ℝ)) < w.re := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  rw [grossenCompletedL_eq_archimedean_mul 𝔪 ψ k hw']
  exact mul_ne_zero (grossenArchimedeanFactor_ne_zero 𝔪 ψ k hw')
    (grossenLFunction_ne_zero_of_one_le_re 𝔪 ψ hk hw)

/-! ### Superlinear ray growth, Hadamard rigidity, and infinitely many zeros in `1/2 ≤ Re w < 1` -/

/-- Superlinear growth of `log ‖grossenCompletedL 𝔪 ψ k σ‖` along the positive real ray (`k ≥ 1`). -/
theorem grossenCompletedL_superlinear_ray (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) (A : ℝ) :
    ∃ σ : ℝ, 1 ≤ σ ∧ A * σ < Real.log ‖grossenCompletedL 𝔪 ψ k (σ : ℂ)‖ := by
  obtain ⟨c, _, hc_pos, hc_le⟩ := exists_pos_le_and_le_norm_grossenLFunction 𝔪 ψ hk
  have hα : 0 < grossenAlpha 𝔪 ψ := grossenAlpha_pos 𝔪 ψ
  set M : ℝ := |A| + |Real.log (grossenAlpha 𝔪 ψ)| + |Real.log c| + 2
  obtain ⟨n, hfact, hn_ge⟩ :=
    ((HTGeometry.eventually_lt_log_factorial (2 * M)).and (eventually_ge_atTop (3 * k + 2))).exists
  set σ : ℝ := (n : ℝ) + 1 - 3 * (k : ℝ)
  have hk_real : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn_real : (3 * (k : ℝ) + 2) ≤ n := by exact_mod_cast hn_ge
  have hσ2 : 2 ≤ σ := by dsimp [σ]; linarith
  have hσ1 : 1 ≤ σ := by linarith
  have hσ_le_n : σ ≤ n := by dsimp [σ]; linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  refine ⟨σ, hσ1, ?_⟩
  have hw_re : -(3 * (k : ℝ)) < (σ : ℂ).re := by simp only [ofReal_re]; linarith
  have harg : (σ : ℂ) + (3 * k : ℕ) = (n : ℂ) + 1 := by
    dsimp [σ]
    push_cast
    ring
  have harch_norm : ‖grossenArchimedeanFactor 𝔪 ψ k (σ : ℂ)‖ =
      grossenAlpha 𝔪 ψ ^ (-((n : ℝ) + 1)) * (n.factorial : ℝ) := by
    rw [grossenArchimedeanFactor, harg, norm_mul, Complex.Gamma_nat_eq_factorial]
    have hpow : ‖(grossenAlpha 𝔪 ψ : ℂ) ^ (-((n : ℂ) + 1))‖ =
        grossenAlpha 𝔪 ψ ^ (-((n : ℝ) + 1)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hα]
      simp
    have hfac_norm : ‖(n.factorial : ℂ)‖ = (n.factorial : ℝ) := by
      rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    rw [hpow, hfac_norm]
  have hL_ge : c ≤ ‖grossenLFunction 𝔪 ψ k (σ : ℂ)‖ :=
    (hc_le (σ : ℂ) (by simpa using hσ2)).1
  have hfac_pos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hprod_pos : 0 < grossenAlpha 𝔪 ψ ^ (-((n : ℝ) + 1)) * (n.factorial : ℝ) * c :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hα _) hfac_pos) hc_pos
  have hnorm_ge : grossenAlpha 𝔪 ψ ^ (-((n : ℝ) + 1)) * (n.factorial : ℝ) * c ≤
      ‖grossenCompletedL 𝔪 ψ k (σ : ℂ)‖ := by
    rw [grossenCompletedL_eq_archimedean_mul 𝔪 ψ k hw_re, norm_mul, harch_norm]
    exact mul_le_mul_of_nonneg_left hL_ge (by positivity)
  have hlog_ge := Real.log_le_log hprod_pos hnorm_ge
  rw [Real.log_mul (by positivity) hc_pos.ne',
    Real.log_mul (Real.rpow_pos_of_pos hα _).ne' hfac_pos.ne',
    Real.log_rpow hα] at hlog_ge
  have hAσ : A * σ ≤ |A| * (n : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)).trans
      (mul_le_mul_of_nonneg_left hσ_le_n (abs_nonneg A))
  have hlogα : -|Real.log (grossenAlpha 𝔪 ψ)| * (2 * (n : ℝ)) ≤
      -((n : ℝ) + 1) * Real.log (grossenAlpha 𝔪 ψ) := by
    have h1 : ((n : ℝ) + 1) * Real.log (grossenAlpha 𝔪 ψ) ≤
        ((n : ℝ) + 1) * |Real.log (grossenAlpha 𝔪 ψ)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
    have h2 : ((n : ℝ) + 1) * |Real.log (grossenAlpha 𝔪 ψ)| ≤
        (2 * (n : ℝ)) * |Real.log (grossenAlpha 𝔪 ψ)| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    linarith
  have hlogc : -|Real.log c| * (n : ℝ) ≤ Real.log c := by
    have h1 : -|Real.log c| ≤ Real.log c := neg_abs_le _
    have h2 : -|Real.log c| * (n : ℝ) ≤ -|Real.log c| * 1 := by
      nlinarith [abs_nonneg (Real.log c), hn1]
    linarith
  have hM_def : 2 * M * (n : ℝ) =
      2 * |A| * (n : ℝ) + 2 * |Real.log (grossenAlpha 𝔪 ψ)| * (n : ℝ) +
        2 * |Real.log c| * (n : ℝ) + 4 * (n : ℝ) := by
    dsimp [M]; ring
  have hpos_A : 0 ≤ |A| * (n : ℝ) := mul_nonneg (abs_nonneg A) (by linarith)
  have hpos_c : 0 ≤ |Real.log c| * (n : ℝ) := mul_nonneg (abs_nonneg _) (by linarith)
  linarith

/-- **`grossenCompletedL` has infinitely many zeros in `ℂ` (`k ≥ 1`).** -/
theorem infinite_zeros_grossenCompletedL (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) :
    {w : ℂ | grossenCompletedL 𝔪 ψ k w = 0}.Infinite := by
  obtain ⟨C, hC0, hgrow⟩ := (orderOneEnvelope_grossenCompletedL 𝔪 ψ hk).subquadratic
  exact _root_.RHTower.zeroSet_infinite_of_subquadratic_superlinear_ray
    (differentiable_grossenCompletedL 𝔪 ψ hk)
    (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2) hC0 hgrow
    (grossenCompletedL_superlinear_ray 𝔪 ψ hk)

/-- Every zero of `grossenCompletedL 𝔪 ψ k` lies strictly inside the open strip `0 < Re w < 1`. -/
theorem mem_openStrip_of_grossenCompletedL_eq_zero (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw0 : grossenCompletedL 𝔪 ψ k w = 0) :
    0 < w.re ∧ w.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hle
    have hle' : w.re ≤ 0 := not_lt.mp hle
    have hre1 : 1 ≤ (1 - conj w).re := by
      simp only [sub_re, one_re, conj_re]; linarith
    have hfe := grossenCompletedL_one_sub 𝔪 ψ hk (conj w)
    rw [conj_conj, hw0, map_zero, mul_zero] at hfe
    exact grossenCompletedL_ne_zero_of_one_le_re 𝔪 ψ hk hre1 hfe
  · by_contra hge
    exact grossenCompletedL_ne_zero_of_one_le_re 𝔪 ψ hk (not_lt.mp hge) hw0

/-- **Infinitely many zeros in the right half-strip `1/2 ≤ Re w < 1`:** for every `k ≥ 1`, modulus
`𝔪`, and ray class character `ψ`, `grossenLFunction 𝔪 ψ k` has infinitely many distinct zeros in
`{w : ℂ | 1 / 2 ≤ w.re ∧ w.re < 1}`. -/
theorem infinite_zeros_grossenLFunction_right_half_strip (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) :
    {w : ℂ | 1 / 2 ≤ w.re ∧ w.re < 1 ∧ grossenLFunction 𝔪 ψ k w = 0}.Infinite := by
  intro hfin
  have hcover : {w : ℂ | grossenCompletedL 𝔪 ψ k w = 0} ⊆
      ⋃ z ∈ {z : ℂ | 1 / 2 ≤ z.re ∧ z.re < 1 ∧ grossenLFunction 𝔪 ψ k z = 0},
        ({z, 1 - conj z} : Set ℂ) := by
    intro w hw0
    have hstrip := mem_openStrip_of_grossenCompletedL_eq_zero 𝔪 ψ hk hw0
    by_cases hhalf : 1 / 2 ≤ w.re
    · have hw_re : -(3 * (k : ℝ)) < w.re := by
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have hL0 : grossenLFunction 𝔪 ψ k w = 0 := by
        rw [grossenLFunction, hw0, zero_div]
      exact mem_biUnion ⟨hhalf, hstrip.2, hL0⟩ (Or.inl rfl)
    · have hhalf' : w.re < 1 / 2 := not_le.mp hhalf
      set z : ℂ := 1 - conj w
      have hz_re : z.re = 1 - w.re := by simp [z]
      have hz_half : 1 / 2 ≤ z.re := by linarith
      have hz_lt1 : z.re < 1 := by linarith [hstrip.1]
      have hfe : grossenCompletedL 𝔪 ψ k z = 0 := by
        dsimp [z]
        rw [grossenCompletedL_one_sub 𝔪 ψ hk (conj w), conj_conj, hw0, map_zero, mul_zero]
      have hL0 : grossenLFunction 𝔪 ψ k z = 0 := by
        rw [grossenLFunction, hfe, zero_div]
      have hw_eq : w = 1 - conj z := by
        dsimp [z]
        rw [map_sub, map_one, conj_conj, sub_sub_cancel]
      exact mem_biUnion ⟨hz_half, hz_lt1, hL0⟩ (Or.inr hw_eq)
  exact infinite_zeros_grossenCompletedL 𝔪 ψ hk
    ((hfin.biUnion fun z _ => (finite_singleton (1 - conj z)).insert z).subset hcover)

/-- **Unbounded ordinates in the right half-strip:** for every `k ≥ 1` and every height `T : ℝ`,
there exists a zero `w` of `grossenLFunction 𝔪 ψ k` with `1 / 2 ≤ w.re < 1` and `T < |w.im|`. -/
theorem exists_zero_grossenLFunction_right_half_strip_im_gt (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) (T : ℝ) :
    ∃ w : ℂ, 1 / 2 ≤ w.re ∧ w.re < 1 ∧ T < |w.im| ∧ grossenLFunction 𝔪 ψ k w = 0 := by
  by_contra hnone
  set R : ℝ := max T 0 + 2
  have hf_univ : AnalyticOnNhd ℂ (grossenCompletedL 𝔪 ψ k) Set.univ :=
    (differentiable_grossenCompletedL 𝔪 ψ hk).differentiableOn.analyticOnNhd isOpen_univ
  have hf_ball : AnalyticOnNhd ℂ (grossenCompletedL 𝔪 ψ k) (Metric.closedBall 0 R) :=
    hf_univ.mono (subset_univ _)
  have hne_loc : ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ¬ ∀ᶠ w in 𝓝 z, grossenCompletedL 𝔪 ψ k w = 0 := by
    intro z _ hev
    have h2 : grossenCompletedL 𝔪 ψ k 2 = 0 :=
      hf_univ.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ z) hev (mem_univ (2 : ℂ))
    exact grossenCompletedL_ne_zero_of_one_le_re 𝔪 ψ hk (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re) h2
  have hball_fin := HTGeometry.finite_zeros_closedBall hf_ball hne_loc
  refine infinite_zeros_grossenLFunction_right_half_strip 𝔪 ψ hk (hball_fin.subset ?_)
  rintro w ⟨hw_lo, hw_hi, hL0⟩
  have him_le : |w.im| ≤ T := not_lt.mp fun him => hnone ⟨w, hw_lo, hw_hi, him, hL0⟩
  have hw_re : -(3 * (k : ℝ)) < w.re := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hΛ0 : grossenCompletedL 𝔪 ψ k w = 0 := by
    rw [grossenCompletedL_eq_archimedean_mul 𝔪 ψ k hw_re, hL0, mul_zero]
  refine ⟨?_, hΛ0⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre_abs : |w.re| ≤ 1 := abs_le.mpr ⟨by linarith, hw_hi.le⟩
  have hT_le : T ≤ max T 0 := le_max_left T 0
  calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    _ ≤ 1 + max T 0 := by linarith
    _ ≤ R := by dsimp [R]; linarith

/-! ### Analytic continuation and zero obstruction of the cubic probe correction -/

/-- **Analytic continuation of the cubic probe's principal correction to `Re s > 1/2`:**
`L(6s - 3, ψ₆ χ_{𝔣(η⁶)}) · grossenDeletedFactors(6s - 3) · fullResidualCorrection(s)`. -/
def continuedProbeCorrection (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) (s : ℂ) : ℂ :=
  grossenLFunction 𝔪 (η ^ 6) 1 (6 * s - 3) *
    grossenDeletedFactors 𝔪 (η ^ 6) 1 S (6 * s - 3) *
    fullResidualCorrection 𝔪 η (fun v => primeKappaAt 𝔪 η v ^ 6) S s

/-- `continuedProbeCorrection 𝔪 η S` is holomorphic on the entire half-plane `Re s > 1/2`. -/
theorem differentiableOn_continuedProbeCorrection (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) :
    DifferentiableOn ℂ (continuedProbeCorrection 𝔪 η S) {s : ℂ | 1 / 2 < s.re} := by
  have hA : ∀ v, ‖primeKappaAt 𝔪 η v ^ 6‖ ≤ 1 := fun v => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_primeKappaAt_le 𝔪 η v)
  have hres := (fullResidualCorrection_properties 𝔪 η _ hA S).1
  have hmap : MapsTo (fun s : ℂ => 6 * s - 3) {s : ℂ | 1 / 2 < s.re}
      {w : ℂ | -(3 * ((1 : ℕ) : ℝ)) < w.re} := by
    intro s hs
    have hs' : 1 / 2 < s.re := hs
    simp only [mem_setOf_eq, sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, Nat.cast_one]
    linarith
  have haff : DifferentiableOn ℂ (fun s : ℂ => 6 * s - 3) {s : ℂ | 1 / 2 < s.re} :=
    ((differentiable_id.const_mul (6 : ℂ)).sub (differentiable_const (3 : ℂ))).differentiableOn
  have hL : DifferentiableOn ℂ (fun s : ℂ => grossenLFunction 𝔪 (η ^ 6) 1 (6 * s - 3))
      {s : ℂ | 1 / 2 < s.re} :=
    (differentiableOn_grossenLFunction 𝔪 (η ^ 6) le_rfl).comp haff hmap
  have hdel : DifferentiableOn ℂ (fun s : ℂ => grossenDeletedFactors 𝔪 (η ^ 6) 1 S (6 * s - 3))
      {s : ℂ | 1 / 2 < s.re} :=
    ((differentiable_grossenDeletedFactors 𝔪 (η ^ 6) 1 S).comp
      ((differentiable_id.const_mul (6 : ℂ)).sub (differentiable_const (3 : ℂ)))).differentiableOn
  exact (hL.mul hdel).mul hres

/-- `continuedProbeCorrection 𝔪 η S` is uniformly bounded on `Re s ≥ 2`. -/
theorem exists_norm_continuedProbeCorrection_le (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) :
    ∃ M : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖continuedProbeCorrection 𝔪 η S s‖ ≤ M := by
  have hA : ∀ v, ‖primeKappaAt 𝔪 η v ^ 6‖ ≤ 1 := fun v => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_primeKappaAt_le 𝔪 η v)
  obtain ⟨M₁, hM₁⟩ := exists_norm_grossenLFunction_le 𝔪 (η ^ 6) le_rfl
  obtain ⟨M₃, hM₃⟩ := (fullResidualCorrection_properties 𝔪 η _ hA S).2.2
  set M₂ : ℝ := 2 ^ Fintype.card (GrossenBadPrime 𝔪 S)
  refine ⟨max M₁ 0 * M₂ * max M₃ 0, fun s hs => ?_⟩
  have hw2 : 2 ≤ (6 * s - 3).re := by
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith
  have hw0 : 0 ≤ (6 * s - 3).re := by linarith
  unfold continuedProbeCorrection
  rw [norm_mul, norm_mul]
  have hb1 : ‖grossenLFunction 𝔪 (η ^ 6) 1 (6 * s - 3)‖ ≤ max M₁ 0 :=
    (hM₁ _ hw2).trans (le_max_left _ _)
  have hb2 : ‖grossenDeletedFactors 𝔪 (η ^ 6) 1 S (6 * s - 3)‖ ≤ M₂ :=
    norm_grossenDeletedFactors_le 𝔪 (η ^ 6) 1 S hw0
  have hb3 : ‖fullResidualCorrection 𝔪 η (fun v => primeKappaAt 𝔪 η v ^ 6) S s‖ ≤ max M₃ 0 :=
    (hM₃ s hs).trans (le_max_left _ _)
  exact mul_le_mul (mul_le_mul hb1 hb2 (norm_nonneg _) (le_max_right _ _))
    hb3 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (by positivity))

/-- On `Re s > 2/3`, `continuedProbeCorrection` agrees with `fullPrincipalCorrection` whenever `S`
contains the ramified prime above `3`. -/
theorem continuedProbeCorrection_eq_fullPrincipalCorrection (𝔪 : Modulus K)
    (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S) {s : ℂ} (hs : 2 / 3 < s.re) :
    continuedProbeCorrection 𝔪 η S s =
      fullPrincipalCorrection 𝔪 η (fun v => primeKappaAt 𝔪 η v ^ 6) S s := by
  have hw1 : 1 < (6 * s - 3).re := by
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith
  rw [fullPrincipalCorrection_probe_eq_grossen_mul_residual 𝔪 η S hS hs,
    grossenEulerProductModS_eq_mul_deletedFactors 𝔪 (η ^ 6) le_rfl S hw1]
  rfl

/-- On `Re s ≥ 7/8`, `continuedProbeCorrection` agrees with `probeCorrection` whenever `S` contains
all primes of norm `≤ 160`. -/
theorem continuedProbeCorrection_eq_probeCorrection (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) {s : ℂ}
    (hs : 7 / 8 ≤ s.re) :
    continuedProbeCorrection 𝔪 η S s = probeCorrection 𝔪 η S s := by
  have hw1 : 1 < (6 * s - 3).re := by
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith
  rw [probeCorrection_eq_grossen_mul_residual 𝔪 η S hS hs,
    grossenEulerProductModS_eq_mul_deletedFactors 𝔪 (η ^ 6) le_rfl S hw1]
  rfl

/-- **Exact zero-locus characterization on `Re s > 1/2`:** for **every** finite prime set `S`,
`continuedProbeCorrection 𝔪 η S s = 0 ↔ grossenLFunction 𝔪 (η ^ 6) 1 (6 * s - 3) = 0`. -/
theorem continuedProbeCorrection_eq_zero_iff (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) {s : ℂ} (hs : 1 / 2 < s.re) :
    continuedProbeCorrection 𝔪 η S s = 0 ↔
      grossenLFunction 𝔪 (η ^ 6) 1 (6 * s - 3) = 0 := by
  have hA : ∀ v, ‖primeKappaAt 𝔪 η v ^ 6‖ ≤ 1 := fun v => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_primeKappaAt_le 𝔪 η v)
  have hw0 : 0 < (6 * s - 3).re := by
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith
  have hdel_ne := grossenDeletedFactors_ne_zero 𝔪 (η ^ 6) 1 S hw0
  have hres_ne := (fullResidualCorrection_properties 𝔪 η _ hA S).2.1 s hs
  unfold continuedProbeCorrection
  rw [mul_assoc, mul_eq_zero]
  exact or_iff_left (mul_ne_zero hdel_ne hres_ne)

/-- **Unconditional nonvanishing on `Re s ≥ 2/3`:** for every finite prime set `S`,
`continuedProbeCorrection 𝔪 η S s ≠ 0` for all `s` with `2 / 3 ≤ s.re`. -/
theorem continuedProbeCorrection_ne_zero_of_two_thirds_le (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) {s : ℂ} (hs : 2 / 3 ≤ s.re) :
    continuedProbeCorrection 𝔪 η S s ≠ 0 := by
  rw [ne_eq, continuedProbeCorrection_eq_zero_iff 𝔪 η S (by linarith)]
  refine grossenLFunction_ne_zero_of_one_le_re 𝔪 (η ^ 6) le_rfl ?_
  simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
  linarith

/-- **Infinitely many zeros in `7/12 ≤ Re s < 2/3` with unbounded ordinates:** for every finite
prime set `S` and every height `T : ℝ`, `continuedProbeCorrection 𝔪 η S` has a zero in
`7/12 ≤ Re s < 2/3` with `T < |s.im|` (and infinitely many zeros in `7/12 ≤ Re s < 2/3`). -/
theorem exists_zero_continuedProbeCorrection_in_strip_im_gt (𝔪 : Modulus K)
    (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O)) (T : ℝ) :
    ∃ s : ℂ, 7 / 12 ≤ s.re ∧ s.re < 2 / 3 ∧ T < |s.im| ∧
      continuedProbeCorrection 𝔪 η S s = 0 := by
  obtain ⟨w, hw_lo, hw_hi, hw_im, hw0⟩ :=
    exists_zero_grossenLFunction_right_half_strip_im_gt 𝔪 (η ^ 6) le_rfl (6 * max T 0)
  set s : ℂ := (w + 3) / 6
  have hs_re : s.re = (w.re + 3) / 6 := by
    dsimp [s]
    rw [div_eq_mul_inv, show (6 : ℂ)⁻¹ = ((6⁻¹ : ℝ) : ℂ) by norm_num,
      mul_comm, Complex.re_ofReal_mul]
    simp only [add_re, re_ofNat]
    ring
  have hs_im : s.im = w.im / 6 := by
    dsimp [s]
    rw [div_eq_mul_inv, show (6 : ℂ)⁻¹ = ((6⁻¹ : ℝ) : ℂ) by norm_num,
      mul_comm, Complex.im_ofReal_mul]
    simp only [add_im, im_ofNat, add_zero]
    ring
  have h6s : 6 * s - 3 = w := by dsimp [s]; ring
  have hs_lo : 7 / 12 ≤ s.re := by rw [hs_re]; linarith
  have hs_hi : s.re < 2 / 3 := by rw [hs_re]; linarith
  have hs_im_gt : T < |s.im| := by
    rw [hs_im, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have hT : T ≤ max T 0 := le_max_left T 0
    linarith
  refine ⟨s, hs_lo, hs_hi, hs_im_gt, ?_⟩
  rw [continuedProbeCorrection_eq_zero_iff 𝔪 η S (by linarith), h6s]
  exact hw0

theorem infinite_zeros_continuedProbeCorrection_in_strip (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) :
    {s : ℂ | 7 / 12 ≤ s.re ∧ s.re < 2 / 3 ∧ continuedProbeCorrection 𝔪 η S s = 0}.Infinite := by
  have hinj : Function.Injective (fun w : ℂ => (w + 3) / (6 : ℂ)) := by
    intro w₁ w₂ h
    linear_combination 6 * h
  refine Set.Infinite.mono ?_
    ((infinite_zeros_grossenLFunction_right_half_strip 𝔪 (η ^ 6) le_rfl).image hinj.injOn)
  rintro _ ⟨w, ⟨hw_lo, hw_hi, hw0⟩, rfl⟩
  have hs_re : ((w + 3) / (6 : ℂ)).re = (w.re + 3) / 6 := by
    rw [div_eq_mul_inv, show (6 : ℂ)⁻¹ = ((6⁻¹ : ℝ) : ℂ) by norm_num,
      mul_comm, Complex.re_ofReal_mul]
    simp only [add_re, re_ofNat]
    ring
  have h6s : 6 * ((w + 3) / (6 : ℂ)) - 3 = w := by ring
  refine ⟨by rw [hs_re]; linarith, by rw [hs_re]; linarith, ?_⟩
  rw [continuedProbeCorrection_eq_zero_iff 𝔪 η S (by rw [hs_re]; linarith), h6s]
  exact hw0

/-- **No-go obstruction below `7/12`:** for every `σ₀ < 7/12` and every finite prime set `S`
containing the primes of norm `≤ 160`, no function `G` holomorphic on `Re s > σ₀` that agrees with
`probeCorrection 𝔪 η S` on `Re s ≥ 2` can be nonvanishing throughout `Re s > σ₀`. -/
theorem no_nonvanishing_continuation_of_probeCorrection_below_seven_twelfths
    (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S)
    {σ₀ : ℝ} (hσ₀ : σ₀ < 7 / 12) :
    ¬ ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, 2 ≤ s.re → G s = probeCorrection 𝔪 η S s) ∧
      (∀ s : ℂ, σ₀ < s.re → G s ≠ 0) := by
  rintro ⟨G, hG_diff, hG_eq, hG_ne⟩
  set U : Set ℂ := {s : ℂ | max σ₀ (1 / 2) < s.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const continuous_re
  have hU_pre : IsPreconnected U := by
    have hU_eq : U = Complex.reCLM ⁻¹' Set.Ioi (max σ₀ (1 / 2)) := rfl
    rw [hU_eq]
    exact ((convex_Ioi _).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hsub1 : U ⊆ {s : ℂ | σ₀ < s.re} := by
    intro s hs
    have hs' : max σ₀ (1 / 2) < s.re := hs
    show σ₀ < s.re
    exact lt_of_le_of_lt (le_max_left _ _) hs'
  have hsub2 : U ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    have hs' : max σ₀ (1 / 2) < s.re := hs
    show 1 / 2 < s.re
    exact lt_of_le_of_lt (le_max_right _ _) hs'
  have hdiff_sub : DifferentiableOn ℂ (G - continuedProbeCorrection 𝔪 η S) U :=
    (hG_diff.mono hsub1).sub ((differentiableOn_continuedProbeCorrection 𝔪 η S).mono hsub2)
  have hana : AnalyticOnNhd ℂ (G - continuedProbeCorrection 𝔪 η S) U :=
    hdiff_sub.analyticOnNhd hU_open
  have h3_mem : (3 : ℂ) ∈ U := by
    change max σ₀ (1 / 2) < (3 : ℂ).re
    simp only [re_ofNat]
    exact max_lt (by linarith) (by norm_num)
  have hev : (G - continuedProbeCorrection 𝔪 η S) =ᶠ[𝓝 (3 : ℂ)] 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℝ) < (3 : ℂ).re)] with s hs
    have hs2 : 2 ≤ s.re := le_of_lt hs
    change G s - continuedProbeCorrection 𝔪 η S s = 0
    rw [hG_eq s hs2, continuedProbeCorrection_eq_probeCorrection 𝔪 η S hS (by linarith), sub_self]
  obtain ⟨s₀, hs₀_lo, hs₀_hi, _, hs₀_zero⟩ :=
    exists_zero_continuedProbeCorrection_in_strip_im_gt 𝔪 η S 0
  have hs₀_mem : s₀ ∈ U := by
    change max σ₀ (1 / 2) < s₀.re
    exact max_lt (lt_of_lt_of_le hσ₀ hs₀_lo) (by linarith)
  have hsub0 : G s₀ - continuedProbeCorrection 𝔪 η S s₀ = 0 :=
    hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_pre h3_mem hev hs₀_mem
  rw [hs₀_zero, sub_zero] at hsub0
  exact hG_ne s₀ (lt_of_lt_of_le hσ₀ hs₀_lo) hsub0

end GaloisForLFunctions.FamilyContinuationTheory
