import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35LargeA
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattDivisorEnergy

/-!
# One-unit-factor branch of Matomäki--Teräväinen Lemma 3.5

Instead of sending both copies of the reciprocal unit block through one affine mean square,
retain one copy pointwise.  The remaining product has support `2 A N'`; its coefficient energy
contains the useful factor `A⁻² N⁻¹`, up to an arbitrarily small divisor power.  Combining this
with the constructed second-derivative estimate gives a new unconditional hybrid range.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Coefficients of one reciprocal unit block times the arbitrary data block. -/
def mtWattOneUnitCoeff (a : ℕ → ℂ) (A N N' : ℕ) : Fin ((2 * A) * N') → ℂ :=
  dirConv (2 * A) N' (mtWattDataCoeff a A) (mtWattUnitCoeff N N')

/-- The one-unit-factor product is one Dirichlet polynomial. -/
theorem mtWattOneUnitProduct_eq_dirPoly
    (a : ℕ → ℂ) (A N N' : ℕ) (t : ℝ) :
    mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t =
      dirPoly ((2 * A) * N') (mtWattOneUnitCoeff a A N N') (-t) := by
  rw [mtWattUnitBlock_eq_dirPoly, mtWattCoefficientBlock_eq_dirPoly]
  calc
    dirPoly N' (mtWattUnitCoeff N N') (-t) *
        dirPoly (2 * A) (mtWattDataCoeff a A) (-t) =
      dirPoly (2 * A) (mtWattDataCoeff a A) (-t) *
        dirPoly N' (mtWattUnitCoeff N N') (-t) := by ring
    _ = dirPoly ((2 * A) * N') (mtWattOneUnitCoeff a A N N') (-t) := by
      rw [dirPoly_mul_eq_dirPoly]
      rfl

/-- The one-unit-factor coefficient energy retains `A⁻² N⁻¹`, up to one divisor power. -/
theorem exists_sum_norm_sq_mtWattOneUnitCoeff_le_divisor
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
      (∑ r : Fin ((2 * A) * N'), ‖mtWattOneUnitCoeff a A N N' r‖ ^ 2) ≤
        C * (((2 * A) * N' : ℕ) : ℝ) ^ δ *
          (1 / (A : ℝ) ^ 2) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
          (1 / (N : ℝ)) := by
  obtain ⟨C, hC, hconv⟩ := exists_sum_norm_sq_dirConv_le_rpow hδ
  refine ⟨C, hC, ?_⟩
  intro a A N N' hA hN hN'
  let b := mtWattDataCoeff a A
  let u := mtWattUnitCoeff N N'
  let E : ℝ := ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2
  have hb := sum_norm_sq_mtWattDataCoeff_le_energy a hA
  have hu := sum_norm_sq_mtWattUnitCoeff_le_inv hN hN'
  have hpow0 : 0 ≤ (((2 * A) * N' : ℕ) : ℝ) ^ δ :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCpow0 : 0 ≤ C * (((2 * A) * N' : ℕ) : ℝ) ^ δ :=
    mul_nonneg hC.le hpow0
  have hbase := hconv (2 * A) N' b u
  calc
    (∑ r : Fin ((2 * A) * N'), ‖mtWattOneUnitCoeff a A N N' r‖ ^ 2) ≤
        C * (((2 * A) * N' : ℕ) : ℝ) ^ δ *
          ((∑ j : Fin (2 * A), ‖b j‖ ^ 2) *
            (∑ k : Fin N', ‖u k‖ ^ 2)) := by
      simpa only [mtWattOneUnitCoeff, b, u] using hbase
    _ ≤ C * (((2 * A) * N' : ℕ) : ℝ) ^ δ *
          (((1 / (A : ℝ) ^ 2) * E) * (1 / (N : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hCpow0
      exact mul_le_mul hb hu (by positivity) (by positivity)
    _ = C * (((2 * A) * N' : ℕ) : ℝ) ^ δ *
          (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) := by ring

/-- Affine mean square for the one-unit-factor product. -/
theorem exists_integral_normSq_mtWattOneUnitProduct_le
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
      ∀ T : ℝ, 1 ≤ T →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * (((2 * A) * N' : ℕ) : ℝ) ^ δ *
          (T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
          (1 / (N : ℝ)) := by
  obtain ⟨C₀, hC₀, henergy⟩ :=
    exists_sum_norm_sq_mtWattOneUnitCoeff_le_divisor hδ
  let Caff : ℝ := 5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2
  refine ⟨Caff * C₀, mul_pos (by dsimp [Caff]; positivity) hC₀, ?_⟩
  intro a A N N' hA hN hN' T hT
  let M := (2 * A) * N'
  let c := mtWattOneUnitCoeff a A N N'
  let Ec := ∑ r : Fin M, ‖c r‖ ^ 2
  let E : ℝ := ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2
  let P : ℝ := ((M : ℕ) : ℝ) ^ δ
  have hT0 : 0 ≤ T := by linarith
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hEc0 : 0 ≤ Ec := by dsimp only [Ec]; positivity
  have hweight :
      (∑ r : Fin M, (((r : ℕ) : ℝ) + 1) * ‖c r‖ ^ 2) ≤ (M : ℝ) * Ec := by
    dsimp only [Ec]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ => by
      have hrM : (r : ℕ) + 1 ≤ M := by omega
      have hrMR : (((r : ℕ) : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast hrM
      exact mul_le_mul_of_nonneg_right hrMR (sq_nonneg _)
  have haff := integral_Icc_normSq_dirPoly_le_affine c hT
  have hfull :
      (∫ t in Set.Icc (-T) T, ‖dirPoly M c t‖ ^ 2) ≤
        Caff * (T + (M : ℝ)) * Ec := by
    calc
      _ ≤ 5 * Real.pi * Real.exp 1 *
            (∑ r : Fin M, (((r : ℕ) : ℝ) + 1) * ‖c r‖ ^ 2) +
          (5 * Real.pi / 2) * Ec * T := by
        simpa only [M, c, Ec] using haff
      _ ≤ 5 * Real.pi * Real.exp 1 * ((M : ℝ) * Ec) +
          (5 * Real.pi / 2) * Ec * T := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hweight (by positivity)) le_rfl
      _ ≤ Caff * (T + (M : ℝ)) * Ec := by
        dsimp only [Caff]
        have hcross : 0 ≤
            (5 * Real.pi * Real.exp 1) * T * Ec +
              (5 * Real.pi / 2) * (M : ℝ) * Ec := by positivity
        nlinarith
  have hreflect :
      (∫ t in Set.Icc (-T) T, ‖dirPoly M c (-t)‖ ^ 2) =
        ∫ t in Set.Icc (-T) T, ‖dirPoly M c t‖ ^ 2 :=
    GaloisForLFunctions.HTGeometry.integral_Icc_normSq_comp_neg
      (fun t : ℝ => dirPoly M c t) hT0
  have hcont : Continuous (fun t : ℝ => ‖dirPoly M c (-t)‖ ^ 2) :=
    ((continuous_dirPoly M c).comp continuous_neg).norm.pow 2
  have hsubset : Set.Ioc (T / 2) T ⊆ Set.Icc (-T) T := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hmono :
      (∫ t in Set.Ioc (T / 2) T, ‖dirPoly M c (-t)‖ ^ 2) ≤
        ∫ t in Set.Icc (-T) T, ‖dirPoly M c (-t)‖ ^ 2 :=
    MeasureTheory.setIntegral_mono_set hcont.integrableOn_Icc
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall fun _ ht => hsubset ht)
  have henergy' : Ec ≤ C₀ * P * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) := by
    simpa only [Ec, E, P, M, c, mul_assoc] using
      henergy a A N N' hA hN hN'
  have hfactor0 : 0 ≤ Caff * (T + (M : ℝ)) := by
    dsimp only [Caff]
    positivity
  calc
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t‖ ^ 2) =
        ∫ t in (T / 2)..T, ‖dirPoly M c (-t)‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      change ‖mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t‖ ^ 2 =
        ‖dirPoly M c (-t)‖ ^ 2
      rw [show dirPoly M c (-t) =
          mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t by
        simpa only [M, c] using (mtWattOneUnitProduct_eq_dirPoly a A N N' t).symm]
    _ = ∫ t in Set.Ioc (T / 2) T, ‖dirPoly M c (-t)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith)]
    _ ≤ ∫ t in Set.Icc (-T) T, ‖dirPoly M c (-t)‖ ^ 2 := hmono
    _ ≤ Caff * (T + (M : ℝ)) * Ec := by rw [hreflect]; exact hfull
    _ ≤ Caff * (T + (M : ℝ)) *
        (C₀ * P * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left henergy' hfactor0
    _ = (Caff * C₀) * ((M : ℕ) : ℝ) ^ δ *
          (T + (M : ℝ)) * (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) := by
      dsimp only [P]
      ring

/-- Second-derivative hybrid with one reciprocal unit factor retained pointwise. -/
theorem exists_integral_mtWatt_oneUnit_secondDerivative
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * (((2 * A) * N' : ℕ) : ℝ) ^ δ *
          (T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
          (1 / (N : ℝ)) *
          (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2 := by
  obtain ⟨C₀, hC₀, hbase⟩ := exists_integral_normSq_mtWattOneUnitProduct_le hδ
  refine ⟨(3072 : ℝ) ^ 2 * C₀, mul_pos (by positivity) hC₀, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT
  let U : ℝ := 3072 * (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T)
  have hT1 : 1 ≤ T := one_le_two.trans hT
  have hTpos : 0 < T := zero_lt_two.trans_le hT
  have hU0 : 0 ≤ U := by dsimp only [U]; positivity
  have hpoint : ∀ t ∈ Set.Icc (T / 2) T,
      ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 ≤
        U ^ 2 * ‖mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t‖ ^ 2 := by
    intro t ht
    have hu := norm_mtWattUnitBlock_le_secondDerivativeWindow hN hNN' hN'
      hTpos ht.1 ht.2
    have hu2 := pow_le_pow_left₀ (norm_nonneg _) (show ‖mtWattUnitBlock N N' t‖ ≤ U by
      simpa only [U] using hu) 2
    rw [norm_mul, mul_pow]
    nlinarith [sq_nonneg ‖mtWattUnitBlock N N' t‖,
      sq_nonneg ‖mtWattCoefficientBlock a A t‖]
  have hunitCont : Continuous (mtWattUnitBlock N N') := continuous_perronPoly _ _ _
  have hcoeffCont : Continuous (mtWattCoefficientBlock a A) := continuous_perronPoly _ _ _
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun t : ℝ => ‖mtWattUnitBlock N N' t‖ ^ 4 *
      ‖mtWattCoefficientBlock a A t‖ ^ 2)
    (g := fun t : ℝ => U ^ 2 *
      ‖mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t‖ ^ 2)
    (by linarith : T / 2 ≤ T)
    (((hunitCont.norm.pow 4).mul (hcoeffCont.norm.pow 2)).intervalIntegrable _ _)
    ((continuous_const.mul ((hunitCont.mul hcoeffCont).norm.pow 2)).intervalIntegrable _ _)
    hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hprod := hbase a A N N' hA hN hN' T hT1
  have hscaled := mul_le_mul_of_nonneg_left hprod (sq_nonneg U)
  calc
    _ ≤ U ^ 2 *
        (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t‖ ^ 2) := hmono
    _ ≤ U ^ 2 *
        (C₀ * (((2 * A) * N' : ℕ) : ℝ) ^ δ *
          (T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
          (1 / (N : ℝ))) := hscaled
    _ = ((3072 : ℝ) ^ 2 * C₀) * (((2 * A) * N' : ℕ) : ℝ) ^ δ *
          (T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
          (1 / (N : ℝ)) *
          (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2 := by
      dsimp only [U]
      ring

/-- On the source height range `A,N ≤ T`, the divisor power in the one-unit hybrid is absorbed
inside the requested `T^ε`; no comparison or analytic premise remains. -/
theorem exists_integral_mtWatt_oneUnit_secondDerivative_height
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → (A : ℝ) ≤ T → (N : ℝ) ≤ T →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * T ^ ε *
          (T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
          (1 / (N : ℝ)) *
          (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2 := by
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨C, hC, hbase⟩ := exists_integral_mtWatt_oneUnit_secondDerivative hδ
  refine ⟨C, hC, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hAT hNT
  have hT0 : 0 ≤ T := by positivity
  have hA0 : 0 ≤ (A : ℝ) := Nat.cast_nonneg _
  have hN'0 : 0 ≤ (N' : ℝ) := Nat.cast_nonneg _
  have hN'T : (N' : ℝ) ≤ 2 * T := by
    have hcast : (N' : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN'
    linarith
  have hMquad : (((2 * A) * N' : ℕ) : ℝ) ≤ 4 * T ^ 2 := by
    push_cast
    have hmul := mul_le_mul hAT hN'T hN'0 hT0
    nlinarith
  have hTtwo : 4 ≤ T ^ 2 := by nlinarith
  have hMfour : (((2 * A) * N' : ℕ) : ℝ) ≤ T ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_right hTtwo (sq_nonneg T)
    nlinarith
  have hpow : (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) ≤ T ^ ε := by
    calc
      (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) ≤ (T ^ 4) ^ (ε / 4) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hMfour hδ.le
      _ = T ^ ε := by
        have hfour : T ^ (4 : ℕ) = T ^ (4 : ℝ) :=
          (Real.rpow_natCast T 4).symm
        rw [hfour, ← Real.rpow_mul hT0]
        congr 1
        ring
  have hraw := hbase a A N N' hA hN hNN' hN' T hT
  let R : ℝ :=
    (T + (((2 * A) * N' : ℕ) : ℝ)) *
      (1 / (A : ℝ) ^ 2) *
      (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
      (1 / (N : ℝ)) *
      (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hscaled := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC.le hR0)
  calc
    _ ≤ C * (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) * R := by
      simpa only [R, hδ, mul_assoc] using hraw
    _ ≤ C * T ^ ε * R := by
      calc
        C * (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) * R =
            (C * R) * (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) := by ring
        _ ≤ (C * R) * T ^ ε := hscaled
        _ = C * T ^ ε * R := by ring
    _ = _ := by
      dsimp only [R]
      ring

end

end RHTower.Sieve
