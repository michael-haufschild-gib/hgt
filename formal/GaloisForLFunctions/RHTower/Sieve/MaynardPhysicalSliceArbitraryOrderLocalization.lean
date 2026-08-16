import GaloisForLFunctions.RHTower.Sieve.MaynardMellinArbitraryOrderDecay
import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceLocalization
import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceCountNormalization
import GaloisForLFunctions.HTGeometry.PowerTailIntegral

noncomputable section
namespace RHTower.Sieve

open Complex Finset MeasureTheory Set
open GaloisForLFunctions.HTGeometry

theorem exists_integral_routeTNormalizedSmoothWindowMellin_one_natOrder_tail_le
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ N H U : ℝ, 1 ≤ N → 0 < H → H ≤ N → 0 < U →
        (∫ y in {y : ℝ | U ≤ |y|},
            ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖) ≤
          Cj * (N / H) ^ (j + 1) * U ^ (-(j : ℝ)) := by
  obtain ⟨Dj, hDj, hraw⟩ :=
    exists_routeTNormalizedSmoothWindowMellin_natOrder_narrow_bound j
  let Cj : ℝ := max 1 (2 * Dj / (j : ℝ))
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hCj : 1 ≤ Cj := le_max_left _ _
  refine ⟨Cj, hCj, ?_⟩
  intro N H U hN hH hHN hU
  let f : ℝ → ℝ := fun y =>
    ‖routeTNormalizedSmoothWindowMellin N H
      ((1 : ℂ) + (y : ℝ) * I)‖
  let K : ℝ := Dj * (N / H) ^ (j + 1)
  have hpoint : ∀ y : ℝ, U ≤ |y| →
      f y ≤ K * |y| ^ (-((j + 1 : ℕ) : ℝ)) := by
    intro y hy
    have hypos : 0 < |y| := hU.trans_le hy
    have hbound := hraw N H hN hH hHN
      ((1 : ℂ) + (y : ℝ) * I) (by norm_num) (by norm_num)
    norm_num at hbound
    have hpow : |y| ^ (-((j + 1 : ℕ) : ℝ)) =
        (|y| ^ (j + 1))⁻¹ := by
      rw [Real.rpow_neg (abs_nonneg y), Real.rpow_natCast]
    rw [hpow]
    rw [mul_comm]
    apply (le_inv_mul_iff₀ (pow_pos hypos (j + 1))).2
    dsimp only [f, K]
    have hNpow : N ^ (1 + (j : ℝ)) = N ^ (j + 1) := by
      rw [show (1 : ℝ) + (j : ℝ) = ((j + 1 : ℕ) : ℝ) by norm_num; ring,
        Real.rpow_natCast]
    rw [hNpow] at hbound
    have hbound' : |y| ^ (j + 1) *
        ‖routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I)‖ ≤ K := by
      calc
        |y| ^ (j + 1) *
            ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖ ≤
            Dj / H ^ (j + 1) * N ^ (j + 1) := hbound
        _ = Dj * (N / H) ^ (j + 1) := by
          rw [div_pow]
          field_simp
    exact hbound'
  have hp : (1 : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_add_one_iff.mpr hj)
  have htail := setIntegral_le_of_le_powerTail
    (f := f) (K := K) (t := U) (p := ((j + 1 : ℕ) : ℝ))
    (fun y => norm_nonneg _) hU hp hpoint
  have hexp : (1 : ℝ) - ((j + 1 : ℕ) : ℝ) = -(j : ℝ) := by
    norm_num
  have hfactor : 2 * Dj / (j : ℝ) ≤ Cj := le_max_right _ _
  have hscale : 0 ≤ (N / H) ^ (j + 1) * U ^ (-(j : ℝ)) := by positivity
  change (∫ y in {y : ℝ | U ≤ |y|}, f y) ≤ _
  calc
    (∫ y in {y : ℝ | U ≤ |y|}, f y) ≤
        2 * K * (U ^ (1 - ((j + 1 : ℕ) : ℝ)) /
          (((j + 1 : ℕ) : ℝ) - 1)) := htail
    _ = (2 * Dj / (j : ℝ)) *
        ((N / H) ^ (j + 1) * U ^ (-(j : ℝ))) := by
      dsimp only [K]
      rw [hexp]
      norm_num
      field_simp
    _ ≤ Cj * ((N / H) ^ (j + 1) * U ^ (-(j : ℝ))) :=
      mul_le_mul_of_nonneg_right hfactor hscale
    _ = Cj * (N / H) ^ (j + 1) * U ^ (-(j : ℝ)) := by ring

theorem exists_integral_routeTAdjacentNormalizedKernel_one_natOrder_tail_le
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ N H R U : ℝ, 1 ≤ N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N → 0 < U →
        (∫ y in {y : ℝ | U ≤ |y|},
            ‖routeTNormalizedSmoothWindowMellin N R
                  ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                  ((1 : ℂ) + (y : ℝ) * I)‖) ≤
          Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ)) := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_routeTNormalizedSmoothWindowMellin_one_natOrder_tail_le j hj
  let Cj : ℝ := (1 + (2 : ℝ) ^ (j + 1)) * C
  have hCj : 1 ≤ Cj := by
    dsimp only [Cj]
    have hpownn : 0 ≤ (2 : ℝ) ^ (j + 1) := by positivity
    nlinarith [hC]
  refine ⟨Cj, hCj, ?_⟩
  intro N H R U hN hH hR hHR hRH hRN hU
  let tail : Set ℝ := {y : ℝ | U ≤ |y|}
  let KR : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I)
  let KH : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  have hHleN : H ≤ N := hHR.trans hRN
  have htailR := htail N R U hN hR hRN hU
  have htailH := htail N H U hN hH hHleN hU
  have hKR : Integrable KR :=
    integrable_routeTNormalizedSmoothWindowMellin_one (by linarith) hR
  have hKH : Integrable KH :=
    integrable_routeTNormalizedSmoothWindowMellin_one (by linarith) hH
  have hmono : (∫ y in tail, ‖KR y - KH y‖) ≤
      ∫ y in tail, (‖KR y‖ + ‖KH y‖) := by
    apply setIntegral_mono_on (hKR.sub hKH).norm.integrableOn
      (hKR.norm.add hKH.norm).integrableOn (measurableSet_centralTail _)
    intro y _hy
    exact norm_sub_le _ _
  have hsplit : (∫ y in tail, (‖KR y‖ + ‖KH y‖)) =
      (∫ y in tail, ‖KR y‖) + ∫ y in tail, ‖KH y‖ :=
    integral_add hKR.norm.integrableOn hKH.norm.integrableOn
  have hratio : R / H ≤ 2 := (div_le_iff₀ hH).2 hRH
  have hratio0 : 0 ≤ R / H := by positivity
  have hratioPow : (R / H) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) :=
    pow_le_pow_left₀ hratio0 hratio (j + 1)
  have hrewrite : N / H = (N / R) * (R / H) := by field_simp
  have hNH : (N / H) ^ (j + 1) ≤
      (2 : ℝ) ^ (j + 1) * (N / R) ^ (j + 1) := by
    rw [hrewrite, mul_pow]
    calc
      (N / R) ^ (j + 1) * (R / H) ^ (j + 1) ≤
          (N / R) ^ (j + 1) * (2 : ℝ) ^ (j + 1) :=
        mul_le_mul_of_nonneg_left hratioPow (by positivity)
      _ = (2 : ℝ) ^ (j + 1) * (N / R) ^ (j + 1) := by ring
  have hfac : 0 ≤ U ^ (-(j : ℝ)) := Real.rpow_nonneg hU.le _
  have hHbound : C * (N / H) ^ (j + 1) * U ^ (-(j : ℝ)) ≤
      C * ((2 : ℝ) ^ (j + 1) * (N / R) ^ (j + 1)) *
        U ^ (-(j : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hfac
    exact mul_le_mul_of_nonneg_left hNH (by linarith)
  calc
    (∫ y in {y : ℝ | U ≤ |y|},
        ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖) =
        ∫ y in tail, ‖KR y - KH y‖ := by rfl
    _ ≤ ∫ y in tail, (‖KR y‖ + ‖KH y‖) := hmono
    _ = (∫ y in tail, ‖KR y‖) + ∫ y in tail, ‖KH y‖ := hsplit
    _ ≤ C * (N / R) ^ (j + 1) * U ^ (-(j : ℝ)) +
        C * (N / H) ^ (j + 1) * U ^ (-(j : ℝ)) :=
      add_le_add (by simpa only [tail, KR] using htailR)
        (by simpa only [tail, KH] using htailH)
    _ ≤ C * (N / R) ^ (j + 1) * U ^ (-(j : ℝ)) +
        C * ((2 : ℝ) ^ (j + 1) * (N / R) ^ (j + 1)) *
          U ^ (-(j : ℝ)) := add_le_add le_rfl hHbound
    _ = Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ)) := by
      dsimp only [Cj]
      ring

theorem exists_integral_norm_physicalSlice_mul_adjacentKernel_natOrder_tail_le
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ {A B : ℕ}, 1 ≤ A → ∀ {N H R U : ℝ},
        1 ≤ N → 0 < H → 0 < R → H ≤ R → R ≤ 2 * H → R ≤ N → 0 < U →
        (∫ y in {y : ℝ | U ≤ |y|},
          ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖) ≤
          ((B : ℝ) * (Real.log B / A)) *
            (Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ))) := by
  obtain ⟨Cj, hCj, htail⟩ :=
    exists_integral_routeTAdjacentNormalizedKernel_one_natOrder_tail_le j hj
  refine ⟨Cj, hCj, ?_⟩
  intro A B hA N H R U hN hH hR hHR hRH hRN hU
  let F : ℝ → ℂ := fun y =>
    dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I) -
      routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  let P : ℝ := (B : ℝ) * (Real.log B / A)
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hKint : Integrable (fun y => ‖K y‖) := by
    exact ((integrable_routeTNormalizedSmoothWindowMellin_one hN0 hR).sub
      (integrable_routeTNormalizedSmoothWindowMellin_one hN0 hH)).norm
  have hprod : Integrable (fun y => ‖F y * K y‖) :=
    (integrable_physicalSlice_mul_adjacentNormalizedMellin hA hN0 hH hR).norm
  have hP : 0 ≤ P := (norm_nonneg (F 0)).trans (by
    simpa only [F, neg_zero] using
      norm_dirPoly_routeTVonMangoldtSliceCoeff_le (B := B) hA 0)
  have hmono : (∫ y in {y : ℝ | U ≤ |y|}, ‖F y * K y‖) ≤
      ∫ y in {y : ℝ | U ≤ |y|}, P * ‖K y‖ := by
    apply setIntegral_mono_on hprod.integrableOn
      (hKint.const_mul P).integrableOn
        (measurableSet_le measurable_const continuous_abs.measurable)
    intro y _hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_dirPoly_routeTVonMangoldtSliceCoeff_le hA (-y)) (norm_nonneg _)
  have hscale : (∫ y in {y : ℝ | U ≤ |y|}, P * ‖K y‖) =
      P * ∫ y in {y : ℝ | U ≤ |y|}, ‖K y‖ := by
    rw [MeasureTheory.integral_const_mul]
  have hfar := htail N H R U hN hH hR hHR hRH hRN hU
  calc
    (∫ y in {y : ℝ | U ≤ |y|},
        ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I))‖) =
        ∫ y in {y : ℝ | U ≤ |y|}, ‖F y * K y‖ := by rfl
    _ ≤ ∫ y in {y : ℝ | U ≤ |y|}, P * ‖K y‖ := hmono
    _ = P * ∫ y in {y : ℝ | U ≤ |y|}, ‖K y‖ := hscale
    _ ≤ P * (Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ))) :=
      mul_le_mul_of_nonneg_left (by simpa only [K] using hfar) hP
    _ = _ := by rfl

/-- Arbitrary-order physical localization.  Order `j+1` changes the far-tail cost from
`(N/R)^2 / V` to `(N/R)^(j+1) V^(-j)`, so a fixed loss is reached at ordinate exponent
`1 + 1/j` rather than `2`. -/
theorem exists_positive_interval_norm_ge_quarter_of_physicalSlice_natOrder_annulus
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ {A B : ℕ}, 1 ≤ A → ∀ {N H R D U T V : ℝ},
        1 ≤ N → 0 < H → 0 < R → H ≤ R → R ≤ 2 * H → R ≤ N →
        0 ≤ U → U ≤ T → T ≤ V → 0 < V → U * (2 * R / N) ≤ 1 →
        D ≤ ‖∫ y : ℝ,
          dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖ →
        let E := D -
          16 * ((B : ℝ) * (Real.log B / A)) * (R / N) * U ^ 2 -
          ((B : ℝ) * (Real.log B / A)) *
            (Cj * (N / R) ^ (j + 1) * V ^ (-(j : ℝ)))
        E / 4 ≤ ‖∫ y in U..T,
          dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖ ∨
        E / 4 ≤ ‖∫ y in T..V,
          dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖ := by
  obtain ⟨Cj, hCj, htail⟩ :=
    exists_integral_norm_physicalSlice_mul_adjacentKernel_natOrder_tail_le j hj
  refine ⟨Cj, hCj, ?_⟩
  intro A B hA N H R D U T V hN hH hR hHR hRH hRN hU hUT hTV hV hsmall hfull
  let f : ℝ → ℂ := fun y =>
    dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
      (routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * I) -
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I))
  let E : ℝ := D -
    16 * ((B : ℝ) * (Real.log B / A)) * (R / N) * U ^ 2 -
    ((B : ℝ) * (Real.log B / A)) *
      (Cj * (N / R) ^ (j + 1) * V ^ (-(j : ℝ)))
  change E / 4 ≤ ‖∫ y in U..T,
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖ ∨
    E / 4 ≤ ‖∫ y in T..V,
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hf : Integrable f :=
    integrable_physicalSlice_mul_adjacentNormalizedMellin hA hN0 hH hR
  have hlow := norm_intervalIntegral_physicalSlice_mul_adjacentKernel_low_le
    (B := B) hA hN0 hH hR hHR hU hsmall
  have hfar := htail (A := A) (B := B) hA
    (N := N) (H := H) (R := R) (U := V) hN hH hR hHR hRH hRN hV
  have hannulus : E ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V}, f y‖ := by
    exact norm_setIntegral_annulus_ge_of_low_tail hf hU (hUT.trans hTV)
      (by simpa only [f] using hfull)
      (by simpa only [f, E] using hlow)
      (by simpa only [f, E] using hfar)
  have hconj : ∀ y : ℝ, f (-y) = (starRingEnd ℂ) (f y) := by
    intro y
    exact conj_physicalSlice_mul_adjacentKernel A B N H R y
  simpa only [f, E] using
    exists_positive_interval_norm_ge_quarter_of_annulus_of_conj
      hf hconj hU hUT hTV hannulus

/-- Every strict Route-T base-phase margin admits one fixed Mellin order and one outer cutoff
exponent.  Tail decay and base-layer decay are then simultaneously strict. -/
theorem exists_routeT_natOrder_outer_phase_window
    {mu alpha : ℝ} (hphase : 1 < mu * (1 - alpha)) :
    ∃ j : ℕ, 1 ≤ j ∧ ∃ v : ℝ,
      1 + 1 / (j : ℝ) < v ∧
      v < mu * (1 - alpha) ∧
      ((j + 1 : ℕ) : ℝ) - (j : ℝ) * v < 0 ∧
      v - mu * (1 - alpha) < 0 := by
  let u : ℝ := mu * (1 - alpha)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < u - 1 by
    dsimp only [u]
    linarith)
  let j : ℕ := n + 1
  have hj : 1 ≤ j := by dsimp only [j]; omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hone : 1 + 1 / (j : ℝ) < u := by
    dsimp only [j]
    norm_num at hn ⊢
    linarith
  let v : ℝ := (1 + 1 / (j : ℝ) + u) / 2
  have hlower : 1 + 1 / (j : ℝ) < v := by dsimp only [v]; linarith
  have hupper : v < u := by dsimp only [v]; linarith
  have hmul : (j : ℝ) + 1 < (j : ℝ) * v := by
    have hfrac : 1 / (j : ℝ) < v - 1 := by linarith
    have := (div_lt_iff₀ hjR).mp hfrac
    nlinarith
  refine ⟨j, hj, v, hlower, ?_, ?_, ?_⟩
  · simpa only [u] using hupper
  · norm_num
    linarith
  · simpa only [u] using sub_neg.mpr hupper

/-- Exact power bookkeeping behind arbitrary-order outer localization. -/
theorem routeT_natOrder_tail_base_phase_identities
    {T mu alpha v : ℝ} {j : ℕ} (hT : 0 < T) :
    T ^ (j + 1) * (T ^ v) ^ (-(j : ℝ)) =
        T ^ (((j + 1 : ℕ) : ℝ) - (j : ℝ) * v) ∧
      T ^ v * (T ^ mu) ^ (alpha - 1) =
        T ^ (v - mu * (1 - alpha)) := by
  constructor
  · calc
      T ^ (j + 1) * (T ^ v) ^ (-(j : ℝ)) =
          T ^ (((j + 1 : ℕ) : ℝ)) * T ^ (v * (-(j : ℝ))) := by
        rw [Real.rpow_natCast, Real.rpow_mul hT.le]
      _ = T ^ (((j + 1 : ℕ) : ℝ) + v * (-(j : ℝ))) := by
        rw [Real.rpow_add hT]
      _ = T ^ (((j + 1 : ℕ) : ℝ) - (j : ℝ) * v) := by
        congr 1
        ring
  · calc
      T ^ v * (T ^ mu) ^ (alpha - 1) =
          T ^ v * T ^ (mu * (alpha - 1)) := by
        rw [Real.rpow_mul hT.le]
      _ = T ^ (v + mu * (alpha - 1)) := by
        rw [Real.rpow_add hT]
      _ = T ^ (v - mu * (1 - alpha)) := by
        congr 1
        ring

/-- Signed mass surviving low-frequency cancellation and arbitrary-order far-tail decay. -/
def routeTPhysicalSliceNatOrderLocalizationSurplus
    (j : ℕ) (C N R U V D : ℝ) : ℝ :=
  D - 16 * routeTPhysicalSliceEnvelope N R * (R / N) * U ^ 2 -
    routeTPhysicalSliceEnvelope N R *
      (C * (N / R) ^ (j + 1) * V ^ (-(j : ℝ)))

/-- Full arbitrary-order physical-slice receiver at the universal transition `N/(2R)`. -/
theorem exists_eventually_physicalSlice_natOrder_annulus_base_or_secondAlternative
    (j : ℕ) (hj : 1 ≤ j) {mu alpha eta : ℝ} (hmu : 0 < mu) (heta : 0 < eta)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2) :
    ∃ Cloc Ccell : ℝ, 1 ≤ Cloc ∧ 1 ≤ Ccell ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        ∀ {H R U V D Tord : ℝ} {Q : ℕ},
          0 < H → 1 ≤ R → H ≤ R → R ≤ 2 * H →
          R ≤ 2 * T ^ mu / T → 1 ≤ U →
          U + 2 ≤ (T ^ mu) / (2 * R) →
          (T ^ mu) / (2 * R) + 2 ≤ V →
          V + 1 ≤ Tord → 0 ≤ Tord → Tord ≤ T ^ mu →
          0 < routeTPhysicalSliceNatOrderLocalizationSurplus j
            Cloc (T ^ mu) R U V D →
          D ≤ ‖∫ y : ℝ,
            dirPoly ⌊T ^ mu + 2 * R⌋₊
                (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
                  ⌊T ^ mu + 2 * R⌋₊) (-y) *
              (routeTNormalizedSmoothWindowMellin (T ^ mu) R
                  ((1 : ℂ) + (y : ℝ) * I) -
                routeTNormalizedSmoothWindowMellin (T ^ mu) H
                  ((1 : ℂ) + (y : ℝ) * I))‖ →
          routeTPhysicalSliceEnvelope (T ^ mu) R ≤
            (((2 ^ Q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) →
          0 < Q →
          routeTPhysicalSliceNatOrderLocalizationSurplus j
                Cloc (T ^ mu) R U V D ≤
              32 * ((T ^ mu) / (2 * R) - U) *
                (T ^ mu) ^ (alpha - 1) ∨
            routeTPhysicalSliceNatOrderLocalizationSurplus j
                Cloc (T ^ mu) R U V D ≤
              2080 * Ccell * (V - (T ^ mu) / (2 * R)) *
                (T ^ mu) ^ (alpha - 1) ∨
            ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
              (∀ i, lam i + 1 ≤ lam (i + 1)) ∧ q < Q ∧
              (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) ≤
                ‖dirPoly ⌊T ^ mu + 2 * R⌋₊
                  (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
                    ⌊T ^ mu + 2 * R⌋₊) (lam r)‖) ∧
              routeTPhysicalSliceNatOrderLocalizationSurplus j
                    Cloc (T ^ mu) R U V D /
                  (8320 * Ccell * (Q : ℝ)) ≤
                (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) *
                  (S.card : ℝ) ∧
              (S.card : ℝ) ≤
                T * (T ^ mu) ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  obtain ⟨Cloc, hCloc, hlocalize⟩ :=
    exists_positive_interval_norm_ge_quarter_of_physicalSlice_natOrder_annulus j hj
  obtain ⟨Ccell, hCcell, houter⟩ :=
    exists_eventually_physicalSlice_tailInterval_base_or_secondAlternative
      (alpha := alpha) hmu heta hbudget
  have hcentral := eventually_physicalSlice_centralInterval_base_or_secondAlternative
    (alpha := alpha) hmu heta hbudget
  refine ⟨Cloc, Ccell, hCloc, hCcell, ?_⟩
  have hTtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T := Filter.eventually_ge_atTop 2
  have hNtop : Filter.Tendsto (fun T : ℝ => T ^ mu) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hmu
  have hNtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T ^ mu :=
    (Filter.tendsto_atTop.1 hNtop) 2
  filter_upwards [houter, hcentral, hTtwo, hNtwo] with T houterT hcentralT hTtwoT hNtwoT
  intro H R U V D Tord Q hH hR hHR hRH hwidth hU hcentralLen houterLen
    hTordTop hTord hTordN hsurplus hfull hP hQ
  let N : ℝ := T ^ mu
  let A : ℕ := ⌊N⌋₊
  let B : ℕ := ⌊N + 2 * R⌋₊
  let W : ℝ := N / (2 * R)
  let E : ℝ := routeTPhysicalSliceNatOrderLocalizationSurplus j Cloc N R U V D
  let v : ℝ := N ^ (alpha - 1)
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hNtwoN : 2 ≤ N := by simpa only [N] using hNtwoT
  have hR0 : 0 < R := by linarith
  have hU0 : 0 < U := by linarith
  have hW0 : 0 < W := by dsimp only [W]; positivity
  have hV0 : 0 < V := by
    change W + 2 ≤ V at houterLen
    linarith
  have hRN : R ≤ N := by
    calc
      R ≤ 2 * N / T := by simpa only [N] using hwidth
      _ ≤ N := by
        rw [div_le_iff₀ hT0]
        nlinarith
  have hUW : U ≤ W := by
    dsimp only [W, N]
    linarith
  have hWV : W ≤ V := by
    dsimp only [W, N]
    linarith
  have hWone : 1 ≤ W := hU.trans hUW
  have hA : 1 ≤ A := by
    have hfloor : N < (A : ℝ) + 1 := by
      dsimp only [A]
      exact Nat.lt_floor_add_one N
    have hAcast : (1 : ℝ) ≤ (A : ℝ) := by linarith
    exact_mod_cast hAcast
  have hsmall : U * (2 * R / N) ≤ 1 := by
    have hfac : 0 < 2 * R / N := by positivity
    calc
      U * (2 * R / N) ≤ W * (2 * R / N) :=
        mul_le_mul_of_nonneg_right hUW hfac.le
      _ = 1 := by
        dsimp only [W]
        field_simp
  have hwingRaw := hlocalize (A := A) (B := B) hA (by linarith : 1 ≤ N) hH hR0 hHR hRH hRN
    (by linarith) hUW hWV hV0 hsmall (by simpa only [A, B, N] using hfull)
  have hwing : E / 4 ≤ ‖∫ y in U..W,
        dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I))‖ ∨
      E / 4 ≤ ‖∫ y in W..V,
        dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I))‖ := by
    simpa only [E, routeTPhysicalSliceNatOrderLocalizationSurplus,
      routeTPhysicalSliceEnvelope, A, B, N, W] using hwingRaw
  have hE : 0 < E := by simpa only [E, N] using hsurplus
  have hEQ : (0 : ℝ) < Q := by exact_mod_cast hQ
  rcases hwing with hcentralWing | houterWing
  · have hcentralBand : ∀ y ∈ Set.Icc U W, |y| ≤ N / (2 * R) := by
      intro y hy
      have hy0 : 0 ≤ y := hU0.le.trans hy.1
      rw [abs_of_nonneg hy0]
      simpa only [W] using hy.2
    have hcentralOut := hcentralT (D := E / 4) hH hR hHR
      (by simpa only [N] using hwidth) (by positivity) hQ
      (by simpa only [W, N] using hcentralLen) hU
      (by dsimp only [W, N]; linarith) hTord
      (by simpa only [N] using hTordN) hcentralBand
      (by simpa only [A, B, N, W] using hcentralWing)
      (by simpa only [routeTPhysicalSliceEnvelope, A, B, N, v] using hP)
    rcases hcentralOut with hbase | hhigh
    · left
      dsimp only [E, v, W, N] at hbase ⊢
      linarith
    · right; right
      obtain ⟨lam, S, q, hgap, hq, hlarge, hmass, hcount⟩ := hhigh
      have hdenSmall : 0 < 128 * (Q : ℝ) := by positivity
      have hdenLarge : 128 * (Q : ℝ) ≤ 8320 * Ccell * (Q : ℝ) := by
        nlinarith
      have hmassWeak : E / (8320 * Ccell * (Q : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
        have hmass' : E / (128 * (Q : ℝ)) ≤
            (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
          convert hmass using 1 <;> ring
        exact (div_le_div_of_nonneg_left hE.le hdenSmall hdenLarge).trans hmass'
      refine ⟨lam, S, q, hgap, hq, ?_, ?_, ?_⟩
      · simpa only [A, B, N, v] using hlarge
      · simpa only [E, N, v] using hmassWeak
      · simpa only [N] using hcount
  · have haway : ∀ y ∈ Set.Icc W V, W ≤ |y| := by
      intro y hy
      have hy0 : 0 ≤ y := hW0.le.trans hy.1
      rw [abs_of_nonneg hy0]
      exact hy.1
    have houterOut := houterT (D := E / 4) (U := W) (a := W) (b := V)
      hH hR hHR hRH
      (by simpa only [N] using hwidth) hW0 (by positivity) hQ
      (by simpa only [W, N] using houterLen) hWone hTordTop hTord
      (by simpa only [N] using hTordN) haway
      (by simpa only [A, B, N, W] using houterWing)
      (by simpa only [routeTPhysicalSliceEnvelope, A, B, N, v] using hP)
    have htransition :
        65 * Ccell * (N / R) ^ 2 / W ^ 2 = 260 * Ccell := by
      dsimp only [W]
      field_simp
      ring
    rcases houterOut with hbase | hhigh
    · right; left
      dsimp only [E, v, N] at hbase ⊢
      rw [htransition] at hbase
      linarith
    · right; right
      obtain ⟨lam, S, q, hgap, hq, hlarge, hmass, hcount⟩ := hhigh
      have hmass' : E / (8320 * Ccell * (Q : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
        rw [htransition] at hmass
        convert hmass using 1 <;> ring
      refine ⟨lam, S, q, hgap, hq, ?_, ?_, ?_⟩
      · simpa only [A, B, N, v] using hlarge
      · simpa only [E, N, v] using hmass'
      · simpa only [N] using hcount

end RHTower.Sieve
