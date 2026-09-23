import GaloisForLFunctions.RHTower.ChenGuptaLiHybridCharacterMeanSquare
import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketFibreSeparation
import GaloisForLFunctions.RHTower.WellSpacedSubset

open Complex MeasureTheory Set Finset

noncomputable section

namespace RHTower.Sieve

noncomputable def characterLogDerivCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * (((2 * Real.pi * Real.log n : ℝ) : ℂ) * Complex.I)

theorem hasDerivAt_characterLogPoly (q N : ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ (q + 1)) (w : ℝ) :
    HasDerivAt (characterLogPoly q N a χ)
      (characterLogPoly q N (characterLogDerivCoeff a) χ w) w := by
  unfold characterLogPoly charSum characterLogDerivCoeff
  have hterm : ∀ n ∈ Finset.Icc 1 N, HasDerivAt
      (fun x : ℝ => (a n * Complex.exp
        (((2 * Real.pi * (x * Real.log n) : ℝ) : ℂ) * Complex.I)) * χ (n : ZMod (q + 1)))
      ((a n * (Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I) *
        (((2 * Real.pi * Real.log n : ℝ) : ℂ) * Complex.I))) *
          χ (n : ZMod (q + 1))) w := by
    intro n hn
    have hg : HasDerivAt
        (fun x : ℝ => (((2 * Real.pi * (x * Real.log n) : ℝ) : ℂ) * Complex.I))
        (((2 * Real.pi * Real.log n : ℝ) : ℂ) * Complex.I) w := by
      have hr : HasDerivAt (fun x : ℝ => 2 * Real.pi * (x * Real.log n))
          (2 * Real.pi * Real.log n) w := by
        simpa only [id_eq, one_mul] using
          ((hasDerivAt_id w).mul_const (Real.log n)).const_mul (2 * Real.pi)
      exact hr.ofReal_comp.mul_const Complex.I
    have he := hg.cexp
    have ha := he.const_mul (a n)
    have hc := ha.mul_const (χ (n : ZMod (q + 1)))
    exact hc
  have hsum := HasDerivAt.sum hterm
  have hfun : (∑ n ∈ Finset.Icc 1 N, fun x : ℝ =>
      (a n * Complex.exp (((2 * Real.pi * (x * Real.log n) : ℝ) : ℂ) * Complex.I)) *
        χ (n : ZMod (q + 1))) =
      fun x : ℝ => ∑ n ∈ Finset.Icc 1 N,
        (a n * Complex.exp (((2 * Real.pi * (x * Real.log n) : ℝ) : ℂ) * Complex.I)) *
          χ (n : ZMod (q + 1)) := by
    funext x
    simp
  rw [hfun] at hsum
  apply hsum.congr_deriv
  apply Finset.sum_congr rfl
  intro n hn
  ring

noncomputable def cglPacketLogFrequency {q R : ℕ}
    (P : RHTower.CGLFibreSeparatedPacket q R) (r : Fin R) : ℝ :=
  -P.ordinate r / (2 * Real.pi)

noncomputable def cglPacketCharacterFrequencySet {q R : ℕ}
    (P : RHTower.CGLFibreSeparatedPacket q R)
    (χ : DirichletCharacter ℂ (q + 1)) : Finset ℝ :=
  ((Finset.univ : Finset (Fin R)).filter (fun r => P.character r = χ)).image
    (cglPacketLogFrequency P)

theorem cglPacketLogFrequency_injectiveOn_fibre {q R : ℕ}
    (P : RHTower.CGLFibreSeparatedPacket q R) (χ : DirichletCharacter ℂ (q + 1)) :
    Set.InjOn (cglPacketLogFrequency P)
      ↑((Finset.univ : Finset (Fin R)).filter (fun r => P.character r = χ)) := by
  intro r hr s hs hrs
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr hs
  by_contra hne
  apply RHTower.cglFibreSeparatedPacket_ordinate_ne P r s hne (hr.trans hs.symm)
  unfold cglPacketLogFrequency at hrs
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  field_simp at hrs
  linarith

theorem sum_cglPacketCharacterFrequencySet {q R : ℕ}
    (P : RHTower.CGLFibreSeparatedPacket q R)
    (F : DirichletCharacter ℂ (q + 1) → ℝ → ℝ) :
    ∑ χ : DirichletCharacter ℂ (q + 1),
        ∑ w ∈ cglPacketCharacterFrequencySet P χ, F χ w
      = ∑ r : Fin R, F (P.character r) (cglPacketLogFrequency P r) := by
  classical
  have himage : ∀ χ : DirichletCharacter ℂ (q + 1),
      ∑ w ∈ cglPacketCharacterFrequencySet P χ, F χ w =
        ∑ r ∈ (Finset.univ : Finset (Fin R)).filter (fun r => P.character r = χ),
          F χ (cglPacketLogFrequency P r) := by
    intro χ
    unfold cglPacketCharacterFrequencySet
    exact Finset.sum_image (cglPacketLogFrequency_injectiveOn_fibre P χ)
  rw [Finset.sum_congr rfl (fun χ _ => himage χ)]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp

noncomputable def characterHybridLengthBound (q N : ℕ) (a : ℕ → ℂ) (T : ℝ) : ℝ :=
  ((5 * Real.exp 1 / 2) * (N : ℝ) +
      (5 / 2) * ((q + 1).totient : ℝ) * T) *
    ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ (2 : ℕ)

theorem sum_cglPacketCharacterFrequencySet_normSq_le {q R N : ℕ}
    (P : RHTower.CGLFibreSeparatedPacket q R) (a : ℕ → ℂ)
    {T : ℝ} (hT : 1 ≤ T) (hheight : ∀ r : Fin R, |P.ordinate r| ≤ T) :
    ∑ χ : DirichletCharacter ℂ (q + 1),
        ∑ w ∈ cglPacketCharacterFrequencySet P χ, ‖characterLogPoly q N a χ w‖ ^ (2 : ℕ)
      ≤ (2 * Real.pi / P.spacing + 1) *
          characterHybridLengthBound q N a (T + P.spacing)
        + characterHybridLengthBound q N (characterLogDerivCoeff a) (T + P.spacing) := by
  classical
  let D : ℝ := 2 * Real.pi
  let δ : ℝ := P.spacing / D
  let A : ℝ := -T / D
  let B : ℝ := T / D
  let H : ℝ := (T + P.spacing) / D
  have hD : 0 < D := by dsimp [D]; positivity
  have hδ : 0 < δ := div_pos P.spacing_pos hD
  have hT0 : 0 ≤ T := by linarith
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact div_le_div_of_nonneg_right (by linarith) hD.le
  have hABδ : A ≤ B + δ := by linarith
  have hH0 : 0 ≤ H := by
    dsimp [H]
    exact div_nonneg (by linarith [P.spacing_pos]) hD.le
  have hT' : 1 ≤ T + P.spacing := by linarith [P.spacing_pos]
  have hper : ∀ χ : DirichletCharacter ℂ (q + 1),
      ∑ w ∈ cglPacketCharacterFrequencySet P χ, ‖characterLogPoly q N a χ w‖ ^ (2 : ℕ)
        ≤ (1 / δ + 1) * (∫ w in Set.Icc (-H) H, ‖characterLogPoly q N a χ w‖ ^ (2 : ℕ))
          + (∫ w in Set.Icc (-H) H,
              ‖characterLogPoly q N (characterLogDerivCoeff a) χ w‖ ^ (2 : ℕ)) := by
    intro χ
    let S := cglPacketCharacterFrequencySet P χ
    let f : ℝ → ℂ := characterLogPoly q N a χ
    let f' : ℝ → ℂ := characterLogPoly q N (characterLogDerivCoeff a) χ
    have hSmem : ∀ x ∈ S, A ≤ x ∧ x ≤ B := by
      intro x hx
      change x ∈ cglPacketCharacterFrequencySet P χ at hx
      rw [cglPacketCharacterFrequencySet, Finset.mem_image] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      have hrange := abs_le.1 (hheight r)
      dsimp [A, B, cglPacketLogFrequency]
      constructor
      · exact div_le_div_of_nonneg_right (neg_le_neg hrange.2) hD.le
      · exact div_le_div_of_nonneg_right (by linarith [hrange.1]) hD.le
    have hSsep : ∀ x ∈ S, ∀ z ∈ S, x ≠ z → δ ≤ |x - z| := by
      intro x hx z hz hxz
      change x ∈ cglPacketCharacterFrequencySet P χ at hx
      change z ∈ cglPacketCharacterFrequencySet P χ at hz
      rw [cglPacketCharacterFrequencySet, Finset.mem_image] at hx hz
      obtain ⟨r, hr, rfl⟩ := hx
      obtain ⟨s, hs, rfl⟩ := hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr hs
      have hrs : r ≠ s := by
        intro heq
        subst s
        exact hxz rfl
      have hsep := RHTower.cglFibreSeparatedPacket_sameCharacter_separation P r s hrs
        (hr.trans hs.symm)
      dsimp [δ, D, cglPacketLogFrequency]
      rw [← sub_div, abs_div, abs_of_pos hD, abs_sub_comm]
      rw [show -P.ordinate s - -P.ordinate r = P.ordinate r - P.ordinate s by ring]
      exact div_le_div_of_nonneg_right hsep hD.le
    have hf : ∀ y ∈ Set.Icc A (B + δ), HasDerivAt f (f' y) y := by
      intro y hy
      exact hasDerivAt_characterLogPoly q N a χ y
    have hfc : Continuous f := continuous_characterLogPoly q N a χ
    have hf'c : Continuous f' := continuous_characterLogPoly q N (characterLogDerivCoeff a) χ
    have hg'int : IntervalIntegrable (fun y => 2 * inner ℝ (f y) (f' y)) volume A (B + δ) :=
      (by fun_prop : Continuous (fun y => 2 * inner ℝ (f y) (f' y))).intervalIntegrable _ _
    have hgint : IntervalIntegrable (fun y => ‖f y‖ ^ (2 : ℕ)) volume A (B + δ) :=
      hfc.norm.pow 2 |>.intervalIntegrable _ _
    have hf'int : IntervalIntegrable (fun y => ‖f' y‖ ^ (2 : ℕ)) volume A (B + δ) :=
      hf'c.norm.pow 2 |>.intervalIntegrable _ _
    have hcrossint : IntervalIntegrable (fun y => 2 * (‖f y‖ * ‖f' y‖)) volume A (B + δ) :=
      (by fun_prop : Continuous (fun y => 2 * (‖f y‖ * ‖f' y‖))).intervalIntegrable _ _
    have hgal := RHTower.gallagher_separated hδ hAB hSmem hSsep hf hg'int hgint hcrossint
    have hcross : (∫ y in A..B + δ, 2 * (‖f y‖ * ‖f' y‖))
        ≤ (∫ y in A..B + δ, ‖f y‖ ^ (2 : ℕ)) + (∫ y in A..B + δ, ‖f' y‖ ^ (2 : ℕ)) := by
      refine le_trans (intervalIntegral.integral_mono_on hABδ hcrossint
        (hgint.add hf'int) ?_) ?_
      · intro y hy
        nlinarith [sq_nonneg (‖f y‖ - ‖f' y‖)]
      · rw [intervalIntegral.integral_add hgint hf'int]
    have hHA : -H ≤ A := by
      dsimp [H, A]
      have hnum : T ≤ T + P.spacing := by linarith [P.spacing_pos]
      have hdiv : T / D ≤ (T + P.spacing) / D :=
        div_le_div_of_nonneg_right hnum hD.le
      simpa only [neg_div] using neg_le_neg hdiv
    have hBH : B + δ ≤ H := by
      dsimp [B, δ, H]
      exact le_of_eq (by ring)
    have hsub : Set.Ioc A (B + δ) ⊆ Set.Icc (-H) H := by
      intro y hy
      exact ⟨hHA.trans (le_of_lt hy.1), hy.2.trans hBH⟩
    have hFbig : IntegrableOn (fun y => ‖f y‖ ^ (2 : ℕ)) (Set.Icc (-H) H) :=
      hfc.norm.pow 2 |>.integrableOn_Icc
    have hDbig : IntegrableOn (fun y => ‖f' y‖ ^ (2 : ℕ)) (Set.Icc (-H) H) :=
      hf'c.norm.pow 2 |>.integrableOn_Icc
    have hIF : (∫ y in A..B + δ, ‖f y‖ ^ (2 : ℕ))
        ≤ ∫ y in Set.Icc (-H) H, ‖f y‖ ^ (2 : ℕ) := by
      rw [intervalIntegral.integral_of_le hABδ]
      exact setIntegral_mono_set hFbig (Filter.Eventually.of_forall fun y => by positivity)
        (Filter.Eventually.of_forall fun y hy => hsub hy)
    have hID : (∫ y in A..B + δ, ‖f' y‖ ^ (2 : ℕ))
        ≤ ∫ y in Set.Icc (-H) H, ‖f' y‖ ^ (2 : ℕ) := by
      rw [intervalIntegral.integral_of_le hABδ]
      exact setIntegral_mono_set hDbig (Filter.Eventually.of_forall fun y => by positivity)
        (Filter.Eventually.of_forall fun y hy => hsub hy)
    have hcoef : (0 : ℝ) ≤ 1 / δ := by positivity
    change (∑ w ∈ S, ‖f w‖ ^ (2 : ℕ)) ≤ _
    have hIFscaled := mul_le_mul_of_nonneg_left hIF hcoef
    linarith
  have hsum :
      ∑ χ : DirichletCharacter ℂ (q + 1),
          ∑ w ∈ cglPacketCharacterFrequencySet P χ, ‖characterLogPoly q N a χ w‖ ^ (2 : ℕ)
        ≤ ∑ χ : DirichletCharacter ℂ (q + 1),
          ((1 / δ + 1) * (∫ w in Set.Icc (-H) H, ‖characterLogPoly q N a χ w‖ ^ (2 : ℕ))
            + (∫ w in Set.Icc (-H) H,
                ‖characterLogPoly q N (characterLogDerivCoeff a) χ w‖ ^ (2 : ℕ))) :=
    Finset.sum_le_sum (fun χ _ => hper χ)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hA := sum_integral_normSq_characterLogPoly_le_length q N a hT'
  have hDpoly := sum_integral_normSq_characterLogPoly_le_length q N
    (characterLogDerivCoeff a) hT'
  have hcoef : (0 : ℝ) ≤ 1 / δ + 1 := by positivity
  have hAscaled := mul_le_mul_of_nonneg_left hA hcoef
  dsimp [H] at hsum hA hDpoly
  dsimp [characterHybridLengthBound]
  dsimp [δ, D] at hsum hcoef hAscaled
  have hrecip : 1 / (P.spacing / (2 * Real.pi)) = 2 * Real.pi / P.spacing := by
    field_simp
  rw [hrecip] at hsum hcoef hAscaled
  linarith

/-- Discrete hybrid mean square on an actual CGL fibre-separated packet. -/
theorem sum_normSq_characterLogPoly_cglPacket_le {q R N : ℕ}
    (P : RHTower.CGLFibreSeparatedPacket q R) (a : ℕ → ℂ)
    {T : ℝ} (hT : 1 ≤ T) (hheight : ∀ r : Fin R, |P.ordinate r| ≤ T) :
    ∑ r : Fin R,
        ‖characterLogPoly q N a (P.character r) (cglPacketLogFrequency P r)‖ ^ (2 : ℕ)
      ≤ (2 * Real.pi / P.spacing + 1) *
          characterHybridLengthBound q N a (T + P.spacing)
        + characterHybridLengthBound q N (characterLogDerivCoeff a) (T + P.spacing) := by
  rw [← sum_cglPacketCharacterFrequencySet P
    (fun χ w => ‖characterLogPoly q N a χ w‖ ^ (2 : ℕ))]
  exact sum_cglPacketCharacterFrequencySet_normSq_le P a hT hheight

end RHTower.Sieve
