import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeLayerExtraction
import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentDefectReparameterization

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter

/-- A large signed integral on a positive interval has a large integral on one multiplicatively
comparable dyadic ordinate shell. -/
theorem exists_comparable_ordinate_shell_integral_norm_ge
    {f : ℝ → ℂ}
    {B U V : ℝ} (hU : 0 < U) (hUV : U ≤ V)
    (hfint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hB : B ≤ ‖∫ y in U..V, f y‖) :
    ∃ J : ℕ, 0 < J ∧
      (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ V / U ∧
      V / U < (((2 ^ J : ℕ) : ℝ)) ∧
      ∃ j ∈ Finset.range J,
        routeTComparableWidthLadder U V (j + 1) ≤
            routeTComparableWidthLadder U V j ∧
        routeTComparableWidthLadder U V j ≤
            2 * routeTComparableWidthLadder U V (j + 1) ∧
        B / (J : ℝ) ≤ ‖∫ y in
          routeTComparableWidthLadder U V (j + 1)..
            routeTComparableWidthLadder U V j, f y‖ := by
  obtain ⟨J, hJ, hbelow, habove, hW0, hWJ⟩ :=
    exists_routeTComparableWidthLadder_endpoint hU hUV
  let W : ℕ → ℝ := routeTComparableWidthLadder U V
  let F : ℕ → ℂ := fun j => ∫ y in U..W j, f y
  have hendpoint : B ≤ ‖F 0 - F J‖ := by
    dsimp only [F]
    change B ≤ ‖(∫ y in U..routeTComparableWidthLadder U V 0, f y) -
      ∫ y in U..routeTComparableWidthLadder U V J, f y‖
    rw [hW0, hWJ]
    simpa using hB
  obtain ⟨j, hj, hlarge⟩ :=
    complex_widthLadder_norm_pigeonhole F hJ hendpoint
  have hadj := routeTComparableWidthLadder_adjacent hU
    (lt_of_lt_of_le hU hUV) j
  refine ⟨J, hJ, hbelow, habove, j, hj, hadj.1, hadj.2, ?_⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (f := f) (a := U) (b := W (j + 1)) (c := W j)
      (hfint U (W (j + 1))) (hfint (W (j + 1)) (W j))
  have hdiff : F j - F (j + 1) = ∫ y in W (j + 1)..W j, f y := by
    dsimp only [F]
    rw [← hadd]
    ring
  rw [hdiff] at hlarge
  simpa only [W] using hlarge

/-- Exact base-`T` exponent of the physical cutoff. -/
def routeTExactCutoffExponent (T : ℝ) (X : ℕ) : ℝ :=
  Real.logb T X

theorem rpow_routeTExactCutoffExponent
    {T : ℝ} {X : ℕ} (hT : 1 < T) (hX : 1 ≤ X) :
    T ^ routeTExactCutoffExponent T X = X := by
  exact Real.rpow_logb (by linarith) hT.ne' (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX))

/-- Power brackets are exactly exponent brackets in canonical cutoff coordinates. -/
theorem routeTExactCutoffExponent_mem_of_rpow_bracket
    {T a b : ℝ} {X : ℕ} (hT : 1 < T) (hX : 1 ≤ X)
    (hlo : T ^ a ≤ X) (hhi : (X : ℝ) ≤ T ^ b) :
    a ≤ routeTExactCutoffExponent T X ∧
      routeTExactCutoffExponent T X ≤ b := by
  have hexact := rpow_routeTExactCutoffExponent hT hX
  constructor
  · apply (Real.strictMono_rpow_of_base_gt_one hT).le_iff_le.mp
    simpa [hexact] using hlo
  · apply (Real.strictMono_rpow_of_base_gt_one hT).le_iff_le.mp
    simpa [hexact] using hhi

/-- Every stopped rung stays inside the endpoint interval. -/
theorem routeTComparableWidthLadder_mem
    {U V : ℝ} (hU : 0 < U) (hUV : U ≤ V) (j : ℕ) :
    routeTComparableWidthLadder U V j ∈ Set.Icc U V := by
  constructor
  · exact le_max_left _ _
  · rw [routeTComparableWidthLadder, max_le_iff]
    constructor
    · exact hUV
    · have hpow : 1 ≤ (((2 ^ j : ℕ) : ℝ)) := by
        exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ))).2
        (by nlinarith)

/-- **Shell-matched pointwise reparametrization.** A large positive interval defect for one exact
cutoff coordinate has a comparable dyadic shell whose lower ordinate is itself the new height.
The aggregate is pointwise unchanged, so the shell is immediately in the new height's `[T,2T]`
counting band. -/
theorem exists_reparametrized_comparable_ordinate_shell_integral_norm_ge
    (L X k : ℕ) {T₀ mu₀ N H R sigma B U V : ℝ}
    (hX : 1 ≤ X) (hT₀ : 1 < T₀) (hX₀ : T₀ ^ mu₀ = X)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hsigma : 0 < sigma)
    (hU : 1 < U) (hUV : U ≤ V)
    (hB : B ≤ ‖∫ y in U..V,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₀ (mu₀ / 120) N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))‖) :
    ∃ J : ℕ, 0 < J ∧
      (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ V / U ∧
      V / U < (((2 ^ J : ℕ) : ℝ)) ∧
      ∃ j ∈ Finset.range J,
        let T₁ := routeTComparableWidthLadder U V (j + 1)
        let mu₁ := routeTExactCutoffExponent T₁ X
        T₁ ∈ Set.Icc U V ∧
        routeTComparableWidthLadder U V j ≤ 2 * T₁ ∧
        T₁ ^ mu₁ = X ∧
        B / (J : ℝ) ≤ ‖∫ y in T₁..routeTComparableWidthLadder U V j,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ (mu₁ / 120) N
              ((sigma : ℂ) + (y : ℝ) * I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((sigma : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((sigma : ℂ) + (y : ℝ) * I))‖ := by
  let f : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T₀ (mu₀ / 120) N
          ((sigma : ℂ) + (y : ℝ) * I) *
      (routeTNormalizedSmoothWindowMellin N R
          ((sigma : ℂ) + (y : ℝ) * I) -
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I))
  have hfR := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
    L X k T₀ (mu₀ / 120) N hN hR hsigma
  have hfH := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
    L X k T₀ (mu₀ / 120) N hN hH hsigma
  have hf : Integrable f := (hfR.sub hfH).congr
    (Filter.Eventually.of_forall fun y => by simp only [f, Pi.sub_apply, mul_sub])
  obtain ⟨J, hJ, hbelow, habove, j, hj, _hdec, hcomp, hlarge⟩ :=
    exists_comparable_ordinate_shell_integral_norm_ge
      (U := U) (V := V) (by linarith) hUV (fun a b => hf.intervalIntegrable)
        (by simpa only [f] using hB)
  let T₁ : ℝ := routeTComparableWidthLadder U V (j + 1)
  let mu₁ : ℝ := routeTExactCutoffExponent T₁ X
  have hT₁mem : T₁ ∈ Set.Icc U V :=
    routeTComparableWidthLadder_mem (by linarith) hUV (j + 1)
  have hT₁ : 1 < T₁ := hU.trans_le hT₁mem.1
  have hX₁ : T₁ ^ mu₁ = X := by
    exact rpow_routeTExactCutoffExponent hT₁ hX
  have hinterval :
      (∫ y in T₁..routeTComparableWidthLadder U V j, f y) =
      ∫ y in T₁..routeTComparableWidthLadder U V j,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ (mu₁ / 120) N
              ((sigma : ℂ) + (y : ℝ) * I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((sigma : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((sigma : ℂ) + (y : ℝ) * I)) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    dsimp only [f]
    rw [heathBrownWindowRelevantEligibleDyadicAggregate_eq_of_rpow_mu_eq_cutoff
      L X k hT₀ hT₁ hX₀ hX₁]
  refine ⟨J, hJ, hbelow, habove, j, hj, ?_⟩
  dsimp only
  refine ⟨hT₁mem, ?_, hX₁, ?_⟩
  · simpa only [T₁] using hcomp
  · rw [← hinterval]
    simpa only [T₁, f] using hlarge

/-- Endpoint power bounds transfer to every exact-cutoff exponent in the ordinate interval. -/
theorem routeTExactCutoffExponent_mem_of_ordinate_interval
    {X : ℕ} {U V T a b : ℝ}
    (hX : 1 ≤ X) (hU : 1 < U)
    (hTmem : T ∈ Set.Icc U V) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hlo : V ^ a ≤ X) (hhi : (X : ℝ) ≤ U ^ b) :
    routeTExactCutoffExponent T X ∈ Set.Icc a b := by
  have hT : 1 < T := hU.trans_le hTmem.1
  have hT0 : 0 ≤ T := hT.le.trans' (by norm_num)
  have hU0 : 0 ≤ U := by linarith
  have hTpowLo : T ^ a ≤ X :=
    (Real.rpow_le_rpow hT0 hTmem.2 ha).trans hlo
  have hTpowHi : (X : ℝ) ≤ T ^ b :=
    hhi.trans (Real.rpow_le_rpow hU0 hTmem.1 hb)
  exact routeTExactCutoffExponent_mem_of_rpow_bracket hT hX hTpowLo hTpowHi

/-- Full Route-T exponent band from endpoint power bounds. -/
theorem routeTExactCutoffExponent_mem_fourThird_eight_of_ordinate_interval
    {X : ℕ} {U V T : ℝ}
    (hX : 1 ≤ X) (hU : 1 < U)
    (hTmem : T ∈ Set.Icc U V)
    (hlo : V ^ (4 / 3 : ℝ) ≤ X) (hhi : (X : ℝ) ≤ U ^ (8 : ℝ)) :
    routeTExactCutoffExponent T X ∈ Set.Icc (4 / 3 : ℝ) 8 :=
  routeTExactCutoffExponent_mem_of_ordinate_interval hX hU hTmem
    (by norm_num) (by norm_num) hlo hhi

/-- Historical selected-cell band from endpoint power bounds. -/
theorem routeTExactCutoffExponent_mem_fourThird_nineteenNinth_of_ordinate_interval
    {X : ℕ} {U V T : ℝ}
    (hX : 1 ≤ X) (hU : 1 < U)
    (hTmem : T ∈ Set.Icc U V)
    (hlo : V ^ (4 / 3 : ℝ) ≤ X)
    (hhi : (X : ℝ) ≤ U ^ (19 / 9 : ℝ)) :
    routeTExactCutoffExponent T X ∈ Set.Icc (4 / 3 : ℝ) (19 / 9 : ℝ) :=
  routeTExactCutoffExponent_mem_of_ordinate_interval hX hU hTmem
    (by norm_num) (by norm_num) hlo hhi

end RHTower.Sieve
