import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaLogPrimeHarmonicTraceRelocationNoGo
import GaloisForLFunctions.RHTower.XiLogEnhancedWeakTraceIdeal
import GaloisForLFunctions.HTGeometry.SchattenApproximationAdditivity
import GaloisForLFunctions.HTGeometry.RectangularWeakSchatten
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# Route-P weak-trace mixing no-go

The canonically diagonal relocation obstruction leaves open a genuinely non-diagonal
IIKS/Fredholm coupling. This file closes that loophole at the operator-ideal level.

The balanced depth-zero Route-P Stokes carrier has signed multipliers `±2/p`. Its ordered
approximation numbers are `2 / p_(n/2)`, hence it belongs to weak Schatten-one. Weak
Schatten-one is additive, contains Schatten-one, and is preserved by bounded left and right
composition. Ordered Xi reciprocal operator does not belong to weak Schatten-one.

Consequently no weak-Schatten-one source can be moved to ordered Xi by a trace-class additive
correction. In particular this excludes every bounded, possibly non-diagonal, left/right mixing
of literal Route-P depth-zero carrier. A viable irregular-RH construction must already carry
logarithmically enhanced Xi-scale density, or use a non-trace-class/nonlinear transport.
-/

open scoped BigOperators InnerProductSpace Nat.Prime
open Filter ContinuousLinearMap

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Schatten-one membership implies weak Schatten-one membership. -/
theorem MemSchattenClass.one_memWeakSchattenClass
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) :
    MemWeakSchattenClass 1 T := by
  have hsummable := hT.one_summable_approxNumber
  let C : ℝ := ∑' n : ℕ, approxNumber T n
  have hC : 0 ≤ C := tsum_nonneg fun n => approxNumber_nonneg T n
  refine ⟨C, hC, fun n => ?_⟩
  rw [Real.rpow_one]
  have hpartial : ∑ k ∈ Finset.range (n + 1), approxNumber T k ≤ C := by
    exact hsummable.sum_le_tsum (Finset.range (n + 1)) fun k _ =>
      approxNumber_nonneg T k
  have hlow : ((n : ℝ) + 1) * approxNumber T n ≤
      ∑ k ∈ Finset.range (n + 1), approxNumber T k := by
    calc
      ((n : ℝ) + 1) * approxNumber T n =
          ∑ _k ∈ Finset.range (n + 1), approxNumber T n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      _ ≤ ∑ k ∈ Finset.range (n + 1), approxNumber T k := by
        apply Finset.sum_le_sum
        intro k hk
        exact approxNumber_antitone T
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hn]
  calc
    approxNumber T n * ((n : ℝ) + 1) =
        ((n : ℝ) + 1) * approxNumber T n := by ring
    _ ≤ ∑ k ∈ Finset.range (n + 1), approxNumber T k := hlow
    _ ≤ C := hpartial

/-- Weak Schatten-one membership is additive. -/
theorem MemWeakSchattenClass.one_add
    {X Y : H →L[ℂ] H} (hX : MemWeakSchattenClass 1 X)
    (hY : MemWeakSchattenClass 1 Y) :
    MemWeakSchattenClass 1 (X + Y) := by
  obtain ⟨CX, hCX, hXbound⟩ := hX
  obtain ⟨CY, hCY, hYbound⟩ := hY
  refine ⟨2 * (CX + CY), by positivity, fun n => ?_⟩
  simp only [Real.rpow_one] at hXbound hYbound ⊢
  let k := n / 2
  have htwok : 2 * k ≤ n := by
    dsimp [k]
    omega
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hindex : (n : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) := by
    exact_mod_cast (show n + 1 ≤ 2 * (k + 1) by
      dsimp [k]
      omega)
  calc
    approxNumber (X + Y) n ≤ approxNumber (X + Y) (2 * k) :=
      approxNumber_antitone (X + Y) htwok
    _ ≤ approxNumber X k + approxNumber Y k :=
      GaloisForLFunctions.HTGeometry.approxNumber_two_mul_add_le X Y k
    _ ≤ CX / ((k : ℝ) + 1) + CY / ((k : ℝ) + 1) :=
      add_le_add (hXbound k) (hYbound k)
    _ = (CX + CY) / ((k : ℝ) + 1) := by ring
    _ ≤ 2 * (CX + CY) / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ hk hn]
      nlinarith

/-- No weak Schatten-one operator is a trace-class displacement from ordered Xi. -/
theorem no_weakSchattenClass_one_traceClass_relocation_to_xiOrderedSignedPrimeOperator :
    ¬ ∃ S : RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert,
      MemWeakSchattenClass 1 S ∧
        MemSchattenClass 1 (xiOrderedSignedPrimeOperator - S) := by
  rintro ⟨S, hS, hdelta⟩
  have hdeltaWeak := hdelta.one_memWeakSchattenClass
  have hsum := hS.one_add hdeltaWeak
  have heq : S + (xiOrderedSignedPrimeOperator - S) =
      xiOrderedSignedPrimeOperator := by abel
  rw [heq] at hsum
  exact xiOrderedSignedPrimeOperator_not_memWeakSchattenClass_one hsum

/-- Ordered singular-value sequence of balanced depth-zero Route-P carrier. -/
def routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber (n : ℕ) : ℝ :=
  routePPrimitiveGammaJuliaDepthZeroStokesMultiplier (nthPrimeSubtype (n / 2))

theorem routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber_pos (n : ℕ) :
    0 < routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber n := by
  rw [routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber,
    routePPrimitiveGammaJuliaDepthZeroStokesMultiplier_eq]
  exact div_pos (by norm_num) (by
    exact_mod_cast (nthPrimeSubtype (n / 2)).property.pos)

theorem routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber_antitone :
    Antitone routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber := by
  intro i j hij
  rw [routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber,
    routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber,
    routePPrimitiveGammaJuliaDepthZeroStokesMultiplier_eq,
    routePPrimitiveGammaJuliaDepthZeroStokesMultiplier_eq]
  have hpmono : (nthPrimeSubtype (i / 2) : ℕ) ≤
      (nthPrimeSubtype (j / 2) : ℕ) :=
    nthPrimeSubtype_strictMono.monotone (Nat.div_le_div_right hij)
  have hpi : (0 : ℝ) < (nthPrimeSubtype (i / 2) : ℝ) := by
    exact_mod_cast (nthPrimeSubtype (i / 2)).property.pos
  exact div_le_div_of_nonneg_left (by norm_num) hpi (by exact_mod_cast hpmono)

/-- Signed depth-zero Route-P multiplier, transported to canonical signed prime ordering. -/
def routePPrimitiveGammaJuliaDepthZeroSignedMultiplier :
    RouteKSignedPrimeIndex → ℂ
  | Sum.inl p =>
      (routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber
        (routeKSignedPrimeNatIndex (Sum.inl p)) : ℂ)
  | Sum.inr p =>
      -(routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber
        (routeKSignedPrimeNatIndex (Sum.inr p)) : ℂ)

theorem nthPrimeSubtype_routeKPrimeRVMIndex (p : Nat.Primes) :
    nthPrimeSubtype (routeKPrimeRVMIndex p) = p := by
  apply routeKPrimeRVMIndex_injective
  rw [routeKPrimeRVMIndex_nthPrimeSubtype]

/-- Positive signed sector is literal Route-P depth-zero Stokes spectrum `2/p`. -/
theorem routePPrimitiveGammaJuliaDepthZeroSignedMultiplier_inl (p : Nat.Primes) :
    routePPrimitiveGammaJuliaDepthZeroSignedMultiplier (Sum.inl p) =
      (routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p : ℂ) := by
  rw [routePPrimitiveGammaJuliaDepthZeroSignedMultiplier,
    routeKSignedPrimeNatIndex,
    routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber]
  have hindex : 2 * routeKPrimeRVMIndex p / 2 =
      routeKPrimeRVMIndex p := by omega
  rw [hindex, nthPrimeSubtype_routeKPrimeRVMIndex]

/-- Negative signed sector is literal balanced Route-P depth-zero Stokes spectrum `-2/p`. -/
theorem routePPrimitiveGammaJuliaDepthZeroSignedMultiplier_inr (p : Nat.Primes) :
    routePPrimitiveGammaJuliaDepthZeroSignedMultiplier (Sum.inr p) =
      -(routePPrimitiveGammaJuliaDepthZeroStokesMultiplier p : ℂ) := by
  rw [routePPrimitiveGammaJuliaDepthZeroSignedMultiplier,
    routeKSignedPrimeNatIndex,
    routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber]
  have hindex : (2 * routeKPrimeRVMIndex p + 1) / 2 =
      routeKPrimeRVMIndex p := by omega
  rw [hindex, nthPrimeSubtype_routeKPrimeRVMIndex]

theorem norm_routePPrimitiveGammaJuliaDepthZeroSignedMultiplier
    (i : RouteKSignedPrimeIndex) :
    ‖routePPrimitiveGammaJuliaDepthZeroSignedMultiplier i‖ =
      routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber
        (routeKSignedPrimeEquiv.symm i) := by
  cases i with
  | inl p =>
      rw [routePPrimitiveGammaJuliaDepthZeroSignedMultiplier,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber_pos _),
        routeKSignedPrimeEquiv_symm_apply]
  | inr p =>
      rw [routePPrimitiveGammaJuliaDepthZeroSignedMultiplier, norm_neg,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber_pos _),
        routeKSignedPrimeEquiv_symm_apply]

theorem norm_routePPrimitiveGammaJuliaDepthZeroSignedMultiplier_le_zero
    (i : RouteKSignedPrimeIndex) :
    ‖routePPrimitiveGammaJuliaDepthZeroSignedMultiplier i‖ ≤
      routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber 0 := by
  rw [norm_routePPrimitiveGammaJuliaDepthZeroSignedMultiplier]
  exact routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber_antitone (Nat.zero_le _)

/-- Balanced signed depth-zero Route-P Stokes operator. -/
def routePPrimitiveGammaJuliaDepthZeroSignedOperator :
    RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert :=
  HTGeometry.ellTwoDiagonal routePPrimitiveGammaJuliaDepthZeroSignedMultiplier
    norm_routePPrimitiveGammaJuliaDepthZeroSignedMultiplier_le_zero

theorem routePPrimitiveGammaJuliaDepthZeroSignedOperator_approxNumber (n : ℕ) :
    approxNumber routePPrimitiveGammaJuliaDepthZeroSignedOperator n =
      routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber n := by
  simpa [routePPrimitiveGammaJuliaDepthZeroSignedOperator] using
    HTGeometry.approxNumber_ellTwoDiagonal_reindex_eq routeKSignedPrimeEquiv
      norm_routePPrimitiveGammaJuliaDepthZeroSignedMultiplier
      (fun n => (routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber_pos n).le)
      (fun {_ _} h => routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber_antitone h) n

/-- Literal Route-P depth-zero operator belongs to weak Schatten-one. -/
theorem routePPrimitiveGammaJuliaDepthZeroSignedOperator_memWeakSchattenClass_one :
    MemWeakSchattenClass 1 routePPrimitiveGammaJuliaDepthZeroSignedOperator := by
  refine ⟨8, by norm_num, fun n => ?_⟩
  rw [Real.rpow_one,
    routePPrimitiveGammaJuliaDepthZeroSignedOperator_approxNumber,
    routePPrimitiveGammaJuliaDepthZeroSignedApproxNumber,
    routePPrimitiveGammaJuliaDepthZeroStokesMultiplier_eq]
  have hk : n / 2 ≤ (nthPrimeSubtype (n / 2) : ℕ) := by
    exact Nat.le_nth fun hf => (Nat.infinite_setOf_prime hf).elim
  have hp : 0 < (nthPrimeSubtype (n / 2) : ℕ) :=
    (nthPrimeSubtype (n / 2)).property.pos
  have hindex : n + 1 ≤ 4 * (nthPrimeSubtype (n / 2) : ℕ) := by
    have hhalf : n + 1 ≤ 2 * (n / 2 + 1) := by omega
    omega
  have hpR : (0 : ℝ) < (nthPrimeSubtype (n / 2) : ℝ) := by exact_mod_cast hp
  have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ hpR hnR]
  exact_mod_cast (show 2 * (n + 1) ≤
      8 * (nthPrimeSubtype (n / 2) : ℕ) by omega)

/-- Every bounded left/right mixing of Route-P depth-zero carrier remains weak Schatten-one. -/
theorem routePPrimitiveGammaJuliaDepthZeroSignedOperator_boundedMixing_memWeakSchattenClass_one
    (A B : RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert) :
    MemWeakSchattenClass 1
      (A ∘L routePPrimitiveGammaJuliaDepthZeroSignedOperator ∘L B) := by
  rw [← memRectWeakSchattenClass_iff_memWeakSchattenClass]
  exact ((memRectWeakSchattenClass_iff_memWeakSchattenClass 1
      routePPrimitiveGammaJuliaDepthZeroSignedOperator).2
        routePPrimitiveGammaJuliaDepthZeroSignedOperator_memWeakSchattenClass_one
      |>.one_comp_left A).one_comp_right B

/-- No bounded non-diagonal mixing of Route-P depth-zero carrier admits trace-class relocation
to ordered Xi reciprocal operator. -/
theorem routePPrimitiveGammaJuliaDepthZeroSignedOperator_boundedMixing_traceClassRelocationNoGo
    (A B : RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert) :
    ¬ MemSchattenClass 1
      (xiOrderedSignedPrimeOperator -
        (A ∘L routePPrimitiveGammaJuliaDepthZeroSignedOperator ∘L B)) := by
  intro htrace
  exact no_weakSchattenClass_one_traceClass_relocation_to_xiOrderedSignedPrimeOperator
    ⟨_, routePPrimitiveGammaJuliaDepthZeroSignedOperator_boundedMixing_memWeakSchattenClass_one
      A B, htrace⟩

/-- **Basis-independent irregular-RH trace-class relocation obstruction.** Route-P source is weak
Schatten-one, no weak-Schatten-one source is trace-class-close to ordered Xi, and every bounded
non-diagonal mixing of literal Route-P source inherits obstruction. -/
theorem routePPrimitive_GammaJulia_depthZero_weakTraceMixingNoGo :
    MemWeakSchattenClass 1 routePPrimitiveGammaJuliaDepthZeroSignedOperator ∧
    (¬ ∃ S : RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert,
      MemWeakSchattenClass 1 S ∧
        MemSchattenClass 1 (xiOrderedSignedPrimeOperator - S)) ∧
    (∀ A B : RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert,
      ¬ MemSchattenClass 1
        (xiOrderedSignedPrimeOperator -
          (A ∘L routePPrimitiveGammaJuliaDepthZeroSignedOperator ∘L B))) := by
  exact ⟨routePPrimitiveGammaJuliaDepthZeroSignedOperator_memWeakSchattenClass_one,
    no_weakSchattenClass_one_traceClass_relocation_to_xiOrderedSignedPrimeOperator,
    routePPrimitiveGammaJuliaDepthZeroSignedOperator_boundedMixing_traceClassRelocationNoGo⟩

end

end RHTower
