import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaLogWeakTraceMixingNoGo
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesApertureResidueTransport
import GaloisForLFunctions.HTGeometry.LpInjectionCompression

/-!
# Full-carrier weak-trace obstruction for primitive Gamma-Julia Route P

The all-depth balanced irregular-RH carrier splits into its depth-zero prime
harmonic diagonal and an explicitly trace-class positive-depth tail.  Hence the
full carrier is weak Schatten-one.  This remains true after arbitrary bounded
left/right channel mixing, so no trace-class correction can relocate it to the
Xi ordered signed-prime operator, which lies outside weak Schatten-one.

This closes the trace-class Fredholm/Malgrange relocation mechanism for the
literal full Route-P carrier, not only its depth-zero restriction.  A surviving
irregular-RH route must cross the ideal boundary, for example through a genuine
Hilbert--Schmidt/regularized-determinant correction or a source operator whose
principal singular asymptotics are already log-enhanced.
-/

open scoped BigOperators InnerProductSpace Nat.Prime
open Filter ContinuousLinearMap

namespace RHTower

noncomputable section

abbrev RoutePPrimitiveGammaJuliaLogBalancedIndex :=
  Fin 2 × (Nat.Primes × ℕ)

/-- Depth-zero signed-prime coordinates inside full Route-P prime-depth carrier. -/
def routePPrimitiveGammaJuliaDepthZeroFullInjection :
    RouteKSignedPrimeIndex → RoutePPrimitiveGammaJuliaLogBalancedIndex
  | Sum.inl p => (0, (p, 0))
  | Sum.inr p => (1, (p, 0))

theorem routePPrimitiveGammaJuliaDepthZeroFullInjection_injective :
    Function.Injective routePPrimitiveGammaJuliaDepthZeroFullInjection := by
  intro i j hij
  cases i with
  | inl p =>
      cases j with
      | inl q =>
          congr
          exact congrArg (fun x => x.2.1) hij
      | inr q =>
          have hside := congrArg Prod.fst hij
          simp [routePPrimitiveGammaJuliaDepthZeroFullInjection] at hside
  | inr p =>
      cases j with
      | inl q =>
          have hside := congrArg Prod.fst hij
          simp [routePPrimitiveGammaJuliaDepthZeroFullInjection] at hside
      | inr q =>
          congr
          exact congrArg (fun x => x.2.1) hij

/-- Zero-extension along an injection vanishes outside the injected coordinate range. -/
theorem lpScalarInjection_coordinate_eq_zero_of_not_mem_range
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f)
    (x : lp (fun _ : ι => ℂ) 2) (j : κ)
    (hj : j ∉ Set.range f) :
    lpScalarInjection f hf x j = 0 := by
  let J := (lpScalarInjection f hf).toContinuousLinearMap
  let Q := lpCoordinatePullback (E := ℂ) f hf
  have hQ : Q (lp.single 2 j 1) = 0 := by
    apply lp.ext
    funext i
    rw [lpCoordinatePullback_apply]
    have hne : f i ≠ j := by
      intro h
      exact hj ⟨i, h⟩
    simp [lp.single_apply, hne]
  have hadj := ContinuousLinearMap.adjoint_inner_left J x (lp.single 2 j 1)
  have hQadj : Q = J.adjoint := by
    exact lpCoordinatePullback_eq_adjoint_lpScalarInjection f hf
  rw [← hQadj, hQ, inner_zero_left, lp.inner_single_left] at hadj
  simpa [J] using hadj.symm

/-- Full-carrier realization of the depth-zero signed Route-P operator. -/
def routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator :
    RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
      RoutePPrimitiveGammaJuliaLogBalancedHilbert :=
  (lpScalarInjection routePPrimitiveGammaJuliaDepthZeroFullInjection
      routePPrimitiveGammaJuliaDepthZeroFullInjection_injective).toContinuousLinearMap ∘L
    routePPrimitiveGammaJuliaDepthZeroSignedOperator ∘L
      lpCoordinatePullback (E := ℂ)
        routePPrimitiveGammaJuliaDepthZeroFullInjection
        routePPrimitiveGammaJuliaDepthZeroFullInjection_injective

theorem routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator_apply
    (x : RoutePPrimitiveGammaJuliaLogBalancedHilbert)
    (ip : RoutePPrimitiveGammaJuliaLogBalancedIndex) :
    routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator x ip =
      if ip.2.2 = 0 then
        routePPrimitiveGammaJuliaLogBalancedMultiplier ip * x ip
      else 0 := by
  rcases ip with ⟨i, pe⟩
  rcases pe with ⟨p, e⟩
  cases e with
  | zero =>
      fin_cases i
      · change routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator x (0, (p, 0)) =
          routePPrimitiveGammaJuliaLogBalancedMultiplier (0, (p, 0)) * x (0, (p, 0))
        rw [routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        change (lpScalarInjection routePPrimitiveGammaJuliaDepthZeroFullInjection
            routePPrimitiveGammaJuliaDepthZeroFullInjection_injective
            (routePPrimitiveGammaJuliaDepthZeroSignedOperator
              (lpCoordinatePullback (E := ℂ)
                routePPrimitiveGammaJuliaDepthZeroFullInjection
                routePPrimitiveGammaJuliaDepthZeroFullInjection_injective x)))
              (routePPrimitiveGammaJuliaDepthZeroFullInjection (Sum.inl p)) = _
        rw [lpScalarInjection_coordinate,
          routePPrimitiveGammaJuliaDepthZeroSignedOperator,
          HTGeometry.ellTwoDiagonal_apply,
          routePPrimitiveGammaJuliaDepthZeroSignedMultiplier_inl,
          lpCoordinatePullback_apply]
        simp [routePPrimitiveGammaJuliaDepthZeroFullInjection,
          routePPrimitiveGammaJuliaLogBalancedMultiplier,
          routePPrimitiveGammaJuliaLogBalancedSpectralSign,
          routePPrimitiveGammaJuliaDepthZeroStokesMultiplier]
      · change routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator x (1, (p, 0)) =
          routePPrimitiveGammaJuliaLogBalancedMultiplier (1, (p, 0)) * x (1, (p, 0))
        rw [routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        change (lpScalarInjection routePPrimitiveGammaJuliaDepthZeroFullInjection
            routePPrimitiveGammaJuliaDepthZeroFullInjection_injective
            (routePPrimitiveGammaJuliaDepthZeroSignedOperator
              (lpCoordinatePullback (E := ℂ)
                routePPrimitiveGammaJuliaDepthZeroFullInjection
                routePPrimitiveGammaJuliaDepthZeroFullInjection_injective x)))
              (routePPrimitiveGammaJuliaDepthZeroFullInjection (Sum.inr p)) = _
        rw [lpScalarInjection_coordinate,
          routePPrimitiveGammaJuliaDepthZeroSignedOperator,
          HTGeometry.ellTwoDiagonal_apply,
          routePPrimitiveGammaJuliaDepthZeroSignedMultiplier_inr,
          lpCoordinatePullback_apply]
        simp [routePPrimitiveGammaJuliaDepthZeroFullInjection,
          routePPrimitiveGammaJuliaLogBalancedMultiplier,
          routePPrimitiveGammaJuliaLogBalancedSpectralSign,
          routePPrimitiveGammaJuliaDepthZeroStokesMultiplier]
  | succ e =>
      change routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator x (i, (p, e + 1)) = 0
      rw [routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      refine lpScalarInjection_coordinate_eq_zero_of_not_mem_range
        routePPrimitiveGammaJuliaDepthZeroFullInjection
        routePPrimitiveGammaJuliaDepthZeroFullInjection_injective _ _ ?_
      rintro ⟨j, hj⟩
      cases j with
      | inl q =>
          have hdepth := congrArg (fun z => z.2.2) hj
          simp [routePPrimitiveGammaJuliaDepthZeroFullInjection] at hdepth
      | inr q =>
          have hdepth := congrArg (fun z => z.2.2) hj
          simp [routePPrimitiveGammaJuliaDepthZeroFullInjection] at hdepth

/-- Real positive-depth remainder of full balanced Route-P multiplier. -/
def routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier
    (ip : RoutePPrimitiveGammaJuliaLogBalancedIndex) : ℝ :=
  if ip.2.2 = 0 then 0 else
    routePPrimitiveGammaJuliaLogBalancedSpectralSign ip.1 *
      routePPrimitiveGammaJuliaLogCofinalTraceWeight ip.2

/-- Summable product majorant for positive-depth balanced Route-P remainder. -/
def routePPrimitiveGammaJuliaLogBalancedRegularTailMajor
    (ip : RoutePPrimitiveGammaJuliaLogBalancedIndex) : ℝ :=
  4 * (1 / (ip.2.1 : ℝ) ^ 2) * (1 / 2 : ℝ) ^ ip.2.2

theorem summable_routePPrimitiveGammaJuliaLogBalancedRegularTailMajor :
    Summable routePPrimitiveGammaJuliaLogBalancedRegularTailMajor := by
  have hnonneg : 0 ≤ routePPrimitiveGammaJuliaLogBalancedRegularTailMajor := by
    rintro ⟨i, pe⟩
    rcases pe with ⟨p, e⟩
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.zero_le (p : ℕ)
    simp only [routePPrimitiveGammaJuliaLogBalancedRegularTailMajor]
    positivity
  rw [summable_prod_of_nonneg hnonneg]
  constructor
  · intro i
    have hinnerNonneg : 0 ≤
        (fun pe : Nat.Primes × ℕ =>
          routePPrimitiveGammaJuliaLogBalancedRegularTailMajor (i, pe)) := by
      intro pe
      exact hnonneg (i, pe)
    rw [summable_prod_of_nonneg hinnerNonneg]
    constructor
    · intro p
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
        (4 * (1 / (p : ℝ) ^ 2))
    · apply (burnolSummable_prime_one_div_sq.mul_left 8).congr
      intro p
      simp only [routePPrimitiveGammaJuliaLogBalancedRegularTailMajor]
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
  · exact Summable.of_finite

theorem abs_routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier_le
    (ip : RoutePPrimitiveGammaJuliaLogBalancedIndex) :
    |routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier ip| ≤
      routePPrimitiveGammaJuliaLogBalancedRegularTailMajor ip := by
  rcases ip with ⟨i, pe⟩
  rcases pe with ⟨p, e⟩
  by_cases he : e = 0
  · subst e
    simp [routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier,
      routePPrimitiveGammaJuliaLogBalancedRegularTailMajor]
  · have hepos : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
    have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    have hpInv : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
      simpa only [one_div] using
        (inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 2)).2 hp2
    have hpow : ((p : ℝ)⁻¹) ^ (e - 1) ≤ (1 / 2 : ℝ) ^ (e - 1) :=
      pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hpInv (e - 1)
    have hdepth : ((((e : ℝ) + 1) ^ 3)⁻¹) ≤ 1 := by
      apply (inv_le_one₀ (by positivity)).mpr
      exact one_le_pow₀ (by norm_num)
    have hsplit : ((p : ℝ)⁻¹) ^ (e + 1) =
        ((p : ℝ)⁻¹) ^ 2 * ((p : ℝ)⁻¹) ^ (e - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hpowTail : ((p : ℝ)⁻¹) ^ (e + 1) ≤
        ((p : ℝ)⁻¹) ^ 2 * (1 / 2 : ℝ) ^ (e - 1) := by
      rw [hsplit]
      gcongr
    rw [routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier,
      if_neg he, abs_mul]
    have hsign : |routePPrimitiveGammaJuliaLogBalancedSpectralSign i| = 8 := by
      fin_cases i <;>
        simp [routePPrimitiveGammaJuliaLogBalancedSpectralSign]
    rw [hsign, abs_of_nonneg (routePPrimitiveGammaJuliaLogCofinalTraceWeight_nonneg _),
      routePPrimitiveGammaJuliaLogCofinalTraceWeight_eq]
    have hbase : 0 ≤ ((p : ℝ)⁻¹) ^ (e + 1) := by positivity
    have htail :
        ((p : ℝ)⁻¹) ^ (e + 1) * ((((e : ℝ) + 1) ^ 3)⁻¹) ≤
          ((p : ℝ)⁻¹) ^ 2 * (1 / 2 : ℝ) ^ (e - 1) := by
      calc
        ((p : ℝ)⁻¹) ^ (e + 1) * ((((e : ℝ) + 1) ^ 3)⁻¹) ≤
            ((p : ℝ)⁻¹) ^ (e + 1) * 1 := by gcongr
        _ ≤ ((p : ℝ)⁻¹) ^ 2 * (1 / 2 : ℝ) ^ (e - 1) := by
          simpa using hpowTail
    change 8 * ((1 / 4 : ℝ) * ((p : ℝ)⁻¹) ^ (e + 1) *
        (((e : ℝ) + 1) ^ 3)⁻¹) ≤
      4 * (1 / (p : ℝ) ^ 2) * (1 / 2 : ℝ) ^ e
    have heq : (1 / 2 : ℝ) ^ (e - 1) =
        2 * (1 / 2 : ℝ) ^ e := by
      have hpowSucc : (1 / 2 : ℝ) ^ e =
          (1 / 2 : ℝ) ^ (e - 1) * (1 / 2 : ℝ) := by
        calc
          (1 / 2 : ℝ) ^ e = (1 / 2 : ℝ) ^ ((e - 1) + 1) := by
            rw [Nat.sub_add_cancel hepos]
          _ = (1 / 2 : ℝ) ^ (e - 1) * (1 / 2 : ℝ) := by
            rw [pow_succ]
      rw [hpowSucc]
      ring
    rw [show 1 / (p : ℝ) ^ 2 = ((p : ℝ)⁻¹) ^ 2 by
      simp [one_div]]
    nlinarith [htail, heq]

theorem summable_abs_routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier :
    Summable (fun ip =>
      |routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier ip|) := by
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    abs_routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier_le
    summable_routePPrimitiveGammaJuliaLogBalancedRegularTailMajor

/-- Positive-depth Route-P remainder is a trace-class real diagonal. -/
def routePPrimitiveGammaJuliaLogBalancedRegularTailOperator :
    RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
      RoutePPrimitiveGammaJuliaLogBalancedHilbert :=
  GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator
    routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier
    summable_abs_routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier

theorem routePPrimitiveGammaJuliaLogBalancedRegularTailOperator_memSchattenClass_one :
    MemSchattenClass 1 routePPrimitiveGammaJuliaLogBalancedRegularTailOperator := by
  exact GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator_memSchattenClass_one
    routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier
    summable_abs_routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier

theorem routePPrimitiveGammaJuliaLogBalancedOperator_apply
    (x : RoutePPrimitiveGammaJuliaLogBalancedHilbert)
    (ip : RoutePPrimitiveGammaJuliaLogBalancedIndex) :
    routePPrimitiveGammaJuliaLogBalancedOperator x ip =
      routePPrimitiveGammaJuliaLogBalancedMultiplier ip * x ip := by
  have hproof : routePPrimitiveGammaJuliaLogBalancedKernel_isHS =
      HilbertSchmidt.isHS_diagMul_infinite
        routePPrimitiveGammaJuliaLogBalancedMultiplier
        summable_norm_routePPrimitiveGammaJuliaLogBalancedMultiplier_sq := by
    apply Subsingleton.elim
  rw [routePPrimitiveGammaJuliaLogBalancedOperator, hproof]
  exact GaloisForLFunctions.HTGeometry.toOperator_diagMul_apply
    routePPrimitiveGammaJuliaLogBalancedMultiplier
    summable_norm_routePPrimitiveGammaJuliaLogBalancedMultiplier_sq x ip

theorem routePPrimitiveGammaJuliaLogBalancedOperator_eq_depthZero_add_regularTail :
    routePPrimitiveGammaJuliaLogBalancedOperator =
      routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator +
        routePPrimitiveGammaJuliaLogBalancedRegularTailOperator := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext ip
  change routePPrimitiveGammaJuliaLogBalancedOperator x ip =
    routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator x ip +
      routePPrimitiveGammaJuliaLogBalancedRegularTailOperator x ip
  rw [routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator_apply]
  rw [routePPrimitiveGammaJuliaLogBalancedRegularTailOperator,
    GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator_apply]
  rw [routePPrimitiveGammaJuliaLogBalancedOperator_apply]
  by_cases he : ip.2.2 = 0
  · simp [he, routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier]
  · rw [if_neg he, routePPrimitiveGammaJuliaLogBalancedRegularTailRealMultiplier,
      if_neg he]
    push_cast
    rw [routePPrimitiveGammaJuliaLogBalancedMultiplier]
    ring

theorem routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator_memWeakSchattenClass_one :
    MemWeakSchattenClass 1 routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator := by
  rw [← memRectWeakSchattenClass_iff_memWeakSchattenClass]
  exact ((memRectWeakSchattenClass_iff_memWeakSchattenClass 1
      routePPrimitiveGammaJuliaDepthZeroSignedOperator).2
        routePPrimitiveGammaJuliaDepthZeroSignedOperator_memWeakSchattenClass_one
      |>.one_comp_left
        (lpScalarInjection routePPrimitiveGammaJuliaDepthZeroFullInjection
          routePPrimitiveGammaJuliaDepthZeroFullInjection_injective).toContinuousLinearMap)
      |>.one_comp_right
        (lpCoordinatePullback (E := ℂ)
          routePPrimitiveGammaJuliaDepthZeroFullInjection
          routePPrimitiveGammaJuliaDepthZeroFullInjection_injective)

/-- Full all-depth balanced Route-P carrier belongs to weak Schatten-one. -/
theorem routePPrimitiveGammaJuliaLogBalancedOperator_memWeakSchattenClass_one :
    MemWeakSchattenClass 1 routePPrimitiveGammaJuliaLogBalancedOperator := by
  rw [routePPrimitiveGammaJuliaLogBalancedOperator_eq_depthZero_add_regularTail]
  exact routePPrimitiveGammaJuliaDepthZeroEmbeddedOperator_memWeakSchattenClass_one.one_add
    routePPrimitiveGammaJuliaLogBalancedRegularTailOperator_memSchattenClass_one.one_memWeakSchattenClass

theorem routePPrimitiveGammaJuliaLogBalancedOperator_boundedChannel_memWeakSchattenClass_one
    (A : RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
      RouteKSignedPrimeHilbert)
    (C : RouteKSignedPrimeHilbert →L[ℂ]
      RoutePPrimitiveGammaJuliaLogBalancedHilbert) :
    MemWeakSchattenClass 1
      (A ∘L routePPrimitiveGammaJuliaLogBalancedOperator ∘L C) := by
  rw [← memRectWeakSchattenClass_iff_memWeakSchattenClass]
  exact ((memRectWeakSchattenClass_iff_memWeakSchattenClass 1
      routePPrimitiveGammaJuliaLogBalancedOperator).2
        routePPrimitiveGammaJuliaLogBalancedOperator_memWeakSchattenClass_one
      |>.one_comp_left A).one_comp_right C

theorem routePPrimitiveGammaJuliaLogBalancedOperator_boundedChannel_traceClassRelocationNoGo
    (A : RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
      RouteKSignedPrimeHilbert)
    (C : RouteKSignedPrimeHilbert →L[ℂ]
      RoutePPrimitiveGammaJuliaLogBalancedHilbert) :
    ¬ MemSchattenClass 1
      (xiOrderedSignedPrimeOperator -
        (A ∘L routePPrimitiveGammaJuliaLogBalancedOperator ∘L C)) := by
  intro htrace
  exact no_weakSchattenClass_one_traceClass_relocation_to_xiOrderedSignedPrimeOperator
    ⟨_, routePPrimitiveGammaJuliaLogBalancedOperator_boundedChannel_memWeakSchattenClass_one
      A C, htrace⟩

/-- Full-carrier irregular-RH trace-class relocation obstruction. -/
theorem routePPrimitive_GammaJulia_logPrimeHarmonic_fullWeakTraceNoGo :
    MemWeakSchattenClass 1 routePPrimitiveGammaJuliaLogBalancedOperator ∧
    ∀ (A : RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
        RouteKSignedPrimeHilbert)
      (C : RouteKSignedPrimeHilbert →L[ℂ]
        RoutePPrimitiveGammaJuliaLogBalancedHilbert),
      ¬ MemSchattenClass 1
        (xiOrderedSignedPrimeOperator -
          (A ∘L routePPrimitiveGammaJuliaLogBalancedOperator ∘L C)) := by
  exact ⟨routePPrimitiveGammaJuliaLogBalancedOperator_memWeakSchattenClass_one,
    routePPrimitiveGammaJuliaLogBalancedOperator_boundedChannel_traceClassRelocationNoGo⟩

end

end RHTower
