import GaloisForLFunctions.HTGeometry.RectangularApproximationNumberLowerBound
import GaloisForLFunctions.RHTower.ProlateSmallApertureDeflatedFactorization

/-!
# Matching small-aperture lower bounds for every prolate rung

Moment deflation gives the upper estimate
`a_k(S₀(c)) = O(|c|^k)`, but rank-one convergence of each deflated block alone
does not give the reverse inequality: the maximizing input can depend on the
deflation order.  The missing uniformity is supplied by the whole finite moment
jet.

Physical monomials of degrees `0,...,k` form a `(k+1)`-dimensional subspace.
On this subspace the joint leading map

`f ↦ (L₀f,...,L_kf)`

is injective, because `L_i f` is the `i`th physical moment of `f` times the
nonzero `i`th aperture residual.  Finite dimensionality therefore gives a
uniform lower bound for this joint map.  Simultaneous convergence of the
finitely many normalized deflated operators transfers that bound to one
deflation order `i ≤ k`; residual projection is contractive and
`|c|^k ≤ |c|^i` near zero.  The rectangular min--max lower-bound theorem then
gives

`a_k(S₀(c)) ≳ |c|^k`.

Together with the existing deflation upper bound, this proves exact positive
power order `|c|^k` for every rectangular approximation number of the
small-aperture Fourier synthesis operator.
-/

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

attribute [local instance] Measure.Subtype.measureSpace

noncomputable local instance :
    (volume : Measure UnitPhysicalInterval).IsOpenPosMeasure :=
  unitPhysicalInterval_volume_isOpenPosMeasure

/-- Polynomial evaluation as a continuous function on the physical interval. -/
def physicalCpolyToContinuous :
    Polynomial ℂ →ₗ[ℂ] C(UnitPhysicalInterval, ℂ) where
  toFun P :=
    { toFun := fun x => Polynomial.eval ((x : ℝ) : ℂ) P
      continuous_toFun := by fun_prop }
  map_add' P Q := by
    ext x
    simp
  map_smul' c P := by
    ext x
    simp

/-- Restriction to the physical interval is faithful on complex polynomials. -/
theorem physicalCpolyToContinuous_injective :
    Function.Injective physicalCpolyToContinuous := by
  intro P Q hPQ
  rw [← sub_eq_zero]
  by_contra hne
  have hroot : Set.Finite {z : ℂ | Polynomial.IsRoot (P - Q) z} :=
    Polynomial.finite_setOf_isRoot hne
  letI : Infinite UnitPhysicalInterval := Set.Icc.infinite (by norm_num)
  let φ : UnitPhysicalInterval → ℂ := fun x => ((x : ℝ) : ℂ)
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact Complex.ofReal_injective hxy
  have hinfinite : (Set.range φ).Infinite :=
    Set.infinite_range_of_injective hφ
  apply hinfinite
  apply hroot.subset
  rintro z ⟨x, rfl⟩
  have hx := DFunLike.congr_fun hPQ x
  simpa [Polynomial.IsRoot, physicalCpolyToContinuous] using sub_eq_zero.mpr hx

/-- Polynomial evaluation as a physical-interval `L²` vector. -/
noncomputable def physicalCpolyToL2 :
    Polynomial ℂ →ₗ[ℂ] UnitPhysicalScalarL2 :=
  (ContinuousMap.toLp 2 (volume : Measure UnitPhysicalInterval) ℂ).toLinearMap.comp
    physicalCpolyToContinuous

/-- The physical-interval `L²` polynomial realization is faithful. -/
theorem physicalCpolyToL2_injective :
    Function.Injective physicalCpolyToL2 := by
  exact (ContinuousMap.toLp_injective (E := ℂ) (p := 2) (𝕜 := ℂ)
    (volume : Measure UnitPhysicalInterval)).comp
      physicalCpolyToContinuous_injective

/-- The `n`th complex monomial in physical-interval `L²`. -/
noncomputable def physicalComplexMonomialL2 (n : ℕ) :
    UnitPhysicalScalarL2 :=
  physicalCpolyToL2 ((Polynomial.X : Polynomial ℂ) ^ n)

theorem physicalComplexMonomialL2_coeFn (n : ℕ) :
    ((physicalComplexMonomialL2 n : UnitPhysicalScalarL2) :
        UnitPhysicalInterval → ℂ) =ᵐ[volume]
      fun x => (((x : ℝ) ^ n : ℝ) : ℂ) := by
  have h := ContinuousMap.coeFn_toLp
    (𝕜 := ℂ) (p := (2 : ENNReal))
    (μ := (volume : Measure UnitPhysicalInterval))
    (physicalCpolyToContinuous ((Polynomial.X : Polynomial ℂ) ^ n))
  simpa [physicalComplexMonomialL2, physicalCpolyToL2,
    physicalCpolyToContinuous] using h

/-- All physical-interval complex monomials are linearly independent in `L²`. -/
theorem linearIndependent_physicalComplexMonomialL2 :
    LinearIndependent ℂ physicalComplexMonomialL2 := by
  have hX : LinearIndependent ℂ
      (fun n : ℕ => (Polynomial.X : Polynomial ℂ) ^ n) := by
    have hb := (Polynomial.basisMonomials ℂ).linearIndependent
    rw [Polynomial.coe_basisMonomials] at hb
    simpa [Polynomial.X_pow_eq_monomial] using hb
  exact hX.map' physicalCpolyToL2
    (LinearMap.ker_eq_bot.mpr physicalCpolyToL2_injective)

/-- Span of the physical monomials of degrees strictly below `k`. -/
def physicalMomentSpan (k : ℕ) : Submodule ℂ UnitPhysicalScalarL2 :=
  Submodule.span ℂ
    (Set.range fun i : Fin k => physicalComplexMonomialL2 (i : ℕ))

noncomputable instance physicalMomentSpan_finiteDimensional (k : ℕ) :
    FiniteDimensional ℂ (physicalMomentSpan k) := by
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- The physical moment span has exactly the expected dimension. -/
theorem finrank_physicalMomentSpan (k : ℕ) :
    Module.finrank ℂ (physicalMomentSpan k) = k := by
  rw [physicalMomentSpan]
  change Module.finrank ℂ (Submodule.span ℂ
    (Set.range (physicalComplexMonomialL2 ∘ fun i : Fin k => (i : ℕ)))) = k
  rw [finrank_span_eq_card
    (linearIndependent_physicalComplexMonomialL2.comp
      (fun i : Fin k => (i : ℕ)) (fun i j h => Fin.ext h)), Fintype.card_fin]

/-- Exact rank-one formula for the leading `k`th deflated synthesis operator:
it reads the `k`th physical moment and emits the nonzero `k`th aperture
residual. -/
theorem apertureMomentLeadingSynthesis_apply (k : ℕ)
    (f : UnitPhysicalScalarL2) :
    apertureMomentLeadingSynthesis k f =
      inner ℂ (physicalComplexMonomialL2 k) f •
        fourierGroundVector 1 (apertureMomentResidual k) k := by
  rw [apertureMomentLeadingSynthesis, apertureMomentSynthesisMap_apply,
    l2Synthesis_apply]
  let q : UnitApertureL2 :=
    fourierGroundVector 1 (apertureMomentResidual k) k
  have hfield : (apertureMomentLeadingFieldL2 k :
      UnitPhysicalInterval → UnitApertureL2) =ᵐ[volume]
      fun x => (((x : ℝ) ^ k : ℝ) : ℂ) • q := by
    have h := ContinuousMap.coeFn_toLp
      (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure UnitPhysicalInterval))
      (apertureMomentFieldCoeff k k)
    simpa [apertureMomentLeadingFieldL2, apertureMomentFieldToL2,
      apertureMomentFieldCoeff, q] using h
  calc
    (∫ x, f x • apertureMomentLeadingFieldL2 k x
        ∂(volume : Measure UnitPhysicalInterval)) =
        ∫ x, (f x * (((x : ℝ) ^ k : ℝ) : ℂ)) • q
          ∂(volume : Measure UnitPhysicalInterval) := by
      apply integral_congr_ae
      filter_upwards [hfield] with x hx
      rw [hx, smul_smul]
    _ = (∫ x, f x * (((x : ℝ) ^ k : ℝ) : ℂ)
          ∂(volume : Measure UnitPhysicalInterval)) • q := by
      rw [integral_smul_const]
    _ = inner ℂ (physicalComplexMonomialL2 k) f • q := by
      congr 1
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [physicalComplexMonomialL2_coeFn k] with x hx
      rw [hx]
      simp [RCLike.inner_apply, mul_comm]

/-- Joint leading moment jet through order `k`. -/
noncomputable def leadingMomentJet (k : ℕ) :
    physicalMomentSpan (k + 1) →ₗ[ℂ]
      (Fin (k + 1) → UnitApertureL2) where
  toFun f i := apertureMomentLeadingSynthesis (i : ℕ) (f : UnitPhysicalScalarL2)
  map_add' f g := by
    ext i
    simp
  map_smul' c f := by
    ext i
    simp

/-- The whole leading moment jet is injective on the degree-at-most-`k`
physical polynomial space. -/
theorem leadingMomentJet_injective (k : ℕ) :
    Function.Injective (leadingMomentJet k) := by
  rw [← LinearMap.ker_eq_bot]
  rw [LinearMap.ker_eq_bot']
  intro f hf
  apply Subtype.ext
  have hmoment : ∀ i : Fin (k + 1),
      inner ℂ (physicalComplexMonomialL2 (i : ℕ))
        (f : UnitPhysicalScalarL2) = 0 := by
    intro i
    have hi := congrFun hf i
    change apertureMomentLeadingSynthesis (i : ℕ) (f : UnitPhysicalScalarL2) = 0 at hi
    rw [apertureMomentLeadingSynthesis_apply] at hi
    exact (smul_eq_zero.mp hi).resolve_right
      (fourierGroundVector_apertureMomentResidual_ne_zero (i : ℕ))
  have hself : inner ℂ (f : UnitPhysicalScalarL2)
      (f : UnitPhysicalScalarL2) = 0 := by
    refine Submodule.span_induction
      (p := fun g _ => inner ℂ g (f : UnitPhysicalScalarL2) = 0)
      ?_ (by simp) ?_ ?_ f.property
    · rintro g ⟨i, rfl⟩
      exact hmoment i
    · intro x y hx hy hix hiy
      rw [inner_add_left, hix, hiy, add_zero]
    · intro c x hx hix
      rw [inner_smul_left, hix, mul_zero]
  exact inner_self_eq_zero.mp hself

/-- Matching lower spectral order for every rung of the undeflated
small-aperture synthesis operator. -/
theorem exists_pos_eventually_rectApproxNumber_full_lower (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ),
        C * |c| ^ k ≤
          rectApproxNumber (apertureMomentFourierSynthesis 0 c) k := by
  classical
  obtain ⟨K, hKpos, hanti⟩ :=
    (leadingMomentJet k).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr (leadingMomentJet_injective k))
  let C : ℝ := (K : ℝ)⁻¹ / 2
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  have hcloseEach : ∀ i : Fin (k + 1),
      ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ),
        ‖normalizedApertureMomentSynthesis (i : ℕ) c -
          apertureMomentLeadingSynthesis (i : ℕ)‖ < C := by
    intro i
    have hzero := (tendsto_iff_norm_sub_tendsto_zero).mp
      (tendsto_normalizedApertureMomentSynthesis (i : ℕ))
    exact hzero.eventually_lt_const hCpos
  have hclose : ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ i : Fin (k + 1),
        ‖normalizedApertureMomentSynthesis (i : ℕ) c -
          apertureMomentLeadingSynthesis (i : ℕ)‖ < C :=
    Filter.eventually_all.mpr hcloseEach
  have hsmallNhd : ∀ᶠ c : ℝ in 𝓝 (0 : ℝ), |c| < 1 := by
    filter_upwards
      [(Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))]
      with c hc
    simpa [Real.dist_eq] using hc
  have hsmall : ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ), |c| < 1 :=
    hsmallNhd.filter_mono nhdsWithin_le_nhds
  filter_upwards [hclose, hsmall, self_mem_nhdsWithin]
    with c hcclose hcsmall hc0
  have hcne : c ≠ 0 := by simpa using hc0
  refine le_rectApproxNumber_of_subspace
    (physicalMomentSpan (k + 1)) ?_ ?_
  · rw [finrank_physicalMomentSpan]
  · intro w hw
    let wf : physicalMomentSpan (k + 1) := ⟨w, hw⟩
    have hjet : (K : ℝ)⁻¹ * ‖w‖ ≤ ‖leadingMomentJet k wf‖ := by
      simpa [dist_eq_norm, wf] using hanti.mul_le_dist wf 0
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm (leadingMomentJet k wf)).1
    have hlead : (K : ℝ)⁻¹ * ‖w‖ ≤
        ‖apertureMomentLeadingSynthesis (i : ℕ) w‖ := by
      calc
        (K : ℝ)⁻¹ * ‖w‖ ≤ ‖leadingMomentJet k wf‖ := hjet
        _ = ‖leadingMomentJet k wf i‖ := hi.symm
        _ = ‖apertureMomentLeadingSynthesis (i : ℕ) w‖ := rfl
    have hdiff :
        ‖apertureMomentLeadingSynthesis (i : ℕ) w -
          normalizedApertureMomentSynthesis (i : ℕ) c w‖ ≤ C * ‖w‖ := by
      calc
        ‖apertureMomentLeadingSynthesis (i : ℕ) w -
            normalizedApertureMomentSynthesis (i : ℕ) c w‖ =
            ‖(normalizedApertureMomentSynthesis (i : ℕ) c -
              apertureMomentLeadingSynthesis (i : ℕ)) w‖ := by
          rw [sub_apply, norm_sub_rev]
        _ ≤ ‖normalizedApertureMomentSynthesis (i : ℕ) c -
              apertureMomentLeadingSynthesis (i : ℕ)‖ * ‖w‖ :=
          (normalizedApertureMomentSynthesis (i : ℕ) c -
            apertureMomentLeadingSynthesis (i : ℕ)).le_opNorm w
        _ ≤ C * ‖w‖ :=
          mul_le_mul_of_nonneg_right (hcclose i).le (norm_nonneg w)
    have htri : ‖apertureMomentLeadingSynthesis (i : ℕ) w‖ ≤
        ‖normalizedApertureMomentSynthesis (i : ℕ) c w‖ + C * ‖w‖ := by
      calc
        ‖apertureMomentLeadingSynthesis (i : ℕ) w‖ =
            ‖normalizedApertureMomentSynthesis (i : ℕ) c w +
              (apertureMomentLeadingSynthesis (i : ℕ) w -
                normalizedApertureMomentSynthesis (i : ℕ) c w)‖ := by
          congr 1
          abel
        _ ≤ ‖normalizedApertureMomentSynthesis (i : ℕ) c w‖ +
              ‖apertureMomentLeadingSynthesis (i : ℕ) w -
                normalizedApertureMomentSynthesis (i : ℕ) c w‖ := norm_add_le _ _
        _ ≤ ‖normalizedApertureMomentSynthesis (i : ℕ) c w‖ + C * ‖w‖ :=
          add_le_add le_rfl hdiff
    have hnormalized : C * ‖w‖ ≤
        ‖normalizedApertureMomentSynthesis (i : ℕ) c w‖ := by
      have hcomb := hlead.trans htri
      dsimp [C] at hcomb ⊢
      linarith
    have hrescale : apertureMomentFourierSynthesis (i : ℕ) c w =
        (c ^ (i : ℕ)) • normalizedApertureMomentSynthesis (i : ℕ) c w := by
      change apertureMomentFourierSynthesis (i : ℕ) c w =
        (c ^ (i : ℕ)) • ((c ^ (i : ℕ))⁻¹ •
          apertureMomentFourierSynthesis (i : ℕ) c) w
      rw [smul_apply, smul_smul,
        mul_inv_cancel₀ (pow_ne_zero _ hcne), one_smul]
    have hdeflated : C * |c| ^ (i : ℕ) * ‖w‖ ≤
        ‖apertureMomentFourierSynthesis (i : ℕ) c w‖ := by
      rw [hrescale, norm_smul, Real.norm_eq_abs, abs_pow]
      have hmul := mul_le_mul_of_nonneg_left hnormalized
        (pow_nonneg (abs_nonneg c) (i : ℕ))
      nlinarith
    have hcontract :
        ‖apertureMomentResidual (i : ℕ)
          (apertureMomentFourierSynthesis 0 c w)‖ ≤
        ‖apertureMomentFourierSynthesis 0 c w‖ := by
      rw [apertureMomentResidual_apply,
        ← (apertureMomentSpan (i : ℕ)).starProjection_orthogonal_val]
      exact (apertureMomentSpan (i : ℕ)).orthogonal.norm_starProjection_apply_le _
    have hfull : C * |c| ^ (i : ℕ) * ‖w‖ ≤
        ‖apertureMomentFourierSynthesis 0 c w‖ := by
      apply hdeflated.trans
      rw [apertureMomentFourierSynthesis_eq_residual_comp,
        ContinuousLinearMap.comp_apply]
      exact hcontract
    have hpow : |c| ^ k ≤ |c| ^ (i : ℕ) :=
      pow_le_pow_of_le_one (abs_nonneg c) hcsmall.le (by omega)
    calc
      C * |c| ^ k * ‖w‖ ≤ C * |c| ^ (i : ℕ) * ‖w‖ := by
        gcongr
      _ ≤ ‖apertureMomentFourierSynthesis 0 c w‖ := hfull

/-- Exact two-sided positive power law for every approximation-number rung. -/
theorem exists_pos_eventually_rectApproxNumber_full_twoSided (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ),
        C * |c| ^ k ≤ rectApproxNumber
            (apertureMomentFourierSynthesis 0 c) k ∧
          rectApproxNumber (apertureMomentFourierSynthesis 0 c) k ≤
            D * |c| ^ k := by
  obtain ⟨C, hCpos, hlower⟩ :=
    exists_pos_eventually_rectApproxNumber_full_lower k
  let D : ℝ := ‖apertureMomentLeadingSynthesis k‖ + 1
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨C, D, hCpos, hDpos, ?_⟩
  have hupper := eventually_rectApproxNumber_full_le_leading_mul_abs_pow
    k (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hlower, hupper] with c hcLower hcUpper
  exact ⟨hcLower, by simpa [D] using hcUpper⟩

end RHTower
