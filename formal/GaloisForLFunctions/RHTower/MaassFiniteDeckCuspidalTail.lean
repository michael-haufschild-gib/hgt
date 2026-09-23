import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalDirichlet
import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichletPeriodization
import GaloisForLFunctions.RHTower.EisensteinFundamentalDomainIntegrability
import GaloisForLFunctions.HTGeometry.LpBoundedSmulMultiplier
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

open Complex Filter MeasureTheory ModularGroup Set Topology UpperHalfPlane
open scoped ContDiff MatrixGroups

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceAverage
  SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceDirection
  MaassCongruenceL2

/-- A fixed positive-height horocycle is a continuous path in the upper half plane. -/
private theorem cusp_point_continuous {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => ofComplex (point x y) := by
  have he : (fun x : ℝ => ofComplex (point x y)) =
      fun x : ℝ => (⟨point x y, by simpa [point] using hy⟩ : ℍ) := by
    funext x
    exact ofComplex_apply_of_im_pos (by simpa [point] using hy)
  rw [he]
  have hm : Continuous fun x : ℝ => point x y := by
    change Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I
    fun_prop
  exact hm.upperHalfPlaneMk (fun _ => by simpa [point] using hy)

/-- Coordinate mass is interval-integrable on every positive-height horocycle. -/
private theorem component_value_normSq_intervalIntegrable {N : ℕ}
    (F : cuspidalFormPreDomain N) (q : Deck N) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => ‖component (F : ℍ → DeckSpace N) q (ofComplex (point x y))‖ ^ (2 : ℕ))
      volume a b := by
  have hF : Continuous (F : ℍ → DeckSpace N) :=
    continuous_of_isChartC1 (cuspidalFormPreDomain.c1 F)
  have hcont : Continuous fun x : ℝ => (F : ℍ → DeckSpace N) (ofComplex (point x y)) q := by
    exact (PiLp.continuous_apply 2 (fun _ : Deck N => ℂ) q).comp
      (hF.comp (cusp_point_continuous hy))
  exact (hcont.norm.pow 2).intervalIntegrable _ _

/-- Coordinate horizontal energy is interval-integrable on every positive-height horocycle. -/
private theorem component_hypGradX_normSq_intervalIntegrable {N : ℕ}
    (F : cuspidalFormPreDomain N) (q : Deck N) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ (2 : ℕ))
      volume a b := by
  have hF : Continuous (hypGradX (F : ℍ → DeckSpace N)) :=
    continuous_hypGradX_vec (cuspidalFormPreDomain.c1 F)
  have hcont : Continuous fun x : ℝ => hypGradX (F : ℍ → DeckSpace N)
      (ofComplex (point x y)) q := by
    exact (PiLp.continuous_apply 2 (fun _ : Deck N => ℂ) q).comp
      (hF.comp (cusp_point_continuous hy))
  exact (hcont.norm.pow 2).intervalIntegrable _ _

/-- The finite-deck coordinate masses sum exactly to the vector mass on a horocycle. -/
theorem sum_component_value_normSq_interval_eq {N : ℕ}
    (F : cuspidalFormPreDomain N) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    (∑ q : Deck N, ∫ x in a..b,
      ‖component (F : ℍ → DeckSpace N) q (ofComplex (point x y))‖ ^ (2 : ℕ)) =
      ∫ x in a..b, ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    rw [EuclideanSpace.norm_sq_eq]
    simp only [component]
  · intro q _
    exact component_value_normSq_intervalIntegrable F q hy a b

/-- The finite-deck coordinate horizontal energies sum exactly to vector energy. -/
theorem sum_component_hypGradX_normSq_interval_eq {N : ℕ}
    (F : cuspidalFormPreDomain N) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    (∑ q : Deck N, ∫ x in a..b,
      ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ (2 : ℕ)) =
      ∫ x in a..b, ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    rw [EuclideanSpace.norm_sq_eq]
  · intro q _
    exact component_hypGradX_normSq_intervalIntegrable F q hy a b

/-- The sharp cuspidal Poincaré estimate directly on one full finite-deck
level period.  Its interval is exactly the one used by the periodic Green
identity. -/
theorem level_cusp_slice_poincare {N : ℕ}
    (F : cuspidalFormPreDomain N) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ),
      ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ))
      ≤ (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * y⁻¹ ^ (2 : ℕ) *
        ∫ x in a..a + (N + 1 : ℕ),
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
  let L : ℝ := N + 1
  let C : ℝ := ((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)
  have hL : 0 < L := by positivity
  rw [← sum_component_value_normSq_interval_eq F hy a (a + (N + 1 : ℕ)),
    ← sum_component_hypGradX_normSq_interval_eq F hy a (a + (N + 1 : ℕ))]
  calc
    ∑ q : Deck N, ∫ x in a..a + (N + 1 : ℕ),
        ‖component (F : ℍ → DeckSpace N) q (ofComplex (point x y))‖ ^ (2 : ℕ)
      ≤ ∑ q : Deck N, C * y⁻¹ ^ (2 : ℕ) *
          ∫ x in a..a + (N + 1 : ℕ),
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro q _
        have hq := component_wirtinger_slice_hypGradX F q hy a
        calc
          ∫ x in a..a + (N + 1 : ℕ),
              ‖component (F : ℍ → DeckSpace N) q (ofComplex (point x y))‖ ^ (2 : ℕ)
            = L * (L⁻¹ * ∫ x in a..a + (N + 1 : ℕ),
                ‖component (F : ℍ → DeckSpace N) q (ofComplex (point x y))‖ ^ (2 : ℕ)) := by
                field_simp [L, ne_of_gt hL]
          _ ≤ L * (C * y⁻¹ ^ (2 : ℕ) *
              (L⁻¹ * ∫ x in a..a + (N + 1 : ℕ),
                ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ (2 : ℕ))) := by
                exact mul_le_mul_of_nonneg_left hq hL.le
          _ = C * y⁻¹ ^ (2 : ℕ) * ∫ x in a..a + (N + 1 : ℕ),
              ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ (2 : ℕ) := by
                field_simp [L, ne_of_gt hL]
    _ = (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * y⁻¹ ^ (2 : ℕ) *
        ∑ q : Deck N, ∫ x in a..a + (N + 1 : ℕ),
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ (2 : ℕ) := by
          rw [Finset.mul_sum]


/-- Cusp-zero finite-deck vectors satisfy the sharp unit-width horizontal Poincaré estimate. -/
theorem unit_cusp_slice_poincare {N : ℕ}
    (F : cuspidalFormPreDomain N) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ))
      ≤ (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * y⁻¹ ^ (2 : ℕ) *
        ∫ x in (0 : ℝ)..1,
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
  let L : ℝ := N + 1
  let C : ℝ := ((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)
  have hsum :
      L⁻¹ * (∫ x in (0 : ℝ)..(N + 1 : ℕ),
        ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ))
        ≤ C * y⁻¹ ^ (2 : ℕ) *
          (L⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) := by
    rw [← sum_component_value_normSq_interval_eq F hy 0 (N + 1 : ℕ),
      ← sum_component_hypGradX_normSq_interval_eq F hy 0 (N + 1 : ℕ),
      Finset.mul_sum]
    calc
      ∑ q : Deck N, L⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
          ‖component (F : ℍ → DeckSpace N) q (ofComplex (point x y))‖ ^ (2 : ℕ)
        ≤ ∑ q : Deck N, C * y⁻¹ ^ (2 : ℕ) *
          (L⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ (2 : ℕ)) := by
          apply Finset.sum_le_sum
          intro q _
          simpa only [L, C, zero_add] using
            component_wirtinger_slice_hypGradX F q hy 0
      _ = C * y⁻¹ ^ (2 : ℕ) *
          ∑ q : Deck N, L⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ (2 : ℕ) := by
          rw [Finset.mul_sum]
      _ = C * y⁻¹ ^ (2 : ℕ) *
          (L⁻¹ * ∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℕ),
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q‖ ^ (2 : ℕ)) := by
          rw [← Finset.mul_sum]
  have hL : (N + 1 : ℝ) ≠ 0 := by positivity
  have hvalue := value_normSq_interval_level_period
    (cuspidalFormPreDomain.toFormPreDomain N F) hy 0
  have hgrad := hypGradX_normSq_interval_level_period
    (cuspidalFormPreDomain.toFormPreDomain N F) hy 0
  have hvalue' :
      (∫ x in (0 : ℝ)..(N + 1 : ℕ),
        ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
        ((N + 1 : ℕ) : ℤ) • ∫ x in (0 : ℝ)..1,
          ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
    simpa only [zero_add, cuspidalFormPreDomain.coe_toFormPreDomain] using hvalue
  have hgrad' :
      (∫ x in (0 : ℝ)..(N + 1 : ℕ),
        ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
        ((N + 1 : ℕ) : ℤ) • ∫ x in (0 : ℝ)..1,
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
    simpa only [zero_add, cuspidalFormPreDomain.coe_toFormPreDomain] using hgrad
  rw [hvalue', hgrad'] at hsum
  rw [zsmul_eq_mul, zsmul_eq_mul] at hsum
  have hcast : (((((N + 1 : ℕ) : ℤ) : ℝ)) = (N + 1 : ℝ)) := by norm_num
  simpa only [L, C, hcast, ← mul_assoc, inv_mul_cancel₀ hL, one_mul] using hsum


/-- The unit-width cusp estimate on the centered cross-section of the modular cell. -/
theorem centered_cusp_slice_poincare {N : ℕ}
    (F : cuspidalFormPreDomain N) {y : ℝ} (hy : 0 < y) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ))
      ≤ (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * y⁻¹ ^ (2 : ℕ) *
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
  have hvalue : Function.Periodic
      (fun x : ℝ => ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) 1 := by
    intro x
    exact congrArg (fun r : ℝ => r ^ (2 : ℕ))
      (form_value_norm_one_periodic (cuspidalFormPreDomain.toFormPreDomain N F) hy x)
  have hgrad : Function.Periodic
      (fun x : ℝ => ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) 1 := by
    intro x
    exact hypGradX_normSq_one_periodic
      (cuspidalFormPreDomain.toFormPreDomain N F) hy x
  have hvalue' := hvalue.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  have hgrad' := hgrad.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  calc
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ))
        = ∫ x in (-(1 / 2 : ℝ))..(-(1 / 2 : ℝ) + 1),
          ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
            congr 1
            ring
    _ = ∫ x in (0 : ℝ)..0 + 1,
          ‖(F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := hvalue'
    _ ≤ (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * y⁻¹ ^ (2 : ℕ) *
          ∫ x in (0 : ℝ)..1,
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
            simpa only [zero_add] using unit_cusp_slice_poincare F hy
    _ = (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * y⁻¹ ^ (2 : ℕ) *
          ∫ x in (-(1 / 2 : ℝ))..(-(1 / 2 : ℝ) + 1),
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
            simpa only [zero_add] using congrArg
              (fun r : ℝ => (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * y⁻¹ ^ (2 : ℕ) * r)
              hgrad'.symm
    _ = (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * y⁻¹ ^ (2 : ℕ) *
          ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
            congr 3
            ring

private theorem ofComplex_point_re_im (z : ℍ) :
    ofComplex (point z.re z.im) = z := by
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos (by simpa [point] using z.im_pos)]
  apply Complex.ext <;> simp [point]

private theorem normSq_integrableOn_fd {N : ℕ} (G : ℍ → DeckSpace N)
    (hcont : Continuous G) (hG : MemLp G 2 cellMeasure) :
    IntegrableOn (fun z => ‖G z‖ ^ (2 : ℕ)) fd volume := by
  have hsq : Integrable (fun z => ‖G z‖ ^ (2 : ℕ)) cellMeasure :=
    (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mp hG
  exact hsq

private theorem weighted_normSq_product_integrable {N : ℕ}
    (G : ℍ → DeckSpace N) (hcont : Continuous G) (hG : MemLp G 2 cellMeasure)
    {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun p : ℝ × ℝ =>
      ‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ)) (RHTower.cuspRect Y) volume := by
  have hfd : IntegrableOn (fun z => ‖G z‖ ^ (2 : ℕ)) fd volume :=
    normSq_integrableOn_fd G hcont hG
  have htail : IntegrableOn (fun z => ‖G z‖ ^ (2 : ℕ))
      (fd ∩ {z : ℍ | Y < z.im}) volume :=
    hfd.mono_set inter_subset_left
  have hleft : IntegrableOn
      (fun z : ℍ => ((‖G (ofComplex (point z.re z.im))‖ ^ (2 : ℕ) : ℝ) : ℂ))
      {z : ℍ | (z.re, z.im) ∈ RHTower.cuspRect Y} volume := by
    rw [RHTower.setOf_coord_cuspRect hY]
    have htailC : IntegrableOn (fun z : ℍ => ((‖G z‖ ^ (2 : ℕ) : ℝ) : ℂ))
        (fd ∩ {z : ℍ | Y < z.im}) volume := htail.ofReal
    refine htailC.congr_fun ?_ (RHTower.measurableSet_fd_inter_above Y)
    intro z _
    change ((‖G z‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      ((‖G (ofComplex (point z.re z.im))‖ ^ (2 : ℕ) : ℝ) : ℂ)
    rw [ofComplex_point_re_im]
  have hprodC :=
    (RHTower.integrableOn_coord_iff (RHTower.measurableSet_cuspRect Y)
      (fun p hp => RHTower.cuspRect_pos (by linarith) hp)
      (fun p => ((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) : ℝ) : ℂ))).mp hleft
  have hprodR : IntegrableOn (fun p : ℝ × ℝ =>
      RCLike.re (((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) : ℝ) : ℂ) /
        ((p.2 : ℝ) : ℂ) ^ (2 : ℕ))) (RHTower.cuspRect Y) volume := hprodC.re
  refine hprodR.congr_fun ?_ (RHTower.measurableSet_cuspRect Y)
  intro p hp
  have hp2 : p.2 ≠ 0 := (RHTower.cuspRect_pos (by linarith) hp).ne'
  have hdiv :
      ((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) : ℝ) : ℂ) /
          ((p.2 : ℝ) : ℂ) ^ (2 : ℕ) =
        ((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    field_simp
  change RCLike.re (((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) : ℝ) : ℂ) /
      ((p.2 : ℝ) : ℂ) ^ (2 : ℕ)) =
    ‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ)
  rw [hdiv]
  rfl

theorem cusp_value_weighted_integrable {N : ℕ} (F : cuspidalFormPreDomain N)
    {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun p : ℝ × ℝ =>
      ‖(F : ℍ → DeckSpace N) (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ))
      (RHTower.cuspRect Y) volume := by
  exact weighted_normSq_product_integrable (F : ℍ → DeckSpace N)
    (continuous_of_isChartC1 (cuspidalFormPreDomain.c1 F))
    (cuspidalFormPreDomain.memLp F) hY

theorem cusp_hypGradX_weighted_integrable {N : ℕ} (F : cuspidalFormPreDomain N)
    {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun p : ℝ × ℝ =>
      ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ))
      (RHTower.cuspRect Y) volume := by
  exact weighted_normSq_product_integrable (hypGradX (F : ℍ → DeckSpace N))
    (continuous_hypGradX_vec (cuspidalFormPreDomain.c1 F))
    (cuspidalFormPreDomain.memLp_gradX F) hY

/-- The vertical hyperbolic derivative has the same literal weighted cusp-tail
integrability as the horizontal derivative. -/
theorem cusp_hypGradY_weighted_integrable {N : ℕ} (F : cuspidalFormPreDomain N)
    {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun p : ℝ × ℝ =>
      ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ))
      (RHTower.cuspRect Y) volume := by
  exact weighted_normSq_product_integrable (hypGradY (F : ℍ → DeckSpace N))
    (continuous_hypGradY_vec (cuspidalFormPreDomain.c1 F))
    (cuspidalFormPreDomain.memLp_gradY F) hY


private theorem centered_setIntegral_div_eq_interval (g : ℝ → ℝ) (y : ℝ) :
    ∫ x in RHTower.unitIcc, g x / y ^ (2 : ℕ) =
      y⁻¹ ^ (2 : ℕ) * ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), g x := by
  rw [MeasureTheory.integral_div, RHTower.unitIcc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- Weighted `L²` membership on the cusp rectangle gives an integrable
centered horocycle energy. -/
private theorem centered_weighted_slice_integrable {N : ℕ}
    (G : ℍ → DeckSpace N) (hcont : Continuous G) (hG : MemLp G 2 cellMeasure)
    {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun y : ℝ => y⁻¹ ^ (2 : ℕ) *
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        ‖G (ofComplex (point x y))‖ ^ (2 : ℕ)) (Ioi Y) volume := by
  have hprod : IntegrableOn (fun p : ℝ × ℝ =>
      ‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ))
      (RHTower.unitIcc ×ˢ Ioi Y) volume := by
    simpa only [RHTower.cuspRect] using weighted_normSq_product_integrable G hcont hG hY
  have hslice : IntegrableOn (fun y : ℝ =>
      ∫ x in RHTower.unitIcc,
        ‖G (ofComplex (point x y))‖ ^ (2 : ℕ) / y ^ (2 : ℕ)) (Ioi Y) volume :=
    RHTower.integrableOn_slice_of_prod_unitIcc hprod
  refine hslice.congr_fun ?_ measurableSet_Ioi
  intro y hy
  exact centered_setIntegral_div_eq_interval
    (fun x => ‖G (ofComplex (point x y))‖ ^ (2 : ℕ)) y

theorem centered_hypGradX_slice_weighted_integrable {N : ℕ}
    (F : cuspidalFormPreDomain N) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun y : ℝ => y⁻¹ ^ (2 : ℕ) *
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ))
      (Ioi Y) volume := by
  exact centered_weighted_slice_integrable (hypGradX (F : ℍ → DeckSpace N))
    (continuous_hypGradX_vec (cuspidalFormPreDomain.c1 F))
    (cuspidalFormPreDomain.memLp_gradX F) hY

theorem centered_hypGradY_slice_weighted_integrable {N : ℕ}
    (F : cuspidalFormPreDomain N) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun y : ℝ => y⁻¹ ^ (2 : ℕ) *
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ))
      (Ioi Y) volume := by
  exact centered_weighted_slice_integrable (hypGradY (F : ℍ → DeckSpace N))
    (continuous_hypGradY_vec (cuspidalFormPreDomain.c1 F))
    (cuspidalFormPreDomain.memLp_gradY F) hY

theorem level_hypGradX_slice_weighted_integrable {N : ℕ}
    (F : cuspidalFormPreDomain N) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun y : ℝ => y⁻¹ ^ (2 : ℕ) *
      ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ))
      (Ioi Y) volume := by
  have hcenter := centered_hypGradX_slice_weighted_integrable F hY
  refine IntegrableOn.congr_fun (hcenter.const_mul (N + 1 : ℝ)) ?_ measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hY |>.trans hy
  have hperiodic : Function.Periodic
      (fun x : ℝ => ‖hypGradX (F : ℍ → DeckSpace N)
        (ofComplex (point x y))‖ ^ (2 : ℕ)) 1 := by
    intro x
    exact hypGradX_normSq_one_periodic
      (cuspidalFormPreDomain.toFormPreDomain N F) hy0 x
  have hshift := hperiodic.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  have hlevel := hypGradX_normSq_interval_level_period
    (cuspidalFormPreDomain.toFormPreDomain N F) hy0 0
  have hlevel' :
      (∫ x in (0 : ℝ)..(N + 1 : ℕ),
        ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
        ((N + 1 : ℕ) : ℤ) • ∫ x in (0 : ℝ)..1,
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
    simpa only [zero_add, cuspidalFormPreDomain.coe_toFormPreDomain] using hlevel
  have hcenter :
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
        ∫ x in (0 : ℝ)..1,
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
    calc
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
          ∫ x in (-(1 / 2 : ℝ))..(-(1 / 2 : ℝ) + 1),
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
              congr 1
              ring
      _ = ∫ x in (0 : ℝ)..0 + 1,
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := hshift
      _ = ∫ x in (0 : ℝ)..1,
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by ring
  have hlength : ((N + 1 : ℕ) : ℝ) = (N + 1 : ℝ) := by norm_num
  have hNatInt : ((((N + 1 : ℕ) : ℤ) : ℝ)) = ((N + 1 : ℕ) : ℝ) := by norm_num
  change (N + 1 : ℝ) * (y⁻¹ ^ (2 : ℕ) *
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
    y⁻¹ ^ (2 : ℕ) * ∫ x in (0 : ℝ)..(N + 1 : ℝ),
      ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)
  calc
    (N + 1 : ℝ) * (y⁻¹ ^ (2 : ℕ) *
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
        ((N + 1 : ℕ) : ℝ) * (y⁻¹ ^ (2 : ℕ) *
          ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
            ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) := by
          rw [hlength]
    _ = y⁻¹ ^ (2 : ℕ) * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
          rw [hlevel', zsmul_eq_mul, hNatInt, ← hcenter]
          ring
    _ = y⁻¹ ^ (2 : ℕ) * ∫ x in (0 : ℝ)..(N + 1 : ℝ),
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
          rw [hlength]

theorem level_hypGradY_slice_weighted_integrable {N : ℕ}
    (F : cuspidalFormPreDomain N) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun y : ℝ => y⁻¹ ^ (2 : ℕ) *
      ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ))
      (Ioi Y) volume := by
  have hcenter := centered_hypGradY_slice_weighted_integrable F hY
  refine IntegrableOn.congr_fun (hcenter.const_mul (N + 1 : ℝ)) ?_ measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hY |>.trans hy
  have hperiodic : Function.Periodic
      (fun x : ℝ => ‖hypGradY (F : ℍ → DeckSpace N)
        (ofComplex (point x y))‖ ^ (2 : ℕ)) 1 := by
    intro x
    exact hypGradY_normSq_one_periodic
      (cuspidalFormPreDomain.toFormPreDomain N F) hy0 x
  have hshift := hperiodic.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  have hlevel := hypGradY_normSq_interval_level_period
    (cuspidalFormPreDomain.toFormPreDomain N F) hy0 0
  have hlevel' :
      (∫ x in (0 : ℝ)..(N + 1 : ℕ),
        ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
        ((N + 1 : ℕ) : ℤ) • ∫ x in (0 : ℝ)..1,
          ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
    simpa only [zero_add, cuspidalFormPreDomain.coe_toFormPreDomain] using hlevel
  have hcenter :
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
        ∫ x in (0 : ℝ)..1,
          ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
    calc
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
          ∫ x in (-(1 / 2 : ℝ))..(-(1 / 2 : ℝ) + 1),
            ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
              congr 1
              ring
      _ = ∫ x in (0 : ℝ)..0 + 1,
            ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := hshift
      _ = ∫ x in (0 : ℝ)..1,
            ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by ring
  have hlength : ((N + 1 : ℕ) : ℝ) = (N + 1 : ℝ) := by norm_num
  have hNatInt : ((((N + 1 : ℕ) : ℤ) : ℝ)) = ((N + 1 : ℕ) : ℝ) := by norm_num
  change (N + 1 : ℝ) * (y⁻¹ ^ (2 : ℕ) *
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
    y⁻¹ ^ (2 : ℕ) * ∫ x in (0 : ℝ)..(N + 1 : ℝ),
      ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)
  calc
    (N + 1 : ℝ) * (y⁻¹ ^ (2 : ℕ) *
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) =
        ((N + 1 : ℕ) : ℝ) * (y⁻¹ ^ (2 : ℕ) *
          ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
            ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ)) := by
          rw [hlength]
    _ = y⁻¹ ^ (2 : ℕ) * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
          ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
          rw [hlevel', zsmul_eq_mul, hNatInt, ← hcenter]
          ring
    _ = y⁻¹ ^ (2 : ℕ) * ∫ x in (0 : ℝ)..(N + 1 : ℝ),
          ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ (2 : ℕ) := by
          rw [hlength]

theorem cusp_normSq_tail_eq_iterated {N : ℕ}
    (G : ℍ → DeckSpace N) (hcont : Continuous G) (hG : MemLp G 2 cellMeasure)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ z in fd ∩ {z : ℍ | Y < z.im}, ‖G z‖ ^ (2 : ℕ)) =
      ∫ y in Ioi Y, y⁻¹ ^ (2 : ℕ) *
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          ‖G (ofComplex (point x y))‖ ^ (2 : ℕ) := by
  have hfd : IntegrableOn (fun z => ‖G z‖ ^ (2 : ℕ)) fd volume :=
    normSq_integrableOn_fd G hcont hG
  have htail : IntegrableOn (fun z => ‖G z‖ ^ (2 : ℕ))
      (fd ∩ {z : ℍ | Y < z.im}) volume :=
    hfd.mono_set inter_subset_left
  have htailC : IntegrableOn (fun z : ℍ => ((‖G z‖ ^ (2 : ℕ) : ℝ) : ℂ))
      (fd ∩ {z : ℍ | Y < z.im}) volume := htail.ofReal
  have hleftC : IntegrableOn
      (fun z : ℍ => ((‖G (ofComplex (point z.re z.im))‖ ^ (2 : ℕ) : ℝ) : ℂ))
      (fd ∩ {z : ℍ | Y < z.im}) volume := by
    refine htailC.congr_fun ?_ (RHTower.measurableSet_fd_inter_above Y)
    intro z _
    change ((‖G z‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      ((‖G (ofComplex (point z.re z.im))‖ ^ (2 : ℕ) : ℝ) : ℂ)
    rw [ofComplex_point_re_im]
  have hprod : IntegrableOn (fun p : ℝ × ℝ =>
      ‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ)) (RHTower.cuspRect Y) volume :=
    weighted_normSq_product_integrable G hcont hG hY
  have hprodC : IntegrableOn (fun p : ℝ × ℝ =>
      ((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) : ℝ) : ℂ) /
        ((p.2 : ℝ) : ℂ) ^ (2 : ℕ)) (RHTower.cuspRect Y) volume := by
    have hprodC' : IntegrableOn (fun p : ℝ × ℝ =>
        ((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ) : ℝ) : ℂ))
        (RHTower.cuspRect Y) volume := hprod.ofReal
    refine hprodC'.congr_fun ?_ (RHTower.measurableSet_cuspRect Y)
    intro p hp
    have hp2 : p.2 ≠ 0 := (RHTower.cuspRect_pos (by linarith) hp).ne'
    push_cast
    field_simp
  have hchart := RHTower.setIntegral_fd_above_eq hY
    (fun p : ℝ × ℝ => ((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) : ℝ) : ℂ))
  have hcoord :
      (∫ z in fd ∩ {z : ℍ | Y < z.im}, ‖G z‖ ^ (2 : ℕ)) =
        ∫ p in RHTower.cuspRect Y,
          ‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ) := by
    calc
      (∫ z in fd ∩ {z : ℍ | Y < z.im}, ‖G z‖ ^ (2 : ℕ))
          = ∫ z in fd ∩ {z : ℍ | Y < z.im},
              RCLike.re ((‖G (ofComplex (point z.re z.im))‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
              apply setIntegral_congr_fun (RHTower.measurableSet_fd_inter_above Y)
              intro z _
              change ‖G z‖ ^ (2 : ℕ) =
                RCLike.re ((‖G (ofComplex (point z.re z.im))‖ ^ (2 : ℕ) : ℝ) : ℂ)
              rw [ofComplex_point_re_im]
              rfl
      _ = RCLike.re (∫ z in fd ∩ {z : ℍ | Y < z.im},
              ((‖G (ofComplex (point z.re z.im))‖ ^ (2 : ℕ) : ℝ) : ℂ)) :=
            integral_re hleftC
      _ = RCLike.re (∫ p in RHTower.cuspRect Y,
              ((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) : ℝ) : ℂ) /
                ((p.2 : ℝ) : ℂ) ^ (2 : ℕ)) := congrArg RCLike.re hchart
      _ = ∫ p in RHTower.cuspRect Y,
          RCLike.re (((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) : ℝ) : ℂ) /
            ((p.2 : ℝ) : ℂ) ^ (2 : ℕ)) := (integral_re hprodC).symm
      _ = ∫ p in RHTower.cuspRect Y,
          ‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ) := by
            apply setIntegral_congr_fun (RHTower.measurableSet_cuspRect Y)
            intro p hp
            have hp2 : p.2 ≠ 0 := (RHTower.cuspRect_pos (by linarith) hp).ne'
            have hdiv :
                ((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) : ℝ) : ℂ) /
                    ((p.2 : ℝ) : ℂ) ^ (2 : ℕ) =
                  ((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ) : ℝ) : ℂ) := by
              push_cast
              field_simp
            change RCLike.re (((‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) : ℝ) : ℂ) /
                ((p.2 : ℝ) : ℂ) ^ (2 : ℕ)) =
              ‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ)
            rw [hdiv]
            rfl
  calc
      (∫ z in fd ∩ {z : ℍ | Y < z.im}, ‖G z‖ ^ (2 : ℕ))
          = ∫ p in RHTower.cuspRect Y,
              ‖G (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ) := hcoord
      _ = ∫ y in Ioi Y, ∫ x in RHTower.unitIcc,
          ‖G (ofComplex (point x y))‖ ^ (2 : ℕ) / y ^ (2 : ℕ) :=
            RHTower.setIntegral_prod_unitIcc hprod
      _ = ∫ y in Ioi Y, y⁻¹ ^ (2 : ℕ) *
          ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
            ‖G (ofComplex (point x y))‖ ^ (2 : ℕ) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y _
            exact centered_setIntegral_div_eq_interval
              (fun x => ‖G (ofComplex (point x y))‖ ^ (2 : ℕ)) y


private theorem cusp_weight_comparison {Y y C M E : ℝ} (hY : 1 ≤ Y) (hy : Y < y)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hslice : M ≤ C * y⁻¹ ^ (2 : ℕ) * E) :
    y⁻¹ ^ (2 : ℕ) * M ≤ C * Y⁻¹ ^ (2 : ℕ) * (y⁻¹ ^ (2 : ℕ) * E) := by
  have hY0 : 0 < Y := by linarith
  have hy0 : 0 < y := by linarith
  have hinv : y⁻¹ ≤ Y⁻¹ := by
    exact (inv_le_inv₀ hy0 hY0).mpr (le_of_lt hy)
  have hweight : y⁻¹ ^ (2 : ℕ) ≤ Y⁻¹ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hinv 2
  have hfactor : 0 ≤ C * y⁻¹ ^ (2 : ℕ) * E := by positivity
  calc
    y⁻¹ ^ (2 : ℕ) * M ≤ y⁻¹ ^ (2 : ℕ) * (C * y⁻¹ ^ (2 : ℕ) * E) :=
      mul_le_mul_of_nonneg_left hslice (by positivity)
    _ = (C * y⁻¹ ^ (2 : ℕ) * E) * y⁻¹ ^ (2 : ℕ) := by ring
    _ ≤ (C * y⁻¹ ^ (2 : ℕ) * E) * Y⁻¹ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hweight hfactor
    _ = C * Y⁻¹ ^ (2 : ℕ) * (y⁻¹ ^ (2 : ℕ) * E) := by ring

/-- Above any height `Y ≥ 1`, finite-deck cuspidal mass is controlled by horizontal energy
with the sharp geometric cusp factor `Y⁻²`. -/
theorem cusp_tail_mass_le_horizontal_energy {N : ℕ} (F : cuspidalFormPreDomain N)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ z in fd ∩ {z : ℍ | Y < z.im}, ‖(F : ℍ → DeckSpace N) z‖ ^ (2 : ℕ)) ≤
      (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * Y⁻¹ ^ (2 : ℕ) *
        ∫ z in fd ∩ {z : ℍ | Y < z.im},
          ‖hypGradX (F : ℍ → DeckSpace N) z‖ ^ (2 : ℕ) := by
  let C : ℝ := ((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)
  let V : ℝ × ℝ → ℝ := fun p =>
    ‖(F : ℍ → DeckSpace N) (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ)
  let E : ℝ × ℝ → ℝ := fun p =>
    ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point p.1 p.2))‖ ^ (2 : ℕ)
  have hVprod : IntegrableOn (fun p : ℝ × ℝ => V p / p.2 ^ (2 : ℕ))
      (RHTower.unitIcc ×ˢ Ioi Y) volume := by
    simpa only [V, RHTower.cuspRect] using cusp_value_weighted_integrable F hY
  have hEprod : IntegrableOn (fun p : ℝ × ℝ => E p / p.2 ^ (2 : ℕ))
      (RHTower.unitIcc ×ˢ Ioi Y) volume := by
    simpa only [E, RHTower.cuspRect] using cusp_hypGradX_weighted_integrable F hY
  have hVraw : IntegrableOn (fun y : ℝ => ∫ x in RHTower.unitIcc, V (x, y) / y ^ (2 : ℕ))
      (Ioi Y) volume := RHTower.integrableOn_slice_of_prod_unitIcc hVprod
  have hEraw : IntegrableOn (fun y : ℝ => ∫ x in RHTower.unitIcc, E (x, y) / y ^ (2 : ℕ))
      (Ioi Y) volume := RHTower.integrableOn_slice_of_prod_unitIcc hEprod
  have hV : IntegrableOn (fun y : ℝ => y⁻¹ ^ (2 : ℕ) *
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), V (x, y)) (Ioi Y) volume := by
    refine hVraw.congr_fun ?_ measurableSet_Ioi
    intro y hy
    exact centered_setIntegral_div_eq_interval (fun x => V (x, y)) y
  have hE : IntegrableOn (fun y : ℝ => y⁻¹ ^ (2 : ℕ) *
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), E (x, y)) (Ioi Y) volume := by
    refine hEraw.congr_fun ?_ measurableSet_Ioi
    intro y hy
    exact centered_setIntegral_div_eq_interval (fun x => E (x, y)) y
  have hCE : IntegrableOn (fun y : ℝ => C * Y⁻¹ ^ (2 : ℕ) *
      (y⁻¹ ^ (2 : ℕ) * ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), E (x, y)))
      (Ioi Y) volume := by
    exact hE.const_mul (C * Y⁻¹ ^ (2 : ℕ))
  have hC : 0 ≤ C := sq_nonneg _
  have hmass := cusp_normSq_tail_eq_iterated (F : ℍ → DeckSpace N)
    (continuous_of_isChartC1 (cuspidalFormPreDomain.c1 F))
    (cuspidalFormPreDomain.memLp F) hY
  have henergy := cusp_normSq_tail_eq_iterated (hypGradX (F : ℍ → DeckSpace N))
    (continuous_hypGradX_vec (cuspidalFormPreDomain.c1 F))
    (cuspidalFormPreDomain.memLp_gradX F) hY
  calc
    (∫ z in fd ∩ {z : ℍ | Y < z.im}, ‖(F : ℍ → DeckSpace N) z‖ ^ (2 : ℕ))
      = ∫ y in Ioi Y, y⁻¹ ^ (2 : ℕ) *
          ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), V (x, y) := by
            simpa only [V] using hmass
    _ ≤ ∫ y in Ioi Y, C * Y⁻¹ ^ (2 : ℕ) *
          (y⁻¹ ^ (2 : ℕ) * ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), E (x, y)) := by
            refine setIntegral_mono_on hV hCE measurableSet_Ioi ?_
            intro y hy
            have hE0 : 0 ≤ ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), E (x, y) := by
              apply intervalIntegral.integral_nonneg (by norm_num)
              intro x hx
              exact sq_nonneg _
            have hy' : Y < y := hy
            have hslice := centered_cusp_slice_poincare F (by linarith)
            exact cusp_weight_comparison hY hy' hC hE0
              (by simpa only [C, V, E] using hslice)
    _ = C * Y⁻¹ ^ (2 : ℕ) *
        ∫ y in Ioi Y, y⁻¹ ^ (2 : ℕ) *
          ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), E (x, y) := by
          rw [MeasureTheory.integral_const_mul]
    _ = C * Y⁻¹ ^ (2 : ℕ) *
        ∫ z in fd ∩ {z : ℍ | Y < z.im},
          ‖hypGradX (F : ℍ → DeckSpace N) z‖ ^ (2 : ℕ) := by
          rw [← henergy]
    _ = (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * Y⁻¹ ^ (2 : ℕ) *
        ∫ z in fd ∩ {z : ℍ | Y < z.im},
          ‖hypGradX (F : ℍ → DeckSpace N) z‖ ^ (2 : ℕ) := by rfl


noncomputable section

def cuspTailCutoff (Y : ℝ) (z : ℍ) : ℂ :=
  Set.indicator {z : ℍ | Y < z.im} (fun _ => 1) z

theorem measurable_cuspTailCutoff (Y : ℝ) : Measurable (cuspTailCutoff Y) := by
  exact Measurable.indicator measurable_const
    (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable)

theorem norm_cuspTailCutoff_le_one (Y : ℝ) (z : ℍ) : ‖cuspTailCutoff Y z‖ ≤ 1 := by
  by_cases hz : Y < z.im <;> simp [cuspTailCutoff, hz]

def cuspTailProjection (N : ℕ) (Y : ℝ) : DeckL2 N →L[ℂ] DeckL2 N :=
  MeasureTheory.lpBoundedSmulCLM (p := 2) (μ := cellMeasure) (H := DeckSpace N)
    (measurable_cuspTailCutoff Y) (by positivity) (norm_cuspTailCutoff_le_one Y)

theorem normSq_cuspTailProjection_toDeckL2 {N : ℕ} (Y : ℝ)
    (F : ℍ → DeckSpace N) (hF : MemLp F 2 cellMeasure) :
    ‖cuspTailProjection N Y (toDeckL2 F hF)‖ ^ (2 : ℕ) =
      ∫ z in fd ∩ {z : ℍ | Y < z.im}, ‖F z‖ ^ (2 : ℕ) := by
  rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  have hproj :
      ((cuspTailProjection N Y (toDeckL2 F hF) : DeckL2 N) : ℍ → DeckSpace N) =ᵐ[cellMeasure]
        fun z => cuspTailCutoff Y z • ((toDeckL2 F hF : DeckL2 N) : ℍ → DeckSpace N) z := by
    exact MeasureTheory.lpBoundedSmulCLM_coeFn (p := 2) (μ := cellMeasure)
      (H := DeckSpace N) (measurable_cuspTailCutoff Y) (by positivity)
        (norm_cuspTailCutoff_le_one Y) (toDeckL2 F hF)
  have hFae := MemLp.coeFn_toLp hF
  calc
    (∫ z, ‖(cuspTailProjection N Y (toDeckL2 F hF) : ℍ → DeckSpace N) z‖ ^ (2 : ℕ)
        ∂cellMeasure) =
        ∫ z, ‖cuspTailCutoff Y z • F z‖ ^ (2 : ℕ) ∂cellMeasure := by
          apply integral_congr_ae
          filter_upwards [hproj, hFae] with z hp hFz
          rw [hp]
          change ‖cuspTailCutoff Y z • (MemLp.toLp F hF : ℍ → DeckSpace N) z‖ ^ (2 : ℕ) = _
          rw [hFz]
    _ = ∫ z in fd, ‖cuspTailCutoff Y z • F z‖ ^ (2 : ℕ) := by rfl
    _ = ∫ z in fd, {z : ℍ | Y < z.im}.indicator (fun z => ‖F z‖ ^ (2 : ℕ)) z := by
          apply setIntegral_congr_fun isClosed_fd.measurableSet
          intro z hz
          by_cases htail : Y < z.im <;> simp [cuspTailCutoff, htail]
    _ = ∫ z in fd ∩ {z : ℍ | Y < z.im}, ‖F z‖ ^ (2 : ℕ) := by
          rw [MeasureTheory.setIntegral_indicator]
          exact measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable


/-- The cusp-tail Poincaré estimate survives the finite-deck cuspidal form completion. -/
theorem cuspidalFormDomain_tail_projection_bound {N : ℕ} {Y : ℝ} (hY : 1 ≤ Y)
    (v : CuspidalFormDomain N) :
    ‖cuspTailProjection N Y ((v : FormTriple N).ofLp 0)‖ ^ (2 : ℕ) ≤
      (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * Y⁻¹ ^ (2 : ℕ) *
        ‖cuspTailProjection N Y ((v : FormTriple N).ofLp 1)‖ ^ (2 : ℕ) := by
  let K : ℝ := ((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ) * Y⁻¹ ^ (2 : ℕ)
  let PX : FormTriple N →L[ℂ] DeckL2 N :=
    (cuspTailProjection N Y).comp (PiLp.proj 2 (fun _ : Fin 3 => DeckL2 N) 0)
  let PG : FormTriple N →L[ℂ] DeckL2 N :=
    (cuspTailProjection N Y).comp (PiLp.proj 2 (fun _ : Fin 3 => DeckL2 N) 1)
  have hclosed : IsClosed {w : FormTriple N | ‖PX w‖ ^ (2 : ℕ) ≤ K * ‖PG w‖ ^ (2 : ℕ)} := by
    apply isClosed_le
    · exact (PX.continuous.norm).pow 2
    · exact continuous_const.mul ((PG.continuous.norm).pow 2)
  have hrange : ((LinearMap.range (cuspidalFormEmbeddingMap N) : Submodule ℂ (FormTriple N)) :
      Set (FormTriple N)) ⊆ {w : FormTriple N | ‖PX w‖ ^ (2 : ℕ) ≤ K * ‖PG w‖ ^ (2 : ℕ)} := by
    rintro w ⟨F, rfl⟩
    change ‖cuspTailProjection N Y (toDeckL2 (F : ℍ → DeckSpace N)
      (cuspidalFormPreDomain.memLp F))‖ ^ (2 : ℕ) ≤ K *
      ‖cuspTailProjection N Y (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
        (cuspidalFormPreDomain.memLp_gradX F))‖ ^ (2 : ℕ)
    rw [normSq_cuspTailProjection_toDeckL2,
      normSq_cuspTailProjection_toDeckL2]
    exact cusp_tail_mass_le_horizontal_energy F hY
  have hclosure : (cuspidalFormDomainClosure N : Set (FormTriple N)) ⊆
      {w : FormTriple N | ‖PX w‖ ^ (2 : ℕ) ≤ K * ‖PG w‖ ^ (2 : ℕ)} := by
    change closure ((LinearMap.range (cuspidalFormEmbeddingMap N) : Submodule ℂ (FormTriple N)) :
      Set (FormTriple N)) ⊆ _
    exact hclosed.closure_subset_iff.mpr hrange
  have hv := hclosure v.property
  exact hv

end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
