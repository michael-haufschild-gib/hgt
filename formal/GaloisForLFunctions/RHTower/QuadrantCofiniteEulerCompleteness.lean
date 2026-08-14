import GaloisForLFunctions.RHTower.WeightedEulerCarrierVanishing
import GaloisForLFunctions.RHTower.CompactCarrierPolynomialDetection
import GaloisForLFunctions.HTGeometry.CarrierAnnihilatesHolomorphicPompeiu
import GaloisForLFunctions.HTGeometry.LocallyConvexDenseOfVanishingDual

/-!
# Cofinite real completeness of the symmetrised Euler tangents on the critical quadrant

Deleting finitely many primes costs nothing.  Once the annihilation of the symmetrised tangents is
assumed only past a prime-logarithm threshold, the sector–Blaschke argument on the rectangular total
carrier still forces the total functional to kill every power of the coordinate, and the two gluings
across the critical line and the real axis then kill the carrier functional itself.

The functional here is real-linear and only the *real* values of the tangents are annihilated: the
Schwarz reflection supplies the missing imaginary half.  So this is real-span density in the
underlying real space of the quadrant's holomorphic functions.

* `RHTower.QuadrantCarrierData.total_coord_pow_eq_zero_cofinite`;
* `RHTower.holoQuadrant_eq_zero_of_annihilates_feEulerTangent`;
* `RHTower.topologicalClosure_span_eulerTangentElement_eq_top`.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

namespace QuadrantCarrierData

variable {f₂ : holoQuadrant →L[ℝ] ℝ} (D : QuadrantCarrierData f₂)

theorem abs_im_le_rad {z : ℂ} (hz : z ∈ D.Ktot) : |z.im| ≤ D.rad :=
  le_trans (Complex.abs_im_le_norm z) (D.norm_le_rad hz)

/-- **The total functional kills every power of the coordinate under cofinite annihilation.** -/
theorem total_coord_pow_eq_zero_cofinite (S : Finset Nat.Primes)
    (hann : ∀ p : Nat.Primes, p ∉ S → f₂ (eulerTangentElement p) = 0) (m : ℕ) :
    D.total (coordMap D.Ktot ^ m) = 0 := by
  classical
  haveI : Nonempty D.Ktot := ⟨⟨_, D.mem_Ktot_corner⟩⟩
  have hre : ∀ z ∈ D.Ktot, (1 - D.b) ≤ z.re := fun z hz => (D.Ktot_re hz).1
  set Bsum : ℝ := ∑ q ∈ S, Real.log ((q : Nat.Primes) : ℝ) with hBsum
  have hBsum0 : 0 ≤ Bsum := by
    rw [hBsum]
    positivity
  set R₀ : ℝ := 1 + Bsum with hR₀def
  have hR₀ : 0 < R₀ := by rw [hR₀def]; linarith
  have hannBig : ∀ p : Nat.Primes, R₀ + 1 < Real.log ((p : ℕ) : ℝ) →
      D.total (compactPrimeEulerUnitTangent (coordMap D.Ktot) (p : ℕ)) = 0 := by
    intro p hp
    have hpnot : p ∉ S := by
      intro hpS
      have hlognonneg : ∀ q ∈ S, 0 ≤ Real.log ((q : Nat.Primes) : ℝ) := by
        intro q _
        exact Real.log_nonneg (by exact_mod_cast q.prop.one_lt.le)
      have hle : Real.log ((p : Nat.Primes) : ℝ) ≤ Bsum := by
        rw [hBsum]
        exact Finset.single_le_sum hlognonneg hpS
      rw [hR₀def] at hp
      have hcast : Real.log ((p : ℕ) : ℝ) = Real.log ((p : Nat.Primes) : ℝ) := rfl
      rw [hcast] at hp
      linarith
    have hval : ∀ z : D.Ktot,
        compactPrimeEulerUnitTangent (coordMap D.Ktot) (p : ℕ) z = eulerTangent (p : ℕ) (z : ℂ) := by
      intro z
      rw [compactPrimeEulerUnitTangent_coordMap D.one_sub_b_pos hre p.2.two_le z]
      rfl
    rw [D.total_feTangent p _ hval, hann p hpnot]
    norm_num
  have hF := compactFourierBorel_eq_zero_of_tangent_annihilation_rightRectangle
    D.total (coordMap D.Ktot) (1 - D.b) D.rad R₀ D.one_sub_b_pos hR₀
    (fun k => hre (k : ℂ) k.2) (fun k => D.abs_im_le_rad k.2) hannBig
  exact map_coordinate_pow_eq_zero_of_fourierBorel_zero D.total (coordMap D.Ktot) hF m

/-- **The transform of the total functional vanishes on the separating vertical strip.** -/
theorem cauchyTransform_total_eq_zero_on_strip_cofinite (S : Finset Nat.Primes)
    (hann : ∀ p : Nat.Primes, p ∉ S → f₂ (eulerTangentElement p) = 0)
    {v : ℂ} (h1 : 1 - D.a < v.re) (h2 : v.re < D.a) :
    functionalCauchyTransform D.total v = 0 := by
  have hfar : ∀ w : ℂ, D.rad < ‖w‖ → functionalCauchyTransform D.total w = 0 := fun w hw =>
    cauchyTransform_eq_zero_of_lt D.total (fun m => D.total_coord_pow_eq_zero_cofinite S hann m)
      D.rad_nonneg (fun z hz => D.norm_le_rad hz) hw
  have hopenfar : IsOpen {w : ℂ | D.rad < ‖w‖} := isOpen_lt continuous_const continuous_norm
  set v₀ : ℂ := ((1 / 2 : ℝ) : ℂ) + ((D.rad + 1 : ℝ) : ℂ) * Complex.I with hv₀
  have hv₀re : v₀.re = 1 / 2 := by rw [hv₀]; simp
  have hv₀im : v₀.im = D.rad + 1 := by rw [hv₀]; simp
  have hv₀far : D.rad < ‖v₀‖ := by
    have h := Complex.abs_im_le_norm v₀
    rw [hv₀im, abs_of_nonneg (by linarith [D.rad_nonneg])] at h
    linarith
  have hv₀strip : v₀ ∈ {w : ℂ | 1 - D.a < w.re ∧ w.re < D.a} := by
    rw [Set.mem_setOf_eq, hv₀re]
    exact ⟨by linarith [D.ha], D.ha⟩
  have hanal : AnalyticOnNhd ℂ (functionalCauchyTransform D.total)
      {w : ℂ | 1 - D.a < w.re ∧ w.re < D.a} :=
    (analyticOnNhd_functionalCauchyTransform D.isCompact_Ktot D.total).mono D.vertStrip_subset
  have hpre : IsPreconnected {w : ℂ | 1 - D.a < w.re ∧ w.re < D.a} :=
    ((convex_halfSpace_re_gt (1 - D.a)).inter (convex_halfSpace_re_lt D.a)).isPreconnected
  have hev : functionalCauchyTransform D.total =ᶠ[nhds v₀] 0 := by
    filter_upwards [hopenfar.mem_nhds hv₀far] with w hw
    exact hfar w hw
  exact hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hv₀strip hev ⟨h1, h2⟩

/-- **The transform of the doubled functional vanishes off the right pair of blocks.** -/
theorem cauchyTransform_doubled_eq_zero_cofinite (S : Finset Nat.Primes)
    (hann : ∀ p : Nat.Primes, p ∉ S → f₂ (eulerTangentElement p) = 0) :
    ∀ v ∉ D.Kt, functionalCauchyTransform D.doubled v = 0 := by
  refine cauchyTransform_eq_zero_of_glue_re (Kc' := D.Kt') D.isCompact_Kt
    (c₁ := 1 - D.a) (c₂ := D.a) (R := D.rad) D.one_sub_a_lt_a
    (fun z hz => D.Kt_re hz) (fun z hz => D.Kt'_re hz)
    (fun z hz => D.norm_le_rad (D.Kt_subset_Ktot hz))
    (fun z hz => D.norm_le_rad (D.Kt'_subset_Ktot hz))
    D.doubled (-D.reflected) ?_ (isPreconnected_compl_doubledRect D.hc D.hcd)
  intro v h1 h2
  have hv : v ∉ D.Ktot := D.vertStrip_subset ⟨h1, h2⟩
  have hvt' : v ∉ D.Kt' := fun hc => hv (D.Kt'_subset_Ktot hc)
  have hT := D.cauchyTransform_total hv
  have hR := D.cauchyTransform_reflected hvt'
  have hz := D.cauchyTransform_total_eq_zero_on_strip_cofinite S hann h1 h2
  rw [hT] at hz
  rw [cauchyTransform_neg, hR]
  linear_combination hz

/-- **The transform of the carrier functional vanishes off its carrier.** -/
theorem cauchyTransform_Lc_eq_zero_cofinite (S : Finset Nat.Primes)
    (hann : ∀ p : Nat.Primes, p ∉ S → f₂ (eulerTangentElement p) = 0) :
    ∀ v ∉ D.Kc, functionalCauchyTransform D.Lc v = 0 := by
  refine cauchyTransform_eq_zero_of_glue (Kc' := D.Kcbar) D.isCompact_Kc
    (c := D.c) (R := D.rad) D.hc
    (fun z hz => D.Kc_im hz) (fun z hz => D.Kcbar_im hz)
    (fun z hz => D.norm_le_rad (D.Kt_subset_Ktot (D.Kc_subset_Kt hz)))
    (fun z hz => D.norm_le_rad (D.Kt_subset_Ktot (D.Kcbar_subset_Kt hz)))
    D.Lc (conjFunctional (fun _ hz => D.conj_mem_Kc hz) D.Lc) ?_
    (isPreconnected_compl_rect D.a D.b D.c D.d)
  intro v h1 h2
  have hvKt : v ∉ D.Kt := midStrip_subset_compl_doubledRect ⟨h1, h2⟩
  have hvKcbar : v ∉ D.Kcbar := fun hc => hvKt (D.Kcbar_subset_Kt hc)
  have hd := D.cauchyTransform_doubled hvKt
  have hc := cauchyTransform_conjFunctional (fun _ hz => D.conj_mem_Kc hz) D.Lc hvKcbar
  have hzero := D.cauchyTransform_doubled_eq_zero_cofinite S hann v hvKt
  rw [hd] at hzero
  rw [hc]
  linear_combination hzero

end QuadrantCarrierData

/-- **Cofinite real annihilation of the symmetrised Euler tangents kills every continuous real
functional on the quadrant's holomorphic space.** -/
theorem holoQuadrant_eq_zero_of_annihilates_feEulerTangent
    (S : Finset Nat.Primes) (f₂ : holoQuadrant →L[ℝ] ℝ)
    (hann : ∀ p : Nat.Primes, p ∉ S → f₂ (eulerTangentElement p) = 0) :
    ∀ y : holoQuadrant, f₂ y = 0 := by
  obtain ⟨D⟩ := exists_quadrantCarrierData f₂
  intro y
  obtain ⟨G, hG, hGy⟩ := y.2
  have hgK : ∀ z : D.Kc, (quadrantRestrict D.hquad y) z = G (z : ℂ) := by
    intro z
    rw [quadrantRestrict_apply]
    exact hGy _
  have hKcQ : D.Kc ⊆ criticalQuadrant := D.hquad
  have hzero := apply_eq_zero_of_cauchyTransform_eq_zero_of_isOpen (K := D.Kc)
    D.isCompact_Kc isOpen_criticalQuadrant hKcQ hG D.Lc
    (D.cauchyTransform_Lc_eq_zero_cofinite S hann) (quadrantRestrict D.hquad y) hgK
  rw [← D.hL y]
  rw [show D.L (quadrantRestrict D.hquad y) = D.Lc (quadrantRestrict D.hquad y) from rfl, hzero]
  simp

/-- **The cofinite symmetrised Euler tangents have dense real span in the quadrant's holomorphic
space.** -/
theorem topologicalClosure_span_eulerTangentElement_eq_top (S : Finset Nat.Primes) :
    (Submodule.span ℝ
      (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
        eulerTangentElement (p : Nat.Primes))).topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs
    (E := holoQuadrant) (Submodule.span ℝ
      (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
        eulerTangentElement (p : Nat.Primes))) ?_
  intro f₂ hf₂
  refine ContinuousLinearMap.ext
    (holoQuadrant_eq_zero_of_annihilates_feEulerTangent S f₂ fun p hp => ?_)
  exact hf₂ _ (Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩)

end RHTower
