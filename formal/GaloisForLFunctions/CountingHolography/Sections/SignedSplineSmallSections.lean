import GaloisForLFunctions.CountingHolography.Sections.DegreePointSectionLattice
import GaloisForLFunctions.CountingHolography.TheTateLimitOfACount

/-!
# Small sections on signed integer spline rays

At every integer vector the contact valuations specify a fractional ideal in ℚ.
The archimedean ball uses the counterterm, the jets and both pole degrees on the
same mesh. The normalized degree is the signed Weil form. The logarithmic
number of small sections sees its positive part; the dual sees the deficit.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset MeasureTheory AbsoluteGeometryOfSpecZ ArithmeticScatteringHolography
open ArithmeticCastelnuovoSeveri BiScaleUncertainty.ChebyshevGauge Zeta23
open scoped ArithmeticFunction.vonMangoldt ComplexConjugate

/-- Integer probe before the common translation into the degree window. -/
def splineSource {N : ℕ} (a : Fin N → ℤ) (u : ℝ) : ℝ :=
  ∑ i, (a i : ℝ) * cubicSpline (u - Real.log ((i : ℝ) + 1))

private def shift : ℝ := Real.log 3 + 5

def windowEnd (N : ℕ) : ℕ := ⌈Real.exp (shift + Real.log (N+1 : ℝ) + 5)⌉₊

/-- All atoms use one shift, independent of the coefficients. -/
def packet {N : ℕ} (a : Fin N → ℤ) (u : ℝ) := splineSource a (u - shift)

private theorem packet_window {N : ℕ} (a : Fin N → ℤ) :
    1 ≤ windowEnd N ∧ ∀ u, u ≤ Real.log 3 ∨ Real.log (windowEnd N) ≤ u → packet a u = 0 := by
  have hK : 0 < windowEnd N := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hlog : shift + Real.log (N+1 : ℝ) + 5 ≤ Real.log (windowEnd N) :=
    (Real.le_log_iff_exp_le (by exact_mod_cast hK)).mpr (Nat.le_ceil _)
  refine ⟨hK, fun u hu => sum_eq_zero fun i _ => ?_⟩
  apply mul_eq_zero_of_right
  apply cubicSpline_eq_zero
  rcases hu with hl | hr
  · have hi : 0 ≤ Real.log ((i : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) i.val])
    have := neg_le_abs (u - shift - Real.log ((i : ℝ) + 1))
    dsimp [shift] at *
    linarith
  · have hi : Real.log ((i : ℝ) + 1) ≤ Real.log (N+1 : ℝ) :=
      Real.log_le_log (by positivity) (by have := i.isLt.le; exact_mod_cast Nat.add_le_add_right this 1)
    linarith only [le_abs_self (u - shift - Real.log ((i : ℝ) + 1)), hr, hi, hlog]

private theorem source_smooth {N : ℕ} (a : Fin N → ℤ) : ContDiff ℝ 2 (splineSource a) :=
  ContDiff.sum fun _ _ => contDiff_const.mul (contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const))

private theorem source_compact {N : ℕ} (a : Fin N → ℤ) : HasCompactSupport (splineSource a) := by
  let F := fun (i : Fin N) (u : ℝ) => (a i : ℝ) * cubicSpline (u - Real.log ((i : ℝ) + 1))
  have hs (i : Fin N) : HasCompactSupport (F i) :=
    (hasCompactSupport_cubicSpline.comp_homeomorph (Homeomorph.subRight (Real.log ((i : ℝ) + 1)))).mul_left
  simpa only [splineSource, F, Finset.sum_apply] using
    (HasCompactSupport.finset_sum (s := Finset.univ) fun i _ => hs i)


theorem integerProbe_eq_source {N : ℕ} (a : Fin N → ℤ) :
    integerProbe N a = (_root_.RHTower.weilFullFunctional (fun k => (Λ k : ℝ))
      (EF.weilTest (cx (splineSource a)) (cx (splineSource a)))).re := by
  let F := fun i : Fin N => translate (Real.log ((i : ℝ) + 1)) (cx cubicSpline)
  have he : (∑ i, conj (a i : ℂ) • F i) = cx (splineSource a) := by
    funext u
    simp [F, cx, splineSource, translate, Finset.sum_apply]
  exact (hermQuad_weilGram _ F (fun i => translate_contDiff (cx_contDiff contDiff_cubicSpline) _)
    (fun i => translate_hasCompactSupport (cx_hasCompactSupport hasCompactSupport_cubicSpline) _)
    (fun i => (a i : ℂ))).trans (by rw [he])

theorem tendsto_packetMeshDegree {N : ℕ} (a : Fin N → ℤ) :
    Tendsto (meshDegree (packet a) (3*windowEnd N)) atTop (𝓝 (integerProbe N a)) := by
  have hf : ContDiff ℝ 2 (packet a) := (source_smooth a).comp (contDiff_id.sub contDiff_const)
  have hc : HasCompactSupport (packet a) := (source_compact a).comp_homeomorph (Homeomorph.subRight shift)
  have h := tendsto_meshDegree hf hc (packet_window a).1 (packet_window a).2
  rwa [packet, weilTest_packet_translate, ← integerProbe_eq_source] at h

private theorem packet_smul {N : ℕ} (a : Fin N → ℤ) (m : ℕ) :
    packet (m • a) = fun u => (m : ℝ) * packet a u := by
  funext u
  simp only [packet, splineSource, mul_sum, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast,
    mul_assoc]

/-- Coefficient mass sets the sample resolution. On every nonzero ray it tends to infinity. -/
def resolution {N : ℕ} (a : Fin N → ℤ) : ℕ := ∑ i, (a i).natAbs

private theorem resolution_smul {N : ℕ} (a : Fin N → ℤ) (m : ℕ) :
    resolution (m • a) = m * resolution a := by
  simp [resolution, Pi.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Finset.mul_sum]

private theorem resolution_pos {N : ℕ} {a : Fin N → ℤ} (ha : a ≠ 0) : 0 < resolution a := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by simpa [funext_iff] using ha
  exact (Int.natAbs_pos.mpr hi).trans_le (single_le_sum (fun j _ => Nat.zero_le (a j).natAbs) (mem_univ i))

/-- The positive generator of the finite-place fractional ideal of the divisor. -/
def generator {N : ℕ} (a : Fin N → ℤ) : ℚ := contactGenerator (packet a) (3*windowEnd N) (resolution a)

/-- The archimedean logarithmic radius of the same divisor. -/
def radius {N : ℕ} (a : Fin N → ℤ) : ℝ := logRadius (packet a) (3*windowEnd N) (resolution a)

/-- Natural-valued logarithmic count of actual small sections. -/
def splineCount {N : ℕ} (a : Fin N → ℤ) : ℕ := sectionHeight (generator a : ℝ) (radius a)

private theorem inv_sq_tendsto : Tendsto (fun m : ℕ => ((m : ℝ)^2)⁻¹) atTop (𝓝 0) :=
  ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop

/-- The signed degree of the metrized lattices recovers every mixed term on the original ray. -/
theorem tendsto_splineDegree {N : ℕ} (a : Fin N → ℤ) :
    Tendsto (fun m : ℕ => (radius (m • a) - Real.log (generator (m • a) : ℝ)) / (m : ℝ)^2)
      atTop (𝓝 (integerProbe N a)) := by
  let L := 3*windowEnd N
  let D := fun m : ℕ => meshDegree (packet (m • a)) L (resolution (m • a)) / (m : ℝ)^2
  have hD : Tendsto D atTop (𝓝 (integerProbe N a)) := by
    by_cases ha : a = 0
    · subst a
      have hq : integerProbe N 0 = 0 := by simpa using integerProbe_smul N 0 (0 : Fin N → ℤ)
      have h := (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℕ)))
      simpa [D, packet, splineSource, meshDegree, logRadius, sampledDegree, degreeForm,
        degreeContact, degreePairing, degreeSample, hq] using h
    · have hr := resolution_pos ha
      have hm : Tendsto (fun m : ℕ => resolution (m • a)) atTop atTop := by
        refine tendsto_atTop_mono (f := id) (fun m => ?_) tendsto_id
        rw [resolution_smul]
        exact Nat.le_mul_of_pos_right _ hr
      refine ((tendsto_packetMeshDegree a).comp hm).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with m hm
      simp only [D, Function.comp_apply, packet_smul, meshDegree_mul]
      exact (mul_div_cancel_left₀ _ (by positivity : (m : ℝ)^2 ≠ 0)).symm
  let C : ℝ := ∑ k ∈ Icc 2 L, Λ k
  have hC : Tendsto (fun m : ℕ => C / (m : ℝ)^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using inv_sq_tendsto.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hD (by simpa using hD.add hC)
  · filter_upwards with m
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have h := (contact_rounding_bounds (packet (m • a)) L (resolution (m • a))).1
    dsimp only [meshDegree, radius, generator, L] at *
    linarith
  · filter_upwards with m
    change _ ≤ _ / _ + C / _
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have h := (contact_rounding_bounds (packet (m • a)) L (resolution (m • a))).2
    dsimp only [meshDegree, radius, generator, C, L] at *
    linarith

/-- The Tate limit of a logarithmic section count over ℚ takes the positive
part of the signed degree. This includes rays of degree zero. -/
private theorem tendsto_sectionHeight {d A : ℕ → ℝ} (hd : ∀ m, 0 < d m) {q : ℝ}
    (h : Tendsto (fun m : ℕ => (A m - Real.log (d m)) / (m : ℝ)^2) atTop (𝓝 q)) :
    Tendsto (fun m : ℕ => (sectionHeight (d m) (A m) : ℝ) / (m : ℝ)^2)
      atTop (𝓝 (max q 0)) := by
  have hmax : Tendsto (fun m : ℕ => max (A m - Real.log (d m)) 0 / (m : ℝ)^2)
      atTop (𝓝 (max q 0)) := by
    apply (h.max (tendsto_const_nhds (x := (0:ℝ)))).congr
    intro m
    rw [← max_div_div_right (sq_nonneg _), zero_div]
  have hC (c : ℝ) : Tendsto (fun m : ℕ => c / (m : ℝ)^2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using inv_sq_tendsto.const_mul c
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hmax.sub (hC 1))
    (by simpa using hmax.add (hC (Real.log 3)))
  · filter_upwards with m
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (sectionHeight_bounds (A := A m) (hd m)).1 (sq_nonneg _)
  · filter_upwards with m
    rw [← add_div]
    exact div_le_div_of_nonneg_right (sectionHeight_bounds (A := A m) (hd m)).2 (sq_nonneg _)

theorem splineCount_tateLimit {N : ℕ} (a : Fin N → ℤ) :
    Tendsto (fun m : ℕ => (splineCount (m • a) : ℝ) / (m : ℝ)^2) atTop
      (𝓝 (max (integerProbe N a) 0)) :=
  tendsto_sectionHeight (d := fun m => (generator (m • a) : ℝ)) (A := fun m => radius (m • a))
    (fun m => by exact_mod_cast contactGenerator_pos _ _ _) (tendsto_splineDegree a)

/-- Small sections of the inverse ideal with the reciprocal radius. -/
def dualCount {N : ℕ} (a : Fin N → ℤ) : ℕ :=
  sectionHeight (generator a : ℝ)⁻¹ (-radius a)

theorem dualCount_tateLimit {N : ℕ} (a : Fin N → ℤ) :
    Tendsto (fun m : ℕ => (dualCount (m • a) : ℝ) / (m : ℝ)^2) atTop
      (𝓝 (max (-integerProbe N a) 0)) := by
  refine tendsto_sectionHeight (d := fun m : ℕ => (generator (m • a) : ℝ)⁻¹)
    (A := fun m => -radius (m • a)) (fun m => inv_pos.mpr (by exact_mod_cast
    contactGenerator_pos (packet (m • a)) (3 * windowEnd N) (resolution (m • a)))) ?_
  apply (tendsto_splineDegree a).neg.congr
  intro m
  rw [Real.log_inv]
  ring

/-- The difference of two natural-valued heights realizes the complete signed form. -/
theorem splineCount_sub_dualCount_tateLimit {N : ℕ} (a : Fin N → ℤ) :
    Tendsto (fun m : ℕ => ((splineCount (m • a) : ℝ) - dualCount (m • a)) / (m : ℝ)^2)
      atTop (𝓝 (integerProbe N a)) := by
  have h := (splineCount_tateLimit a).sub (dualCount_tateLimit a)
  rcases le_total 0 (integerProbe N a) with hq | hq
  · simpa only [sub_div, max_eq_left hq, max_eq_right (neg_nonpos.mpr hq), sub_zero] using h
  · simpa only [sub_div, max_eq_right hq, max_eq_left (neg_nonneg.mpr hq), zero_sub, neg_neg] using h

/-- The remaining obstruction is positive quadratic growth of the dual small sections. -/
theorem riemannHypothesis_iff_dualCount_subquadratic :
    RiemannHypothesis ↔ ∀ (N : ℕ) (a : Fin N → ℤ),
      Tendsto (fun m : ℕ => (dualCount (m • a) : ℝ) / (m : ℝ)^2) atTop (𝓝 0) := by
  rw [riemannHypothesis_iff_integerProbes]
  constructor
  · intro h N a
    simpa only [max_eq_right (neg_nonpos.mpr (h N a))] using dualCount_tateLimit a
  · intro h N a
    have he := tendsto_nhds_unique (dualCount_tateLimit a) (h N a)
    have := le_max_left (-integerProbe N a) 0
    linarith

/-- One nonzero section on each ray after every positive quadratic enlargement
of the log radius is enough. The section may depend on the ray and the scale. -/
theorem riemannHypothesis_iff_smallSections_with_slack :
    RiemannHypothesis ↔ ∀ (N : ℕ) (a : Fin N → ℤ) (ε : ℝ), 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∃ z ∈ smallSections (generator (m • a) : ℝ)
        (radius (m • a) + ε * (m : ℝ)^2), z ≠ 0 := by
  rw [riemannHypothesis_iff_integerProbes]
  constructor
  · intro h N a ε hε
    have hl := (tendsto_splineDegree a).eventually_const_lt ((neg_lt_zero.mpr hε).trans_le (h N a))
    filter_upwards [hl, eventually_ge_atTop 1] with m hm hm1
    have hm2 : 0 < (m : ℝ)^2 := by positivity
    have hmul := (lt_div_iff₀ hm2).mp hm
    apply (exists_nonzero_smallSection (by exact_mod_cast contactGenerator_pos _ _ _)).mpr
    linarith only [hmul]
  · intro h N a
    by_contra! hq
    let ε := -(integerProbe N a) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hlt := (tendsto_splineDegree a).eventually_lt_const (show integerProbe N a < -ε by
      dsimp [ε]; linarith)
    obtain ⟨m, hm, hz, hm1⟩ := (hlt.and ((h N a ε hε).and (eventually_ge_atTop 1))).exists
    have hm2 : 0 < (m : ℝ)^2 := by positivity
    have hmul := (div_lt_iff₀ hm2).mp hm
    have hz' := (exists_nonzero_smallSection (by exact_mod_cast contactGenerator_pos _ _ _)).mp hz
    linarith only [hmul, hz']

#print axioms splineCount_sub_dualCount_tateLimit
#print axioms riemannHypothesis_iff_dualCount_subquadratic
#print axioms riemannHypothesis_iff_smallSections_with_slack

end GaloisForLFunctions.CountingHolography.Sections
