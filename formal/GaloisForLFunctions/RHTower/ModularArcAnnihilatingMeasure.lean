import GaloisForLFunctions.RHTower.ModularArcWhittakerPositivity
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Combination

/-!
# A probability measure on the modular bottom arc annihilating every Whittaker mode

Parametrize the bottom arc `{u² + y² = 1, |u| ≤ ½}` of the standard fundamental domain of
`SL₂(ℤ)` by `u ∈ I = [−½, ½]`, `y = √(1 − u²)`.  For `c_n = 2π(n+1)` put

`C_n(u) = K₀(c_n y(u)) cos(c_n u)`,   `S_n(u) = K₀(c_n y(u)) sin(c_n u)`,

the restrictions to the arc of the decaying Whittaker functions `K₀(2π|m|y) e^{2πimu}`, `m ≠ 0`
(up to the positive factor `√y`).

**Theorem** (`exists_probabilityMeasure_arc_annihilating`).  There is a probability measure `μ` on
`I` with `∫ C_n dμ = ∫ S_n dμ = 0` for every `n`.

Proof.
* *Finite stage* (`exists_probabilityMeasure_arc_small`).  If `0` were not in the closed convex hull
  of `{(C_n(u), S_n(u))_{n<N} : u ∈ I}`, the separation theorem would give a linear functional, i.e.
  coefficients `a_n, b_n`, with `Σ a_n C_n + b_n S_n > 0` on the arc.  This contradicts
  `whittakerArc_coeff_eq_zero`.  So convex combinations of point masses make the first `N` moments
  `δ`-small.
* *Limit* (Prokhorov).  `ProbabilityMeasure I` is compact and the moments are weakly continuous, so
  the nested closed nonempty sets `T_k = {|moments_{n<k}| ≤ 1/(k+1)}` have a common point.
-/

open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- The parameter interval `I = [−½, ½]` of the bottom arc. -/
abbrev ArcParam : Type := Icc (-1 / 2 : ℝ) (1 / 2)

/-- The height of the arc above `u`: `y(u) = √(1 − u²)`. -/
def modularArcHeight (u : ℝ) : ℝ := Real.sqrt (1 - u ^ 2)

theorem modularArcHeight_pos {u : ℝ} (hu : u ∈ Icc (-1 / 2 : ℝ) (1 / 2)) : 0 < modularArcHeight u := by
  unfold modularArcHeight
  apply Real.sqrt_pos.mpr
  nlinarith [hu.1, hu.2]

theorem modularArcHeight_sq {u : ℝ} (hu : u ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    u ^ 2 + modularArcHeight u ^ 2 = 1 := by
  unfold modularArcHeight
  rw [Real.sq_sqrt (by nlinarith [hu.1, hu.2])]
  ring

theorem continuous_arcK (n : ℕ) :
    Continuous fun u : ArcParam => kMoment 0 (arcFreq n * modularArcHeight u) := by
  have hc : Continuous fun u : ArcParam => arcFreq n * modularArcHeight u := by
    unfold modularArcHeight; fun_prop
  exact (continuousOn_kMoment 0).comp_continuous hc fun u =>
    mul_pos (arcFreq_pos n) (modularArcHeight_pos u.2)

/-- `C_n` on the arc, as a bounded continuous function. -/
def arcCosMode (n : ℕ) : ArcParam →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun u => kMoment 0 (arcFreq n * modularArcHeight u) * Real.cos (arcFreq n * u),
      (continuous_arcK n).mul (by fun_prop)⟩

/-- `S_n` on the arc, as a bounded continuous function. -/
def arcSinMode (n : ℕ) : ArcParam →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun u => kMoment 0 (arcFreq n * modularArcHeight u) * Real.sin (arcFreq n * u),
      (continuous_arcK n).mul (by fun_prop)⟩

theorem arcCosMode_apply (n : ℕ) (u : ArcParam) :
    arcCosMode n u = kMoment 0 (arcFreq n * modularArcHeight u) * Real.cos (arcFreq n * u) := rfl

theorem arcSinMode_apply (n : ℕ) (u : ArcParam) :
    arcSinMode n u = kMoment 0 (arcFreq n * modularArcHeight u) * Real.sin (arcFreq n * u) := rfl

/-- The moment vector of the first `N` modes at a point of the arc. -/
def arcMomentVec (N : ℕ) (u : ArcParam) : (Fin N → ℝ) × (Fin N → ℝ) :=
  (fun i => arcCosMode i u, fun i => arcSinMode i u)

/-- A continuous linear functional on `ℝ^N × ℝ^N` is a sum over coordinates. -/
theorem strongDual_prod_apply_eq_sum {N : ℕ} (f : StrongDual ℝ ((Fin N → ℝ) × (Fin N → ℝ)))
    (x y : Fin N → ℝ) :
    f (x, y) = ∑ i, x i * f (Pi.single i 1, 0) + ∑ i, y i * f (0, Pi.single i 1) := by
  have hxy : (x, y) = ContinuousLinearMap.inl ℝ _ (Fin N → ℝ) x +
      ContinuousLinearMap.inr ℝ (Fin N → ℝ) _ y := by
    simp
  rw [hxy, map_add]
  have h1 := LinearMap.pi_apply_eq_sum_univ
    ((f.comp (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ))).toLinearMap) x
  have h2 := LinearMap.pi_apply_eq_sum_univ
    ((f.comp (ContinuousLinearMap.inr ℝ (Fin N → ℝ) (Fin N → ℝ))).toLinearMap) y
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, smul_eq_mul] at h1 h2
  simp only [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  rw [h1, h2]
  have hs : ∀ i : Fin N, (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    intro i; ext j; simp [Pi.single_apply, eq_comm]
  simp only [hs]

/-- The integral of a bounded continuous function against a finite convex combination of point
masses. -/
theorem integral_sum_dirac {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (z : ι → ArcParam) (g : ArcParam →ᵇ ℝ) :
    ∫ u, g u ∂(∑ i, (ENNReal.ofReal (w i)) • Measure.dirac (z i)) = ∑ i, w i * g (z i) := by
  rw [integral_finsetSum_measure fun i _ => (g.integrable _).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

/-- **Finite stage.** -/
theorem exists_probabilityMeasure_arc_small (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ μ : ProbabilityMeasure ArcParam, ∀ n < N,
      |∫ u, arcCosMode n u ∂(μ : Measure ArcParam)| ≤ δ ∧
        |∫ u, arcSinMode n u ∂(μ : Measure ArcParam)| ≤ δ := by
  set Φ := arcMomentVec N with hΦ
  set C := closure (convexHull ℝ (range Φ)) with hC
  by_cases h0 : (0 : (Fin N → ℝ) × (Fin N → ℝ)) ∈ C
  · obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp h0 δ hδ
    obtain ⟨ι, hι, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hp
    choose u hu using hz
    set μ₀ : Measure ArcParam := ∑ i, (ENNReal.ofReal (w i)) • Measure.dirac (u i) with hμ₀
    have hprob : IsProbabilityMeasure μ₀ := by
      constructor
      rw [hμ₀, Measure.coe_finsetSum, Finset.sum_apply]
      simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul,
        mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw0 i, hw1, ENNReal.ofReal_one]
    refine ⟨⟨μ₀, hprob⟩, fun n hn => ?_⟩
    have hpn : ‖p‖ < δ := by simpa [dist_comm] using hdist
    have hcomp : ∀ i, Φ (u i) = z i := hu
    have hp1 : p.1 ⟨n, hn⟩ = ∑ i, w i * arcCosMode n (u i) := by
      rw [← hsum]
      simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hcomp i]
      rfl
    have hp2 : p.2 ⟨n, hn⟩ = ∑ i, w i * arcSinMode n (u i) := by
      rw [← hsum]
      simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hcomp i]
      rfl
    have hb1 : |p.1 ⟨n, hn⟩| ≤ ‖p‖ :=
      (norm_le_pi_norm p.1 ⟨n, hn⟩).trans (norm_fst_le p) |>.trans_eq' (Real.norm_eq_abs _).symm
    have hb2 : |p.2 ⟨n, hn⟩| ≤ ‖p‖ :=
      (norm_le_pi_norm p.2 ⟨n, hn⟩).trans (norm_snd_le p) |>.trans_eq' (Real.norm_eq_abs _).symm
    refine ⟨?_, ?_⟩
    · change |∫ x, arcCosMode n x ∂μ₀| ≤ δ
      rw [hμ₀, integral_sum_dirac w hw0 u, ← hp1]
      linarith
    · change |∫ x, arcSinMode n x ∂μ₀| ≤ δ
      rw [hμ₀, integral_sum_dirac w hw0 u, ← hp2]
      linarith
  · exfalso
    obtain ⟨f, s, hf0, hfC⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ (range Φ)).closure isClosed_closure h0
    rw [map_zero] at hf0
    have hpos : ∀ u : ArcParam, s < f (Φ u) := fun u =>
      hfC _ (subset_closure (subset_convexHull ℝ _ (mem_range_self u)))
    set a : ℕ → ℝ := fun n => if h : n < N then f (Pi.single ⟨n, h⟩ 1, 0) else 0 with ha
    set b : ℕ → ℝ := fun n => if h : n < N then f (0, Pi.single ⟨n, h⟩ 1) else 0 with hb
    have hrepr : ∀ u : ArcParam, f (Φ u) =
        whittakerArcSum N a b u (modularArcHeight u) := by
      intro u
      rw [hΦ, arcMomentVec, strongDual_prod_apply_eq_sum, ← Finset.sum_add_distrib,
        whittakerArcSum, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [arcCosMode_apply, arcSinMode_apply, arcTrig, ha, hb, dif_pos i.2]
      ring
    have harc : ∀ u y, 0 < y → |u| ≤ 1 / 2 → u ^ 2 + y ^ 2 = 1 →
        0 ≤ whittakerArcSum N a b u y := by
      intro u y hy hu huy
      have huI : u ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
        rw [abs_le] at hu; exact ⟨by linarith [hu.1], hu.2⟩
      have hyh : y = modularArcHeight u := by
        unfold modularArcHeight
        rw [show 1 - u ^ 2 = y ^ 2 by linarith, Real.sqrt_sq hy.le]
      rw [hyh, ← hrepr ⟨u, huI⟩]
      exact (hf0.trans (hpos ⟨u, huI⟩)).le
    have hzero : ∀ m < N, a m = 0 ∧ b m = 0 := fun m hm =>
      whittakerArc_coeff_eq_zero N a b harc hm
    have hsum0 : whittakerArcSum N a b 0 (modularArcHeight 0) = 0 := by
      unfold whittakerArcSum
      refine Finset.sum_eq_zero fun n hn => ?_
      have := hzero n (Finset.mem_range.mp hn)
      simp [arcTrig, this.1, this.2]
    have h0mem : (0 : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := ⟨by norm_num, by norm_num⟩
    have := hpos ⟨0, h0mem⟩
    rw [hrepr] at this
    simp only at this
    rw [hsum0] at this
    linarith

/-- **A probability measure on the modular arc annihilating every decaying Whittaker mode.** -/
theorem exists_probabilityMeasure_arc_annihilating :
    ∃ μ : ProbabilityMeasure ArcParam, ∀ n : ℕ,
      ∫ u, arcCosMode n u ∂(μ : Measure ArcParam) = 0 ∧
        ∫ u, arcSinMode n u ∂(μ : Measure ArcParam) = 0 := by
  set T : ℕ → Set (ProbabilityMeasure ArcParam) := fun k =>
    {μ | ∀ n < k, |∫ u, arcCosMode n u ∂(μ : Measure ArcParam)| ≤ 1 / ((k : ℝ) + 1) ∧
      |∫ u, arcSinMode n u ∂(μ : Measure ArcParam)| ≤ 1 / ((k : ℝ) + 1)} with hT
  have hclosed : ∀ k, IsClosed (T k) := by
    intro k
    have hc : ∀ g : ArcParam →ᵇ ℝ, Continuous fun μ : ProbabilityMeasure ArcParam =>
        |∫ u, g u ∂(μ : Measure ArcParam)| := fun g =>
      continuous_abs.comp (ProbabilityMeasure.continuous_integral_boundedContinuousFunction g)
    have : T k = ⋂ n ∈ Finset.range k,
        ({μ : ProbabilityMeasure ArcParam | |∫ u, arcCosMode n u ∂(μ : Measure ArcParam)| ≤
            1 / ((k : ℝ) + 1)} ∩
          {μ | |∫ u, arcSinMode n u ∂(μ : Measure ArcParam)| ≤ 1 / ((k : ℝ) + 1)}) := by
      ext μ
      simp [hT, Finset.mem_range]
    rw [this]
    exact isClosed_biInter fun n _ =>
      (isClosed_le (hc _) continuous_const).inter (isClosed_le (hc _) continuous_const)
  have hmono : ∀ k, T (k + 1) ⊆ T k := by
    intro k μ hμ n hn
    have h := hμ n (by omega)
    have hle : 1 / ((↑(k + 1) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith
    exact ⟨h.1.trans hle, h.2.trans hle⟩
  have hne : ∀ k, (T k).Nonempty := fun k =>
    exists_probabilityMeasure_arc_small k (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hmono hne
    ((hclosed 0).isCompact) hclosed
  rw [mem_iInter] at hμ
  refine ⟨μ, fun n => ?_⟩
  have key : ∀ g : ArcParam →ᵇ ℝ, (∀ k, n < k → |∫ u, g u ∂(μ : Measure ArcParam)| ≤
      1 / ((k : ℝ) + 1)) → ∫ u, g u ∂(μ : Measure ArcParam) = 0 := by
    intro g hg
    by_contra hne0
    have hpos : 0 < |∫ u, g u ∂(μ : Measure ArcParam)| := abs_pos.mpr hne0
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    have := hg (k + n + 1) (by omega)
    have hle : 1 / ((↑(k + n + 1) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith
  exact ⟨key _ fun k hk => (hμ k n hk).1, key _ fun k hk => (hμ k n hk).2⟩

end

end RHTower
