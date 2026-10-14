import GaloisForLFunctions.RHTower.ModularSideArcWhittakerPositivity
import GaloisForLFunctions.RHTower.BesselKZeroLogarithmicEdge
import GaloisForLFunctions.RHTower.ModularArcAnnihilatingMeasure

/-!
# A measure on the side arcs annihilating every Whittaker mode, with no mass at the cusp

The side arcs of the modular cylinder are parametrized by `s ∈ [−½, ½]` with height
`y(s) = √(2|s| − s²)` (`sideArcHeight`): for `s ≥ 0` the point `s + iy` lies on `|z − 1| = 1`,
for `s ≤ 0` the point `1 + s + iy` lies on `|z| = 1`, and `s = 0` is the cusp.  For
`c_n = 2π(n+1)` put

`C̃_n(s) = ρ_n(y(s)) cos(c_n s)`,   `S̃_n(s) = ρ_n(y(s)) sin(c_n s)`,

with `ρ_n(y) = K₀(c_n y)/K₀(c_0 y)` for `y > 0` and `ρ_n(0) = 1` (`kRatio`).  Since
`K₀(ar)/K₀(r) → 1` as `r → 0⁺` (`tendsto_kMoment_zero_mul_div`), these are continuous on the closed
parameter interval: dividing by `K₀(c_0 y)` puts all modes on the same logarithmic singularity, and
the cusp becomes an ordinary point of a compact space.

**Theorem** (`exists_probabilityMeasure_sideArc_annihilating`).  There is a probability measure `μ`
on `[−½, ½]` with `∫ C̃_n dμ = ∫ S̃_n dμ = 0` for every `n` and `μ{0} = 0`.

Proof.
* Finite stage: separation as for the bottom arc.  A strictly positive combination of the `C̃_n`,
  `S̃_n` would make the Whittaker sum positive on both side arcs, which
  `whittakerSideArc_coeff_eq_zero` forbids.
* Limit: Prokhorov on the compact space of probability measures.
* No cusp atom (`measure_cusp_eq_zero_of_sideArc_annihilating`): `|C̃_n| ≤ 1`, `C̃_n(0) = 1`, and
  `C̃_n(s) → 0` as `n → ∞` for `s ≠ 0` because `ρ_n(y) ≤ e^{−(c_n − c_0) y}`.  Dominated convergence
  turns `0 = ∫ C̃_n dμ` into `μ{0} = 0`.

Off the cusp, `μ/K₀(c_0 y)` is a finite positive measure whose integral against every decaying
Whittaker restriction `K₀(c_n y) e^{±i c_n s}` vanishes.
-/

open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### The side-arc height -/

/-- The height `y(s) = √(2|s| − s²)` of the side arcs over the parameter `s`. -/
def sideArcHeight (s : ℝ) : ℝ := Real.sqrt (2 * |s| - s ^ 2)

theorem sideArcHeight_nonneg (s : ℝ) : 0 ≤ sideArcHeight s := Real.sqrt_nonneg _

theorem continuous_sideArcHeight : Continuous sideArcHeight := by
  unfold sideArcHeight; fun_prop

@[simp] theorem sideArcHeight_zero : sideArcHeight 0 = 0 := by simp [sideArcHeight]

theorem two_abs_sub_sq_nonneg {s : ℝ} (hs : s ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    0 ≤ 2 * |s| - s ^ 2 := by
  have h := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  rw [← sq_abs]
  nlinarith [abs_nonneg s]

theorem sideArcHeight_sq {s : ℝ} (hs : s ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    sideArcHeight s ^ 2 = 2 * |s| - s ^ 2 :=
  Real.sq_sqrt (two_abs_sub_sq_nonneg hs)

theorem sideArcHeight_pos {s : ℝ} (hs : s ∈ Icc (-1 / 2 : ℝ) (1 / 2)) (h0 : s ≠ 0) :
    0 < sideArcHeight s := by
  apply Real.sqrt_pos.mpr
  have h := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hp := abs_pos.mpr h0
  rw [← sq_abs]
  nlinarith

/-! ### The normalized Bessel ratio -/

/-- `ρ_n(y) = K₀(c_n y)/K₀(c_0 y)`, extended by `1` at `y = 0`. -/
def kRatio (n : ℕ) (y : ℝ) : ℝ :=
  if y = 0 then 1 else kMoment 0 (arcFreq n * y) / kMoment 0 (arcFreq 0 * y)

@[simp] theorem kRatio_zero (n : ℕ) : kRatio n 0 = 1 := by simp [kRatio]

theorem kRatio_of_ne {n : ℕ} {y : ℝ} (hy : y ≠ 0) :
    kRatio n y = kMoment 0 (arcFreq n * y) / kMoment 0 (arcFreq 0 * y) := by
  simp [kRatio, hy]

theorem arcFreq_eq_mul (n : ℕ) : arcFreq n = ((n : ℝ) + 1) * arcFreq 0 := by
  unfold arcFreq; push_cast; ring

theorem arcFreq_zero_le (n : ℕ) : arcFreq 0 ≤ arcFreq n := by
  rw [arcFreq_eq_mul n]
  have := arcFreq_pos 0
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

theorem kRatio_nonneg (n : ℕ) (y : ℝ) : 0 ≤ kRatio n y := by
  unfold kRatio
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (kMoment_nonneg 0 _) (kMoment_nonneg 0 _)

theorem kRatio_le_one (n : ℕ) {y : ℝ} (hy : 0 ≤ y) : kRatio n y ≤ 1 := by
  rcases hy.eq_or_lt with h | h
  · rw [← h, kRatio_zero]
  · rw [kRatio_of_ne h.ne']
    have h0 := mul_pos (arcFreq_pos 0) h
    have hK := kMoment_zero_pos_of_pos h0
    rw [div_le_one hK]
    exact WeilHigherDenominator.kMoment_zero_antitone h0
      (mul_le_mul_of_nonneg_right (arcFreq_zero_le n) h.le)

/-- `ρ_n(y) ≤ e^{−(c_n − c_0) y}` for `y > 0`. -/
theorem kRatio_le_exp (n : ℕ) {y : ℝ} (hy : 0 < y) :
    kRatio n y ≤ Real.exp (-(arcFreq n * y - arcFreq 0 * y)) := by
  rw [kRatio_of_ne hy.ne']
  have h0 := mul_pos (arcFreq_pos 0) hy
  have hK := kMoment_zero_pos_of_pos h0
  rw [div_le_iff₀ hK]
  exact kMoment_le_exp_mul 0 h0 (mul_le_mul_of_nonneg_right (arcFreq_zero_le n) hy.le)

theorem continuousOn_kRatio (n : ℕ) : ContinuousOn (kRatio n) (Ici 0) := by
  intro y hy
  rcases (mem_Ici.mp hy).eq_or_lt with h | h
  · rw [← h, ← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, kRatio_zero]
    have hlin : Tendsto (fun y : ℝ => arcFreq 0 * y) (𝓝[>] 0) (𝓝[>] 0) := by
      have hc : ContinuousWithinAt (fun y : ℝ => arcFreq 0 * y) (Ioi 0) 0 :=
        (continuous_const.mul continuous_id).continuousWithinAt
      have := hc.tendsto_nhdsWithin (t := Ioi 0) fun y hy => mul_pos (arcFreq_pos 0) hy
      simpa using this
    have hlim := (tendsto_kMoment_zero_mul_div (a := (n : ℝ) + 1)
      (by positivity)).comp hlin
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (y : ℝ) ≠ 0 := (show (0 : ℝ) < y from hy).ne'
    simp only [Function.comp_apply]
    rw [kRatio_of_ne hy0, arcFreq_eq_mul n, mul_assoc]
  · have hev : kRatio n =ᶠ[𝓝 y] fun y => kMoment 0 (arcFreq n * y) / kMoment 0 (arcFreq 0 * y) := by
      filter_upwards [lt_mem_nhds h] with z hz
      exact kRatio_of_ne hz.ne'
    refine (ContinuousAt.congr ?_ hev.symm).continuousWithinAt
    have hc1 : ContinuousAt (fun y => kMoment 0 (arcFreq n * y)) y :=
      ((continuousOn_kMoment 0).continuousAt (Ioi_mem_nhds (mul_pos (arcFreq_pos n) h))).comp
        (continuous_const.mul continuous_id).continuousAt
    have hc2 : ContinuousAt (fun y => kMoment 0 (arcFreq 0 * y)) y :=
      ((continuousOn_kMoment 0).continuousAt (Ioi_mem_nhds (mul_pos (arcFreq_pos 0) h))).comp
        (continuous_const.mul continuous_id).continuousAt
    exact hc1.div hc2 (kMoment_zero_pos_of_pos (mul_pos (arcFreq_pos 0) h)).ne'

theorem continuous_kRatio_sideArcHeight (n : ℕ) :
    Continuous fun s : ArcParam => kRatio n (sideArcHeight s) :=
  (continuousOn_kRatio n).comp_continuous (continuous_sideArcHeight.comp continuous_subtype_val)
    fun _ => sideArcHeight_nonneg _

/-! ### The normalized side-arc modes -/

/-- `C̃_n` on the side arcs, as a bounded continuous function. -/
def sideCosMode (n : ℕ) : ArcParam →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun s => kRatio n (sideArcHeight s) * Real.cos (arcFreq n * s),
      (continuous_kRatio_sideArcHeight n).mul (by fun_prop)⟩

/-- `S̃_n` on the side arcs, as a bounded continuous function. -/
def sideSinMode (n : ℕ) : ArcParam →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun s => kRatio n (sideArcHeight s) * Real.sin (arcFreq n * s),
      (continuous_kRatio_sideArcHeight n).mul (by fun_prop)⟩

theorem sideCosMode_apply (n : ℕ) (s : ArcParam) :
    sideCosMode n s = kRatio n (sideArcHeight s) * Real.cos (arcFreq n * s) := rfl

theorem sideSinMode_apply (n : ℕ) (s : ArcParam) :
    sideSinMode n s = kRatio n (sideArcHeight s) * Real.sin (arcFreq n * s) := rfl

/-- The moment vector of the first `N` side-arc modes. -/
def sideMomentVec (N : ℕ) (s : ArcParam) : (Fin N → ℝ) × (Fin N → ℝ) :=
  (fun i => sideCosMode i s, fun i => sideSinMode i s)

/-- Off the cusp, a combination of the normalized modes is the Whittaker sum divided by
`K₀(c_0 y)`. -/
theorem sum_sideModes_eq (N : ℕ) (a b : ℕ → ℝ) {s : ℝ} (hy : sideArcHeight s ≠ 0) :
    ∑ n ∈ Finset.range N, kRatio n (sideArcHeight s) * arcTrig a b n s =
      whittakerArcSum N a b s (sideArcHeight s) / kMoment 0 (arcFreq 0 * sideArcHeight s) := by
  unfold whittakerArcSum
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [kRatio_of_ne hy]
  ring

/-- **Finite stage.** -/
theorem exists_probabilityMeasure_sideArc_small (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ μ : ProbabilityMeasure ArcParam, ∀ n < N,
      |∫ s, sideCosMode n s ∂(μ : Measure ArcParam)| ≤ δ ∧
        |∫ s, sideSinMode n s ∂(μ : Measure ArcParam)| ≤ δ := by
  set Φ := sideMomentVec N with hΦ
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
    have hp1 : p.1 ⟨n, hn⟩ = ∑ i, w i * sideCosMode n (u i) := by
      rw [← hsum]
      simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hcomp i]
      rfl
    have hp2 : p.2 ⟨n, hn⟩ = ∑ i, w i * sideSinMode n (u i) := by
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
    · change |∫ x, sideCosMode n x ∂μ₀| ≤ δ
      rw [hμ₀, integral_sum_dirac w hw0 u, ← hp1]
      linarith
    · change |∫ x, sideSinMode n x ∂μ₀| ≤ δ
      rw [hμ₀, integral_sum_dirac w hw0 u, ← hp2]
      linarith
  · exfalso
    obtain ⟨f, s₀, hf0, hfC⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ (range Φ)).closure isClosed_closure h0
    rw [map_zero] at hf0
    have hpos : ∀ s : ArcParam, s₀ < f (Φ s) := fun s =>
      hfC _ (subset_closure (subset_convexHull ℝ _ (mem_range_self s)))
    set a : ℕ → ℝ := fun n => if h : n < N then f (Pi.single ⟨n, h⟩ 1, 0) else 0 with ha
    set b : ℕ → ℝ := fun n => if h : n < N then f (0, Pi.single ⟨n, h⟩ 1) else 0 with hb
    have hrepr : ∀ s : ArcParam, f (Φ s) =
        ∑ n ∈ Finset.range N, kRatio n (sideArcHeight s) * arcTrig a b n s := by
      intro s
      rw [hΦ, sideMomentVec, strongDual_prod_apply_eq_sum, ← Finset.sum_add_distrib,
        ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [sideCosMode_apply, sideSinMode_apply, arcTrig, ha, hb, dif_pos i.2]
      ring
    -- positivity of the Whittaker sum on both side arcs
    have hside : ∀ s : ArcParam, (s : ℝ) ≠ 0 →
        0 ≤ whittakerArcSum N a b s (sideArcHeight s) := by
      intro s hs
      have hy := sideArcHeight_pos s.2 hs
      have hK := kMoment_zero_pos_of_pos (mul_pos (arcFreq_pos 0) hy)
      have h1 := hf0.trans (hpos s)
      rw [hrepr, sum_sideModes_eq N a b hy.ne'] at h1
      exact (div_pos_iff_of_pos_right hK).mp h1 |>.le
    have harc₁ : ∀ u y, 0 < y → 0 ≤ u → u ≤ 1 / 2 → (u - 1) ^ 2 + y ^ 2 = 1 →
        0 ≤ whittakerArcSum N a b u y := by
      intro u y hy hu0 hu1 huy
      have huI : u ∈ Icc (-1 / 2 : ℝ) (1 / 2) := ⟨by linarith, hu1⟩
      have hyh : y = sideArcHeight u := by
        unfold sideArcHeight
        rw [abs_of_nonneg hu0, show 2 * u - u ^ 2 = y ^ 2 by linarith, Real.sqrt_sq hy.le]
      have hu0' : u ≠ 0 := by
        rintro rfl
        nlinarith
      rw [hyh]
      exact hside ⟨u, huI⟩ hu0'
    have harc₂ : ∀ u y, 0 < y → 1 / 2 ≤ u → u ≤ 1 → u ^ 2 + y ^ 2 = 1 →
        0 ≤ whittakerArcSum N a b u y := by
      intro u y hy hu0 hu1 huy
      have huI : u - 1 ∈ Icc (-1 / 2 : ℝ) (1 / 2) := ⟨by linarith, by linarith⟩
      have hyh : y = sideArcHeight (u - 1) := by
        unfold sideArcHeight
        rw [abs_of_nonpos (by linarith), show 2 * -(u - 1) - (u - 1) ^ 2 = y ^ 2 by nlinarith,
          Real.sqrt_sq hy.le]
      have hu0' : u - 1 ≠ 0 := by
        intro h
        have : u = 1 := by linarith
        subst this
        nlinarith
      have hper := whittakerArcSum_periodic N a b (u - 1) y
      rw [sub_add_cancel] at hper
      rw [hper, hyh]
      exact hside ⟨u - 1, huI⟩ hu0'
    have hzero : ∀ m < N, a m = 0 ∧ b m = 0 := fun m hm =>
      whittakerSideArc_coeff_eq_zero N a b harc₁ harc₂ hm
    have h0mem : (0 : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := ⟨by norm_num, by norm_num⟩
    have := hf0.trans (hpos ⟨0, h0mem⟩)
    rw [hrepr] at this
    have hsum0 : ∑ n ∈ Finset.range N,
        kRatio n (sideArcHeight ((⟨0, h0mem⟩ : ArcParam) : ℝ)) *
          arcTrig a b n ((⟨0, h0mem⟩ : ArcParam) : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have := hzero n (Finset.mem_range.mp hn)
      simp [arcTrig, this.1, this.2]
    linarith

/-- **A probability measure on the side arcs annihilating every normalized Whittaker mode.** -/
theorem exists_probabilityMeasure_sideArc_moments :
    ∃ μ : ProbabilityMeasure ArcParam, ∀ n : ℕ,
      ∫ s, sideCosMode n s ∂(μ : Measure ArcParam) = 0 ∧
        ∫ s, sideSinMode n s ∂(μ : Measure ArcParam) = 0 := by
  set T : ℕ → Set (ProbabilityMeasure ArcParam) := fun k =>
    {μ | ∀ n < k, |∫ s, sideCosMode n s ∂(μ : Measure ArcParam)| ≤ 1 / ((k : ℝ) + 1) ∧
      |∫ s, sideSinMode n s ∂(μ : Measure ArcParam)| ≤ 1 / ((k : ℝ) + 1)} with hT
  have hclosed : ∀ k, IsClosed (T k) := by
    intro k
    have hc : ∀ g : ArcParam →ᵇ ℝ, Continuous fun μ : ProbabilityMeasure ArcParam =>
        |∫ s, g s ∂(μ : Measure ArcParam)| := fun g =>
      continuous_abs.comp (ProbabilityMeasure.continuous_integral_boundedContinuousFunction g)
    have : T k = ⋂ n ∈ Finset.range k,
        ({μ : ProbabilityMeasure ArcParam | |∫ s, sideCosMode n s ∂(μ : Measure ArcParam)| ≤
            1 / ((k : ℝ) + 1)} ∩
          {μ | |∫ s, sideSinMode n s ∂(μ : Measure ArcParam)| ≤ 1 / ((k : ℝ) + 1)}) := by
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
    exists_probabilityMeasure_sideArc_small k (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hmono hne
    ((hclosed 0).isCompact) hclosed
  rw [mem_iInter] at hμ
  refine ⟨μ, fun n => ?_⟩
  have key : ∀ g : ArcParam →ᵇ ℝ, (∀ k, n < k → |∫ s, g s ∂(μ : Measure ArcParam)| ≤
      1 / ((k : ℝ) + 1)) → ∫ s, g s ∂(μ : Measure ArcParam) = 0 := by
    intro g hg
    by_contra hne0
    have hpos : 0 < |∫ s, g s ∂(μ : Measure ArcParam)| := abs_pos.mpr hne0
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    have := hg (k + n + 1) (by omega)
    have hle : 1 / ((↑(k + n + 1) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith
  exact ⟨key _ fun k hk => (hμ k n hk).1, key _ fun k hk => (hμ k n hk).2⟩

/-! ### No mass at the cusp -/

/-- The cusp `{s = 0}` of the parameter interval. -/
def sideCusp : Set ArcParam := {s | (s : ℝ) = 0}

theorem measurableSet_sideCusp : MeasurableSet sideCusp :=
  (isClosed_eq continuous_subtype_val continuous_const).measurableSet

theorem tendsto_sideCosMode (s : ArcParam) :
    Tendsto (fun n => sideCosMode n s) atTop (𝓝 (sideCusp.indicator 1 s)) := by
  by_cases hs : (s : ℝ) = 0
  · have hmem : s ∈ sideCusp := hs
    rw [indicator_of_mem hmem]
    refine tendsto_const_nhds.congr fun n => ?_
    rw [sideCosMode_apply, hs, sideArcHeight_zero, kRatio_zero, mul_zero, Real.cos_zero]
    simp
  · have hmem : s ∉ sideCusp := hs
    rw [indicator_of_notMem hmem]
    have hy := sideArcHeight_pos s.2 hs
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(arcFreq n * sideArcHeight s -
        arcFreq 0 * sideArcHeight s))) atTop (𝓝 0) := by
      have hlin : Tendsto (fun n : ℕ => arcFreq n * sideArcHeight s - arcFreq 0 * sideArcHeight s)
          atTop atTop := by
        have h1 : Tendsto (fun n : ℕ => arcFreq n) atTop atTop := by
          unfold arcFreq
          exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop
            (by positivity)
        exact tendsto_atTop_add_const_right _ _ (h1.atTop_mul_const hy)
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    refine squeeze_zero_norm (fun n => ?_) hexp
    rw [sideCosMode_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (kRatio_nonneg _ _)]
    calc kRatio n (sideArcHeight s) * |Real.cos (arcFreq n * s)|
        ≤ kRatio n (sideArcHeight s) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (kRatio_nonneg _ _)
      _ ≤ _ := by rw [mul_one]; exact kRatio_le_exp n hy

/-- **No mass at the cusp.**  A finite measure annihilating every `C̃_n` has `μ{0} = 0`. -/
theorem measure_cusp_eq_zero_of_sideArc_annihilating (μ : Measure ArcParam) [IsFiniteMeasure μ]
    (h : ∀ n, ∫ s, sideCosMode n s ∂μ = 0) : μ sideCusp = 0 := by
  have hdom := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    (fun n => (sideCosMode n).continuous.aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun s => by
      rw [sideCosMode_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (kRatio_nonneg _ _)]
      exact (mul_le_mul (kRatio_le_one n (sideArcHeight_nonneg _)) (Real.abs_cos_le_one _)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
    (Eventually.of_forall tendsto_sideCosMode)
  simp only [h, integral_indicator_one measurableSet_sideCusp] at hdom
  have hreal : μ.real sideCusp = 0 := tendsto_nhds_unique hdom tendsto_const_nhds
  rwa [measureReal_eq_zero_iff (measure_ne_top μ _)] at hreal

/-- **The side-arc annihilating measure.**  A probability measure on `[−½, ½]` with no mass at the
cusp `s = 0` that annihilates every normalized side-arc Whittaker mode. -/
theorem exists_probabilityMeasure_sideArc_annihilating :
    ∃ μ : ProbabilityMeasure ArcParam, (∀ n : ℕ,
      ∫ s, sideCosMode n s ∂(μ : Measure ArcParam) = 0 ∧
        ∫ s, sideSinMode n s ∂(μ : Measure ArcParam) = 0) ∧
      (μ : Measure ArcParam) sideCusp = 0 := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_sideArc_moments
  exact ⟨μ, hμ, measure_cusp_eq_zero_of_sideArc_annihilating _ fun n => (hμ n).1⟩

end

end RHTower
