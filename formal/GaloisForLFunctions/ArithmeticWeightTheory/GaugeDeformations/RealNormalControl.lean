import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import GaloisForLFunctions.Bottcher.Montel

/-!
# Uniform real control of nonnegative prime families

Baire converts pointwise summability of continuous nonnegative terms into
a finite-sum bound on one interval. Integration preserves that bound.
A common Lipschitz estimate then bounds squared peak heights by interval
mass, supplying the real input for complex propagation of smallness.
-/


open Set Metric Filter Topology MeasureTheory
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Pointwise summability of continuous nonnegative terms gives a uniform bound on some interval. -/
theorem exists_interval_sum_bound {ι : Type*} {f : ι → ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hc : ∀ i, ContinuousOn (f i) (Ioo (-R) R))
    (hn : ∀ i t, t ∈ Ioo (-R) R → 0 ≤ f i t)
    (hs : ∀ t ∈ Ioo (-R) R, Summable (fun i => f i t)) :
    ∃ c r C : ℝ, 0 < r ∧ 0 < C ∧ |c| + r < R ∧
      ∀ t : ℝ, |t - c| ≤ r → ∀ F : Finset ι, ∑ i ∈ F, f i t ≤ C := by
  classical
  let X := ↥(Ioo (-R) R)
  letI : BaireSpace X := isOpen_Ioo.baireSpace
  letI : Nonempty X := ⟨⟨0, by constructor <;> linarith only [hR]⟩⟩
  let E : ℕ → Set X := fun n => {t | ∀ F : Finset ι, ∑ i ∈ F, f i t ≤ (n : ℝ)}
  have hcont (i : ι) : Continuous (fun t : X => f i t) :=
    continuousOn_iff_continuous_restrict.mp (hc i)
  have hclosed (n : ℕ) : IsClosed (E n) := by
    have he : E n = ⋂ F : Finset ι, {t : X | ∑ i ∈ F, f i t ≤ (n : ℝ)} := by
      ext t
      simp only [E, mem_setOf_eq, mem_iInter]
    rw [he]
    exact isClosed_iInter (fun F => isClosed_le (continuous_finsetSum _ (fun i _ => hcont i))
      continuous_const)
  have hcover : ⋃ n, E n = univ := by
    apply eq_univ_iff_forall.mpr
    intro t
    obtain ⟨n, hn'⟩ := exists_nat_gt (∑' i, f i t)
    apply mem_iUnion.mpr ⟨n, ?_⟩
    intro F
    exact ((hs t t.2).sum_le_tsum F (fun i _ => hn i t t.2)).trans hn'.le
  obtain ⟨n, c, hci⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hci)
  have hcR : |(c : ℝ)| < R := abs_lt.mpr c.2
  let r := min (ε / 2) ((R - |(c : ℝ)|) / 2)
  have hr : 0 < r := lt_min (by linarith only [hε]) (by linarith only [hcR])
  have hrε : r ≤ ε / 2 := min_le_left _ _
  have hrR : r ≤ (R - |(c : ℝ)|) / 2 := min_le_right _ _
  refine ⟨c, r, n + 1, hr, by positivity, by linarith only [hrR, hcR], ?_⟩
  intro t ht F
  have htR : |t| < R := by
    have ha : |t| ≤ |t - (c : ℝ)| + |(c : ℝ)| := by
      simpa only [sub_add_cancel] using abs_add_le (t - (c : ℝ)) (c : ℝ)
    linarith only [ha, ht, hrR, hcR]
  let t' : X := ⟨t, abs_lt.mp htR⟩
  have htmem : t' ∈ ball c ε := by
    rw [mem_ball, Subtype.dist_eq, Real.dist_eq]
    exact ht.trans_lt (by linarith only [hrε, hε])
  have h := he htmem F
  exact h.trans (by norm_num)

/-- Uniform bounds for nonnegative finite sums survive interval integration. -/
theorem summable_interval_integrals_of_sum_bound {ι : Type*} {f : ι → ℝ → ℝ}
    {a b C : ℝ} (hab : a ≤ b)
    (hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (hn : ∀ i t, t ∈ Icc a b → 0 ≤ f i t)
    (hb : ∀ t ∈ Icc a b, ∀ F : Finset ι, ∑ i ∈ F, f i t ≤ C) :
    Summable (fun i => ∫ t in a..b, f i t) := by
  classical
  have hi (i : ι) : IntervalIntegrable (f i) volume a b :=
    (hc i).intervalIntegrable_of_Icc hab
  apply summable_of_sum_le (fun i => intervalIntegral.integral_nonneg hab (hn i))
    (c := (b - a) * C)
  intro F
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  have hsc : ContinuousOn (fun t => ∑ i ∈ F, f i t) (Icc a b) :=
    continuousOn_iff_continuous_restrict.mpr
      (continuous_finsetSum F (fun i _ => continuousOn_iff_continuous_restrict.mp (hc i)))
  have hs : IntervalIntegrable (fun t => ∑ i ∈ F, f i t) volume a b :=
    hsc.intervalIntegrable_of_Icc hab
  have h := intervalIntegral.integral_mono_on hab hs intervalIntegrable_const
    (fun t ht => hb t ht F)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

/-- A Lipschitz peak has enough interval mass to bound its squared height. -/
theorem sq_le_interval_integral_of_lipschitz {g : ℝ → ℝ} {c r L M : ℝ}
    (hr : 0 < r) (hL : 0 ≤ L) (hM : 0 < M)
    (hc : ContinuousOn g (Icc (c - r) (c + r)))
    (hn : ∀ t ∈ Icc (c - r) (c + r), 0 ≤ g t)
    (hb : ∀ t ∈ Icc (c - r) (c + r), g t ≤ M)
    (hlip : ∀ t ∈ Icc (c - r) (c + r), ∀ u ∈ Icc (c - r) (c + r),
      |g u - g t| ≤ L * |u - t|)
    {t : ℝ} (ht : |t - c| ≤ r / 2) :
    g t ^ 2 ≤ 4 * (L + M / r) * ∫ u in (c - r)..(c + r), g u := by
  have ht' := abs_le.mp ht
  have htJ : t ∈ Icc (c - r) (c + r) := by constructor <;> linarith only [ht'.1, ht'.2, hr]
  let K := L + M / r
  have hK : 0 < K := add_pos_of_nonneg_of_pos hL (div_pos hM hr)
  have hKL : L ≤ K := le_add_of_nonneg_right (div_nonneg hM.le hr.le)
  have hgt : 0 ≤ g t := hn t htJ
  let d := g t / (2 * K)
  have hd : 0 ≤ d := div_nonneg hgt (by positivity)
  have hKd : K * d = g t / 2 := by dsimp [d]; field_simp
  have hKr : K * r = L * r + M := by dsimp [K]; field_simp
  have hdr : d ≤ r / 2 := by
    apply (div_le_iff₀ (show 0 < 2 * K by positivity)).mpr
    have hgtM := hb t htJ
    nlinarith only [hKr, hgtM, mul_nonneg hL hr.le]
  have hsub : Icc t (t + d) ⊆ Icc (c - r) (c + r) := by
    intro u hu
    constructor <;> linarith only [hu.1, hu.2, ht'.1, ht'.2, hdr, hr]
  have hpeak (u : ℝ) (hu : u ∈ Icc t (t + d)) : g t / 2 ≤ g u := by
    have hl := hlip t htJ u (hsub hu)
    rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hl
    have hlow := neg_le_abs (g u - g t)
    have hud : u - t ≤ d := by linarith only [hu.2]
    have hLd : L * d ≤ K * d := mul_le_mul_of_nonneg_right hKL hd
    have hLu : L * (u - t) ≤ L * d := mul_le_mul_of_nonneg_left hud hL
    linarith only [hl, hlow, hLd, hLu, hKd]
  have hIt : IntervalIntegrable g volume t (t + d) :=
    (hc.mono hsub).intervalIntegrable_of_Icc (by linarith only [hd])
  have hIJ : IntervalIntegrable g volume (c - r) (c + r) :=
    hc.intervalIntegrable_of_Icc (by linarith only [hr])
  have hlo := intervalIntegral.integral_mono_on (show t ≤ t + d by linarith only [hd])
    (intervalIntegrable_const (c := g t / 2)) hIt hpeak
  simp only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hlo
  have hmono := intervalIntegral.integral_mono_interval htJ.1
    (show t ≤ t + d by linarith only [hd])
    (show t + d ≤ c + r by linarith only [ht'.2, hdr])
    (show 0 ≤ᵐ[volume.restrict (Ioc (c - r) (c + r))] g from
      (ae_restrict_mem measurableSet_Ioc).mono (fun u hu => hn u ⟨hu.1.le, hu.2⟩)) hIJ
  have hmul := mul_le_mul_of_nonneg_left (hlo.trans hmono) (show 0 ≤ 4 * K by positivity)
  have he : 4 * K * (d * (g t / 2)) = g t ^ 2 := by
    calc
      _ = 2 * (K * d) * g t := by ring
      _ = _ := by rw [hKd]; ring
  rw [he] at hmul
  exact hmul

#print axioms exists_interval_sum_bound
#print axioms sq_le_interval_integral_of_lipschitz

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
