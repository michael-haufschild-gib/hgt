import GaloisForLFunctions.RHTower.DeningerMeyerStripCardinal

/-! # Infinite sums with every original Mellin strip weight retained

A cofinite summable majorant for each weighted strip seminorm pays original
source admission. Locally uniform convergence also retains every derivative.
-/

open Complex Filter Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

theorem deningerMeyerStripSeries_locallyUniform {ι : Type*} {T : ι → ℂ → ℂ}
    {u : ι → ℝ} (hu : Summable u)
    (hb : ∀ r : ℝ, ∀ᶠ i in cofinite, ∀ z : ℂ, |z.re| ≤ r → ‖T i z‖ ≤ u i) :
    TendstoLocallyUniformlyOn (fun s : Finset ι => fun z => ∑ i ∈ s, T i z)
      (fun z => ∑' i, T i z) atTop univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  apply (tendstoUniformlyOn_tsum_of_cofinite_eventually hu (hb r)).mono
  intro z hz
  exact (Complex.abs_re_le_norm z).trans
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hr hz)

theorem deningerMeyerStripSeries_regular {ι : Type*} {T : ι → ℂ → ℂ}
    (hT : ∀ i, DeningerEntireMellinRegular (T i)) {u : ι → ℝ} (hu : Summable u)
    (hb : ∀ (r : ℝ) (K : ℕ), ∀ᶠ i in cofinite, ∀ z : ℂ, |z.re| ≤ r →
      ‖T i z‖*(1+z.im^2)^K ≤ u i) :
    DeningerEntireMellinRegular (fun z => ∑' i, T i z) := by
  classical
  have hloc := deningerMeyerStripSeries_locallyUniform hu (fun r => by simpa using hb r 0)
  have hdiff : Differentiable ℂ (fun z => ∑' i, T i z) := by
    rw [← differentiableOn_univ]
    exact hloc.differentiableOn (Eventually.of_forall fun s =>
      (Differentiable.fun_sum fun i _ => (hT i).differentiable).differentiableOn) isOpen_univ
  intro α β
  refine ⟨fun z _ _ => hdiff z, fun a b _ _ K => ?_⟩
  let r := |a|+|b|
  choose C hC₀ hC using fun i => (hT i).weighted_strip_bound r K
  let good : ι → Prop := fun i => ∀ z : ℂ, |z.re| ≤ r →
    ‖T i z‖*(1+z.im^2)^K ≤ u i
  let v : ι → ℝ := fun i => if good i then u i else C i
  have hv : Summable v := hu.congr_cofinite (by
    filter_upwards [hb r K] with i hi
    simp only [v, if_pos (show good i from hi)])
  have hvb : ∀ i z, |z.re| ≤ r → ‖T i z‖*(1+z.im^2)^K ≤ v i := by
    intro i z hz
    dsimp [v]
    split_ifs with hi
    · exact hi z hz
    · exact hC i z hz
  refine ⟨∑' i, v i, fun z hza hzb => ?_⟩
  have hz : |z.re| ≤ r := by
    dsimp [r]
    rw [abs_le]
    constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b,
      neg_le_abs b, abs_nonneg a, abs_nonneg b]
  have hbound : ∀ i, ‖T i z‖ ≤ v i/(1+z.im^2)^K := fun i =>
    (le_div_iff₀ (by positivity : 0 < (1+z.im^2)^K)).mpr (hvb i z hz)
  have hvdiv := hv.div_const ((1+z.im^2)^K)
  have hn : Summable (fun i => ‖T i z‖) := hvdiv.of_norm_bounded (by
    intro i
    simpa only [norm_norm] using hbound i)
  calc ‖∑' i, T i z‖ ≤ ∑' i, ‖T i z‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i, v i/(1+z.im^2)^K := hn.tsum_le_tsum hbound hvdiv
    _ = (∑' i, v i)/(1+z.im^2)^K := tsum_div_const

theorem deningerEntireLocallyUniform_iteratedDeriv {ι : Type*} {p : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, Differentiable ℂ (F i))
    (hf : TendstoLocallyUniformlyOn F f p univ) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv k (F i))
      (iteratedDeriv k f) p univ := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      have hdiff : ∀ i, Differentiable ℂ (iteratedDeriv k (F i)) := by
        intro i
        exact (hF i).contDiff.differentiable_iteratedDeriv' k
      simpa only [iteratedDeriv_succ, Function.comp_def] using
        ih.deriv (Eventually.of_forall fun i => (hdiff i).differentiableOn) isOpen_univ

/-- A cardinal series passes every prescribed finite jet to its sum. -/
theorem deningerMeyerStripSeries_germ {ι : Type*} {T : ι → ℂ → ℂ}
    (hT : ∀ i, Differentiable ℂ (T i)) {H : ℂ → ℂ}
    (hH : Differentiable ℂ H)
    (hlim : TendstoLocallyUniformlyOn (fun s : Finset ι => fun z => ∑ i ∈ s, T i z)
      H atTop univ) (j : ι) {w : ℂ} {m : ℕ} {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f w)
    (hself : (m : ℕ∞) ≤ analyticOrderAt (fun z => T j z-f z) w)
    (hother : ∀ i, i ≠ j → (m : ℕ∞) ≤ analyticOrderAt (T i) w) :
    (m : ℕ∞) ≤ analyticOrderAt (fun z => H z-f z) w := by
  classical
  have hA : AnalyticAt ℂ H w := hH.differentiableOn.analyticAt univ_mem
  have hTA : ∀ i, AnalyticAt ℂ (T i) w := fun i =>
    (hT i).differentiableOn.analyticAt univ_mem
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA.sub hf)).mpr
  intro k hk
  change iteratedDeriv k (H-f) w = 0
  rw [iteratedDeriv_sub hA.contDiffAt hf.contDiffAt, sub_eq_zero]
  have hself' : iteratedDeriv k (T j) w = iteratedDeriv k f w := by
    have h := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hTA j).sub hf)).mp
      hself k hk
    change iteratedDeriv k (T j-f) w = 0 at h
    rw [iteratedDeriv_sub (hTA j).contDiffAt hf.contDiffAt, sub_eq_zero] at h
    exact h
  have hother' : ∀ i, i ≠ j → iteratedDeriv k (T i) w = 0 := fun i hi =>
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hTA i)).mp (hother i hi) k hk
  have hdlim := (deningerEntireLocallyUniform_iteratedDeriv
    (fun s => Differentiable.fun_sum fun i _ => hT i) hlim k).tendsto_at (mem_univ w)
  apply tendsto_nhds_unique hdlim
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_atTop.2 ⟨{j}, fun s hs => hs⟩] with s hs
  rw [iteratedDeriv_fun_sum (fun i _ => (hTA i).contDiffAt),
    Finset.sum_eq_single j]
  · exact hself'.symm
  · intro i _ hij
    exact hother' i hij
  · intro hj
    exact (hj (hs (Finset.mem_singleton_self j))).elim

end
end RHTower
