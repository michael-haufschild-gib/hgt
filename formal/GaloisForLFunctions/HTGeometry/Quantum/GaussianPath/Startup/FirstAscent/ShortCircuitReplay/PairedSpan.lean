import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ShortCircuitReplay.PairedProfile

/-! # Sharp local separation of two visits at the same circuit tolerance -/

open Set Real Filter MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
open SpectralArcs ThermodynamicEdges
noncomputable section

private def chord (x : ℝ) := 2*sin (min x (2*π)/8)

private theorem angle_mem {x : ℝ} (hx : 0≤x) :
    min x (2*π)/8 ∈ Icc (-(π/2)) (π/2) :=
  ⟨by linarith only [le_min hx two_pi_pos.le,pi_pos],by linarith only [min_le_right x (2*π),pi_pos]⟩

private theorem chord_mono {x y : ℝ} (hx : 0≤x) (hxy : x≤y) : chord x≤chord y :=
  mul_le_mul_of_nonneg_left (monotoneOn_sin (angle_mem hx) (angle_mem (hx.trans hxy))
    (div_le_div_of_nonneg_right (min_le_min_right _ hxy) (by norm_num))) zero_le_two

private theorem threshold {e : ℝ} (he : e ∈ Ioo (0:ℝ) (sqrt 2)) {x : ℝ} (hx : 0≤x) :
    (x < 8*arcsin (e/2) → chord x < e) ∧ (8*arcsin (e/2) < x → e < chord x) := by
  have hs := sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hu : e/2 ∈ Icc (-1:ℝ) 1 := ⟨by linarith only [he.1],by nlinarith only [hs,he.2,he.1]⟩
  have hq : π/4 ∈ Icc (-(π/2)) (π/2) := ⟨by linarith only [pi_pos],by linarith only [pi_pos]⟩
  have ha : arcsin (e/2)<π/4 := (arcsin_lt_iff_lt_sin hu hq).mpr (by rw [sin_pi_div_four]; linarith only [he.2])
  constructor
  · intro h
    have hl := (lt_arcsin_iff_sin_lt (angle_mem hx) hu).mp
      (by linarith only [min_le_left x (2*π),h])
    change 2*sin _<e
    linarith only [hl]
  · intro h
    have hl : 8*arcsin (e/2) < min x (2*π) := lt_min h (by linarith only [ha])
    have hh := (arcsin_lt_iff_lt_sin hu (angle_mem hx)).mp (by linarith only [hl])
    change e<2*sin _
    linarith only [hh]

/-- Below √2, all pairs of sublinear-budget visits on a bounded lag interval
have scaled separation at most 8 arcsin(e/2)/w up to vanishing error.
Separations arbitrarily close to this bound occur after every origin. -/
theorem gaussian_sharp_pair_span :
    ∃ w : ℝ, 0<w ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      let N := fun n : ℕ => ((n+2:ℕ):ℝ)
      let H := fun n => shellOperator (pathPauliDisorderShell ω n)
      Tendsto (fun n => physicalWidth ω n/N n) atTop (𝓝 w) ∧
      ∀ i j : ℕ→ℕ, Tendsto (fun n => ((i n+j n:ℕ):ℝ)/N n) atTop (𝓝 0) →
        ∀ e ∈ Ioo (0:ℝ) (sqrt 2), ∀ T > (0:ℝ), ∀ η > (0:ℝ), ∀ᶠ n in atTop,
          let x := 8*arcsin (e/2)/w
          (∀ v : ℝ, ∀ t∈Icc (0:ℝ) T, orbitCircuitDistance (H n) (i n) v ≤ e →
            orbitCircuitDistance (H n) (j n) (v+t) ≤ e → N n*t < x+η) ∧
          ∀ a : ℝ, ∃ v ≥ a, ∃ t∈Icc (0:ℝ) T, x-η < N n*t ∧
            orbitCircuitDistance (H n) (i n) v < e ∧ orbitCircuitDistance (H n) (j n) (v+t) < e := by
  obtain ⟨w,hw,hh⟩ := gaussian_paired_profile
  refine ⟨w,hw,?_⟩
  filter_upwards [hh] with ω hh
  intro N H
  refine ⟨hh.1,?_⟩
  intro i j hs e he T hT η hη
  let x := 8*arcsin (e/2)/w
  let l := max 0 (x-η/2)
  let u := x+η
  have hx : 0<x := div_pos (mul_pos (by norm_num) (arcsin_pos.mpr (half_pos he.1))) hw
  have hl : 0≤l := le_max_left .. 
  have hu : 0≤u := (add_pos hx hη).le
  have hlow := (threshold he (mul_nonneg hl hw.le)).1 ((lt_div_iff₀ hw).mp
    (show l<x from max_lt hx (sub_lt_self _ (half_pos hη))))
  have hhigh := (threshold he (mul_nonneg hu hw.le)).2 ((div_lt_iff₀ hw).mp (lt_add_of_pos_right x hη))
  let δ := min (e-chord (l*w)) (chord (u*w)-e)/2
  have hδ : 0<δ := half_pos (lt_min (sub_pos.mpr hlow) (sub_pos.mpr hhigh))
  have hδl : δ < e-chord (l*w) := (half_lt_self (lt_min (sub_pos.mpr hlow) (sub_pos.mpr hhigh))).trans_le (min_le_left ..)
  have hδu : δ < chord (u*w)-e := (half_lt_self (lt_min (sub_pos.mpr hlow) (sub_pos.mpr hhigh))).trans_le (min_le_right ..)
  obtain ⟨M,hM⟩ := exists_nat_ge (l/T)
  filter_upwards [hh.2 i j hs T δ hδ,eventually_ge_atTop M] with n hn hmn
  intro x'
  have hN : 0<N n := by dsimp only [N]; positivity
  constructor
  · intro v t ht hv ht'
    by_contra! ho
    have hm := chord_mono (mul_nonneg hu hw.le) (mul_le_mul_of_nonneg_right ho hw.le)
    have hc := hn v t ht
    change |pairError (H n) (i n) (j n) v t-chord (N n*t*w)|≤δ at hc
    have hpair := (pairError_le (H n) (i n) (j n) (le_refl v) t).trans (max_le hv ht')
    linarith only [(abs_le.mp hc).1,hδu,hm,hpair]
  · intro a
    have hlT : l/T ≤ N n := hM.trans (Nat.cast_le.mpr (show M≤n+2 by omega))
    have ht : l/N n∈Icc (0:ℝ) T := ⟨div_nonneg hl hN.le,(div_le_iff₀ hN).mpr (by
      simpa only [mul_comm T] using (div_le_iff₀ hT).mp hlT)⟩
    have heq : N n*(l/N n)=l := by field_simp
    have hc := hn a (l/N n) ht
    rw [heq] at hc
    change |pairError (H n) (i n) (j n) a (l/N n)-chord (l*w)|≤δ at hc
    obtain ⟨v,hv,h₁,h₂⟩ := (pairError_lt_iff (H n) (i n) (j n) a (l/N n) e).mp
      (by linarith only [(abs_le.mp hc).2,hδl])
    exact ⟨v,hv,l/N n,ht,heq.symm ▸ (show x-η<l by
      apply lt_of_lt_of_le _ (le_max_right ..); linarith only [hη]),h₁,h₂⟩

#print axioms gaussian_sharp_pair_span
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
