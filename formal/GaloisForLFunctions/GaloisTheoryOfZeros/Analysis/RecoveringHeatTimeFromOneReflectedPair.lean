import GaloisForLFunctions.GaloisTheoryOfZeros.TheHermiteMonodromyOfACollision
import GaloisForLFunctions.Bottcher.EvenHoloExtension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Recovering heat time from a single reflected pair

The fold in Guyomard–Pahl–Rasel–Gaaloul (arXiv:2611.13032, §II)
uses a quadratic map to describe the merging of two rays. For the
de Bruijn heat family the squared gap of any two opposite noncentral
Hermite sheets is a local analytic coordinate in physical time, even
in a cluster with more sheets. The pair centre is analytic in that
same gap coordinate. At a double zero the inverse slope is exactly 1/8.
-/

noncomputable section
open Complex Filter Topology Metric RHTower.DeBruijn
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
namespace GaloisForLFunctions.GaloisTheoryOfZeros

private theorem descend_even_germ {f : ℂ → ℂ} (ha : AnalyticAt ℂ f 0)
    (he : ∀ᶠ s in 𝓝 0, f (-s) = f s) :
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 = f 0 ∧
      ∀ᶠ s in 𝓝 0, V (s^2) = f s := by
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp (ha.eventually_analyticAt.and he)
  obtain ⟨V,hV,h⟩ := Bottcher.exists_analytic_factor_of_even hr
    (fun s hm => (hs hm).1.differentiableAt.differentiableWithinAt) (fun s hm => (hs hm).2)
  exact ⟨V,hV.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (sq_pos_of_pos hr))),
    by simpa using h 0 (mem_ball_self hr),
    Filter.mem_of_superset (ball_mem_nhds 0 hr) fun s hs => h s hs⟩

/-- The two zeros have an analytic midpoint. Their signed half-gap is
s times an analytic factor with constant term ρ in physical time s². -/
theorem IsCollision.reflected_pair_coordinates {τ z ρ : ℂ} {m : ℕ}
    (hc : IsCollision τ z m) (hr : heatModelFwd m ρ = 0) :
    ∃ C U : ℂ → ℂ, AnalyticAt ℂ C 0 ∧ AnalyticAt ℂ U 0 ∧ C 0=z ∧ U 0=ρ ∧
      ∀ᶠ s in 𝓝 0, collisionZero τ z m ρ s = C (s^2)+s*U (s^2) ∧
        collisionZero τ z m (-ρ) s = C (s^2)-s*U (s^2) := by
  let Y := collisionBranch τ z m ρ
  have hY : AnalyticAt ℂ Y 0 := (collisionBranch_spec hc hr).1
  have hY0 : Y 0=ρ := (collisionBranch_spec hc hr).2.1
  have hneg : AnalyticAt ℂ Y (-0) := by simpa using hY
  have hYn : AnalyticAt ℂ (fun s : ℂ => Y (-s)) 0 := hneg.comp analyticAt_id.neg
  let A (s : ℂ) := z+s*((Y s-Y (-s))/2)
  let B (s : ℂ) := (Y s+Y (-s))/2
  have hA : AnalyticAt ℂ A 0 := analyticAt_const.add
    (analyticAt_id.mul ((hY.sub hYn).div analyticAt_const (by norm_num)))
  have hB : AnalyticAt ℂ B 0 := (hY.add hYn).div analyticAt_const (by norm_num)
  obtain ⟨C,hC,hC0,hCe⟩ := descend_even_germ hA (Eventually.of_forall fun s => by
    dsimp only [A]; rw [neg_neg]; ring)
  obtain ⟨U,hU,hU0,hUe⟩ := descend_even_germ hB (Eventually.of_forall fun s => by
    dsimp only [B]; rw [neg_neg,add_comm])
  have hunit : U 0=ρ := by rw [hU0]; simp only [B,neg_zero,hY0]; ring
  refine ⟨C,U,hC,hU,by simpa [A] using hC0,hunit,?_⟩
  filter_upwards [hCe,hUe,collisionBranch_neg hc hr] with s hs hu hn
  rw [hs,hu]
  change (z+s*Y s=A s+s*B s) ∧ z+s*collisionBranch τ z m (-ρ) s=A s-s*B s
  rw [hn]
  dsimp only [A,B,Y]
  constructor <;> ring

/-- Given only the unordered positions of an opposite pair, its squared
gap recovers both the elapsed physical time and the midpoint by analytic
functions. The derivative of the time reconstruction is 1/(4ρ²). -/
theorem IsCollision.time_and_midpoint_of_squared_gap {τ z ρ : ℂ} {m : ℕ}
    (hc : IsCollision τ z m) (hr : heatModelFwd m ρ = 0) (hn : ρ≠0) :
    ∃ T P : ℂ → ℂ, AnalyticAt ℂ T 0 ∧ AnalyticAt ℂ P 0 ∧ T 0=0 ∧ P 0=z ∧
      deriv T 0=(4*ρ^2)⁻¹ ∧ ∀ᶠ s in 𝓝 0,
        let a := collisionZero τ z m ρ s
        let b := collisionZero τ z m (-ρ) s
        T ((a-b)^2)=s^2 ∧ P ((a-b)^2)=(a+b)/2 := by
  obtain ⟨C,U,hC,hU,hC₀,hU₀,hs⟩ := hc.reflected_pair_coordinates hr
  let D (w : ℂ) := w*(4*(U w)^2)
  have hD : AnalyticAt ℂ D 0 := analyticAt_id.mul (analyticAt_const.mul (hU.pow 2))
  have hD₀ : D 0=0 := zero_mul _
  have hd : deriv D 0 = 4*ρ^2 := by
    have h := ((hasDerivAt_id (0:ℂ)).mul ((hU.differentiableAt.hasDerivAt.pow 2).const_mul 4)).deriv
    have hf : id * (fun w : ℂ => 4 * (U^2) w) = D := by funext w; rfl
    rw [hf] at h
    simpa only [Pi.pow_apply,id_eq,one_mul,zero_mul,add_zero,hU₀] using h
  have hne : deriv D 0≠0 := hd ▸ mul_ne_zero (by norm_num) (pow_ne_zero 2 hn)
  let T := hD.hasStrictDerivAt.localInverse _ _ _ hne
  have hTa : AnalyticAt ℂ T 0 := by
    simpa only [hD₀] using (hD.analyticAt_localInverse hne : AnalyticAt ℂ T (D 0))
  have hleft : ∀ᶠ w in 𝓝 0, T (D w)=w := hD.hasStrictDerivAt.eventually_left_inverse hne
  have hT₀ : T 0=0 := by simpa only [hD₀] using hleft.self_of_nhds
  have hCT : AnalyticAt ℂ C (T 0) := by rwa [hT₀]
  have hP : AnalyticAt ℂ (fun w => C (T w)) 0 := hCT.comp hTa
  have hTd : deriv T (D 0)=(deriv D 0)⁻¹ := (hD.hasStrictDerivAt.to_localInverse hne).hasDerivAt.deriv
  have hsq : Tendsto (fun s : ℂ => s^2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun s : ℂ => s^2) := by fun_prop
    simpa only [zero_pow (by decide : 2≠0)] using hc.tendsto (0:ℂ)
  refine ⟨T,fun w => C (T w),hTa,hP,hT₀,by simpa only [hT₀] using hC₀,
    by simpa only [hD₀,hd] using hTd,?_⟩
  filter_upwards [hs,hsq.eventually hleft] with s hp hinv
  dsimp only
  rw [hp.1,hp.2]
  have he : (C (s^2)+s*U (s^2)-(C (s^2)-s*U (s^2)))^2 = D (s^2) := by
    dsimp only [D]; ring
  rw [he,hinv]
  exact ⟨rfl,by ring⟩

/-- For a double collision the two roots have a universal inverse
slope, independent of the collision location and the time slice. -/
theorem IsCollision.double_gap_inverse {τ z : ℂ} (hc : IsCollision τ z 2) :
    ∃ T : ℂ → ℂ, AnalyticAt ℂ T 0 ∧ T 0=0 ∧ deriv T 0=1/8 ∧
      ∀ᶠ s in 𝓝 0, T ((collisionZero τ z 2 (Real.sqrt 2) s -
        collisionZero τ z 2 (-(Real.sqrt 2:ℂ)) s)^2) = s^2 := by
  let r : ℂ := (Real.sqrt 2:ℝ)
  have hr : heatModelFwd 2 r=0 := heatModelFwd_profileRoot
    (by rw [profileRoots_two]; exact Finset.mem_insert_self ..)
  have hsq : r^2=2 := by
    dsimp only [r]
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn : r≠0 := by intro h; rw [h] at hsq; norm_num at hsq
  obtain ⟨T,_,ha,_,h0,_,hd,h⟩ := hc.time_and_midpoint_of_squared_gap hr hn
  refine ⟨T,ha,h0,by rw [hd,hsq]; norm_num,h.mono fun _ hh => hh.1⟩

#print axioms IsCollision.reflected_pair_coordinates
#print axioms IsCollision.time_and_midpoint_of_squared_gap
#print axioms IsCollision.double_gap_inverse
end GaloisForLFunctions.GaloisTheoryOfZeros
