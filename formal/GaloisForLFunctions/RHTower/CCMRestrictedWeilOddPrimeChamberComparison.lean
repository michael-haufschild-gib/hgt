import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolePrimeChamber
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Strict odd-pole positivity between endpoints with the same prime cutoff

For the actual moving odd pole, the shifted second derivative is strictly
negative at every matching-cutoff aperture at least two. The proof retains the
full prime tent and Gamma–polar terms, using only admitted uniform boundary and
elementary hyperbolic bounds. A minimum principle then proves strict positivity
inside a fixed-cutoff interval from nonnegative actual endpoint energies.
No endpoint positivity, all-aperture source sign, or RH premise is supplied.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace RHTower

private theorem sq_le_two_cosh_sub {s : ℝ} (hs : 0 ≤ s) : s^2 ≤ 2*(Real.cosh s-1) := by
  have hh : 0 ≤ s/2 := by linarith
  have hS := Real.self_le_sinh_iff.mpr hh
  have hsq : (s/2)^2 ≤ Real.sinh (s/2)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (show 0 ≤ Real.sinh (s/2)+s/2 by linarith)]
  have hC := Real.cosh_two_mul (s/2)
  rw [show 2*(s/2)=s by ring] at hC
  nlinarith [Real.cosh_sq_sub_sinh_sq (s/2)]

/-- The actual odd energy has strictly negative shifted second derivative in every
matching prime cutoff chamber at aperture at least two. -/
theorem ccmWeilOddPoleChamber_shifted_second_neg (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊=⌊Real.exp (2*a.1)⌋₊) (hb : 2 ≤ b.1) :
    deriv (deriv (ccmWeilOddPoleChamber a)) b.1-ccmWeilOddPoleChamber a b.1 < 0 := by
  rw [deriv_deriv_ccmWeilOddPoleChamber_sub a b.2,
    ← ccmWeilPoleCross_eq_chamber_of_floor_eq a b hf]
  have hquad := sq_le_two_cosh_sub b.2.le
  have hc3 : 3 ≤ Real.cosh b.1 := by nlinarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hB : ccmGammaPoleCrossBoundaryMass b ≤ 7 := by
    have h := ccmGammaPoleCrossBoundaryMass_le b
    linarith [Real.pi_lt_four]
  have hlog : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hk : (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*(2*b.1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.one_half_lt_eulerMascheroniConstant])
      (by linarith [b.2])
  have hC : ccmWeilPoleCross b ≤ 2*b.1^2+4*Real.sinh b.1^2+7 := by
    have he := ccmWeilPoleCross_eq b
    have hT := ccmPolarPrimeTent_nonneg b
    nlinarith
  have hExp : 5 ≤ Real.exp (2*b.1) := by
    have h := Real.add_one_le_exp (2*b.1)
    linarith
  have hfrac : 4/(Real.exp (2*b.1)-1) ≤ 1 := by
    rw [div_le_iff₀ (by linarith : 0 < Real.exp (2*b.1)-1)]
    linarith
  have hDen : 0 < Real.exp (4*b.1)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith [b.2]))
  have hGamma : 0 ≤ 4*Real.exp (-b.1)*(1+Real.exp (4*b.1))/(Real.exp (4*b.1)-1) := by positivity
  have he := Real.exp_pos (-b.1)
  have h2 := Real.cosh_two_mul b.1
  have hCS := Real.cosh_sq_sub_sinh_sq b.1
  have hsq := mul_nonneg (sub_nonneg.mpr hc3) (Real.cosh_pos b.1).le
  nlinarith

private theorem second_nonneg_of_localMin {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hm,hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hzero := heq.deriv.deriv_eq
  simp only [deriv_const'] at hzero
  linarith

private theorem interval_nonneg_of_shifted_second_neg {f : ℝ → ℝ} {l r : ℝ}
    (hc : ContinuousOn f (Icc l r))
    (hd : ∀ x∈Ioo l r, deriv (deriv f) x-f x < 0)
    (hl : 0 ≤ f l) (hr : 0 ≤ f r) : ∀ x∈Icc l r, 0 ≤ f x := by
  intro x hx
  by_contra hn
  have hxneg : f x < 0 := lt_of_not_ge hn
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨x,hx⟩ hc
  have hmneg : f m < 0 := (hmin hx).trans_lt hxneg
  have hlm : l < m := by
    by_contra h
    have he : m=l := le_antisymm (le_of_not_gt h) hm.1
    rw [he] at hmneg
    linarith
  have hmr : m < r := by
    by_contra h
    have he : m=r := le_antisymm hm.2 (le_of_not_gt h)
    rw [he] at hmneg
    linarith
  have hnhds := Icc_mem_nhds hlm hmr
  have hs := second_nonneg_of_localMin (hmin.isLocalMin hnhds) (hc.continuousAt hnhds)
  have hforce := hd m ⟨hlm,hmr⟩
  linarith

private theorem interval_pos_of_shifted_second_neg {f : ℝ → ℝ} {l r : ℝ}
    (hc : ContinuousOn f (Icc l r))
    (hd : ∀ x∈Ioo l r, deriv (deriv f) x-f x < 0)
    (hl : 0 ≤ f l) (hr : 0 ≤ f r) : ∀ x∈Ioo l r, 0 < f x := by
  intro x hx
  have hn := interval_nonneg_of_shifted_second_neg hc hd hl hr
  by_contra h
  have he : f x=0 := le_antisymm (le_of_not_gt h) (hn x ⟨hx.1.le,hx.2.le⟩)
  have hm : IsMinOn f (Icc l r) x := by
    intro y hy
    rw [he]
    exact hn y hy
  have hnhds := Icc_mem_nhds hx.1 hx.2
  have hs := second_nonneg_of_localMin (hm.isLocalMin hnhds) (hc.continuousAt hnhds)
  have hforce := hd x hx
  rw [he] at hforce
  linarith

private theorem floor_eq_between (a b c : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊=⌊Real.exp (2*a.1)⌋₊) (hc : c.1∈Icc a.1 b.1) :
    ⌊Real.exp (2*c.1)⌋₊=⌊Real.exp (2*a.1)⌋₊ := by
  have hl := Nat.floor_mono (Real.exp_le_exp.mpr (show 2*a.1 ≤ 2*c.1 by linarith [hc.1]))
  have hr := Nat.floor_mono (Real.exp_le_exp.mpr (show 2*c.1 ≤ 2*b.1 by linarith [hc.2]))
  exact le_antisymm (hr.trans hf.le) hl

private theorem chamber_continuousOn (a b : SuzukiPositiveAperture) :
    ContinuousOn (ccmWeilOddPoleChamber a) (Icc a.1 b.1) := by
  intro s hs
  exact (differentiableAt_ccmWeilOddPoleChamber a (by linarith [a.2,hs.1])).continuousAt.continuousWithinAt

private theorem chamber_force (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊=⌊Real.exp (2*a.1)⌋₊) (ha : 2 ≤ a.1) :
    ∀ s∈Ioo a.1 b.1, deriv (deriv (ccmWeilOddPoleChamber a)) s-ccmWeilOddPoleChamber a s < 0 := by
  intro s hs
  let c : SuzukiPositiveAperture := ⟨s,by linarith [a.2,hs.1]⟩
  exact ccmWeilOddPoleChamber_shifted_second_neg a c
    (floor_eq_between a b c hf ⟨hs.1.le,hs.2.le⟩) (by dsimp [c]; linarith [hs.1])

/-- Nonnegative actual odd energies at two radii in one cutoff chamber force
strictly positive actual odd energy at every intermediate radius, once the left radius is at least two. -/
theorem ccmWeilOddPole_pos_between_same_cutoff (a b c : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊=⌊Real.exp (2*a.1)⌋₊) (ha : 2 ≤ a.1) (hc : c.1∈Ioo a.1 b.1)
    (hQa : 0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)))
    (hQb : 0 ≤ ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b (-1))) :
    0 < ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c (-1)) := by
  rw [ccmWeilOddPole_eq_chamber_of_floor_eq a a rfl] at hQa
  rw [ccmWeilOddPole_eq_chamber_of_floor_eq a b hf] at hQb
  rw [ccmWeilOddPole_eq_chamber_of_floor_eq a c (floor_eq_between a b c hf ⟨hc.1.le,hc.2.le⟩)]
  exact interval_pos_of_shifted_second_neg (chamber_continuousOn a b) (chamber_force a b hf ha) hQa hQb c.1 hc

/-- Exact actual-source endpoint criterion on each fixed prime cutoff chamber above radius two. -/
theorem ccmWeilOddPole_nonneg_interval_iff_endpoints (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊=⌊Real.exp (2*a.1)⌋₊) (ha : 2 ≤ a.1) (hab : a.1 ≤ b.1) :
    (∀ c : SuzukiPositiveAperture, c.1∈Icc a.1 b.1 →
      0 ≤ ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c (-1))) ↔
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) ∧
      0 ≤ ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b (-1)) := by
  constructor
  · intro h
    exact ⟨h a ⟨le_rfl,hab⟩,h b ⟨hab,le_rfl⟩⟩
  · rintro ⟨hQa,hQb⟩ c hc
    rw [ccmWeilOddPole_eq_chamber_of_floor_eq a a rfl] at hQa
    rw [ccmWeilOddPole_eq_chamber_of_floor_eq a b hf] at hQb
    rw [ccmWeilOddPole_eq_chamber_of_floor_eq a c (floor_eq_between a b c hf hc)]
    exact interval_nonneg_of_shifted_second_neg (chamber_continuousOn a b) (chamber_force a b hf ha) hQa hQb c.1 hc

end RHTower
