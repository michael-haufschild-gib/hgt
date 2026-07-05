/-
A Jensen quotient below two certifies a simple zero with zero-free difference quotient.

Jensen's inequality bounds the zero divisor mass of an analytic function on `closedBall c r` by
`log(M/‖f c‖)/log(R/r)`, given a sup bound `M` on the outer circle and a nonzero anchor at the
center.  When that quotient is below two the divisor mass is at most one, so a known zero `ρ'`
in the inner ball is the ONLY zero there and it is simple: the difference quotient
`dslope f ρ'` is zero-free on the inner ball and the derivative at the zero does not vanish.
Instantiated at the finite carrier `gN`, this produces from scalar data exactly the one-zero
window structure — zero-free cofactor, exact factorization, nonvanishing derivative — that the
minimum-modulus floor and the derivative-floor producers consume.
-/
import GaloisForLFunctions.RHTower.CarrierSlope

open Complex Metric

namespace RHTower

/-- **Simple-zero structure from a Jensen quotient below two.**  An analytic function on
`closedBall c R` with nonzero center anchor, sup `M` on the outer circle, and Jensen quotient
`log(M/‖f c‖)/log(R/r) < 2` has at a known zero `ρ' ∈ closedBall c r` its ONLY inner-ball zero,
simple: the derivative at `ρ'` does not vanish, `f` is zero-free on `closedBall c r ∖ {ρ'}`,
and the difference quotient `dslope f ρ'` is zero-free on the whole inner closed ball. -/
theorem simple_zero_structure_of_jensen {f : ℂ → ℂ} {c ρ' : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hfc : f c ≠ 0) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    (hjensen : Real.log (M / ‖f c‖) / Real.log (R / r) < 2)
    (hρ' : ρ' ∈ closedBall c r) (hzero : f ρ' = 0) :
    deriv f ρ' ≠ 0 ∧
      (∀ z ∈ closedBall c r, z ≠ ρ' → f z ≠ 0) ∧
      ∀ z ∈ closedBall c r, dslope f ρ' z ≠ 0 := by
  have hR : 0 < R := lt_trans hr hrR
  have hsub : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall hrR.le
  have hρR : ρ' ∈ closedBall c R := hsub hρ'
  have hfsub : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono hsub
  -- order is finite everywhere (identity theorem against the anchor)
  have hpre : IsPreconnected (closedBall c R) := (convex_closedBall c R).isPreconnected
  have hcmem : c ∈ closedBall c R := mem_closedBall_self hR.le
  have hordfin : ∀ z ∈ closedBall c R, analyticOrderAt f z ≠ ⊤ := by
    intro z hz htop
    have hev : f =ᶠ[nhds z] 0 := analyticOrderAt_eq_top.mp htop
    exact hfc (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hz hev hcmem)
  -- Jensen: the total inner divisor mass is at most one
  have hrabs : |r| = r := abs_of_pos hr
  have hRabs : |R| = R := abs_of_pos hR
  have hsum := AnalyticOnNhd.sum_divisor_le (c := c) (f := f) (M := M)
    (r := r) (R := R)
    (by rw [hrabs]; exact hr) (by rw [hrabs, hRabs]; exact hrR) hM
    (by rw [hRabs]; exact hf) hfc (by rw [hRabs]; exact hbound)
  rw [hrabs] at hsum
  set D := MeromorphicOn.divisor f (closedBall c r) with hD_def
  have hsum1 : (∑ᶠ u, D u) ≤ 1 := by
    have h2 : ((∑ᶠ u, D u : ℤ) : ℝ) < 2 := lt_of_le_of_lt hsum hjensen
    have h3 : (∑ᶠ u, D u) < 2 := by exact_mod_cast h2
    omega
  have hDnn : ∀ u, 0 ≤ D u := fun u => by
    simpa using (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfsub) u
  have hDap : ∀ z ∈ closedBall c r,
      D z = ((analyticOrderAt f z).map (Nat.cast)).untop₀ := fun z hz =>
    MeromorphicOn.AnalyticOnNhd.divisor_apply hfsub hz
  -- the divisor value at any inner point is the (finite) analytic order
  have hDord : ∀ z ∈ closedBall c r, ∀ n : ℕ, analyticOrderAt f z = n → D z = n := by
    intro z hz n hn
    rw [hDap z hz, hn]
    simp
  -- at ρ' the order is at least one
  have hordρ0 : analyticOrderAt f ρ' ≠ 0 := fun h0 =>
    ((hf ρ' hρR).analyticOrderAt_eq_zero.mp h0) hzero
  obtain ⟨nρ, hnρ⟩ := WithTop.ne_top_iff_exists.mp (hordfin ρ' hρR)
  have hnρ0 : nρ ≠ 0 := by
    intro h0
    rw [h0] at hnρ
    exact hordρ0 hnρ.symm
  have hDρ : D ρ' = nρ := hDord ρ' hρ' nρ hnρ.symm
  have hDρ1 : 1 ≤ D ρ' := by
    rw [hDρ]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnρ0
  -- finite support bookkeeping
  have hfin := D.finiteSupport (isCompact_closedBall c r)
  have hρS : ρ' ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    omega
  have hDρsum : D ρ' ≤ ∑ᶠ u, D u := by
    rw [finsum_eq_sum _ hfin]
    exact Finset.single_le_sum (fun i _ => hDnn i) hρS
  -- every other inner point carries divisor zero
  have hDother : ∀ u ∈ closedBall c r, u ≠ ρ' → D u = 0 := by
    intro u hu hne
    by_contra hDu
    have huS : u ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Function.mem_support]
      exact hDu
    have hadd : D u + D ρ' ≤ ∑ k ∈ hfin.toFinset, D k :=
      Finset.add_le_sum (fun i _ => hDnn i) huS hρS hne
    rw [← finsum_eq_sum _ hfin] at hadd
    have hDu1 : 1 ≤ D u := by
      have := hDnn u
      omega
    omega
  -- other points are non-zeros of f
  have hfother : ∀ z ∈ closedBall c r, z ≠ ρ' → f z ≠ 0 := by
    intro z hz hne
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hordfin z (hsub hz))
    have hDz : D z = n := hDord z hz n hn.symm
    rw [hDother z hz hne] at hDz
    have hn0 : n = 0 := by exact_mod_cast hDz.symm
    rw [hn0] at hn
    exact (hf z (hsub hz)).analyticOrderAt_eq_zero.mp hn.symm
  -- the zero at ρ' is simple
  have hord1 : analyticOrderAt f ρ' = 1 := by
    have hnρ1 : nρ = 1 := by
      have : D ρ' ≤ 1 := le_trans hDρsum hsum1
      rw [hDρ] at this
      have : nρ ≤ 1 := by exact_mod_cast this
      omega
    rw [← hnρ, hnρ1]
    rfl
  have hfa : AnalyticAt ℂ f ρ' := hf ρ' hρR
  have hderiv : deriv f ρ' ≠ 0 := by
    have hkey := hfa.analyticOrderAt_deriv_add_one
    simp only [hzero, sub_zero] at hkey
    rw [hord1] at hkey
    have hord0 : analyticOrderAt (deriv f) ρ' = 0 := by
      cases hor : analyticOrderAt (deriv f) ρ' with
      | top => rw [hor] at hkey; simp at hkey
      | coe k =>
        rw [hor] at hkey
        norm_cast at hkey ⊢
        omega
    exact (hfa.deriv.analyticOrderAt_eq_zero).mp hord0
  refine ⟨hderiv, hfother, ?_⟩
  intro z hz
  rcases eq_or_ne z ρ' with rfl | hne
  · rw [dslope_same]
    exact hderiv
  · rw [dslope_of_ne _ hne, slope_def_field, hzero, sub_zero]
    exact div_ne_zero (hfother z hz hne) (sub_ne_zero.mpr hne)

/-- **One-zero carrier window from Jensen scalars.**  A nonzero carrier anchor at the center,
a carrier sup `M` on the outer circle, a Jensen quotient below two, and one known carrier zero
in the inner ball produce the complete one-zero window structure consumed by the
minimum-modulus floor and the derivative-floor producers: the difference quotient is analytic
and zero-free on the inner ball, factors the carrier exactly, and the derivative at the zero
does not vanish. -/
theorem gN_one_zero_window_of_jensen {N : ℕ} {c ρ' : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hball : ∀ z ∈ closedBall c R, z.re < 1)
    (hfc : gN N c ≠ 0) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere c R, ‖gN N z‖ ≤ M)
    (hjensen : Real.log (M / ‖gN N c‖) / Real.log (R / r) < 2)
    (hρ' : ρ' ∈ closedBall c r) (hzero : gN N ρ' = 0) :
    AnalyticOnNhd ℂ (dslope (gN N) ρ') (ball c r) ∧
      (∀ z ∈ ball c r, dslope (gN N) ρ' z ≠ 0) ∧
      (∀ z ∈ ball c r, gN N z = (z - ρ') * dslope (gN N) ρ' z) ∧
      deriv (gN N) ρ' ≠ 0 := by
  have hsub : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall hrR.le
  have hgan : AnalyticOnNhd ℂ (gN N) (closedBall c R) := by
    intro z hz
    exact gN_analyticAt (Gammaℝ_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re]
      linarith [hball z hz]))
  obtain ⟨hderiv, _, hds0⟩ := simple_zero_structure_of_jensen hr hrR hgan hfc hM
    hbound hjensen hρ' hzero
  have hρR : ρ' ∈ closedBall c R := hsub hρ'
  refine ⟨?_, ?_, ?_, hderiv⟩
  · intro z hz
    exact analyticAt_dslope_of_analyticAt (hgan ρ' hρR)
      (hgan z (hsub (ball_subset_closedBall hz)))
  · intro z hz
    exact hds0 z (ball_subset_closedBall hz)
  · intro z _
    have hs := sub_smul_dslope (gN N) ρ' z
    rw [hzero, sub_zero, smul_eq_mul] at hs
    exact hs.symm

end RHTower

namespace RHTower

/-- **One-zero window package from signs and Jensen scalars.**  A sign change of the (real)
completed carrier between two line heights inside `closedBall c rz`, a nonzero carrier anchor
at `c`, a carrier sup on the outer Jensen circle, and a Jensen quotient below two together
produce an on-line point `ρ'` near `c` that is a zero of both the completed and the finite
carrier, together with the complete one-zero window structure: the difference quotient of the
carrier is analytic and zero-free on the inner Jensen ball, factors the carrier exactly, and
the carrier derivative at `ρ'` does not vanish.  Every hypothesis is one-dimensional or scalar
data anchored at the known center. -/
theorem carrier_one_zero_package_of_signs_jensen {N : ℕ} {c : ℂ}
    {t₁ t₂ rz rJ RJ M_J : ℝ}
    (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂)
    (hrz0 : 0 < rz) (hrzJ : rz ≤ rJ) (hrJR : rJ < RJ)
    (hstrip : ∀ z ∈ closedBall c RJ, 0 < z.re ∧ z.re < 1)
    (hbr : ∀ τ ∈ Set.Icc t₁ t₂,
      ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I ∈ closedBall c rz)
    (hsign : (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
      * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0)
    (hfc : gN N c ≠ 0) (hMJ : 1 ≤ M_J)
    (hbound : ∀ z ∈ sphere c RJ, ‖gN N z‖ ≤ M_J)
    (hjensen : Real.log (M_J / ‖gN N c‖) / Real.log (RJ / rJ) < 2) :
    ∃ ρ' : ℂ, ρ'.re = 1 / 2 ∧ ρ' ∈ closedBall c rz ∧
      completedGN N ρ' = 0 ∧ gN N ρ' = 0 ∧
      AnalyticOnNhd ℂ (dslope (gN N) ρ') (ball c rJ) ∧
      (∀ z ∈ ball c rJ, dslope (gN N) ρ' z ≠ 0) ∧
      (∀ z ∈ ball c rJ, gN N z = (z - ρ') * dslope (gN N) ρ' z) ∧
      deriv (gN N) ρ' ≠ 0 := by
  obtain ⟨τ, hτmem, hτzero⟩ := exists_online_carrier_zero_of_sign_change N h12 hsign
  set ρ' : ℂ := ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I with hρ'def
  have hρre : ρ'.re = 1 / 2 := by simp [hρ'def]
  have hρim : ρ'.im = τ := by simp [hρ'def]
  have hρrz : ρ' ∈ closedBall c rz := hbr τ hτmem
  have hτpos : 0 < τ := lt_of_lt_of_le ht₁ hτmem.1
  have hρ0 : ρ' ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [hρim] at this
    simp at this
    linarith
  have hρ1 : ρ' ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [hρim] at this
    simp at this
    linarith
  have hGne : Gammaℝ ρ' ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rw [hρre]; norm_num)
  have harch0 : archFactor ρ' ≠ 0 :=
    mul_ne_zero
      (div_ne_zero (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)) two_ne_zero) hGne
  have hgzero : gN N ρ' = 0 := by
    have hmul : archFactor ρ' * gN N ρ' = 0 := hτzero
    exact (mul_eq_zero.mp hmul).resolve_left harch0
  have hρrJ : ρ' ∈ closedBall c rJ := (closedBall_subset_closedBall hrzJ) hρrz
  obtain ⟨hdan, hd0, hdfact, hdderiv⟩ := gN_one_zero_window_of_jensen
    (lt_of_lt_of_le hrz0 hrzJ) hrJR (fun z hz => (hstrip z hz).2)
    hfc hMJ hbound hjensen hρrJ hgzero
  exact ⟨ρ', hρre, hρrz, hτzero, hgzero, hdan, hd0, hdfact, hdderiv⟩

end RHTower
