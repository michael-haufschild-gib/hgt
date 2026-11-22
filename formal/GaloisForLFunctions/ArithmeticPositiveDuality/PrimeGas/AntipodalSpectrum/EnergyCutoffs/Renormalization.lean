import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.Recursion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.Divisor
import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedMellin

/-!
# Renormalized finite heat measurements of zeta zeros

Subtracting the power divergence predicted by the square-root density
gives a convergent cutoff on the open right half-plane away from one.
The cutoff recursion transmits the radial zeta limit to the physical sum.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open Filter
open scoped Topology

private def powerTerm (X : ℕ) (w : ℂ) := (X:ℂ)^(1-w)/(1-w)

/-- The heat through product X² minus the density counterterm (2/(C−1))·X^(1−w)/(1−w). -/
def renormalizedCutoff (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :=
  shellCutoff t j X w - (2/((tailRadix t j).val-1:ℂ))*powerTerm X w

/-- A contraction at the quotient cutoff transmits an asymptotically vanishing error. -/
private theorem quotient_contraction (C : ℕ) (hC : 1 < C) (q : ℂ) (hq : ‖q‖ < 1)
    (u : ℕ → ℂ) (hv : Tendsto (fun n => u n-q*u (n/C)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  let v (n : ℕ) := u n-q*u (n/C)
  have herr (n : ℕ) : ‖u n‖ ≤ ‖v n‖+‖q‖*‖u (n/C)‖ := by
    calc ‖u n‖ = ‖v n+q*u (n/C)‖ := by rw [v,sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans_eq (by rw [norm_mul])
  obtain ⟨A,hA⟩ := (Metric.isBounded_range_of_tendsto v hv).exists_norm_le
  let B := max ‖u 0‖ (A/(1-‖q‖))
  have hq' : 0 < 1-‖q‖ := sub_pos.mpr hq
  have hB : A ≤ B*(1-‖q‖) := (div_le_iff₀ hq').mp (le_max_right _ _)
  have hub (n : ℕ) : ‖u n‖ ≤ B := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact le_max_left _ _
      · have h := add_le_add (hA (v n) ⟨n,rfl⟩)
          (mul_le_mul_of_nonneg_left (ih _ (Nat.div_lt_self hn hC)) (norm_nonneg q))
        exact (herr n).trans (h.trans (by linarith only [hB]))
  have hdiv := Nat.tendsto_div_const_atTop (Nat.zero_lt_one.trans hC).ne'
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hv' : ∀ᶠ n : ℕ in atTop, ‖v n‖ < (ε/2)*(1-‖q‖) := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hv _ (mul_pos (half_pos hε) hq'))
  have step (k : ℕ) : ∀ᶠ n : ℕ in atTop, ‖u n‖ ≤ ε/2+‖q‖^k*B := by
    induction k with
    | zero =>
      simpa only [pow_zero,one_mul] using Eventually.of_forall
        (fun n => (hub n).trans (le_add_of_nonneg_left (half_pos hε).le))
    | succ k ih =>
      filter_upwards [hv',hdiv.eventually ih] with n hn hprev
      refine (herr n).trans ((add_le_add hn.le (mul_le_mul_of_nonneg_left hprev (norm_nonneg q))).trans_eq ?_)
      rw [pow_succ]
      ring
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).mul_const B
  rw [zero_mul] at hpow
  obtain ⟨k,hk⟩ := (hpow.eventually_lt_const (half_pos hε)).exists
  filter_upwards [step k] with n hn
  rw [dist_zero_right]
  linarith only [hn,hk]

private theorem radial_residual (w : ℂ) (hw : 0 < w.re) (h1 : w ≠ 1) :
    Tendsto (fun X => radialCutoff X w-powerTerm X w) atTop (𝓝 (riemannZeta w)) := by
  simpa only [radialCutoff,powerTerm,Complex.ofReal_natCast] using
    (_root_.RHTower.tendsto_sum_cpow_sub_pow hw h1)

private theorem scaled_radial_residual (C : ℕ+) (w : ℂ) (hw : 0 < w.re) (h1 : w ≠ 1) :
    Tendsto (fun X : ℕ => heat w C*radialCutoff (X/C.val) w - (C.val:ℂ)⁻¹*powerTerm X w)
      atTop (𝓝 (riemannZeta w*heat w C)) := by
  have h := _root_.RHTower.tendsto_coPoissonMellinKernel hw h1 (Nat.cast_pos.mpr C.pos : (0:ℝ) < C.val)
  simpa only [_root_.RHTower.coPoissonMellinKernel,Nat.floor_div_natCast,Nat.floor_natCast,
    Complex.ofReal_natCast,heat_eq_cpow,radialCutoff,powerTerm] using h

/-- The finite measurement after density subtraction converges in the entire open heat half-plane away from the pole. -/
theorem renormalized_cutoff_limit (t : ExceptionalTime) (j : ℕ) (z : {w : ℂ // 0 < w.re ∧ w ≠ 1}) :
    let q := heat z.val (tailRadix t j)
    Tendsto (fun X => renormalizedCutoff t j X z.val) atTop (𝓝 (2*q*riemannZeta z.val/(1-q))) := by
  let C := tailRadix t j
  let w := z.val
  let q := heat w C
  let D : ℂ := 2/((C.val:ℂ)-1)
  let L := 2*q*riemannZeta w/(1-q)
  let U (X : ℕ) := renormalizedCutoff t j X w
  have hc : 1 < C.val := radix_gt_one t j
  have hq : ‖q‖ < 1 := heat_contraction C hc w z.property.1
  have hne : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (fun he => hq.ne (by rw [← he,norm_one]))
  have hc0 : (C.val:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr C.ne_zero
  have hc1 : (C.val:ℂ) ≠ 1 := by exact_mod_cast hc.ne'
  have hd : (2+D)*(C.val:ℂ)⁻¹ = D := by
    dsimp [D]
    field_simp [hc0,sub_ne_zero.mpr hc1]
    <;> ring
  have hL : (1-q)*L = 2*q*riemannZeta w := by
    exact mul_div_cancel₀' _ hne
  have hs := (scaled_radial_residual C w z.property.1 z.property.2).const_mul (2+D)
  have hr := ((radial_residual w z.property.1 z.property.2).comp (Nat.tendsto_div_const_atTop C.ne_zero)).const_mul (D*q)
  have hgap := (hs.sub hr).sub (tendsto_const_nhds (x := (1-q)*L))
  have hz : (2+D)*(riemannZeta w*q) - D*q*riemannZeta w - (1-q)*L = 0 := by rw [hL]; ring
  change Tendsto _ atTop (𝓝 ((2+D)*(riemannZeta w*q)-D*q*riemannZeta w-(1-q)*L)) at hgap
  rw [hz] at hgap
  have hres : Tendsto (fun X : ℕ => U X-L-q*(U (X/C.val)-L)) atTop (𝓝 0) := by
    apply hgap.congr
    intro X
    change (2+D)*(q*radialCutoff (X/C.val) w-(C.val:ℂ)⁻¹*powerTerm X w) -
      D*q*(radialCutoff (X/C.val) w-powerTerm (X/C.val) w)-(1-q)*L =
      (shellCutoff t j X w-D*powerTerm X w)-L-q*(shellCutoff t j (X/C.val) w-D*powerTerm (X/C.val) w-L)
    rw [shell_cutoff_recursion t j X w]
    change _ = (q*(2*radialCutoff (X/C.val) w+shellCutoff t j (X/C.val) w)-D*powerTerm X w)-L-
      q*(shellCutoff t j (X/C.val) w-D*powerTerm (X/C.val) w-L)
    linear_combination -(powerTerm X w)*hd
  have h := (quotient_contraction C.val hc q hq (fun X => U X-L) hres).add_const L
  simpa only [sub_add_cancel,zero_add] using h

/-- Vanishing of the measured limit is exactly vanishing of zeta. -/
theorem cutoff_vanishes_iff (t : ExceptionalTime) (j : ℕ) (z : {w : ℂ // 0 < w.re ∧ w ≠ 1}) :
    Tendsto (fun X => renormalizedCutoff t j X z.val) atTop (𝓝 0) ↔ riemannZeta z.val = 0 := by
  let q := heat z.val (tailRadix t j)
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  have h1 : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (fun he =>
    (heat_contraction _ (radix_gt_one t j) _ z.property.1).ne (show ‖q‖ = 1 by rw [← he,norm_one]))
  have h := renormalized_cutoff_limit t j z
  change Tendsto _ atTop (𝓝 (2*q*riemannZeta z.val/(1-q))) at h
  constructor
  · intro hz
    have he := tendsto_nhds_unique h hz
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp he).resolve_right h1)).resolve_left (mul_ne_zero (by norm_num) hq)
  · intro hz
    simpa only [hz,mul_zero,zero_div] using h

/-- RH expressed entirely through the renormalized finite measurements and isometry of the binary split. -/
theorem rh_iff_vanishing_cutoffs_isometric (t : ExceptionalTime) (j : ℕ) :
    RiemannHypothesis ↔ ∀ s : {s : ℂ // 0 < s.re ∧ s.re < 1/2},
      Tendsto (fun X => renormalizedCutoff t j X (2*s.val)) atTop (𝓝 0) →
        ∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split (2*s.val) f x := by
  rw [rh_iff_response_zeros_isometric t]
  apply forall_congr' fun s => ?_
  have hpos : 0 < (2*s.val).re := by rw [two_mul,Complex.add_re]; linarith only [s.property.1]
  have hlt : (2*s.val).re < 1 := by rw [two_mul,Complex.add_re]; linarith only [s.property.2]
  have h1 : 2*s.val ≠ 1 := fun he => hlt.ne (by rw [he,Complex.one_re])
  rw [response_zero_iff t ⟨s.val,s.property.1⟩,cutoff_vanishes_iff t j ⟨2*s.val,hpos,h1⟩]

#print axioms renormalized_cutoff_limit
#print axioms cutoff_vanishes_iff
#print axioms rh_iff_vanishing_cutoffs_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
