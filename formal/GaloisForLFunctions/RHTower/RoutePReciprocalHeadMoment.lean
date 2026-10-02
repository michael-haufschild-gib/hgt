import GaloisForLFunctions.RHTower.DivisorContinuousHeadMellin
import GaloisForLFunctions.RHTower.MobiusDivisorUniformLocalRegularity
import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreInterpolation
import GaloisForLFunctions.RHTower.MobiusDivisorShellAnchorDebt

/-!
# Fresh reciprocal-prime mass forces a critical head spike

The inverse-five-halves moment of the literal finite-core head is positive
and factors by the reciprocal Euler product. Fresh helpers leave the entire
earlier head unchanged. Uniform critical linear envelopes on the remaining
tail therefore force the Euler-product loss to vanish as its admission clock
escapes. This controls actual head values, not a sufficient norm upper bound.

A fixed positive reciprocal mass of arbitrarily late helpers consequently
forces the retained head itself, and hence the complete retained energy, to
exceed every fixed critical square budget after the admission horizon.
The result concerns finite processed cores. It does not bound or refute the
complete native Route-P history, whose signed payment remains open.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Finset Filter Topology
namespace RHTower

def routePReciprocalHeadMoment (P : Finset ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x ^ (-(5/2 : ℝ)) * mobiusDivisorContinuousHead P x

private theorem moment_integrand (P : Finset ℕ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-(3/2 : ℂ)-1) * (mobiusDivisorContinuousHead P x : ℂ) =
      ((x ^ (-(5/2 : ℝ)) * mobiusDivisorContinuousHead P x : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.le]
  congr 2
  push_cast
  ring

theorem routeP_reciprocal_head_moment_integrable (P : Finset ℕ) :
    IntegrableOn (fun x => x ^ (-(5/2 : ℝ)) * mobiusDivisorContinuousHead P x) (Ioi 0) := by
  have h := mellinConvergent_mobiusDivisorContinuousHead P (s := (3/2 : ℂ)) (by norm_num)
  apply h.re.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ((x : ℂ) ^ (-(3/2 : ℂ)-1) * (mobiusDivisorContinuousHead P x : ℂ)).re = _
  rw [moment_integrand P hx]
  rfl

private theorem moment_re (P : Finset ℕ) :
    (mellin (fun x => (mobiusDivisorContinuousHead P x : ℂ)) (-(3/2 : ℂ))).re =
      routePReciprocalHeadMoment P := by
  have hi := mellinConvergent_mobiusDivisorContinuousHead P (s := (3/2 : ℂ)) (by norm_num)
  have hr := integral_re hi
  simp only [RCLike.re_to_complex] at hr
  rw [mellin, ← hr]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change ((x : ℂ) ^ (-(3/2 : ℂ)-1) * (mobiusDivisorContinuousHead P x : ℂ)).re = _
  rw [moment_integrand P hx]
  rfl

theorem routeP_reciprocal_head_moment_euler (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    routePReciprocalHeadMoment P =
      (∏ p ∈ P, (1-1/(p : ℝ))) * routePReciprocalHeadMoment ∅ := by
  have he : divisorCoreMellinEuler P (3/2 : ℂ) =
      (((∏ p ∈ P, (1-1/(p : ℝ))) : ℝ) : ℂ) := by
    rw [divisorCoreMellinEuler, Complex.ofReal_prod]
    apply prod_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have harg : (1/2-(3/2 : ℂ))*(Real.log p : ℂ) = -(Real.log p : ℂ) := by ring
    rw [harg, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hp0]
    push_cast
    simp only [one_div]
  have h := congrArg Complex.re
    (mellin_mobiusDivisorContinuousHead_euler P hP (s := (3/2 : ℂ)) (by norm_num))
  have hu : (fun x : ℝ => (divisorContinuousUnitHead x : ℂ)) =
      (fun x => (mobiusDivisorContinuousHead ∅ x : ℂ)) := by
    funext x
    simp [mobiusDivisorContinuousHead]
  rw [he, hu, Complex.re_ofReal_mul, moment_re, moment_re] at h
  exact h

theorem routeP_reciprocal_head_moment_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 < routePReciprocalHeadMoment P := by
  rw [routeP_reciprocal_head_moment_euler P hP]
  apply mul_pos
  · apply prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    have h : 1/(p : ℝ) < 1 := (div_lt_one (by linarith : (0 : ℝ) < p)).mpr hp1
    linarith
  · unfold routePReciprocalHeadMoment
    apply (integral_pos_iff_support_of_nonneg_ae _ (routeP_reciprocal_head_moment_integrable ∅)).mpr
    · have hsub : Ioo (1 : ℝ) 2 ⊆ Function.support
          (fun x => x ^ (-(5/2 : ℝ)) * mobiusDivisorContinuousHead ∅ x) := by
        intro x hx
        have he : mobiusDivisorContinuousHead ∅ x = divisorContinuousUnitHead x := by
          simp [mobiusDivisorContinuousHead]
        rw [Function.mem_support, he]
        exact (mul_pos (Real.rpow_pos_of_pos (by linarith [hx.1]) _)
          (divisorContinuousUnitHead_pos_first hx)).ne'
      apply lt_of_lt_of_le _ (measure_mono hsub)
      rw [Measure.restrict_apply measurableSet_Ioo,
        inter_eq_left.mpr (show Ioo (1 : ℝ) 2 ⊆ Ioi 0 from fun x hx => by
          change 0 < x; linarith [hx.1]), Real.volume_Ioo]
      norm_num
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa [mobiusDivisorContinuousHead] using
        mul_nonneg (Real.rpow_nonneg hx.le (-(5/2 : ℝ))) (divisorContinuousUnitHead_nonneg x)

theorem routeP_reciprocal_head_moment_stability (P Q : Finset ℕ)
    {B C D : ℝ} (hB : 1 ≤ B)
    (hearly : ∀ x : ℝ, x ≤ B → mobiusDivisorContinuousHead P x = mobiusDivisorContinuousHead Q x)
    (hP : ∀ x : ℝ, B < x → |mobiusDivisorContinuousHead P x| ≤ C*x)
    (hQ : ∀ x : ℝ, B < x → |mobiusDivisorContinuousHead Q x| ≤ D*x) :
    |routePReciprocalHeadMoment P-routePReciprocalHeadMoment Q| ≤
      2*(C+D)/Real.sqrt B := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  let f := fun x : ℝ => x ^ (-(5/2 : ℝ)) *
    (mobiusDivisorContinuousHead P x-mobiusDivisorContinuousHead Q x)
  have hi : IntegrableOn f (Ioi 0) := by
    have h := (routeP_reciprocal_head_moment_integrable P).sub
      (routeP_reciprocal_head_moment_integrable Q)
    apply h.congr
    filter_upwards with x
    simp only [f, Pi.sub_apply]
    ring
  have he : routePReciprocalHeadMoment P-routePReciprocalHeadMoment Q =
      ∫ x in Ioi B, f x := by
    unfold routePReciprocalHeadMoment
    rw [← integral_sub (routeP_reciprocal_head_moment_integrable P)
      (routeP_reciprocal_head_moment_integrable Q)]
    simp_rw [← mul_sub]
    change (∫ x in Ioi (0 : ℝ), f x) = _
    have hsplit := setIntegral_union (Ioc_disjoint_Ioi (a := (0 : ℝ)) le_rfl)
      measurableSet_Ioi (hi.mono_set (fun x hx => hx.1))
      (hi.mono_set (Ioi_subset_Ioi hB0.le))
    rw [Ioc_union_Ioi_eq_Ioi hB0.le] at hsplit
    have hz : (∫ x in Ioc (0 : ℝ) B, f x) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      simp [f, hearly x hx.2]
    rwa [hz, zero_add] at hsplit
  rw [he]
  have hig := (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2 : ℝ) < -1) hB0).const_mul (C+D)
  have him := hi.mono_set (Ioi_subset_Ioi hB0.le)
  calc
    _ ≤ ∫ x in Ioi B, |f x| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume.restrict (Ioi B)) f
    _ ≤ ∫ x in Ioi B, (C+D)*x ^ (-(3/2 : ℝ)) := by
      apply setIntegral_mono_on him.abs hig measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := hB0.trans hx
      have hb := (abs_sub _ _).trans (add_le_add (hP x hx) (hQ x hx))
      have hr0 : 0 ≤ x ^ (-(5/2 : ℝ)) := Real.rpow_nonneg hx0.le _
      dsimp [f]
      rw [abs_mul, abs_of_nonneg hr0]
      apply (mul_le_mul_of_nonneg_left hb hr0).trans_eq
      rw [show -(3/2 : ℝ) = -(5/2)+1 by ring, Real.rpow_add hx0, Real.rpow_one]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hB0]
      rw [show -(3/2 : ℝ)+1 = -(1/2) by ring, Real.rpow_neg hB0.le, ← Real.sqrt_eq_rpow]
      ring

private theorem head_agrees_below_fresh (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ p ∈ S, p.Prime) (hdis : Disjoint P S)
    {B : ℝ} (hfresh : ∀ p ∈ S, B < (p : ℝ)) {x : ℝ} (hx : x ≤ B) :
    mobiusDivisorContinuousHead (P ∪ S) x = mobiusDivisorContinuousHead P x := by
  have hxp (p : ℕ) (hp : p ∈ S) : x ≤ (p : ℝ) := hx.trans (hfresh p hp).le
  rw [head_shell_over_base P S hP hS hdis]
  · have hz : (∑ p ∈ S, Real.sqrt p * mobiusDivisorContinuousHead P (x/p)) = 0 := by
      apply sum_eq_zero
      intro p hp
      rw [mobiusDivisorContinuousHead_eq_zero P
        ((div_le_one (by exact_mod_cast (hS p hp).pos)).mpr (hxp p hp)), mul_zero]
    rw [hz, sub_zero]
  · intro p hp q hq
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (hS q hq).one_lt.le
    exact (hxp p hp).trans (by nlinarith only [mul_nonneg hp0 (sub_nonneg.mpr hq1)])

private theorem density_le_exp (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, (1-1/(p : ℝ))) ≤ Real.exp (-(∑ p ∈ S, 1/(p : ℝ))) := by
  calc
    _ ≤ ∏ p ∈ S, Real.exp (-(1/(p : ℝ))) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_lt.le
        have h := (div_le_one (by exact_mod_cast (hS p hp).pos : (0 : ℝ) < p)).mpr hp1
        linarith
      · intro p _
        simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(1/(p : ℝ)))
    _ = _ := by rw [← Real.exp_sum, sum_neg_distrib]

/-- Fresh reciprocal mass has an actual critical-head cost, independently of all helper signs. -/
theorem routeP_fresh_helper_reciprocal_mass_cost (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ p ∈ S, p.Prime) (hdis : Disjoint P S)
    {B C D : ℝ} (hB : 1 ≤ B)
    (hfresh : ∀ p ∈ S, B < (p : ℝ))
    (hparent : ∀ x : ℝ, B < x → |mobiusDivisorContinuousHead P x| ≤ C*x)
    (hprepared : ∀ x : ℝ, B < x → |mobiusDivisorContinuousHead (P ∪ S) x| ≤ D*x) :
    routePReciprocalHeadMoment P * (1-Real.exp (-(∑ p ∈ S, 1/(p : ℝ)))) ≤
      2*(C+D)/Real.sqrt B := by
  have hQ : ∀ p ∈ P ∪ S, p.Prime := fun p hp => (mem_union.mp hp).elim (hP p) (hS p)
  have hm := routeP_reciprocal_head_moment_pos P hP
  have he : routePReciprocalHeadMoment (P ∪ S) =
      routePReciprocalHeadMoment P * (∏ p ∈ S, (1-1/(p : ℝ))) := by
    rw [routeP_reciprocal_head_moment_euler (P ∪ S) hQ,
      routeP_reciprocal_head_moment_euler P hP, prod_union hdis]
    ring
  have hstable := routeP_reciprocal_head_moment_stability P (P ∪ S) hB
    (fun x hx => (head_agrees_below_fresh P S hP hS hdis hfresh hx).symm) hparent hprepared
  calc
    _ ≤ routePReciprocalHeadMoment P * (1-(∏ p ∈ S, (1-1/(p : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left (by linarith [density_le_exp S hS]) hm.le
    _ = routePReciprocalHeadMoment P-routePReciprocalHeadMoment (P ∪ S) := by rw [he]; ring
    _ ≤ |routePReciprocalHeadMoment P-routePReciprocalHeadMoment (P ∪ S)| := le_abs_self _
    _ ≤ _ := hstable

private theorem continuous_head_bound_of_square_tail (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {B K : ℝ} (hB : 1 ≤ B) (hK : 0 ≤ K)
    (hbudget : ∀ M : ℕ, B < (M : ℝ) → mobiusDivisorSelectionFibre M P ∅ ^ 2 ≤ K*(M : ℝ)^2) :
    ∀ x : ℝ, B < x → |mobiusDivisorContinuousHead P x| ≤ 2*(Real.sqrt K+24)*x := by
  intro x hx
  let N := ⌈x⌉₊
  have hx1 : 1 ≤ x := hB.trans hx.le
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hxN : x ≤ (N : ℝ) := Nat.le_ceil x
  have hN1 : (1 : ℝ) ≤ N := hx1.trans hxN
  have hNB : B < (N : ℝ) := hx.trans_le hxN
  have hNx : (N : ℝ) < x+1 := Nat.ceil_lt_add_one hx0
  have hN2 : (N : ℝ) ≤ 2*x := by linarith
  have hsN : Real.sqrt N ≤ (N : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have he : mobiusDivisorSelectionFibre N P ∅ ^ 2 ≤ K*(N : ℝ)^2 :=
    hbudget N hNB
  have hsq : (Real.sqrt K*(N : ℝ))^2 = K*(N : ℝ)^2 := by
    rw [mul_pow, Real.sq_sqrt hK]
  have hh : |mobiusDivisorContinuousHead P N| ≤ Real.sqrt K*N := by
    rw [mobiusDivisorContinuousHead_nat P hP]
    have ha := abs_nonneg (mobiusDivisorSelectionFibre N P ∅)
    have hb : 0 ≤ Real.sqrt K*(N : ℝ) := by positivity
    nlinarith [sq_abs (mobiusDivisorSelectionFibre N P ∅)]
  have hd : |x-(N : ℝ)| ≤ 1 := by rw [abs_of_nonpos (by linarith)]; linarith
  have hl := (abs_mobiusDivisorContinuousHead_sub_le P N hxN le_rfl).trans
    (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 24*Real.sqrt N))
  calc
    _ = |(mobiusDivisorContinuousHead P x-mobiusDivisorContinuousHead P N)+
        mobiusDivisorContinuousHead P N| := by congr 1; ring
    _ ≤ |mobiusDivisorContinuousHead P x-mobiusDivisorContinuousHead P N|+
        |mobiusDivisorContinuousHead P N| := abs_add_le _ _
    _ ≤ 24*(N : ℝ)+Real.sqrt K*N := by nlinarith
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg K]

/-- A fixed positive fresh reciprocal mass forces the literal retained head itself
to exceed every proposed critical square budget after its admission horizon. -/
theorem routeP_fresh_reciprocal_mass_forces_head_spike (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {η : ℝ} (hη : 0 < η) {K : ℝ} (hK : 0 ≤ K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ X : ℝ, B ≤ X → ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → Disjoint P S → (∀ p ∈ S, X < (p : ℝ)) →
      η ≤ (∑ p ∈ S, 1/(p : ℝ)) →
      ∃ M : ℕ, X < (M : ℝ) ∧ K*(M : ℝ)^2 < mobiusDivisorSelectionFibre M (P ∪ S) ∅ ^ 2 := by
  obtain ⟨C, hC, hparent⟩ := exists_bound_mobiusDivisorContinuousHead P
  let D := 2*(Real.sqrt K+24)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let δ := routePReciprocalHeadMoment P*(1-Real.exp (-η))
  have hδ : 0 < δ := by
    apply mul_pos (routeP_reciprocal_head_moment_pos P hP)
    have h := Real.exp_lt_one_iff.mpr (show -η < 0 by linarith)
    linarith
  let a := 2*(C+D)/δ+1
  have ha : 1 ≤ a := by
    have hnon : 0 ≤ 2*(C+D)/δ := by positivity
    dsimp [a]
    linarith
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  let B := a^2
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hstrict : 2*(C+D)/Real.sqrt B < δ := by
    rw [show Real.sqrt B = a by dsimp [B]; rw [Real.sqrt_sq_eq_abs, abs_of_pos ha0]]
    apply (div_lt_iff₀ ha0).mpr
    dsimp [a]
    have hc : 2*(C+D)/δ*δ = 2*(C+D) := div_mul_cancel₀ _ hδ.ne'
    nlinarith
  refine ⟨B, hB, ?_⟩
  intro X hBX S hS hdis hfresh hmass
  have hX : 1 ≤ X := hB.trans hBX
  have hstrictX : 2*(C+D)/Real.sqrt X < δ :=
    (div_le_div_of_nonneg_left (by positivity)
      (Real.sqrt_pos.mpr (zero_lt_one.trans_le hB)) (Real.sqrt_le_sqrt hBX)).trans_lt hstrict
  by_contra hn
  push Not at hn
  have hQ : ∀ p ∈ P ∪ S, p.Prime := fun p hp => (mem_union.mp hp).elim (hP p) (hS p)
  have hprepared := continuous_head_bound_of_square_tail (P ∪ S) hQ hX hK hn
  have hpbound : ∀ x : ℝ, X < x → |mobiusDivisorContinuousHead P x| ≤ C*x := by
    intro x hx
    have hx1 : 1 ≤ x := hX.trans hx.le
    have hs : Real.sqrt x ≤ x := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    exact (hparent x).trans (mul_le_mul_of_nonneg_left hs hC)
  have hcost := routeP_fresh_helper_reciprocal_mass_cost P S hP hS hdis hX
    hfresh hpbound hprepared
  have hexp : Real.exp (-(∑ p ∈ S, 1/(p : ℝ))) ≤ Real.exp (-η) :=
    Real.exp_le_exp.mpr (by linarith)
  have hδle : δ ≤ routePReciprocalHeadMoment P*(1-Real.exp (-(∑ p ∈ S, 1/(p : ℝ)))) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (routeP_reciprocal_head_moment_pos P hP).le
  exact (not_lt_of_ge (hδle.trans hcost)) hstrictX

/-- The head spike also forces the complete retained source energy to exceed the budget. -/
theorem routeP_fresh_reciprocal_mass_forces_energy_spike (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {η : ℝ} (hη : 0 < η) {K : ℝ} (hK : 0 ≤ K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ X : ℝ, B ≤ X → ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → Disjoint P S → (∀ p ∈ S, X < (p : ℝ)) →
      η ≤ (∑ p ∈ S, 1/(p : ℝ)) →
      ∃ M : ℕ, X < (M : ℝ) ∧ K*(M : ℝ)^2 < mobiusDivisorSelectionEnergy M (P ∪ S) := by
  obtain ⟨B,hB,h⟩ := routeP_fresh_reciprocal_mass_forces_head_spike P hP hη hK
  refine ⟨B,hB,?_⟩
  intro X hX S hS hdis hfresh hmass
  obtain ⟨M,hM,hspike⟩ := h X hX S hS hdis hfresh hmass
  refine ⟨M,hM,hspike.trans_le ?_⟩
  simpa using sum_mobiusDivisorSelectionFibre_sq_le_energy M (P ∪ S) {∅}

end RHTower

