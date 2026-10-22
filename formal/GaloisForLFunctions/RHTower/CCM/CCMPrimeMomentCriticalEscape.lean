import GaloisForLFunctions.RHTower.CCM.CCMPrimeMomentPotentialEscape
import GaloisForLFunctions.RHTower.ChebyshevSchmidtOmega

/-!
# Actual nonlinear prime forcing at critical normalization

The negative central Laplace residue produces critical-scale potential
excursions. The exact normalized potential increment depends on the
ordinary Chebyshev error. Its two proved oscillation signs select an
arbitrarily late interior minimum containing a low potential value.

At this prime-entry valley the Chebyshev cumulative lies within one
admitted atom of the physical cutoff. The atom tends to zero at critical
normalization, so the positive displacement square cannot erase the
negative forcing. Consequently `D_n / sqrt(n)` has a fixed negative
amplitude on every integer tail, unconditionally.

This does not assert eventual negativity, a uniform forcing bound, or
the canonical-head Gamma--prime--polar sign.
-/

noncomputable section
open Filter Topology
namespace RHTower

private def normalizedPotential (n : ℕ) : ℝ :=
  ccmPrimeMomentPotential n / Real.sqrt n

private theorem sqrt_step_pos (n : ℕ) :
    0 < Real.sqrt (n+1 : ℕ)-Real.sqrt n := by
  apply sub_pos.mpr
  apply Real.sqrt_lt_sqrt (Nat.cast_nonneg (α := ℝ) n)
  exact_mod_cast Nat.lt_succ_self n

private theorem normalized_step (n : ℕ) (hn : 1 ≤ n) :
    (normalizedPotential (n+1)-normalizedPotential n)*Real.sqrt n*Real.sqrt (n+1 : ℕ) =
      (Real.sqrt (n+1 : ℕ)-Real.sqrt n)*
        (Chebyshev.psi n+1-Real.sqrt n*Real.sqrt (n+1 : ℕ)) := by
  have ha : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn))
  have hb : Real.sqrt (n+1 : ℕ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hu := ccmPrimeMomentPotential_succ_sub n
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have ht := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+1))
  unfold normalizedPotential
  field_simp
  unfold ccmPrimeMomentPotential at *
  linear_combination Real.sqrt n*hu-(Real.sqrt (n+1 : ℕ)-Real.sqrt n)*hs

private theorem normalized_down_of_psi (n : ℕ) (hn : 1 ≤ n)
    (hp : Chebyshev.psi n+1 < (n : ℝ)) :
    normalizedPotential (n+1) < normalizedPotential n := by
  have hs := normalized_step n hn
  have hg := sqrt_step_pos n
  have ha := Real.sqrt_nonneg (n : ℝ)
  have hq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hprod := mul_nonneg ha hg.le
  have hright : (Real.sqrt (n+1 : ℕ)-Real.sqrt n)*
      (Chebyshev.psi n+1-Real.sqrt n*Real.sqrt (n+1 : ℕ)) < 0 :=
    mul_neg_of_pos_of_neg hg (by nlinarith)
  have hmul : 0 < Real.sqrt n*Real.sqrt (n+1 : ℕ) := by positivity
  by_contra! hh
  have hp := mul_nonneg (sub_nonneg.mpr hh) hmul.le
  nlinarith only [hs, hright, hp]

private theorem normalized_up_of_psi (n : ℕ) (hn : 1 ≤ n)
    (hp : (n : ℝ) < Chebyshev.psi n) :
    normalizedPotential n < normalizedPotential (n+1) := by
  have hs := normalized_step n hn
  have hg := sqrt_step_pos n
  have hb := Real.sqrt_nonneg (n+1 : ℕ)
  have hq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+1))
  have hprod := mul_nonneg hb hg.le
  have hright : 0 < (Real.sqrt (n+1 : ℕ)-Real.sqrt n)*
      (Chebyshev.psi n+1-Real.sqrt n*Real.sqrt (n+1 : ℕ)) := by
    apply mul_pos hg
    have hcast : ((n+1 : ℕ) : ℝ) = (n : ℝ)+1 := by push_cast; rfl
    nlinarith only [hq,hprod,hp,hcast]
  have hmul : 0 < Real.sqrt n*Real.sqrt (n+1 : ℕ) := by positivity
  by_contra! hh
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh) hmul.le
  nlinarith only [hs, hright, hp]

private theorem cofinal_normalized_steps (N : ℕ) :
    (∃ n : ℕ, max 1 N ≤ n ∧ normalizedPotential (n+1) < normalizedPotential n) ∧
    (∃ n : ℕ, max 1 N ≤ n ∧ normalizedPotential n < normalizedPotential (n+1)) := by
  obtain ⟨c,hc,hminus,hplus⟩ := chebyshevPsi_sub_omega_pm
  constructor
  · obtain ⟨x,hx,hlarge,hroot⟩ :=
      (hminus.and_eventually ((eventually_ge_atTop ((max 1 N : ℕ) : ℝ)).and
        (Real.tendsto_sqrt_atTop.eventually_gt_atTop (2/c)))).exists
    have hn : max 1 N ≤ ⌊x⌋₊ := Nat.le_floor hlarge
    refine ⟨⌊x⌋₊,hn,normalized_down_of_psi _ ((le_max_left _ _).trans hn) ?_⟩
    have hfloor := Nat.lt_floor_add_one x
    have hcs : 2 < c*Real.sqrt x := by
      have h := (div_lt_iff₀ hc).mp hroot
      nlinarith
    rw [Chebyshev.psi_eq_psi_coe_floor] at hx
    linarith
  · obtain ⟨x,hx,hlarge⟩ :=
      (hplus.and_eventually (eventually_ge_atTop ((max 1 N : ℕ) : ℝ))).exists
    have hn : max 1 N ≤ ⌊x⌋₊ := Nat.le_floor hlarge
    refine ⟨⌊x⌋₊,hn,normalized_up_of_psi _ ((le_max_left _ _).trans hn) ?_⟩
    have hx0 : 0 ≤ x := by
      have hN : (0 : ℝ) ≤ (max 1 N : ℕ) := by positivity
      linarith
    have hfloor := Nat.floor_le hx0
    have hp := mul_nonneg hc.le (Real.sqrt_nonneg x)
    rw [Chebyshev.psi_eq_psi_coe_floor] at hx
    linarith

private theorem atom_eventually_small {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, criticalMellinAtomWeight n < c/2 := by
  have hh := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).bound
    (by positivity : (0 : ℝ) < c/4)
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually hh
  filter_upwards [hn,eventually_ge_atTop 1] with n hn hpos
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hpos))
  have he : |(n : ℝ)^(1/2 : ℝ)| = Real.sqrt n := by
    rw [← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, he] at hn
  have hv := ArithmeticFunction.vonMangoldt_le_log (n := n)
  rw [criticalMellinAtomWeight_eq_div_sqrt]
  apply (div_lt_iff₀ hs).mpr
  nlinarith [le_abs_self (Real.log (n : ℝ))]

private theorem normalized_valley_forcing (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 1 ≤ n)
    (hleft : normalizedPotential (n+1) ≤ normalizedPotential n)
    (hright : normalizedPotential (n+1) ≤ normalizedPotential (n+2))
    (hlow : normalizedPotential (n+1) < -c)
    (hw : criticalMellinAtomWeight (n+1) < c/2) :
    ccmPrimeMomentDiscrepancy (n+1) < -(c/4)*Real.sqrt (n+1 : ℕ) := by
  have hl := normalized_step n hn
  have hr := normalized_step (n+1) (by omega)
  have hg := sqrt_step_pos n
  have hg' := sqrt_step_pos (n+1)
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have ht := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+1))
  have hu := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+2))
  have ha := Real.sqrt_nonneg (n : ℝ)
  have hb : 0 < Real.sqrt (n+1 : ℕ) := by positivity
  have hd : 0 < Real.sqrt (n+2 : ℕ) := by positivity
  have hpre : Chebyshev.psi n+1 ≤ Real.sqrt n*Real.sqrt (n+1 : ℕ) := by
    have hneg := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hleft)
      (mul_nonneg ha hb.le)
    by_contra! hh
    have hp := mul_pos hg (sub_pos.mpr hh)
    nlinarith only [hl,hneg,hp]
  have hpost : Real.sqrt (n+1 : ℕ)*Real.sqrt (n+2 : ℕ) ≤ Chebyshev.psi (n+1 : ℕ)+1 := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hright) (mul_nonneg hb.le hd.le)
    simp only [Nat.add_assoc, Nat.reduceAdd] at hr hg'
    by_contra! hh
    have hp := mul_neg_of_pos_of_neg hg' (sub_neg.mpr hh)
    nlinarith only [hr,hnonneg,hp]
  have hpsi : Chebyshev.psi (n+1 : ℕ) = Chebyshev.psi n+ArithmeticFunction.vonMangoldt (n+1) := by
    simp only [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ n+1)]
  have hweight : criticalMellinAtomWeight (n+1)*Real.sqrt (n+1 : ℕ) =
      ArithmeticFunction.vonMangoldt (n+1) := by
    rw [criticalMellinAtomWeight_eq_div_sqrt, div_mul_cancel₀ _ hb.ne']
  have hmass : 0 ≤ primeMassHalf (n+1 : ℕ) := by
    unfold primeMassHalf
    exact Finset.sum_nonneg fun j _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.sqrt_nonneg _)
  have hq : (n+1 : ℕ) ≤ Chebyshev.psi (n+1 : ℕ)+1 := by
    have hp := mul_nonneg hb.le hg'.le
    simp only [Nat.add_assoc, Nat.reduceAdd] at hp
    nlinarith
  have hq' : Chebyshev.psi (n+1 : ℕ)+1 <
      (n+1 : ℕ)+criticalMellinAtomWeight (n+1)*Real.sqrt (n+1 : ℕ) := by
    have hp := mul_pos hb hg
    rw [hpsi]
    nlinarith only [hpre,hp,ht,hweight]
  have hlow' : ccmPrimeMomentPotential (n+1) < -c*Real.sqrt (n+1 : ℕ) :=
    (div_lt_iff₀ hb).mp hlow
  have hm : 1+primeMassHalf (n+1 : ℕ)/2 < Real.sqrt (n+1 : ℕ)-c/4 := by
    unfold ccmPrimeMomentPotential at hlow'
    have hw' := mul_lt_mul_of_pos_right hw hb
    nlinarith only [hlow',hq',hw',ht,hb]
  have hprod := mul_pos
    (show 0 < Real.sqrt (n+1 : ℕ)-c/4-(1+primeMassHalf (n+1 : ℕ)/2) by linarith)
    (show 0 < Real.sqrt (n+1 : ℕ)+(1+primeMassHalf (n+1 : ℕ)/2) by linarith)
  unfold ccmPrimeMomentDiscrepancy
  nlinarith [mul_nonneg hc.le hmass]

/-- A fixed negative critical amplitude of the actual nonlinear prime forcing
occurs on every arithmetic tail. All source weights and the positive square remain. -/
theorem ccmPrimeMomentDiscrepancy_critical_negative_cofinally :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, max 1 N ≤ n ∧
      ccmPrimeMomentDiscrepancy n < -c*Real.sqrt n := by
  classical
  obtain ⟨c,hc,hescape⟩ := ccmPrimeMomentPotential_critical_negative_cofinally
  obtain ⟨K,hK⟩ := eventually_atTop.mp (atom_eventually_small hc)
  refine ⟨c/4,by positivity,fun N => ?_⟩
  obtain ⟨k,hk,hdown⟩ := (cofinal_normalized_steps (max N K)).1
  obtain ⟨j,hj,hjlow⟩ := hescape (k+1)
  have hjk : k+1 ≤ j := (le_max_right _ _).trans hj
  have hj1 : 1 ≤ j := (le_max_left _ _).trans hj
  have hjnorm : normalizedPotential j < -c :=
    (div_lt_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj1)))).mpr hjlow
  obtain ⟨l,hl,hup⟩ := (cofinal_normalized_steps j).2
  have hjl : j ≤ l := (le_max_right _ _).trans hl
  obtain ⟨r,hr,hmin⟩ := (Finset.Icc k (l+1)).exists_min_image normalizedPotential
    ⟨k,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩
  obtain ⟨hkr,hrl⟩ := Finset.mem_Icc.mp hr
  have hkr' : k < r := by
    have hm := hmin (k+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    by_contra! he
    have her : r = k := by omega
    rw [her] at hm
    linarith
  have hrl' : r ≤ l := by
    have hm := hmin l (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    by_contra! he
    have her : r = l+1 := by omega
    rw [her] at hm
    linarith
  have hlow := (hmin j (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)).trans_lt hjnorm
  have hleft := hmin (r-1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have hright := hmin (r+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk
  have hkN : N ≤ k := (le_max_left N K).trans ((le_max_right _ _).trans hk)
  have hkK : K ≤ k := (le_max_right N K).trans ((le_max_right _ _).trans hk)
  have he : r-1+1 = r := by omega
  have he' : r-1+2 = r+1 := by omega
  refine ⟨r,by omega,?_⟩
  have hv := normalized_valley_forcing c hc (r-1) (by omega)
    (by simpa only [he] using hleft) (by simpa only [he,he'] using hright)
    (by simpa only [he] using hlow) (by simpa only [he] using hK r (by omega))
  simpa only [he] using hv

end RHTower
