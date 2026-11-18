import GaloisForLFunctions.CountingHolography.Sections.OrdinaryPrimeSectionModuli
import GaloisForLFunctions.CountingHolography.Sections.UniformQuadratureForPrimeContacts

/-!
# Uniform pole quadrature over moving conductors

An atom at conductor d on the logarithmic mesh of denominator r has exactly
the samples of the unit-conductor atom at denominator rd. Its exponential
weight acquires the factor dᵗ. Convergence for the single fixed atom therefore
bounds the quadrature error simultaneously at every horizon.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology MeasureTheory AbsoluteGeometryOfSpecZ BiScaleUncertainty.ChebyshevGauge

private def center : ℝ := Real.log 3 + 5
private def unitAtom (u : ℝ) : ℝ := cubicSpline (u-center)
private def cutoff : ℕ := ⌈Real.exp (center+4)⌉₊+1

/-- Exponentially weighted conductor degree of an integer divisor. -/
def conductorExpMoment {N : ℕ} (t : ℝ) (a : Fin N → ℤ) : ℝ :=
  ∑ i : Fin N, (a i : ℝ)*Real.exp (t*Real.log ((i : ℝ)+1))

/-- The pole moment supplied by a single atom at conductor one. -/
def unitAtomMoment (t : ℝ) : ℝ := ∫ u : ℝ, unitAtom u * Real.exp (t*u)

theorem unitAtomMoment_pos (t : ℝ) : 0 < unitAtomMoment t := by
  have hunit : (∫ u, cubicSpline u) = 1 := _root_.RHTower.WeilDeletion.integral_upow one_pos 3
  obtain ⟨x,hx⟩ : ∃ x, cubicSpline x ≠ 0 := by
    by_contra! h
    simp_rw [h, integral_zero] at hunit
    exact zero_ne_one hunit
  have hc : Continuous unitAtom := contDiff_cubicSpline.continuous.comp (continuous_id.sub continuous_const)
  have hs : HasCompactSupport unitAtom := hasCompactSupport_cubicSpline.comp_homeomorph (Homeomorph.subRight center)
  apply (hc.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integral_pos_of_hasCompactSupport_nonneg_nonzero
    hs.mul_right (fun u => mul_nonneg (cubicSpline_nonneg _) (Real.exp_pos _).le) (x := x+center)
  exact mul_ne_zero (by simpa only [unitAtom, add_sub_cancel_right] using hx)
    (Real.exp_ne_zero _)

private theorem cutoff_pos : 0 < cutoff := Nat.succ_pos _

private theorem atom_window (u : ℝ) (hu : u ≤ Real.log 3 ∨ Real.log cutoff ≤ u) : unitAtom u = 0 := by
  apply cubicSpline_eq_zero
  rcases hu with h | h
  · have hb := neg_le_abs (u-center)
    dsimp [center] at *
    linarith
  · have hceil := Nat.le_ceil (Real.exp (center+4))
    have hh : Real.exp (center+4) < (cutoff : ℝ) := by
      unfold cutoff
      push_cast
      linarith only [hceil]
    have hK := (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr cutoff_pos)).mpr hh
    linarith only [hK,h,le_abs_self (u-center)]

private theorem cutoff_le_horizon {N d : ℕ} (hd : d ≤ N) : (cutoff+1)*d ≤ windowEnd N := by
  have hbase : 3 ≤ Real.exp (center+4) := by
    have h := Real.add_one_le_exp (center+4)
    dsimp only [center] at *
    linarith only [h,Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
  have hK : (cutoff : ℝ)+1 ≤ Real.exp (center+5) := by
    have hceil : (cutoff : ℝ) < Real.exp (center+4)+2 := by
      unfold cutoff
      push_cast
      linarith only [Nat.ceil_lt_add_one (Real.exp_pos (center+4)).le]
    have hmul := mul_le_mul_of_nonneg_left (Real.add_one_le_exp 1) (Real.exp_pos (center+4)).le
    rw [show center+5 = center+4+1 by ring, Real.exp_add]
    linarith only [hceil,hbase,hmul]
  have he : Real.exp (center+5)*((N : ℝ)+1) ≤ windowEnd N := by
    change _ ≤ (⌈Real.exp (center+Real.log ((N : ℝ)+1)+5)⌉₊ : ℝ)
    rw [show center+Real.log ((N : ℝ)+1)+5 = (center+5)+Real.log ((N : ℝ)+1) by ring,
      Real.exp_add (center+5) _, Real.exp_log (by positivity)]
    exact Nat.le_ceil _
  have hd' : (d : ℝ) ≤ (N : ℝ)+1 := by
    have : (d : ℝ) ≤ N := by exact_mod_cast hd
    linarith
  exact_mod_cast (mul_le_mul hK hd' (Nat.cast_nonneg _) (Real.exp_pos _).le).trans he

private def meshTerm (r j : ℕ) (t : ℝ) : ℝ :=
  unitAtom (Real.log ((j : ℝ)/r)) * Real.exp (t*Real.log ((j : ℝ)/r)) / j

private theorem translated_sampledDegree {N r d : ℕ} (hr : 0 < r) (hd : 0 < d) (hdN : d ≤ N) (t : ℝ) :
    (∑ j ∈ Ioc r (r+3*windowEnd N*r), unitAtom (Real.log ((j : ℝ)/r)-Real.log d) *
        Real.exp (t*Real.log ((j : ℝ)/r)) / j) =
      Real.exp (t*Real.log d) * sampledDegree unitAtom (3*cutoff) (r*d) t := by
  let S := Ioc r (r+3*windowEnd N*r)
  let J := Ioc (r*d) (r*d+3*cutoff*(r*d))
  have hrd := Nat.mul_pos hr hd
  have hlog (j : ℕ) (hj : 0 < j) : Real.log ((j : ℝ)/r) =
      Real.log ((j : ℝ)/(r*d : ℕ)) + Real.log d := by
    simp only [Nat.cast_mul, Real.log_div (Nat.cast_ne_zero.mpr hj.ne') (Nat.cast_ne_zero.mpr hr.ne'),
      Real.log_div (Nat.cast_ne_zero.mpr hj.ne') (mul_ne_zero (Nat.cast_ne_zero.mpr hr.ne') (Nat.cast_ne_zero.mpr hd.ne')),
      Real.log_mul (Nat.cast_ne_zero.mpr hr.ne') (Nat.cast_ne_zero.mpr hd.ne')]
    ring
  have hJS : J ⊆ S := by
    intro j hj
    obtain ⟨hl,hh⟩ := mem_Ioc.mp hj
    have hcut := Nat.mul_le_mul_right (3*r) (cutoff_le_horizon hdN)
    exact mem_Ioc.mpr ⟨(Nat.le_mul_of_pos_right _ hd).trans_lt hl,
      by nlinarith only [hh,hcut,Nat.zero_le (r*d),Nat.zero_le r]⟩
  have hzero (j : ℕ) (hj : j ∈ S) (hj' : j ∉ J) : meshTerm (r*d) j t = 0 := by
    have hjp := hr.trans (mem_Ioc.mp hj).1
    have hrd' : (0:ℝ) < (r*d : ℕ) := Nat.cast_pos.mpr hrd
    suffices h : unitAtom (Real.log ((j : ℝ)/(r*d : ℕ))) = 0 by simp only [meshTerm,h,zero_mul,zero_div]
    apply atom_window
    by_cases hl : j ≤ r*d
    · exact Or.inl ((Real.log_nonpos (by positivity) ((div_le_one hrd').mpr (by exact_mod_cast hl))).trans
        (Real.log_nonneg (by norm_num)))
    · have hh : r*d+3*cutoff*(r*d) < j := lt_of_not_ge fun h => hj' (mem_Ioc.mpr ⟨lt_of_not_ge hl,h⟩)
      have hh' : cutoff*(r*d) ≤ j := by nlinarith only [hh, Nat.zero_le (cutoff*(r*d)),Nat.zero_le (r*d)]
      exact Or.inr (Real.log_le_log (Nat.cast_pos.mpr cutoff_pos) ((le_div_iff₀ hrd').mpr (by exact_mod_cast hh')))
  calc _ = Real.exp (t*Real.log d) * ∑ j ∈ S, meshTerm (r*d) j t := by
          rw [mul_sum]
          apply sum_congr rfl
          intro j hj
          rw [hlog j (hr.trans (mem_Ioc.mp hj).1),add_sub_cancel_right,mul_add,Real.exp_add]
          unfold meshTerm
          ring
       _ = _ := by
          congr 1
          exact (sum_subset hJS hzero).symm

private theorem expand_sampledDegree {N r : ℕ} (hr : 0 < r) (a : Fin N → ℤ) (t : ℝ) :
    sampledDegree (packet a) (3*windowEnd N) r t = ∑ i : Fin N,
      (a i : ℝ)*Real.exp (t*Real.log ((i : ℝ)+1)) * sampledDegree unitAtom (3*cutoff) (r*(i.val+1)) t := by
  have hrow (j : ℕ) : degreeSample (packet a) r j = ∑ i : Fin N, (a i : ℝ) *
      unitAtom (Real.log ((j : ℝ)/r)-Real.log ((i : ℝ)+1)) := by
    unfold degreeSample packet splineSource unitAtom
    apply sum_congr rfl
    intro i _
    change _ * cubicSpline (_ - center - _) = _
    rw [sub_right_comm]
  change (∑ j ∈ Ioc r (r+3*windowEnd N*r), degreeSample (packet a) r j *
    Real.exp (t*Real.log ((j : ℝ)/r)) / j) = _
  simp_rw [hrow, sum_mul, sum_div, mul_assoc, mul_div_assoc]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_sum]
  have h := translated_sampledDegree (d := i.val+1) hr (Nat.succ_pos i.val) i.isLt t
  simp only [Nat.cast_add, Nat.cast_one] at h
  simpa only [mul_assoc, mul_div_assoc] using congrArg (fun v : ℝ => (a i : ℝ)*v) h

private theorem unitAtom_quadrature_error (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r : ℕ}, 0 < r →
      |sampledDegree unitAtom (3*cutoff) r t-unitAtomMoment t| ≤ C/r := by
  let G (u : ℝ) := unitAtom u * Real.exp (t*u)
  have hf : ContDiff ℝ 2 unitAtom := contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const)
  have hg : ContDiff ℝ 2 G := hf.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hs : HasCompactSupport unitAtom := hasCompactSupport_cubicSpline.comp_homeomorph (Homeomorph.subRight center)
  have hG : HasCompactSupport G := hs.mul_right
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hG hg (by norm_num)
  obtain ⟨B,hB⟩ := ((hG.isCompact_range hg.continuous).image continuous_abs).bddAbove
  have hb (u : ℝ) : |G u| ≤ B := hB ⟨G u, ⟨u,rfl⟩, rfl⟩
  have hl (u v : ℝ) : |G v-G u| ≤ (K : ℝ)*|v-u| := hK.dist_le_mul v u
  let L := 3*cutoff
  have hL : Real.log cutoff ≤ Real.log (1+(L : ℝ)) := by
    apply Real.log_le_log (Nat.cast_pos.mpr cutoff_pos)
    dsimp only [L]
    push_cast
    linarith only [Nat.cast_nonneg (α := ℝ) cutoff]
  have hz (u : ℝ) (hu : u ≤ 0 ∨ Real.log (1+(L : ℝ)) ≤ u) : G u = 0 := by
    apply mul_eq_zero_of_left
    apply atom_window
    exact hu.imp (fun h => h.trans (Real.log_nonneg (by norm_num))) (hL.trans ·)
  have hi : (∫ u in (0:ℝ)..Real.log (1+(L : ℝ)), G u) = unitAtomMoment t := by
    rw [intervalIntegral.integral_of_le (Real.log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) L)))]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rcases not_and_or.mp hu with h | h
    · exact hz u (Or.inl (le_of_not_gt h))
    · exact hz u (Or.inr (le_of_not_ge h))
  refine ⟨2*((K : ℝ)+B), mul_nonneg (by norm_num) (add_nonneg K.coe_nonneg ((abs_nonneg _).trans (hb 0))),
    fun {r} hr => ?_⟩
  have he := degreeSum_uniform_error hg.continuous K.coe_nonneg hb hl L hr (hz _ (Or.inl le_rfl)) (hz _ (Or.inr le_rfl))
  rwa [hi] at he

/-- Each conductor d improves the single-atom mesh error by a further factor
1/d. This estimate also applies when the signed conductor moment vanishes. -/
theorem conductor_moment_quadrature_error (t : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {N r : ℕ}, 0 < r → ∀ a : Fin N → ℤ,
      |sampledDegree (packet a) (3*windowEnd N) r t - unitAtomMoment t * conductorExpMoment t a| ≤
        (C/r) * conductorExpMoment (t-1) (fun i => |a i|) := by
  obtain ⟨C,hC,h⟩ := unitAtom_quadrature_error t
  refine ⟨C,hC,fun {N r} hr a => ?_⟩
  rw [expand_sampledDegree hr]
  unfold conductorExpMoment
  simp only [mul_sum]
  rw [← sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  let w := Real.exp (t*Real.log ((i : ℝ)+1))
  let s := sampledDegree unitAtom (3*cutoff) (r*(i.val+1)) t
  have hd : 0 < (i : ℝ)+1 := by positivity
  have he : |s-unitAtomMoment t| ≤ C / ((r : ℝ)*((i : ℝ)+1)) := by
    simpa only [s,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using h (r := r*(i.val+1)) (Nat.mul_pos hr (Nat.succ_pos i.val))
  change |(a i : ℝ)*w*s - unitAtomMoment t*((a i : ℝ)*w)| ≤ _
  rw [show (a i : ℝ)*w*s - unitAtomMoment t*((a i : ℝ)*w) =
    ((a i : ℝ)*w)*(s-unitAtomMoment t) by ring, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), Int.cast_abs,
    sub_mul,one_mul, Real.exp_sub, Real.exp_log hd]
  refine (mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)).trans_eq ?_
  change |(a i : ℝ)| *w*(C/((r : ℝ)*((i : ℝ)+1))) = C/r*(|(a i : ℝ)| *(w/((i : ℝ)+1)))
  rw [div_mul_eq_div_div]
  ring

/-- Uniform relative error in a signed pole reading, measured against the
same conductor weights on the absolute coefficients. Each fixed exponent uses one resolution
threshold for all conductor horizons. -/
theorem uniform_conductor_moment_quadrature (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∀ {N r : ℕ}, R ≤ r → ∀ a : Fin N → ℤ,
      |sampledDegree (packet a) (3*windowEnd N) r t - unitAtomMoment t * conductorExpMoment t a| ≤
        ε * conductorExpMoment t (fun i => |a i|) := by
  obtain ⟨C,hC,h⟩ := conductor_moment_quadrature_error t
  obtain ⟨R,hR⟩ := exists_nat_gt (C/ε)
  refine ⟨max 1 R,fun {N r} hr a => ?_⟩
  have hr1 : 0 < r := (le_max_left 1 R).trans hr
  have he : C/(r : ℝ) ≤ ε := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hr1)).mpr
    have hR' : (R : ℝ) ≤ r := by exact_mod_cast (le_max_right 1 R).trans hr
    linarith only [(div_lt_iff₀ hε).mp (hR.trans_le hR')]
  have hm : conductorExpMoment (t-1) (fun i => |a i|) ≤ conductorExpMoment t (fun i => |a i|) := by
    apply sum_le_sum
    intro i _
    have hx : 0 ≤ Real.log ((i : ℝ)+1) := Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) i.val])
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hx])) (by exact_mod_cast abs_nonneg (a i))
  apply (h hr1 a).trans
  apply mul_le_mul he hm _ hε.le
  exact sum_nonneg fun i _ => mul_nonneg (by exact_mod_cast abs_nonneg (a i)) (Real.exp_pos _).le

#print axioms conductor_moment_quadrature_error
#print axioms uniform_conductor_moment_quadrature

end GaloisForLFunctions.CountingHolography.Sections
