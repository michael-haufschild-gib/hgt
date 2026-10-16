import GaloisForLFunctions.RHTower.OddSectorWindowPurification
import GaloisForLFunctions.RHTower.MarkovOddSectorFarkasAndOneSidedPBAP

/-!
# Signed arithmetic coordinates inside an arbitrary odd aperture

Every integer lag strictly below the diameter has both signs of its coordinate
represented by a smooth odd source strictly inside the aperture. The bump width
is chosen after the aperture, including when the lag is arbitrarily close to
the diameter. No extra arithmetic coordinates are introduced.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ContDiff

noncomputable section
namespace RHTower.OddSector
open WeilOneSided

private theorem evenNarrowBump_smooth (j : ℕ) : ContDiff ℝ ∞ (evenNarrowBump j) :=
  ((narrowBump j).contDiff.add ((narrowBump j).contDiff.comp contDiff_neg)).div_const 2

private theorem oddNarrowBump_smooth (j : ℕ) : ContDiff ℝ ∞ (oddNarrowBump j) :=
  contDiff_id.mul (evenNarrowBump_smooth j)

private theorem shift_pair_support {g : ℝ → ℝ} {r : ℝ}
    (hg : ∀ x, r < |x| → g x = 0) (h c : ℝ) :
    tsupport (fun x => (((g (x-h/2)+c*g (x+h/2))/2 : ℝ) : ℂ)) ⊆
      Icc (-(r+|h|/2)) (r+|h|/2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  apply abs_le.mp
  by_contra hn
  have hh : r+|h|/2 < |x| := lt_of_not_ge hn
  have h₁ : r < |x-h/2| := by
    have ht := abs_add_le (x-h/2) (h/2)
    rw [sub_add_cancel,abs_div,abs_two] at ht
    linarith
  have h₂ : r < |x+h/2| := by
    have ht := abs_add_le (x+h/2) (-(h/2))
    rw [add_neg_cancel_right,abs_neg,abs_div,abs_two] at ht
    linarith
  apply hx
  dsimp
  rw [hg _ h₁,hg _ h₂]
  simp

private theorem exists_small_bump_index (a : SuzukiPositiveAperture) (j : LogIndex)
    (hj : Real.log (j : ℕ) < 2*a.1) :
    ∃ m : ℕ, (1/(4*((m : ℝ)+1))) ≤ 1/(4*((j : ℕ)+1)) ∧
      1/(4*((m : ℝ)+1))+Real.log (j : ℕ)/2 < a.1 := by
  let d := a.1-Real.log (j : ℕ)/2
  have hd : 0 < d := by dsimp [d]; linarith
  obtain ⟨m,hm⟩ := exists_nat_gt (max (j : ℝ) (1/d))
  have hjm : (j : ℝ) ≤ m := (le_max_left _ _).trans hm.le
  have hdm : 1 < (m : ℝ)*d := (div_lt_iff₀ hd).mp ((le_max_right _ _).trans_lt hm)
  refine ⟨m,?_,?_⟩
  · apply div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num)
    · positivity
    · linarith
  have hr : 1/(4*((m : ℝ)+1)) < d := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  dsimp [d] at hr
  linarith

/-- Every active arithmetic coordinate has two strictly interior odd source rays. -/
theorem exists_interior_signed_coordinates (a : SuzukiPositiveAperture) (j : LogIndex)
    (hj : Real.log (j : ℕ) < 2*a.1) :
    ∃ p m : InteriorWindowedSmoothOddTestFn a, ∃ kp km : ℝ,
      0 < kp ∧ 0 < km ∧
      logVector p.1.1.1 = Finsupp.single j kp ∧
      logVector m.1.1.1 = Finsupp.single j (-km) := by
  classical
  obtain ⟨b,hbj,hba⟩ := exists_small_bump_index a j hj
  let gp := oddNarrowBump b
  let gm := evenNarrowBump b
  have hps : ContDiff ℝ ∞ gp := oddNarrowBump_smooth b
  have hms : ContDiff ℝ ∞ gm := evenNarrowBump_smooth b
  have hp : ContDiff ℝ ∞ (fun x => (evenShift gp (Real.log j) x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((hps.comp (contDiff_id.sub contDiff_const)).add
        (hps.comp (contDiff_id.add contDiff_const)) |>.div_const 2)
  have hm : ContDiff ℝ ∞ (fun x => (oddShift gm (Real.log j) x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((hms.comp (contDiff_id.sub contDiff_const)).sub
        (hms.comp (contDiff_id.add contDiff_const)) |>.div_const 2)
  have hpc : HasCompactSupport (fun x => (evenShift gp (Real.log j) x : ℂ)) :=
    (hasCompactSupport_evenShift (hasCompactSupport_oddNarrowBump b) _).comp_left
      Complex.ofReal_zero
  have hmc : HasCompactSupport (fun x => (oddShift gm (Real.log j) x : ℂ)) :=
    (hasCompactSupport_oddShift (hasCompactSupport_evenNarrowBump b) _).comp_left
      Complex.ofReal_zero
  have hlog : 0 ≤ Real.log (j : ℕ) := Real.log_natCast_nonneg _
  have hsup (g : ℝ → ℝ) (hg : ∀ x, 1/(4*((b : ℝ)+1)) < |x| → g x=0) (c : ℝ) :
      tsupport (fun x => (((g (x-Real.log j/2)+c*g (x+Real.log j/2))/2 : ℝ) : ℂ)) ⊆
        Ioo (-a.1) a.1 := by
    have hs := shift_pair_support hg (Real.log j) c
    rw [abs_of_nonneg hlog] at hs
    intro x hx
    have hh := hs hx
    constructor <;> linarith [hh.1,hh.2]
  let p : InteriorWindowedSmoothOddTestFn a :=
    ⟨⟨⟨⟨_,hp.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)),hpc⟩,
      fun x => by
        change (evenShift gp (Real.log j) (-x) : ℂ) = -(evenShift gp (Real.log j) x : ℂ)
        rw [evenShift_neg_of_odd (oddNarrowBump_neg b),Complex.ofReal_neg]⟩,hp⟩,
      by simpa only [evenShift,one_mul] using hsup gp (fun x hx => oddNarrowBump_eq_zero b hx) 1⟩
  let m : InteriorWindowedSmoothOddTestFn a :=
    ⟨⟨⟨⟨_,hm.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)),hmc⟩,
      fun x => by
        change (oddShift gm (Real.log j) (-x) : ℂ) = -(oddShift gm (Real.log j) x : ℂ)
        rw [oddShift_neg (evenNarrowBump_neg b),Complex.ofReal_neg]⟩,hm⟩,
      by simpa only [oddShift,neg_one_mul,sub_eq_add_neg] using
        hsup gm (fun x hx => evenNarrowBump_eq_zero b hx) (-1)⟩
  have hsqrt : 0 < Real.sqrt (j : ℕ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < j.1 by omega))
  refine ⟨p,m,(∫ x,gp x^2)/(2*Real.sqrt j),(∫ x,gm x^2)/(2*Real.sqrt j),
    div_pos (integral_oddNarrowBump_sq_pos b) (mul_pos two_pos hsqrt),
    div_pos (integral_evenNarrowBump_sq_pos b) (mul_pos two_pos hsqrt),?_,?_⟩
  · ext n
    rw [logVector_apply,Finsupp.single_apply]
    change logValue (fun x => (evenShift gp (Real.log j) x : ℂ)) n = _
    rw [logValue_evenShift_log_eq_ite hps.continuous
      (hasCompactSupport_oddNarrowBump b) j.2
      (fun x hx => oddNarrowBump_eq_zero b (hbj.trans_lt hx)) n.2]
    by_cases hn : n=j
    · subst n; simp
    · rw [if_neg (fun h => hn (Subtype.ext h)),if_neg (fun h => hn h.symm)]
  · ext n
    rw [logVector_apply,Finsupp.single_apply]
    change logValue (fun x => (oddShift gm (Real.log j) x : ℂ)) n = _
    rw [logValue_oddShift_log_eq_ite hms.continuous
      (hasCompactSupport_evenNarrowBump b) j.2
      (fun x hx => evenNarrowBump_eq_zero b (hbj.trans_lt hx)) n.2]
    by_cases hn : n=j
    · subst n; simp
    · rw [if_neg (fun h => hn (Subtype.ext h)),if_neg (fun h => hn h.symm)]

end RHTower.OddSector
