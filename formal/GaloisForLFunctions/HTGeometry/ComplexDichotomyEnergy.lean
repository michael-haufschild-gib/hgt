import GaloisForLFunctions.HTGeometry.HorizonEnergyGronwall
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Complex free-frequency energy with an integrable horizon perturbation. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def dichotomyEnergy (P M : ℝ → ℂ) (t : ℝ) : ℝ := ‖P t‖^(2 : ℕ)+‖M t‖^(2 : ℕ)

def dichotomyEnergyRate (w p m g : ℂ) : ℝ :=
  -4*w.re*‖m‖^(2 : ℕ)+2*((g*(starRingEnd ℂ) p).re+(g*(starRingEnd ℂ) m).re)

/-- The real part of the free frequency is the exact growth rate in the two free-mode channels. -/
theorem dichotomyEnergy_hasDerivAt {P M : ℝ → ℂ} {w g : ℂ} {t : ℝ}
    (hP : HasDerivAt P ((w-(w.re:ℂ))*P t+g) t)
    (hM : HasDerivAt M ((-w-(w.re:ℂ))*M t+g) t) :
    HasDerivAt (dichotomyEnergy P M) (dichotomyEnergyRate w (P t) (M t) g) t := by
  convert! hP.norm_sq.add hM.norm_sq using 1
  simp only [dichotomyEnergyRate,Complex.inner,← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
    Complex.add_re,Complex.sub_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.add_im,Complex.sub_im,Complex.neg_im,Complex.conj_re,Complex.conj_im]
  ring

/-- A decaying channel coupling gives an integrable backward energy loss and a bounded forward rate. -/
theorem dichotomyEnergyRate_bounds (w p m g : ℂ) (hw : w.re ≤ 0) (A B e : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hg : ‖g‖ ≤ e*(A*(‖p‖+‖m‖)+B)) :
    -(4*A+2*B)*e*(‖p‖^(2 : ℕ)+‖m‖^(2 : ℕ)+1) ≤ dichotomyEnergyRate w p m g ∧
    dichotomyEnergyRate w p m g ≤ (-4*w.re+4*A+2*B)*(‖p‖^(2 : ℕ)+‖m‖^(2 : ℕ)+1) := by
  let N := ‖p‖+‖m‖
  let E := ‖p‖^(2 : ℕ)+‖m‖^(2 : ℕ)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hN2 : N^(2 : ℕ) ≤ 2*E := by dsimp [N,E]; nlinarith [sq_nonneg (‖p‖-‖m‖)]
  have hN1 : N ≤ E+1 := by dsimp [N,E]; nlinarith [sq_nonneg (‖p‖-1),sq_nonneg (‖m‖-1)]
  have hb : 2*N*‖g‖ ≤ (4*A+2*B)*e*(E+1) := by
    calc
      _ ≤ 2*N*(e*(A*N+B)) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = e*(2*A*N^(2 : ℕ)+2*B*N) := by ring
      _ ≤ e*(2*A*(2*E)+2*B*(E+1)) := by gcongr
      _ ≤ (4*A+2*B)*e*(E+1) := by nlinarith [mul_nonneg hA he]
  have hp := Complex.abs_re_le_norm (g*(starRingEnd ℂ) p)
  have hm := Complex.abs_re_le_norm (g*(starRingEnd ℂ) m)
  simp only [norm_mul,norm_conj] at hp hm
  rw [abs_le] at hp hm
  have hl : -(4*A+2*B)*e*(E+1) ≤ 2*((g*(starRingEnd ℂ) p).re+(g*(starRingEnd ℂ) m).re) := by
    dsimp [N] at hb
    nlinarith [hp.1,hm.1]
  have hh : 2*((g*(starRingEnd ℂ) p).re+(g*(starRingEnd ℂ) m).re) ≤ (4*A+2*B)*e*(E+1) := by
    dsimp [N] at hb
    nlinarith [hp.2,hm.2]
  have hfree : 0 ≤ -4*w.re*‖m‖^(2 : ℕ) := mul_nonneg (by linarith) (sq_nonneg _)
  have hfree' : -4*w.re*‖m‖^(2 : ℕ) ≤ -4*w.re*E := by
    apply mul_le_mul_of_nonneg_left ?_ (by linarith)
    dsimp [E]
    nlinarith [sq_nonneg ‖p‖]
  have he' : (4*A+2*B)*e*(E+1) ≤ (4*A+2*B)*(E+1) := by
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) he1) (by positivity)
  constructor
  · dsimp [dichotomyEnergyRate]
    exact hl.trans (le_add_of_nonneg_left hfree)
  · dsimp [dichotomyEnergyRate]
    change _ ≤ (-4*w.re+4*A+2*B)*(E+1)
    nlinarith

/-- The entire negative-ray energy is bounded from one interior datum. -/
theorem dichotomyEnergy_bound (P M G : ℝ → ℂ) (w : ℂ) (hw : w.re ≤ 0) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hP : ∀ t < 0, HasDerivAt P ((w-(w.re:ℂ))*P t+G t) t)
    (hM : ∀ t < 0, HasDerivAt M ((-w-(w.re:ℂ))*M t+G t) t)
    (hG : ∀ t < 0, ‖G t‖ ≤ Real.exp (2*t)*(A*(‖P t‖+‖M t‖)+B)) :
    ∀ t < 0, dichotomyEnergy P M t+1 ≤
      max ((dichotomyEnergy P M (-1)+1)*Real.exp ((4*A+2*B)/2))
        ((dichotomyEnergy P M (-1)+1)*Real.exp (-4*w.re+4*A+2*B)) := by
  have hb (t : ℝ) (ht : t < 0) := dichotomyEnergyRate_bounds w (P t) (M t) (G t) hw A B
    (Real.exp (2*t)) hA hB (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith)) (hG t ht)
  exact horizon_energy_bound (by positivity) (by linarith)
    (fun t _ => by dsimp [dichotomyEnergy]; positivity)
    (fun t ht => dichotomyEnergy_hasDerivAt (hP t ht) (hM t ht))
    (fun t ht => (hb t ht).1) (fun t ht => (hb t ht).2)

end
end GaloisForLFunctions.HTGeometry
