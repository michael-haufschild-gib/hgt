import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEnergies

/-! # Absolute mass of a linear energy on the spin cube -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass
open SpanningDensity
noncomputable section

/-- Longitudinal onsite energy at a spin configuration. -/
def linearEnergy {n : ℕ} (a : Fin n → ℝ) (s : Fin n → Bool) := ∑ i, a i*spin (s i)

private theorem sum_cons {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    ∑ s, f s = ∑ s : Fin n → Bool, (f (Fin.cons false s)+f (Fin.cons true s)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp f,Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [Finset.sum_add_distrib,add_comm]
  rfl

private theorem linear_cons {n : ℕ} (a : Fin (n+1) → ℝ) (b : Bool) (s : Fin n → Bool) :
    linearEnergy a (Fin.cons b s)=a 0*spin b+linearEnergy (fun i => a i.succ) s := by
  rw [linearEnergy,Fin.sum_univ_succ]
  rfl

/-- Summing over one sign at a time gives variance V and fourth moment
at most 3V², with a common unnormalized cube factor. -/
theorem spin_moments (n : ℕ) (a : Fin n → ℝ) :
    let D := (2:ℝ)^n
    let V := ∑ i, (a i)^2
    (∑ s, (linearEnergy a s)^2)=D*V ∧ (∑ s, (linearEnergy a s)^4)≤3*D*V^2 := by
  induction n with
  | zero => simp [linearEnergy]
  | succ n ih =>
    let v := ∑ i : Fin n, (a i.succ)^2
    let d := (2:ℝ)^n
    let w := linearEnergy (fun i : Fin n => a i.succ)
    have h := ih (fun i => a i.succ)
    change (∑ s, (w s)^2)=d*v ∧ (∑ s, (w s)^4)≤3*d*v^2 at h
    have hV : (∑ i, (a i)^2)=(a 0)^2+v := Fin.sum_univ_succ _
    have hd : ((Fintype.card (Fin n → Bool)):ℝ)=d := by simp [d]
    dsimp only
    rw [hV,pow_succ]
    change _=d*2*((a 0)^2+v) ∧ _≤3*(d*2)*((a 0)^2+v)^2
    constructor
    · rw [sum_cons]
      have eqn (s : Fin n → Bool) :
          (linearEnergy a (Fin.cons false s))^2+(linearEnergy a (Fin.cons true s))^2 =
          2*(a 0)^2+2*(w s)^2 := by simp only [linear_cons,spin,w]; norm_num; ring
      simp only [eqn,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum,h.1,hd]
      ring
    · rw [sum_cons]
      have eqn (s : Fin n → Bool) :
          (linearEnergy a (Fin.cons false s))^4+(linearEnergy a (Fin.cons true s))^4 =
          2*(a 0)^4+(12*(a 0)^2)*(w s)^2+2*(w s)^4 := by simp only [linear_cons,spin,w]; norm_num; ring
      simp only [eqn,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum,h.1,hd]
      nlinarith only [h.2,mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) n) (show 0≤(a 0)^4 by positivity)]

/-- The mean absolute signed sum controls its root-mean-square uniformly
in the number and strengths of the fields. -/
theorem spin_absolute_lower (n : ℕ) (a : Fin n → ℝ) :
    (2:ℝ)^n * sqrt (∑ i, (a i)^2) ≤ 8*∑ s, |linearEnergy a s| := by
  let v := ∑ i, (a i)^2
  let r := sqrt v
  let d := (2:ℝ)^n
  have hv : 0≤v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr : r^2=v := sq_sqrt hv
  have hd : 0<d := by dsimp only [d]; positivity
  rcases eq_or_lt_of_le (sqrt_nonneg v) with h|h
  · change d*r ≤ _
    rw [show r=0 from h.symm,mul_zero]
    positivity
  · change 0<r at h
    obtain ⟨h2,h4⟩ := spin_moments n a
    change (∑ s, (linearEnergy a s)^2)=d*v at h2
    change (∑ s, (linearEnergy a s)^4)≤3*d*v^2 at h4
    have point (x : ℝ) : 4*r^2*x^2 ≤ 8*r^3*|x|+x^4 := by
      by_cases hx : |x|≤2*r
      · have hb := mul_le_mul_of_nonneg_right hx (mul_nonneg (sq_nonneg r) (abs_nonneg x))
        nth_rw 1 [←sq_abs x]
        nlinarith only [hb,show 0≤x^4 by positivity]
      · have hb := (sq_le_sq₀ (by positivity : 0≤2*r) (abs_nonneg x)).mpr (le_of_not_ge hx)
        rw [sq_abs] at hb
        nlinarith only [mul_le_mul_of_nonneg_right hb (sq_nonneg x),mul_nonneg (pow_pos h 3).le (abs_nonneg x)]
    have hp := Finset.sum_le_sum (s:=Finset.univ) fun s _ => point (linearEnergy a s)
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,h2] at hp
    have cancel : r^3*(d*r)≤r^3*(8*∑ s, |linearEnergy a s|) := by
      rw [←hr] at hp h4
      linarith only [hp,h4]
    exact le_of_mul_le_mul_left cancel (pow_pos h 3)

end
end GaloisForLFunctions.HTGeometry.SpectralGapMass
