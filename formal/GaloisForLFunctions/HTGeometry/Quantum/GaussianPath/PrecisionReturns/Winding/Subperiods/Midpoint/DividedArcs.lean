import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Primitive

/-! # Enclosing arcs at an exact integer subdivision of a scalar visit -/

open Set
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
noncomputable section
variable {I : Type*} {w : I → ℝ} {t r : ℝ} {b : I} {z : I → ℤ}

/-- Divide each winding with remainder. At one dth of the original
date the phases occupy d arcs of width r/d and leave a gap of width
at least (1−r)/d. -/
theorem divided_upper (h : Anchored w t r b z) {d : ℕ} (hd : 0<d) :
    Anchored w (t/d) (((d:ℝ)-1+r)/d) b (fun i => z i/(d:ℤ)) := by
  have hd' := Nat.cast_pos (α:=ℝ).mpr hd
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  intro i
  have hrec : (z i:ℝ)=((z i%(d:ℤ):ℤ):ℝ)+(d:ℝ)*((z i/(d:ℤ):ℤ):ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv (z i) (d:ℤ)).symm
  have hrem : (0:ℝ)≤((z i%(d:ℤ):ℤ):ℝ) := by exact_mod_cast Int.emod_nonneg (z i) hdZ.ne'
  have hle : ((z i%(d:ℤ):ℤ):ℝ)≤(d:ℝ)-1 := by
    exact_mod_cast (show z i%(d:ℤ)≤(d:ℤ)-1 by have := Int.emod_lt_of_pos (z i) hdZ; omega)
  have he : t/(d:ℝ)*(w i-w b)-((z i/(d:ℤ):ℤ):ℝ)=
      (t*(w i-w b)-(z i:ℝ)+((z i%(d:ℤ):ℤ):ℝ))/d := by
    field_simp [hd'.ne']
    linarith only [hrec]
  rw [he]
  exact ⟨div_nonneg (add_nonneg (h i).1 hrem) hd'.le,
    div_le_div_of_nonneg_right (by linarith only [(h i).2,hle]) hd'.le⟩

/-- A half-open gap between integers forces all full-date windings
to be divisible by d if the subdivided arc is too short. -/
theorem divisible_of_short_division (h : Anchored w t r b z)
    {d : ℕ} (hd : 0<d) {u : ℝ} {c : I} {y : I → ℤ}
    (hh : Anchored w (t/d) u c y) (hu : (d:ℝ)*u+r<1) : ∀ i, (d:ℤ) ∣ z i := by
  have hd' := Nat.cast_pos (α:=ℝ).mpr hd
  let E (i : I) := t*(w i-w b)-(z i:ℝ)
  let F (i : I) := t/(d:ℝ)*(w i-w c)-(y i:ℝ)
  have hr : 0≤r := (h b).1.trans (h b).2
  have eqn (i : I) :
      ((z i-(d:ℤ)*(y i-y b):ℤ):ℝ)=(d:ℝ)*F i-(d:ℝ)*F b-E i := by
    dsimp only [E,F]
    push_cast
    field_simp [hd'.ne']
    ring
  intro i
  let k := z i-(d:ℤ)*(y i-y b)
  have hb' : (d:ℝ)*F b ≤ (d:ℝ)*u := mul_le_mul_of_nonneg_left (hh b).2 hd'.le
  have hi' : (d:ℝ)*F i ≤ (d:ℝ)*u := mul_le_mul_of_nonneg_left (hh i).2 hd'.le
  have hn (j : I) : 0≤(d:ℝ)*F j := mul_nonneg hd'.le (hh j).1
  have hsmall : (-1:ℝ)<k ∧ (k:ℝ)<1 := by
    change -1<((z i-(d:ℤ)*(y i-y b):ℤ):ℝ) ∧ ((z i-(d:ℤ)*(y i-y b):ℤ):ℝ)<1
    rw [eqn]
    exact ⟨by linarith only [hn i,hb',(show E i≤r from (h i).2),hu],
      by linarith only [hi',hn b,(show 0≤E i from (h i).1),hr,hu]⟩
  have hz : (-1:ℤ)<k ∧ k<1 := by exact_mod_cast hsmall
  exact ⟨y i-y b,sub_eq_zero.mp (by change k=0; omega)⟩

#print axioms divided_upper
#print axioms divisible_of_short_division
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
