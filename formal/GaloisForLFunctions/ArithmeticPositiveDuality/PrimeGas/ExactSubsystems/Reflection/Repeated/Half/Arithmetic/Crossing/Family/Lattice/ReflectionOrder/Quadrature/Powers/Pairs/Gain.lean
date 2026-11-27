import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Pairs.Bezout
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Angular

/-! # Exact sensitivity of two occupations of one elementary prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Pairs

open Real

def harmonics (a b : ℕ+) : Bool → ℕ+
  | false => a
  | true => b

private theorem two_radius (a b : ℕ+) (c : Bool → ℝ) :
    fitRadius (harmonics a b) c =
      |(b : ℝ)*c false-(a : ℝ)*c true| / ((a : ℝ)+(b : ℝ)) := by
  apply le_antisymm
  · apply peak_le.mpr
    rintro ⟨i,j⟩
    cases i <;> cases j <;>
      simp [harmonics,abs_sub_comm,add_comm] <;> positivity
  · exact to_peak (fun ij : Bool × Bool =>
      |(harmonics a b ij.2 : ℝ)*c ij.1-(harmonics a b ij.1 : ℝ)*c ij.2| /
        ((harmonics a b ij.1 : ℝ)+(harmonics a b ij.2 : ℝ))) (false,true)

/-- For coprime occupations the finite interval problem has defect
zero or the reciprocal of the sum, according to the parity of the difference. -/
theorem primitive_defect (a b : ℕ+) (cop : Nat.Coprime a.val b.val) :
    defect (harmonics a b) = (residue a b : ℝ)/((a : ℝ)+(b : ℝ)) := by
  let k := harmonics a b
  have radius (c : Centers k) : fitRadius k (oddCenter k c) =
      |(b : ℝ)*(2*((c false).val : ℝ)+1)-(a : ℝ)*(2*((c true).val : ℝ)+1)| /
        ((a : ℝ)+(b : ℝ)) := two_radius a b _
  apply le_antisymm
  · obtain ⟨i,j,hit⟩ := finite_bezout a b cop
    let c : Centers k := fun | false => i | true => j
    apply (defect_le k c).trans
    rw [radius]
    have realEq : (b : ℝ)*(2*(i.val : ℝ)+1)-(a : ℝ)*(2*(j.val : ℝ)+1)=(residue a b : ℝ) := by
      exact_mod_cast hit
    change |(b : ℝ)*(2*(i.val : ℝ)+1)-(a : ℝ)*(2*(j.val : ℝ)+1)| / _ ≤ _
    rw [realEq,abs_of_nonneg (by exact_mod_cast (residue_bounds a b).1 : (0 : ℝ) ≤ residue a b)]
  · obtain ⟨c,u,near⟩ := defect_witness k
    apply le_trans _ ((fit_iff _ _ _).mp ⟨u,near⟩)
    rw [radius]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast least_odd a b (c false).val (c true).val

/-- Multiplying both occupations by a common factor changes only the
phase variable. All real phases are still attained. -/
theorem dilation (d a b : ℕ+) :
    gain (harmonics (d*a) (d*b))=gain (harmonics a b) := by
  have phases (y : ℝ) : angular (harmonics (d*a) (d*b)) y =
      angular (harmonics a b) ((d : ℝ)*y) := by
    unfold angular
    congr 1
    funext i
    have scale : (harmonics (d*a) (d*b) i : ℝ)*y =
        (harmonics a b i : ℝ)*((d : ℝ)*y) := by
      cases i <;> simp only [harmonics,PNat.mul_coe,Nat.cast_mul] <;> ring
    rw [scale]
  obtain ⟨u,hu⟩ := attain_gain (harmonics (d*a) (d*b))
  obtain ⟨v,hv⟩ := attain_gain (harmonics a b)
  have hd : (d : ℝ)≠0 := Nat.cast_ne_zero.mpr d.ne_zero
  apply le_antisymm
  · have le := gain_le (harmonics (d*a) (d*b)) (v/(d : ℝ))
    have recover : (d : ℝ)*(v/(d : ℝ))=v := by rw [mul_comm,div_mul_cancel₀ _ hd]
    rwa [phases,recover,hv] at le
  · exact (gain_le _ ((d : ℝ)*u)).trans_eq ((phases u).symm.trans hu)

/-- The positive reduced occupation of a shell after removing a divisor. -/
private def primitive (a g : ℕ+) (h : g.val ∣ a.val) : ℕ+ :=
  ⟨a.val/g.val,Nat.div_pos (Nat.le_of_dvd a.pos h) g.pos⟩

private theorem restore_primitive (a g : ℕ+) (h : g.val ∣ a.val) :
    g*primitive a g h=a := Subtype.ext (Nat.mul_div_cancel' h)

/-- Closed pair formula, expressed through the two positive reduced occupations. -/
theorem pair_gain (a b : ℕ+) :
    let g := a.val.gcd b.val
    let A := a.val/g
    let B := b.val/g
    gain (harmonics a b)=sin (π/2*(((((B : ℤ)-(A : ℤ))%2 : ℤ) : ℝ)/((A : ℝ)+(B : ℝ)))) := by
  let g : ℕ+ := ⟨a.val.gcd b.val,Nat.gcd_pos_of_pos_left _ a.pos⟩
  let A := primitive a g (Nat.gcd_dvd_left _ _)
  let B := primitive b g (Nat.gcd_dvd_right _ _)
  have cop : A.val.Coprime B.val := Nat.coprime_div_gcd_div_gcd g.pos
  have eq : gain (harmonics a b)=gain (harmonics A B) := by
    simpa only [A,B,restore_primitive] using dilation g A B
  rw [eq,gain,primitive_defect A B cop]
  rfl

private theorem primitive_optimum (a b : ℕ+) (cop : a.val.Coprime b.val) :
    gain (harmonics a b) ≤ 1/2 ∧
      (gain (harmonics a b)=1/2 ↔ a.val+b.val=3) := by
  have ha := a.pos
  have hb := b.pos
  have formula : gain (harmonics a b)=
      sin (π/2*((residue a b : ℝ)/((a : ℝ)+(b : ℝ)))) := by
    rw [gain,primitive_defect a b cop]
  by_cases three : a.val+b.val=3
  · have pair : (a.val=1 ∧ b.val=2) ∨ (a.val=2 ∧ b.val=1) := by omega
    have hit : gain (harmonics a b)=1/2 := by
      rw [formula]
      rcases pair with ⟨u,v⟩ | ⟨u,v⟩ <;>
        norm_num [residue,u,v] <;> convert sin_pi_div_six using 2 <;> ring
    exact ⟨hit.le,iff_of_true hit three⟩
  · have strict : gain (harmonics a b)<1/2 := by
      rw [formula]
      by_cases two : a.val+b.val=2
      · have u : a.val=1 := by omega
        have v : b.val=1 := by omega
        norm_num [residue,u,v]
      · have bound : (3 : ℝ)<(a : ℝ)+(b : ℝ) := by
          exact_mod_cast (show 3<a.val+b.val by omega)
        have den : 0<(a : ℝ)+(b : ℝ) := by linarith only [bound]
        obtain ⟨low,high⟩ := residue_bounds a b
        have hlo : (0 : ℝ) ≤ residue a b := by exact_mod_cast low
        have hhi : (residue a b : ℝ) ≤ 1 := by exact_mod_cast high
        have fr : (residue a b : ℝ)/((a : ℝ)+(b : ℝ))<1/3 := by
          apply (div_lt_iff₀ den).mpr
          linarith only [bound,hhi]
        have angle := mul_lt_mul_of_pos_left fr (by positivity : 0<π/2)
        rw [show π/2*(1/3)=π/6 by ring] at angle
        rw [←sin_pi_div_six]
        have hp := pi_pos
        apply strictMonoOn_sin _ _ angle
        · exact ⟨(by linarith only [hp] : -(π/2)≤0).trans
            (mul_nonneg (by positivity) (div_nonneg hlo den.le)),
            angle.le.trans (by linarith only [hp])⟩
        · constructor <;> linarith only [hp]
    exact ⟨strict.le,iff_of_false strict.ne three⟩

/-- Every pair has normalized gain at most one half. Equality holds
exactly when one shell is the square of the other. -/
theorem optimal_pair (a b : ℕ+) :
    gain (harmonics a b) ≤ 1/2 ∧
      (gain (harmonics a b)=1/2 ↔ b.val=2*a.val ∨ a.val=2*b.val) := by
  let g : ℕ+ := ⟨a.val.gcd b.val,Nat.gcd_pos_of_pos_left _ a.pos⟩
  let A := primitive a g (Nat.gcd_dvd_left _ _)
  let B := primitive b g (Nat.gcd_dvd_right _ _)
  have cop : A.val.Coprime B.val := Nat.coprime_div_gcd_div_gcd g.pos
  have ea : g*A=a := restore_primitive _ _ _
  have eb : g*B=b := restore_primitive _ _ _
  have same := dilation g A B
  rw [ea,eb] at same
  obtain ⟨bound,eq⟩ := primitive_optimum A B cop
  refine ⟨same.le.trans bound,?_⟩
  rw [same,eq]
  have ha := A.pos
  have hb := B.pos
  have ca : g.val*A.val=a.val := congrArg Subtype.val ea
  have cb : g.val*B.val=b.val := congrArg Subtype.val eb
  constructor
  · intro three
    rcases (show (A.val=1 ∧ B.val=2) ∨ (A.val=2 ∧ B.val=1) by omega) with ⟨u,v⟩ | ⟨u,v⟩
    · exact Or.inl (by rw [←ca,←cb,u,v]; omega)
    · exact Or.inr (by rw [←ca,←cb,u,v]; omega)
  · rintro (twice | twice)
    · have scaled : g.val*B.val=g.val*(2*A.val) := by rw [cb,twice,←ca]; ring
      have dbl := Nat.eq_of_mul_eq_mul_left g.pos scaled
      have divides : A.val ∣ B.val := ⟨2,by rw [dbl,Nat.mul_comm]⟩
      have dg := Nat.dvd_gcd (dvd_refl A.val) divides
      rw [cop.gcd_eq_one] at dg
      have small := Nat.le_of_dvd Nat.zero_lt_one dg
      omega
    · have scaled : g.val*A.val=g.val*(2*B.val) := by rw [ca,twice,←cb]; ring
      have dbl := Nat.eq_of_mul_eq_mul_left g.pos scaled
      have divides : B.val ∣ A.val := ⟨2,by rw [dbl,Nat.mul_comm]⟩
      have dg := Nat.dvd_gcd divides (dvd_refl B.val)
      rw [cop.gcd_eq_one] at dg
      have small := Nat.le_of_dvd Nat.zero_lt_one dg
      omega

#print axioms optimal_pair

#print axioms primitive_defect
#print axioms dilation
#print axioms pair_gain

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Pairs
