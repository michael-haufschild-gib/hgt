import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.IntegralLift
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Dominance
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Calibration

/-! # A uniform bound on the dilation of any resonant specialization -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Real MvPolynomial

/-- Every inclusion along the integral dilates of these shells bounds the
target scale in units of the source scale. -/
def ScaleBound {ι : Type*} (a : ι → ℕ+) (t C : ℝ) := ∀ A B : ℕ, 0<A → 0<B →
  sampledKernel a (t*A) ≤ sampledKernel a (t*B) → (B : ℝ)<C*A

/-- Complex realizability bounds signed real target orders as well. -/
def RadialBound {ι : Type*} (a : ι → ℕ+) (t C : ℝ) := ∀ A : ℕ, 0<A → ∀ b : ℝ,
  sampledKernel a (t*A) ≤ sampledKernel a (t*b) → |b|<C*A

private theorem bound_of_relation {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℕ+)
    (t : ℝ) (inj : Function.Injective (fun i => t*energy (a i)))
    (c : ι → ℤ) (live : ∀ i, c i ≠ 0)
    (zero : ∑ i, (c i : ℝ)*exp (t*energy (a i))=0) :
    ∃ C : ℝ, 0<C ∧ RadialBound a t C := by
  classical
  let E (i : ι) := t*energy (a i)
  let x (i : ι) := exp (E i)
  let P : MvPolynomial ι ℤ := ∑ i, C (c i)*X i
  have evaluation {K : Type} [Field K] [CharZero K] (z : ι → K) :
      aeval z P=∑ i, (c i : K)*z i := by
    simp only [P,map_sum,map_mul,aeval_C,aeval_X]
    rfl
  obtain ⟨M,pos,dom⟩ := radial_bound E inj c live
  refine ⟨M,pos,fun A hA B inc => ?_⟩
  have aPos : (0 : ℝ)<A := Nat.cast_pos.mpr hA
  let r := (B : ℝ)/A
  have cancel (i : ι) : (A : ℝ)*(r*E i)=(t*B)*energy (a i) := by
    dsimp only [r,E]
    field_simp
  let y i := exp ((t*B)*energy (a i))
  have xa : x^A=fun i => exp ((t*A)*energy (a i)) := by
    funext i
    change exp (E i)^A=_
    rw [← exp_nat_mul]
    congr 1
    dsimp only [E]
    ring
  obtain ⟨z,roots,keep⟩ := lift_power_relations x y hA (by rw [xa]; exact inc)
  have moduli (i : ι) : ‖z i‖=exp (r*E i) := by
    apply (pow_left_inj₀ (norm_nonneg _) (exp_pos _).le hA.ne').mp
    rw [← norm_pow,roots,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (exp_pos _),← exp_nat_mul,cancel]
  have bound := dom r z moduli ((evaluation z).symm.trans (keep P ((evaluation x).trans zero)))
  change |B/(A : ℝ)|<M at bound
  rw [abs_div,abs_of_pos aPos,div_lt_iff₀ aPos] at bound
  exact bound

private theorem injective_energy : Function.Injective energy := by
  intro a b h
  have eq := congrArg exp h
  simp only [energy,exp_log (Nat.cast_pos.mpr a.pos),exp_log (Nat.cast_pos.mpr b.pos)] at eq
  exact PNat.coe_injective (Nat.cast_injective (R := ℝ) eq)

/-- A single finite set of integer labels controls all integral dilations of
a resonant order, regardless of the sizes of the two integer scales. -/
theorem resonance_radial_bound {t : ℝ} (ht : 0<t) (res : Resonant t) :
    ∃ (S : Finset Exponent) (C : ℝ), 0<C ∧ RadialBound (fun i : S => label i.val) t C := by
  classical
  obtain ⟨P,hP,root⟩ := (resonant_iff_polynomial t).mp res
  let S := P.support
  obtain ⟨w,hw⟩ := support_nonempty.mpr hP
  letI : Nonempty S := ⟨⟨w,hw⟩⟩
  let a (i : S) := label i.val
  let c (i : S) := coeff i.val P
  have inj : Function.Injective (fun i => t*energy (a i)) :=
    (mul_right_injective₀ ht.ne').comp (injective_energy.comp (label.injective.comp Subtype.val_injective))
  have zero : ∑ i : S, (c i : ℝ)*exp (t*energy (a i))=0 := by
    let g (v : Exponent) := ((coeff v P : ℤ) : ℝ)*shellPower t (label v)
    have sum := Finset.sum_coe_sort P.support g
    exact (show (∑ i : S, (c i : ℝ)*exp (t*energy (a i)))=∑ v ∈ P.support, g v from by
      simpa only [g,shellPower_exp] using sum).trans ((value_sum P t).symm.trans root)
  obtain ⟨C,pos,bound⟩ := bound_of_relation a t inj c (fun i => mem_support_iff.mp i.property) zero
  exact ⟨S,C,pos,bound⟩

theorem resonance_scale_bound {t : ℝ} (ht : 0<t) (res : Resonant t) :
    ∃ (S : Finset Exponent) (C : ℝ), 0<C ∧ ScaleBound (fun i : S => label i.val) t C := by
  obtain ⟨S,C,pos,bound⟩ := resonance_radial_bound ht res
  refine ⟨S,C,pos,fun A B ha hb inc => ?_⟩
  simpa only [abs_of_pos (Nat.cast_pos.mpr hb : (0 : ℝ)<B)] using bound A ha B inc

#print axioms resonance_radial_bound
#print axioms resonance_scale_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
