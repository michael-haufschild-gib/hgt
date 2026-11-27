import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Separation

/-! # Finite-order phase specializations of thermal probe orders -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open MvPolynomial

/-- Every original polynomial relation survives one assignment of torsion
phases to the target coordinates. The integer m is a common exponent. -/
def TorsionSpecialization (m : ℕ) (t u : ℝ) := ∃ χ : Nat.Primes → ℂ,
  (∀ p, χ p^m=1) ∧ ∀ P : PolynomialRing, value t P=0 →
    aeval (fun p => χ p*(coordinates u p : ℂ)) P=0

private theorem coord_power (s : ℝ) (m : ℕ) :
    coordinates (s*m)=(coordinates s)^m := by
  funext p
  exact Real.rpow_mul_natCast (by positivity : 0 ≤ (p.val : ℝ)) s m

/-- The integral lift yields compatible phases for all prime coordinates and all
relations simultaneously. Expansion of a polynomial proves the converse. -/
theorem powered_kernel_iff (t u : ℝ) {m : ℕ} (hm : 0 < m) :
    kernel (t*m) ≤ kernel (u*m) ↔ TorsionSpecialization m t u := by
  let f (p : Nat.Primes) := (coordinates u p : ℂ)
  have nz (p : Nat.Primes) : f p ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.rpow_pos_of_pos (Nat.cast_pos.mpr p.property.pos) u).ne'
  have target (p : Nat.Primes) : (coordinates (u*m) p : ℂ)=f p^m := by
    rw [coord_power,Pi.pow_apply,Complex.ofReal_pow]
  constructor
  · intro h
    obtain ⟨z,roots,keep⟩ := lift_power_relations (coordinates t) (coordinates (u*m)) hm (by
      rw [← coord_power]; exact h)
    let χ (p : Nat.Primes) := z p/f p
    have phase (p : Nat.Primes) : χ p^m=1 := by
      change (z p / f p)^m = 1
      rw [div_pow,roots,target,div_self (pow_ne_zero _ (nz p))]
    have recover : (fun p => χ p*(coordinates u p : ℂ))=z :=
      funext fun p => div_mul_cancel₀ _ (nz p)
    refine ⟨χ,phase,fun P hp => ?_⟩
    rw [recover]
    exact keep P hp
  · rintro ⟨χ,phase,keep⟩ P src
    let z (p : Nat.Primes) := χ p*f p
    have root : value t (expand m P)=0 := by
      change aeval (coordinates t) (expand m P)=0
      rw [aeval_expand,← coord_power]
      exact src
    have complexRoot : aeval (z^m) P=0 := by
      rw [← aeval_expand]
      exact keep _ root
    have power : z^m=fun p => (coordinates (u*m) p : ℂ) := by
      funext p
      change (χ p*f p)^m = _
      rw [mul_pow,phase,one_mul,target]
    rw [power] at complexRoot
    have transport :
        ((value (u*m) P : ℝ) : ℂ)=aeval (fun p => (coordinates (u*m) p : ℂ)) P :=
      comp_aeval_apply (coordinates (u*m)) (IsScalarTower.toAlgHom ℤ ℝ ℂ) P
    exact Complex.ofReal_eq_zero.mp (transport.trans complexRoot)

theorem scaled_forcing_iff {t u : ℝ} (ht : 0<t) (hu : 0<u) {m : ℕ} (hm : 0 < m) :
    Forces (t*m) (u*m) ↔ TorsionSpecialization m t u ∨ TorsionSpecialization m t (-u) := by
  have pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [forces_iff (mul_pos ht pos) (mul_pos hu pos),← neg_mul,powered_kernel_iff t u hm,
    powered_kernel_iff t (-u) hm]

/-- Existence of a rational dilation which forces a second order is equivalent
to existence of one common torsion exponent on a signed target. -/
theorem rational_dilation_iff {t u : ℝ} (ht : 0<t) (hu : 0<u) :
    (∃ q : ℚ, 0<q ∧ Forces ((q : ℝ)*t) ((q : ℝ)*u)) ↔
      ∃ m : ℕ, 0 < m ∧ (TorsionSpecialization m t u ∨ TorsionSpecialization m t (-u)) := by
  constructor
  · rintro ⟨q,hq,force⟩
    obtain ⟨a,b,ha,_,rep⟩ := natural_ratio q hq
    have step := forces_dilate force b
    have scale (x : ℝ) : (q : ℝ)*x*b=x*a := by linear_combination x*rep
    exact ⟨a,ha,(scaled_forcing_iff ht hu ha).mp (by simpa only [scale] using step)⟩
  · rintro ⟨m,hm,phase⟩
    refine ⟨(m : ℚ),Nat.cast_pos.mpr hm,?_⟩
    simpa only [Rat.cast_natCast,mul_comm (m : ℝ)] using (scaled_forcing_iff ht hu hm).mpr phase

#print axioms powered_kernel_iff
#print axioms scaled_forcing_iff
#print axioms rational_dilation_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
