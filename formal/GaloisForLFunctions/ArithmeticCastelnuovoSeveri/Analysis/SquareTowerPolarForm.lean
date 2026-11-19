import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.SquareTowerPolarCoordinates
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CrossTowerCollarAndFiniteEulerLatticePositivity

/-!
# Integer levels of the arithmetic polar form on square towers

On sites 1,b²,…,b²ᵈ, the square roots in the arithmetic polar kernel
are rational powers of b. Multiplying the form by bᵈ gives twice the
product of the two integral reciprocal readings of the coefficients.
Thus a level consists of congruence-restricted divisor pairs, each with
a freely variable integer lattice of rank d−1 when d≥1.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SquareTower

def sites (b : Base) (n : ℕ) : Fin n ↪ ℕ where
  toFun i := (b.val^i.val)^2
  inj' i j h := Fin.ext (Nat.pow_right_injective b.property (Nat.pow_left_injective (by decide : 2≠0) h))

private theorem site_ratio (b : Base) {n : ℕ} (i j : Fin n) :
    Real.sqrt ((sites b n j:ℝ)/(sites b n i:ℝ))=(b.val:ℝ)^j.val/(b.val:ℝ)^i.val := by
  change Real.sqrt ((((b.val^j.val)^2:ℕ):ℝ)/(((b.val^i.val)^2:ℕ):ℝ))=_
  simp only [Nat.cast_pow]
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (by positivity),Real.sqrt_sq (by positivity)]

theorem complementary_exponents {d : ℕ} (i : Fin (d+1)) : i.val+i.rev.val=d := by
  rw [Fin.val_rev]
  have h := i.isLt
  omega

/-- The actual polar form on an arbitrary integer-valued lattice section
is an integral product after multiplication by half the endpoint scale. -/
theorem lattice_polar_product (b : Base) (d : ℕ) (c : ℕ → ℤ) :
    let x : Coeff (d+1) := fun i => c (sites b (d+1) i)
    (b.val:ℝ)^d*latticePolarForm (univ.map (sites b (d+1))) (fun a => (c a:ℝ)) =
      2*(forward b.val x:ℝ)*(backward b.val x:ℝ) := by
  intro x
  let u (i : Fin (d+1)) := (x i:ℝ)*(b.val:ℝ)^i.val
  let v (i : Fin (d+1)) := (x i:ℝ)/(b.val:ℝ)^i.val
  have factor : latticePolarForm (univ.map (sites b (d+1))) (fun a => (c a:ℝ)) =
      2*(∑ i,u i)*(∑ i,v i) := by
    calc
      _ = ∑ i, ∑ j, (u i*v j+v i*u j) := by
        simp only [latticePolarForm,sum_map,site_ratio]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        dsimp only [u,v,x]
        ring
      _ = (∑ i,u i)*(∑ j,v j)+(∑ i,v i)*(∑ j,u j) := by
        simp only [sum_mul,sum_add_distrib]
        simp only [mul_sum]
      _ = _ := by ring
  have left : (forward b.val x:ℝ)=∑ i,u i := by simp [forward,u]
  have hp : (0:ℝ)<b.val := by exact_mod_cast (show 0<b.val by have h := b.property; omega)
  have right : (b.val:ℝ)^d*(∑ i,v i)=(backward b.val x:ℝ) := by
    unfold backward
    push_cast
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    have prod : (b.val:ℝ)^i.val*(b.val:ℝ)^i.rev.val=(b.val:ℝ)^d := by
      rw [←pow_add,complementary_exponents]
    dsimp only [v]
    rw [←prod]
    field_simp [pow_ne_zero i.val hp.ne']
  rw [factor,left,←right]
  ring

private def extend (b : Base) {n : ℕ} (x : Coeff n) (a : ℕ) : ℤ := by
  classical
  exact if h : ∃ i, sites b n i=a then x h.choose else 0

private theorem extend_at (b : Base) {n : ℕ} (x : Coeff n) (i : Fin n) : extend b x (sites b n i)=x i := by
  have h : ∃ j, sites b n j=sites b n i := ⟨i,rfl⟩
  rw [extend,dif_pos h]
  exact congrArg x ((sites b n).injective h.choose_spec)

/-- The arithmetic polar pairing of integer coefficients supported on the square tower. -/
def polar (b : Base) {d : ℕ} (x : Coeff (d+1)) :=
  latticePolarForm (univ.map (sites b (d+1))) (fun a => (extend b x a:ℝ))

theorem polar_product (b : Base) {d : ℕ} (x : Coeff (d+1)) :
    (b.val:ℝ)^d*polar b x=2*(forward b.val x:ℝ)*(backward b.val x:ℝ) := by
  simpa only [polar,extend_at] using lattice_polar_product b d (extend b x)

theorem normalized_level_iff (b : Base) {d : ℕ} (x : Coeff (d+1)) (N : ℤ) :
    (b.val:ℝ)^d*polar b x=2*(N:ℝ) ↔ forward b.val x*backward b.val x=N := by
  rw [polar_product,mul_assoc,mul_right_inj' (by norm_num : (2:ℝ)≠0)]
  norm_cast

/-- Level two has the same polar energy as each signed single-site coefficient. -/
theorem unit_iff (b : Base) {d : ℕ} (x : Coeff (d+1)) :
    polar b x=2 ↔ forward b.val x*backward b.val x=(b.val:ℤ)^d := by
  have hp : (0:ℝ)<b.val := by exact_mod_cast (show 0<b.val by have h := b.property; omega)
  have h := normalized_level_iff b x ((b.val:ℤ)^d)
  push_cast at h
  rw [mul_comm (2:ℝ),mul_right_inj' (pow_ne_zero _ hp.ne')] at h
  exact h

/-- Every scaled integer level of the arithmetic polar form is parametrized
by its admissible factor pairs and exactly n unrestricted integer coordinates. -/
def polarLevelEquiv (b : Base) (n : ℕ) (N : ℤ) :
    {x : Coeff (n+2) // (b.val:ℝ)^(n+1)*polar b x=2*(N:ℝ)} ≃
      Admissible b.val (n+1) N × Coeff n :=
  (Equiv.subtypeEquivRight (fun x => normalized_level_iff b x N)).trans (levelEquiv b n N)

#print axioms lattice_polar_product
#print axioms unit_iff
#print axioms polarLevelEquiv
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SquareTower
