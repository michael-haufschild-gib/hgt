import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.WeilGaussianSemigroup

/-!
# Recovering cubic jump rates from heating

Position-square heating measures the sum of squared jump derivatives. For a
quadratic bank this determines every dephasing rate by the midpoint rule.
For a cubic bank one Gram entry remains free, the inner product of its linear
and cubic coefficients. One off-diagonal rate determines it.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.CubicHeating
open Finset

/-- Constant jump offsets cancel in both observables. -/
structure Jump where
  a : ℝ
  b : ℝ
  c : ℝ

def value (f : Jump) (x : ℝ) := f.a*x+f.b*x^2+f.c*x^3
def slope (f : Jump) (x : ℝ) := f.a+2*f.b*x+3*f.c*x^2

variable {k l : ℕ}

def heat (F : Fin k → Jump) (x : ℝ) := ∑ i, (slope (F i) x)^2
def rate (F : Fin k → Jump) (x y : ℝ) := ∑ i, gapCost (value (F i) x) (value (F i) y)
def mixed (F : Fin k → Jump) := ∑ i, (F i).a*(F i).c

/-- Four off-center evaluations recover the cubic coefficient of the quartic
heating profile. Its quartic coefficient also uses the origin. -/
private def predict (H : ℝ → ℝ) (A t d : ℝ) :=
  let B := (H 2 - H (-2) - 2*(H 1-H (-1)))/144
  let C := (H 2 + H (-2) - 4*(H 1+H (-1))+6*H 0)/216
  d^2/2*(H t+2*d^2*(A+2*B*t+3*C*t^2)+d^4*C)

private theorem atom (f : Jump) (t d : ℝ) :
    gapCost (value f (t+d)) (value f (t-d)) =
      predict (fun z => (slope f z)^2) (f.a*f.c) t d := by
  unfold gapCost value predict slope
  ring

private theorem sum_formula (F : Fin k → Jump) (s : Finset (Fin k)) (t d : ℝ) :
    ∑ i ∈ s, gapCost (value (F i) (t+d)) (value (F i) (t-d)) =
      predict (fun z => ∑ i ∈ s, (slope (F i) z)^2) (∑ i ∈ s, (F i).a*(F i).c) t d := by
  induction s using Finset.induction_on with
  | empty => simp [predict]
  | insert i s hi ih =>
    rw [sum_insert hi,ih,atom]
    simp only [sum_insert hi]
    unfold predict
    ring

private theorem rate_midpoint (F : Fin k → Jump) (x y : ℝ) :
    rate F x y = predict (heat F) (mixed F) ((x+y)/2) ((x-y)/2) := by
  have h := sum_formula F univ ((x+y)/2) ((x-y)/2)
  rwa [show (x+y)/2+(x-y)/2=x by ring,show (x+y)/2-(x-y)/2=y by ring] at h

/-- All pairs of banks with the same heating law differ by one universal
quartic gap term, regardless of their numbers of jumps. -/
theorem heating_ambiguity (F : Fin k → Jump) (G : Fin l → Jump) :
    heat F = heat G → ∀ x y, rate F x y - rate G x y = (x-y)^4/16*(mixed F-mixed G) := by
  intro he x y
  rw [rate_midpoint,rate_midpoint,he]
  unfold predict
  ring

/-- One rate measured at any two distinct levels repairs the missing Gram entry. -/
theorem single_rate_recovery (F : Fin k → Jump) (G : Fin l → Jump) (p : {z : ℝ × ℝ // z.1 ≠ z.2}) :
    heat F = heat G → (rate F p.val.1 p.val.2 = rate G p.val.1 p.val.2 ↔ rate F = rate G) := by
  intro he
  have h := heating_ambiguity F G he
  constructor
  · intro hp
    have hz := h p.val.1 p.val.2
    rw [hp,sub_self] at hz
    have hA := (mul_eq_zero.mp hz.symm).resolve_left (div_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr p.2)) (by norm_num))
    funext x y
    exact sub_eq_zero.mp (by rw [h x y,hA,mul_zero])
  · intro hR
    rw [hR]

/-- Without cubic terms the heating at the midpoint already gives the exact rate. -/
theorem quadratic_midpoint (A B : Fin k → ℝ) (x y : ℝ) :
    let F := fun i => Jump.mk (A i) (B i) 0
    rate F x y = (x-y)^2/8*heat F ((x+y)/2) := by
  dsimp only
  unfold rate heat
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  unfold gapCost value slope
  ring

/-- The ambiguity occurs already for two channels versus one. The squared
derivatives agree by the Pythagorean identity, while every separated pair
has different dephasing. -/
theorem cubic_counterexample :
    ∃ (F : Fin 1 → Jump) (G : Fin 2 → Jump), heat F = heat G ∧
      ∀ x y, rate F x y - rate G x y = (x-y)^4/24 := by
  let F : Fin 1 → Jump := fun _ => ⟨1,0,1/3⟩
  let G : Fin 2 → Jump := ![⟨1,0,-1/3⟩,⟨0,1,0⟩]
  have he : heat F = heat G := by
    funext x
    simp only [heat,Fin.sum_univ_one,Fin.sum_univ_two,F,G,Matrix.cons_val_zero,Matrix.cons_val_one,slope]
    ring
  refine ⟨F,G,he,fun x y => ?_⟩
  rw [heating_ambiguity F G he]
  simp only [mixed,Fin.sum_univ_one,Fin.sum_univ_two,F,G,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- The recovered scalar rates determine every arithmetic Gaussian evolution. -/
theorem evolution_recovery (F : Fin k → Jump) (G : Fin l → Jump) (p : {z : ℝ × ℝ // z.1 ≠ z.2}) :
    heat F = heat G → rate F p.val.1 p.val.2 = rate G p.val.1 p.val.2 →
    ∀ {n : ℕ} (v : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      jumpEvolution t (fun i j => value (F i) (v j)) A =
      jumpEvolution t (fun i j => value (G i) (v j)) A := by
  intro he hp n v A t
  have hR := (single_rate_recovery F G p he).mp hp
  ext i j
  change (Real.exp (-t*rate F (v i) (v j)) : ℂ)*A i j = (Real.exp (-t*rate G (v i) (v j)) : ℂ)*A i j
  rw [hR]

#print axioms heating_ambiguity
#print axioms single_rate_recovery
#print axioms quadratic_midpoint
#print axioms cubic_counterexample
#print axioms evolution_recovery
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.CubicHeating
