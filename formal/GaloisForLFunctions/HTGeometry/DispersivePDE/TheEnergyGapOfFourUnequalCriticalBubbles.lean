import GaloisForLFunctions.HTGeometry.CoppoKerrPhaseGeometry

/-!
# Global minimizers for four unequal synchronized bubbles

The four-component system of Fan–Giaretto–Soave, Theorem 1.8, has a
quartic amplitude energy in dimension four. In relative amplitudes about
any positive synchronized state, its exact energy gap is a sum of seven
squares. Thus unequal self-interactions still determine all signed
minimizers and the global minimum energy.
-/

noncomputable section
namespace HTGeometry
namespace CriticalQuartet

/-- Product of the four amplitudes in the competitive interaction. -/
def product (x : Fin 4 → ℝ) : ℝ := x 0*x 1*x 2*x 3

/-- Sum over the four component labels. -/
def total (x : Fin 4 → ℝ) : ℝ := x 0+x 1+x 2+x 3

theorem product_pos {x : Fin 4 → ℝ} (hx : ∀ i, 0 < x i) : 0 < product x :=
  mul_pos (mul_pos (mul_pos (hx 0) (hx 1)) (hx 2)) (hx 3)

private theorem total_nonneg {x : Fin 4 → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ total x :=
  add_nonneg (add_nonneg (add_nonneg (hx 0) (hx 1)) (hx 2)) (hx 3)

theorem le_total {x : Fin 4 → ℝ} (hx : ∀ i, 0 ≤ x i) (j : Fin 4) : x j ≤ total x := by
  unfold total
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by fin_cases j <;> simp
  rcases cases with rfl|rfl|rfl|rfl <;> linarith only [hx 0,hx 1,hx 2,hx 3]

/-- Four-mode Kerr energy. Multiplication by four removes the conventional
denominator in the quartic potential. -/
def energy (μ : Fin 4 → ℝ) (m b : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  total (fun i => μ i*x i^4-2*m*x i^2)-4*b*product x

/-- Positive synchronized equations after multiplying the equation of
each amplitude by that amplitude. -/
def Synchronized (μ : Fin 4 → ℝ) (m b : ℝ) (x : Fin 4 → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ ∀ i, μ i*x i^4=m*x i^2+b*product x

/-- Pairing the amplitudes of an equal-coefficient quartet gives exactly
twice the two-site Kerr energy. -/
theorem paired_energy (m b x y : ℝ) :
    energy (fun _ => 1) m b ![x,x,y,y]=2*coppoKerrEnergy m (-b) x y := by
  change (1*x^4-2*m*x^2)+(1*x^4-2*m*x^2)+(1*y^4-2*m*y^2)+(1*y^4-2*m*y^2)-4*b*(x*x*y*y)=_
  unfold coppoKerrEnergy
  ring

/-- The quartic arithmetic-geometric mean defect is three squares,
including the sign constraint on the whole product. -/
def mixingGap (t : Fin 4 → ℝ) : ℝ :=
  (t 0^2-t 1^2)^2+(t 2^2-t 3^2)^2+2*(t 0*t 1-t 2*t 3)^2

theorem mixingGap_identity (t : Fin 4 → ℝ) : mixingGap t=total (fun i => t i^4)-4*product t := by
  unfold mixingGap total product
  ring

private theorem mixing_nonneg (t : Fin 4 → ℝ) : 0 ≤ mixingGap t := by unfold mixingGap; positivity

/-- The mixing term vanishes precisely on the common-magnitude rays
with positive product, including their common origin. -/
theorem mixingGap_eq_zero (t : Fin 4 → ℝ) : mixingGap t=0 ↔
    (∀ i, t i^2=t 0^2) ∧ product t=t 0^4 := by
  constructor
  · intro hz
    unfold mixingGap at hz
    have A := sq_nonneg (t 0^2-t 1^2)
    have B := sq_nonneg (t 2^2-t 3^2)
    have C := sq_nonneg (t 0*t 1-t 2*t 3)
    have h01 : t 0^2=t 1^2 := sub_eq_zero.mp (sq_eq_zero_iff.mp
      (show (t 0^2-t 1^2)^2=0 by linarith only [hz,A,B,C]))
    have h23 : t 2^2=t 3^2 := sub_eq_zero.mp (sq_eq_zero_iff.mp
      (show (t 2^2-t 3^2)^2=0 by linarith only [hz,A,B,C]))
    have pair : t 0*t 1=t 2*t 3 := sub_eq_zero.mp (sq_eq_zero_iff.mp
      (show (t 0*t 1-t 2*t 3)^2=0 by linarith only [hz,A,B,C]))
    have same : t 0^2=t 2^2 := by
      apply (sq_eq_sq₀ (sq_nonneg _) (sq_nonneg _)).mp
      calc (t 0^2)^2 = (t 0*t 1)^2 := by rw [mul_pow,←h01]; ring
           _ = (t 2*t 3)^2 := by rw [pair]
           _ = (t 2^2)^2 := by rw [mul_pow,←h23]; ring
    refine ⟨fun i => ?_,?_⟩
    · fin_cases i <;> first | rfl | exact h01.symm | exact same.symm | exact h23.symm.trans same.symm
    · change t 0*t 1*t 2*t 3=t 0^4
      rw [mul_assoc (t 0*t 1),←pair,←sq,mul_pow,←h01]
      ring
  · rintro ⟨hs,hp⟩
    have fourth (i : Fin 4) : t i^4=t 0^4 := by
      calc t i^4 = (t i^2)^2 := by ring
           _ = (t 0^2)^2 := by rw [hs i]
           _ = _ := by ring
    rw [mixingGap_identity,hp]
    unfold total
    linarith only [fourth 1,fourth 2,fourth 3]

/-- Four radial squares and three mixing squares give the global gap at
arbitrary relative amplitudes, including negative or zero entries. -/
theorem energy_gap {μ x : Fin 4 → ℝ} {m b : ℝ}
    (h : Synchronized μ m b x) (t : Fin 4 → ℝ) :
    energy μ m b (fun i => x i*t i) + m*total (fun i => x i^2) =
      total (fun i => m*x i^2*(t i^2-1)^2)+b*product x*mixingGap t := by
  have site i : μ i*(x i*t i)^4 - 2*m*(x i*t i)^2 + m*x i^2 =
      m*x i^2*(t i^2-1)^2 + (b*product x)*t i^4 := by
    have p := congrArg (fun a : ℝ => a*t i^4) (h.2 i)
    change (μ i*x i^4)*t i^4=(m*x i^2+b*product x)*t i^4 at p
    linarith only [p]
  have factor : product (fun i => x i*t i)=product x*product t := by unfold product; ring
  rw [energy,factor,mixingGap_identity]
  unfold total
  linarith only [site 0,site 1,site 2,site 3]

/-- The energy of a synchronized positive state equals its negative
quadratic mass. -/
theorem energy_at_solution {μ x : Fin 4 → ℝ} {m b : ℝ} (h : Synchronized μ m b x) :
    energy μ m b x = -m*total (fun i => x i^2) := by
  have gap := energy_gap h (fun _ => 1)
  simp only [mul_one,one_pow,sub_self,zero_pow (by decide : 2≠0),mul_zero,mixingGap,add_zero,total] at gap
  change energy μ m b x = _
  unfold total
  linarith only [gap]

private theorem restore {x : Fin 4 → ℝ} (hx : ∀ i, 0 < x i) (y : Fin 4 → ℝ) :
    (fun i => x i*(y i/x i))=y := by
  funext i
  rw [mul_comm,div_mul_cancel₀ _ (hx i).ne']

/-- Each positive synchronized state is a global minimizer on the full
real amplitude space. -/
theorem global_min {μ x : Fin 4 → ℝ} {m b : ℝ} (hm : 0 < m) (hb : 0 < b)
    (h : Synchronized μ m b x) (y : Fin 4 → ℝ) : energy μ m b x ≤ energy μ m b y := by
  let t i := y i/x i
  have g := energy_gap h t
  rw [restore h.1 y] at g
  have rad := total_nonneg (fun i => mul_nonneg (mul_nonneg hm.le (sq_nonneg (x i))) (sq_nonneg (t i^2-1)))
  have mix := mul_nonneg (mul_pos hb (product_pos h.1)).le (mixing_nonneg t)
  linarith only [g,rad,mix,energy_at_solution h]

/-- Complete signed equality law. All four relative amplitudes have
unit square and their product is one. -/
theorem signed_minimizers {μ x : Fin 4 → ℝ} {m b : ℝ} (hm : 0 < m) (hb : 0 < b)
    (h : Synchronized μ m b x) (t : Fin 4 → ℝ) :
    energy μ m b (fun i => x i*t i)=energy μ m b x ↔
      (∀ i, t i^2=1) ∧ product t=1 := by
  let A i := m*x i^2*(t i^2-1)^2
  have pos i : 0 ≤ A i := mul_nonneg (mul_nonneg hm.le (sq_nonneg _)) (sq_nonneg _)
  have hc := mul_pos hb (product_pos h.1)
  have mix := mixing_nonneg t
  have g := energy_gap h t
  change _=total A+b*product x*mixingGap t at g
  have value := energy_at_solution h
  have four (he : ∀ i, t i^2=1) : total (fun i => t i^4)=4 := by
    have p (i : Fin 4) : t i^4=1 := by
      rw [show t i^4=(t i^2)^2 by ring,he i,one_pow]
    norm_num [total,p]
  constructor
  · intro eq
    have vanish : total A+b*product x*mixingGap t=0 := by linarith only [g,eq,value]
    have rad := total_nonneg pos
    have mixprice := mul_nonneg hc.le mix
    have hzero : total A=0 := by linarith only [rad,mixprice,vanish]
    have all (i : Fin 4) : t i^2=1 := by
      have z := le_total pos i
      rw [hzero] at z
      have ai : A i=0 := le_antisymm z (pos i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp ai).resolve_left
        (mul_pos hm (sq_pos_of_pos (h.1 i))).ne'))
    have mz : mixingGap t=0 := (mul_eq_zero.mp (show b*product x*mixingGap t=0 by
      linarith only [vanish,hzero])).resolve_left hc.ne'
    rw [mixingGap_identity,four all] at mz
    exact ⟨all,by linarith only [mz]⟩
  · rintro ⟨all,ht⟩
    have rz : total A=0 := by simp [total,A,all]
    rw [mixingGap_identity,four all,ht,rz] at g
    linarith only [g,value]

/-- Strict positivity selects exactly one of the sign-related global
minimizers, so there is at most one positive synchronized state. -/
theorem synchronized_unique {μ x y : Fin 4 → ℝ} {m b : ℝ} (hm : 0 < m) (hb : 0 < b)
    (hx : Synchronized μ m b x) (hy : Synchronized μ m b y) : x=y := by
  let t i := y i/x i
  have eq : energy μ m b (fun i => x i*t i)=energy μ m b x := by
    rw [restore hx.1 y]
    exact le_antisymm (global_min hm hb hy x) (global_min hm hb hx y)
  have magn := ((signed_minimizers hm hb hx t).mp eq).1
  funext i
  have hi : 0 < t i := div_pos (hy.1 i) (hx.1 i)
  have one : t i=1 := (sq_eq_sq₀ hi.le zero_le_one).mp (by simpa only [one_pow] using magn i)
  exact ((div_eq_one_iff_eq (hx.1 i).ne').mp one).symm

/-- Exact remainder in the optimal magnitude-stability inequality. Each
radial remainder vanishes only at zero or at the synchronized magnitude. -/
theorem radial_stability_remainder {μ x : Fin 4 → ℝ} {m b : ℝ}
    (h : Synchronized μ m b x) (t : Fin 4 → ℝ) :
    energy μ m b (fun i => x i*t i)-energy μ m b x-
      m*total (fun i => (|x i*t i|-x i)^2) =
    total (fun i => m*x i^2*(|t i|-1)^2*|t i| * (|t i|+2)) + b*product x*mixingGap t := by
  have site (i : Fin 4) : m*x i^2*(t i^2-1)^2-m*(|x i*t i|-x i)^2 =
      m*x i^2*(|t i|-1)^2*|t i| * (|t i|+2) := by
    rw [abs_mul,abs_of_pos (h.1 i),←sq_abs (t i)]
    ring
  have gap := energy_gap h t
  have base := energy_at_solution h
  unfold total at gap base ⊢
  linarith only [gap,base,site 0,site 1,site 2,site 3]

/-- Equality in sharp magnitude stability occurs at the origin and at
the signed global minimizers. -/
theorem radial_stability_equality {μ x : Fin 4 → ℝ} {m b : ℝ} (hm : 0<m) (hb : 0<b)
    (h : Synchronized μ m b x) (t : Fin 4 → ℝ) :
    energy μ m b (fun i => x i*t i)-energy μ m b x =
      m*total (fun i => (|x i*t i|-x i)^2) ↔
    (∀ i, t i=0) ∨ ((∀ i, t i^2=1) ∧ product t=1) := by
  let R i := m*x i^2*(|t i|-1)^2*|t i| * (|t i|+2)
  have pos (i : Fin 4) : 0≤R i := by dsimp only [R]; positivity
  have hc := mul_pos hb (product_pos h.1)
  have mix := mul_nonneg hc.le (mixing_nonneg t)
  have gap := radial_stability_remainder h t
  change _=total R+b*product x*mixingGap t at gap
  constructor
  · intro eq
    have rz : total R=0 := by linarith only [gap,eq,total_nonneg pos,mix]
    have mz : mixingGap t=0 := (mul_eq_zero.mp (show b*product x*mixingGap t=0 by
      linarith only [gap,eq,rz])).resolve_left hc.ne'
    obtain ⟨equal,prod⟩ := (mixingGap_eq_zero t).mp mz
    by_cases z : t 0=0
    · exact Or.inl (fun i => sq_eq_zero_iff.mp (by simpa only [z,zero_pow (by decide : 2≠0)] using equal i))
    have mag := abs_pos.mpr z
    have zero : R 0=0 := le_antisymm ((le_total pos 0).trans_eq rz) (pos 0)
    have pre := (mul_eq_zero.mp zero).resolve_right (show 0 < |t 0|+2 by positivity).ne'
    have sqz := (mul_eq_zero.mp ((mul_eq_zero.mp pre).resolve_right mag.ne')).resolve_left
      (mul_pos hm (sq_pos_of_pos (h.1 0))).ne'
    have unit : |t 0|=1 := sub_eq_zero.mp (sq_eq_zero_iff.mp sqz)
    have u2 : t 0^2=1 := by rw [←sq_abs,unit,one_pow]
    refine Or.inr ⟨fun i => (equal i).trans u2,?_⟩
    calc product t = t 0^4 := prod
         _ = (t 0^2)^2 := by ring
         _ = 1 := by rw [u2,one_pow]
  · rintro (zero | unit)
    · have rg : total R=0 := by simp [total,R,zero]
      have mg : mixingGap t=0 := by simp [mixingGap,zero]
      linarith only [gap,rg,mg,show b*product x*mixingGap t=0 by rw [mg,mul_zero]]
    · have eq := (signed_minimizers hm hb h t).mpr unit
      have mag (i : Fin 4) : |t i|=1 := (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp
        (by simpa only [sq_abs,one_pow] using unit.1 i)
      have site (i : Fin 4) : (|x i*t i|-x i)^2=0 := by rw [abs_mul,abs_of_pos (h.1 i),mag,mul_one,sub_self]; norm_num
      simp only [eq,sub_self,total,site,add_zero,mul_zero]

/-- Global quadratic stability in the four magnitudes. Vanishing
amplitudes realize equality and determine the optimal constant m. -/
theorem best_radial_stability {μ x : Fin 4 → ℝ} {m b : ℝ} (hm : 0 < m) (hb : 0 < b)
    (h : Synchronized μ m b x) (c : ℝ) :
    (∀ y : Fin 4 → ℝ, c*total (fun i => (|y i|-x i)^2) ≤ energy μ m b y-energy μ m b x) ↔ c≤ m := by
  constructor
  · intro all
    have z := all (fun _ => 0)
    simp only [abs_zero,zero_sub,neg_sq,energy,total,product,zero_pow (by decide : 4≠0),
      zero_pow (by decide : 2≠0),mul_zero,sub_zero,add_zero] at z
    have base := energy_at_solution h
    unfold energy total product at base
    have ht : 0 < x 0^2+x 1^2+x 2^2+x 3^2 := by
      have hx := sq_pos_of_pos (h.1 0)
      positivity
    apply le_of_mul_le_mul_right _ ht
    linarith only [z,base]
  · intro hc y
    apply (mul_le_mul_of_nonneg_right hc (total_nonneg (fun i => sq_nonneg (|y i|-x i)))).trans
    let t i := y i/x i
    have rem := radial_stability_remainder h t
    have site (i : Fin 4) : x i*t i=y i := congrFun (restore h.1 y) i
    simp only [site] at rem
    have rad := total_nonneg (fun i => show 0≤m*x i^2*(|t i|-1)^2*|t i| * (|t i|+2) by positivity)
    have mix := mul_nonneg (mul_pos hb (product_pos h.1)).le (mixing_nonneg t)
    linarith only [rem,rad,mix]

#print axioms energy_gap
#print axioms best_radial_stability
#print axioms radial_stability_equality
#print axioms global_min
#print axioms signed_minimizers
#print axioms synchronized_unique
end CriticalQuartet
end HTGeometry
