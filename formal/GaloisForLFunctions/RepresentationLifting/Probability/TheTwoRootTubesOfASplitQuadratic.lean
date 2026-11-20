import GaloisForLFunctions.RepresentationLifting.OperatorKernels.PadicNilpotence
import GaloisForLFunctions.RepresentationLifting.Probability.FiniteQuotientHaar
import GaloisForLFunctions.RHTower.FieldOnePadicCyclicHaarQuadrature
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Congruence tubes around a pair of p-adic roots

The product of the distances to two centers is a strictly increasing
function of the distance to the nearer center. This gives the exact
transition between one and two residue balls for a split quadratic,
including roots coinciding modulo high powers of two.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Metric
noncomputable section
variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

/-- Isosceles ultrametric triangles determine the product of the two
distances from their minimum and the distance between the centers. -/
theorem ultrametric_two_root_product (x a b : X) :
    dist x a*dist x b = min (dist x a) (dist x b)*max (dist a b) (min (dist x a) (dist x b)) := by
  have tri := dist_triangle_max a x b
  rw [dist_comm a x] at tri
  rcases lt_trichotomy (dist x a) (dist x b) with h|h|h
  · have hab := IsUltrametricDist.dist_eq_max_of_dist_ne_dist a x b
      (show dist a x ≠ dist x b by rw [dist_comm a x]; exact h.ne)
    rw [dist_comm a x,max_eq_right h.le] at hab
    rw [min_eq_left h.le,hab,max_eq_left h.le]
  · rw [h,max_self] at tri
    rw [h,min_self,max_eq_right tri]
  · have hab := IsUltrametricDist.dist_eq_max_of_dist_ne_dist a x b
      (show dist a x ≠ dist x b by rw [dist_comm a x]; exact h.ne')
    rw [dist_comm a x,max_eq_left h.le] at hab
    rw [min_eq_right h.le,hab,max_eq_left h.le,mul_comm]

private theorem strict_product_radius (d : ℝ) {s r : ℝ} (hs : 0≤s) (h : s<r) :
    s*max d s < r*max d r := calc
  _ ≤ s*max d r := mul_le_mul_of_nonneg_left (max_le_max_left _ h.le) hs
  _ < _ := mul_lt_mul_of_pos_right h ((hs.trans_lt h).trans_le (le_max_right d r))

/-- A product sublevel set is exactly the union of the two closed balls.
The displayed threshold works for coincident centers as well. -/
theorem ultrametric_two_root_balls (a b : X) {r : ℝ} (hr : 0≤r) :
    {x | dist x a*dist x b ≤ r*max (dist a b) r} =
      closedBall a r ∪ closedBall b r := by
  ext x
  simp only [Set.mem_setOf_eq,Set.mem_union,mem_closedBall,← min_le_iff]
  rw [ultrametric_two_root_product]
  have hmin := le_min (dist_nonneg (x:=x) (y:=a)) (dist_nonneg (x:=x) (y:=b))
  constructor
  · exact fun h => le_of_not_gt fun he => (strict_product_radius _ hr he).not_ge h
  · intro h
    rcases eq_or_lt_of_le h with he|he
    · rw [he]
    · exact (strict_product_radius _ hmin he).le

/-- Below the center separation the two root balls are disjoint. -/
theorem disjoint_quadratic_root_balls {a b : X} {r : ℝ} (h : r<dist a b) :
    Disjoint (closedBall a r) (closedBall b r) := by
  apply Set.disjoint_left.mpr
  intro x ha hb
  have hax : dist a x≤r := by simpa only [dist_comm a x] using (mem_closedBall.mp ha)
  exact h.not_ge ((dist_triangle_max a x b).trans (max_le hax (mem_closedBall.mp hb)))

/-- At and above the center separation the same sublevel set is one ball. -/
theorem ultrametric_merged_root_ball {a b : X} {r : ℝ} (h : dist a b≤r) :
    {x | dist x a*dist x b ≤ r^2} = closedBall a r := by
  have hr : 0≤r := dist_nonneg.trans h
  have he := ultrametric_two_root_balls a b hr
  rw [max_eq_right h,←sq] at he
  have hb : b∈closedBall a r := by simpa only [mem_closedBall,dist_comm b a] using h
  rw [he,←IsUltrametricDist.closedBall_eq_of_mem hb,Set.union_self]

variable (p : ℕ) [Fact p.Prime]

/-- A p-adic residue fiber is the root ball of precisely the prime-power
radius, viewed inside the full integral ring. -/
theorem padic_root_ball_eq_residue (a : ℤ_[p]) (k : ℕ) :
    closedBall a ((p:ℝ)^(-(k:ℤ))) = {x | PadicInt.toZModPow k x=PadicInt.toZModPow k a} := by
  ext x
  rw [mem_closedBall,dist_eq_norm,← OperatorKernels.padicProjection_eq_zero_iff_norm_le,
    Set.mem_setOf_eq,map_sub,sub_eq_zero]

/-- For separated roots, a quadratic congruence is exactly one of two
linear congruences. The scale r is specified by its product with the
distance between the roots, so the identity is valid at every prime. -/
theorem padic_separated_quadratic_congruence (a b : ℤ_[p]) (h k : ℕ)
    (hsep : (p:ℝ)^(-(k:ℤ)) < dist a b)
    (hscale : (p:ℝ)^(-(k:ℤ))*dist a b=(p:ℝ)^(-(h:ℤ))) :
    {x | PadicInt.toZModPow h ((x-a)*(x-b))=0} =
      {x | PadicInt.toZModPow k x=PadicInt.toZModPow k a} ∪
        {x | PadicInt.toZModPow k x=PadicInt.toZModPow k b} := by
  have hp : (0:ℝ)<p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have he := ultrametric_two_root_balls a b (zpow_nonneg hp.le (-(k:ℤ)))
  rw [max_eq_left hsep.le,hscale,padic_root_ball_eq_residue,padic_root_ball_eq_residue] at he
  rw [←he]
  ext x
  simp only [Set.mem_setOf_eq,OperatorKernels.padicProjection_eq_zero_iff_norm_le,
    dist_eq_norm,norm_mul]

open MeasureTheory RHTower

private instance integralHaarProbability : IsProbabilityMeasure (fieldOnePadicIntNormalizedHaar p) :=
  ⟨fieldOnePadicIntNormalizedHaar_univ p⟩

/-- Haar probability of a single integral residue ball. -/
theorem padic_linear_root_ball_mass (a : ℤ_[p]) (k : ℕ) :
    (fieldOnePadicIntNormalizedHaar p).real (closedBall a ((p:ℝ)^(-(k:ℤ))))=1/(p:ℝ)^k := by
  let f := PadicInt.toZModPow (p:=p) k
  letI : NeZero (p^k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : Unique {z : ZMod (p^k) // z=f a} := ⟨⟨⟨f a,rfl⟩⟩,fun z => Subtype.ext z.property⟩
  have h := haar_finite_quotient_probability (fieldOnePadicIntNormalizedHaar p) f.toAddMonoidHom
    (ZMod.ringHom_surjective f) (fieldOnePadicInt_toZModPow_continuous p k) (fun z => z=f a)
  change (fieldOnePadicIntNormalizedHaar p).real {x | f x=f a} = _ at h
  rw [Nat.card_unique (α:={z : ZMod (p^k) // z=f a}),Nat.card_zmod,Nat.cast_one,Nat.cast_pow] at h
  rw [padic_root_ball_eq_residue]
  exact h

/-- The separated and merged root tubes have, respectively, twice and once
the Haar mass of a single linear congruence class. -/
theorem padic_separated_quadratic_tube_mass (a b : ℤ_[p]) (h k : ℕ)
    (hsep : (p:ℝ)^(-(k:ℤ))<dist a b) (hscale : (p:ℝ)^(-(k:ℤ))*dist a b=(p:ℝ)^(-(h:ℤ))) :
    (fieldOnePadicIntNormalizedHaar p).real {x | PadicInt.toZModPow h ((x-a)*(x-b))=0} =
      2/(p:ℝ)^k := by
  rw [padic_separated_quadratic_congruence p a b h k hsep hscale,←padic_root_ball_eq_residue,
    ←padic_root_ball_eq_residue,measureReal_union (disjoint_quadratic_root_balls hsep)
      isClosed_closedBall.measurableSet,padic_linear_root_ball_mass,padic_linear_root_ball_mass]
  ring

/-- The finite quadratic root count is the exact Haar mass of its
congruence tube times the size of the residue ring. -/
private theorem residue_root_fraction (a b : ℤ_[p]) (h : ℕ) :
    let f := PadicInt.toZModPow (p:=p) h
    (Nat.card {z : ZMod (p^h) // (z-f a)*(z-f b)=0}:ℝ)/(p:ℝ)^h =
      (fieldOnePadicIntNormalizedHaar p).real {x | f ((x-a)*(x-b))=0} := by
  let f := PadicInt.toZModPow (p:=p) h
  letI : NeZero (p^h) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hq := haar_finite_quotient_probability (fieldOnePadicIntNormalizedHaar p) f.toAddMonoidHom
    (ZMod.ringHom_surjective f) (fieldOnePadicInt_toZModPow_continuous p h)
    (fun z => (z-f a)*(z-f b)=0)
  change (fieldOnePadicIntNormalizedHaar p).real {x | (f x-f a)*(f x-f b)=0} = _ at hq
  rw [Nat.card_zmod,Nat.cast_pow] at hq
  change _ = (fieldOnePadicIntNormalizedHaar p).real {x | f ((x-a)*(x-b))=0}
  simpa only [map_mul,map_sub] using hq.symm

/-- Exact merged branch in both even and odd precision. The distance in
the integral ring has integral valuation, so its square passes the h-th
residue test exactly at precision ceil(h/2). -/
theorem padic_double_root_congruence (a b : ℤ_[p]) (h : ℕ)
    (hab : PadicInt.toZModPow ((h+1)/2) a=PadicInt.toZModPow ((h+1)/2) b) :
    let k := (h+1)/2
    {x | PadicInt.toZModPow h ((x-a)*(x-b))=0} =
      {x | PadicInt.toZModPow k x=PadicInt.toZModPow k a} := by
  let k := (h+1)/2
  let r := (p:ℝ)^(-(k:ℤ))
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr : 0<r := zpow_pos (zero_lt_one.trans hp) _
  have hclose : dist a b≤r := by
    change a∈closedBall b ((p:ℝ)^(-(k:ℤ)))
    rw [padic_root_ball_eq_residue]
    exact hab
  change _ = {x | PadicInt.toZModPow k x=PadicInt.toZModPow k a}
  rw [←padic_root_ball_eq_residue]
  ext x
  rw [Set.mem_setOf_eq,OperatorKernels.padicProjection_eq_zero_iff_norm_le,norm_mul,
    ←dist_eq_norm x a,←dist_eq_norm x b,mem_closedBall]
  change dist x a*dist x b≤(p:ℝ)^(-(h:ℤ)) ↔ dist x a≤r
  by_cases hx : dist x a≤r
  · have hy := (dist_triangle_max x a b).trans (max_le hx hclose)
    have hs : r*r≤(p:ℝ)^(-(h:ℤ)) := by
      dsimp only [r]
      rw [←zpow_add₀ (zero_lt_one.trans hp).ne',zpow_le_zpow_iff_right₀ hp]
      dsimp only [k]
      omega
    exact iff_of_true ((mul_le_mul hx hy dist_nonneg hr.le).trans hs) hx
  · have hfar : dist a b<dist x a := hclose.trans_lt (lt_of_not_ge hx)
    have hs := IsUltrametricDist.dist_eq_max_of_dist_ne_dist x a b hfar.ne'
    rw [max_eq_left hfar.le] at hs
    have hz : x-a≠0 := by
      intro he
      apply hx
      rw [sub_eq_zero.mp he,dist_self]
      exact hr.le
    have hn : dist x a=(p:ℝ)^(-((x-a).valuation:ℤ)) := by
      rw [dist_eq_norm,PadicInt.norm_eq_zpow_neg_valuation hz]
    have hv : (x-a).valuation<k := by
      have hh := lt_of_not_ge hx
      rw [hn] at hh
      exact_mod_cast neg_lt_neg_iff.mp ((zpow_lt_zpow_iff_right₀ hp).mp hh)
    apply iff_of_false _ hx
    rw [hs,hn,←zpow_add₀ (zero_lt_one.trans hp).ne',zpow_le_zpow_iff_right₀ hp]
    dsimp only [k] at hv
    omega

/-- The merged quadratic tube has the Haar mass of a single residue
class at precision ceil(h/2), in even and odd precision alike. -/
theorem padic_merged_quadratic_tube_mass (a b : ℤ_[p]) (h : ℕ)
    (hab : PadicInt.toZModPow ((h+1)/2) a=PadicInt.toZModPow ((h+1)/2) b) :
    (fieldOnePadicIntNormalizedHaar p).real {x | PadicInt.toZModPow h ((x-a)*(x-b))=0} =
      1/(p:ℝ)^((h+1)/2) := by
  rw [padic_double_root_congruence p a b h hab,←padic_root_ball_eq_residue,padic_linear_root_ball_mass]

private theorem padic_radius_product (p : ℕ) [Fact p.Prime] (j k : ℕ) :
    (p:ℝ)^(-(k:ℤ))*(p:ℝ)^(-(j:ℤ))=(p:ℝ)^(-((k+j:ℕ):ℤ)) := by
  rw [←zpow_add₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p:ℝ)≠0)]
  congr 1
  push_cast
  ring

/-- Distinct p-adic roots with separation of valuation j have exactly
2p^j solutions at every precision k+j with k>j. -/
theorem card_separated_quadratic_residues (a b : ℤ_[p]) {j k : ℕ} (hjk : j<k)
    (hab : dist a b=(p:ℝ)^(-(j:ℤ))) :
    let f := PadicInt.toZModPow (p:=p) (k+j)
    Nat.card {z : ZMod (p^(k+j)) // (z-f a)*(z-f b)=0}=2*p^j := by
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp' := (zero_lt_one.trans hp).ne'
  have hsep : (p:ℝ)^(-(k:ℤ))<dist a b := by
    rw [hab,zpow_lt_zpow_iff_right₀ hp]
    omega
  have scale : (p:ℝ)^(-(k:ℤ))*dist a b=(p:ℝ)^(-((k+j:ℕ):ℤ)) := by
    rw [hab,padic_radius_product]
  have h := (residue_root_fraction p a b (k+j)).trans
    (padic_separated_quadratic_tube_mass p a b (k+j) k hsep scale)
  rw [div_eq_div_iff (pow_ne_zero _ hp') (pow_ne_zero _ hp'),pow_add (p:ℝ) k j,
    show 2*((p:ℝ)^k*(p:ℝ)^j)=(2*(p:ℝ)^j)*(p:ℝ)^k by ring] at h
  exact_mod_cast (isUnit_iff_ne_zero.mpr (pow_ne_zero k hp')).mul_left_inj.mp h

/-- The congruence fibre at coincident residue roots has p^floor(h/2)
points. This includes residue characteristic two and odd precision. -/
theorem card_double_quadratic_residues (a b : ℤ_[p]) (h : ℕ)
    (hab : PadicInt.toZModPow ((h+1)/2) a=PadicInt.toZModPow ((h+1)/2) b) :
    let f := PadicInt.toZModPow (p:=p) h
    Nat.card {z : ZMod (p^h) // (z-f a)*(z-f b)=0}=p^(h/2) := by
  let k := (h+1)/2
  have hp : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hmass := (residue_root_fraction p a b h).trans (padic_merged_quadratic_tube_mass p a b h hab)
  change _/(p:ℝ)^h=1/(p:ℝ)^k at hmass
  have he : (p:ℝ)^h=(p:ℝ)^(h/2)*(p:ℝ)^k := by
    rw [←pow_add]
    congr 1
    dsimp only [k]
    omega
  rw [div_eq_div_iff (pow_ne_zero _ hp) (pow_ne_zero _ hp),one_mul,he] at hmass
  exact_mod_cast (isUnit_iff_ne_zero.mpr (pow_ne_zero k hp)).mul_left_inj.mp hmass

#print axioms padic_double_root_congruence
#print axioms card_separated_quadratic_residues
#print axioms card_double_quadratic_residues

#print axioms padic_separated_quadratic_tube_mass
#print axioms padic_merged_quadratic_tube_mass
#print axioms ultrametric_two_root_product
#print axioms ultrametric_two_root_balls
#print axioms ultrametric_merged_root_ball
#print axioms padic_separated_quadratic_congruence
end
end GaloisForLFunctions.RepresentationLifting
