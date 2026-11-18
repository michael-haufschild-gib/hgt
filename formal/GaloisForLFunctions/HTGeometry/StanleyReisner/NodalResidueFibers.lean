import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.DivisorJetReciprocity
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Residue-ring points of the normal-crossing equation

Counting the coordinate axes over residue rings must include nonzero
annihilators. For any prescribed product the solution count is a divisor
sum. The prime-power specialization distinguishes the singular fiber
from every nonzero fiber.
-/
namespace GaloisForLFunctions.HTGeometry.NormalCrossings
open Finset MvPolynomial
open scoped Classical
noncomputable section


private theorem divides_target (m a t : ℕ) :
    (a:ZMod m) ∣ (t:ZMod m) ↔ Nat.gcd m a ∣ t := by
  let d := Nat.gcd m a
  have hdm : d ∣ m := Nat.gcd_dvd_left _ _
  have hda : d ∣ a := Nat.gcd_dvd_right _ _
  constructor
  · rintro ⟨y,hy⟩
    have he := congrArg (ZMod.castHom hdm (ZMod d)) hy
    simp only [map_natCast,map_mul,(ZMod.natCast_eq_zero_iff a d).mpr hda,zero_mul] at he
    exact (ZMod.natCast_eq_zero_iff t d).mp he
  · rintro ⟨v,hv⟩
    have he : (d:ℤ) = m*(Nat.gcdA m a)+a*(Nat.gcdB m a) := Nat.gcd_eq_gcd_ab _ _
    have hh := congrArg (Int.castRingHom (ZMod m)) he
    simp only [map_add,map_mul,Int.coe_castRingHom,Int.cast_natCast,ZMod.natCast_self,zero_mul,zero_add] at hh
    refine ⟨((Nat.gcdB m a : ℤ):ZMod m)*(v:ZMod m),?_⟩
    rw [hv,Nat.cast_mul,hh,mul_assoc]

private def fiberShift {R : Type*} [CommRing R] (w b : R) :
    {y : R // w*y = w*b} ≃ {y : R // w*y=0} where
  toFun y := ⟨y.val-b,by rw [mul_sub,y.property,sub_self]⟩
  invFun y := ⟨y.val+b,by rw [mul_add,y.property,zero_add]⟩
  left_inv y := Subtype.ext (sub_add_cancel _ _)
  right_inv y := Subtype.ext (add_sub_cancel_right _ _)

/-- Which fixed-coordinate fibers exist and how many points they carry. -/
theorem nodal_row_card (m : ℕ+) (a t : ℕ) :
    Nat.card {y : ZMod (m:ℕ) // (a:ZMod (m:ℕ))*y = t} =
      if Nat.gcd (m:ℕ) a ∣ t then Nat.gcd (m:ℕ) a else 0 := by
  split_ifs with hd
  · obtain ⟨y,hy⟩ := (divides_target (m:ℕ) a t).mpr hd
    rw [hy,Nat.card_congr (fiberShift (a:ZMod (m:ℕ)) y)]
    let f := (nsmulAddMonoidHom a : ZMod (m:ℕ) →+ ZMod (m:ℕ))
    have e : {y : ZMod (m:ℕ) // (a:ZMod (m:ℕ))*y=0} ≃ f.ker :=
      Equiv.subtypeEquivRight fun y => by simp [f,nsmul_eq_mul]
    rw [Nat.card_congr e]
    simpa only [f,Nat.card_zmod] using IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod (m:ℕ)) a
  · letI : IsEmpty {y : ZMod (m:ℕ) // (a:ZMod (m:ℕ))*y=t} :=
      ⟨fun y => hd ((divides_target (m:ℕ) a t).mp ⟨y.val,y.property.symm⟩)⟩
    exact Nat.card_of_isEmpty

/-- Residue-ring points on the fiber xy=t. -/
abbrev nodalFiber (m t : ℕ) := {v : ZMod m × ZMod m // v.1*v.2=t}

private def nodalRows (m : ℕ+) (t : ℕ) : nodalFiber m t ≃
    Σ i : Fin (m:ℕ), {y : ZMod (m:ℕ) // (i.val:ZMod (m:ℕ))*y=t} where
  toFun v := ⟨⟨v.val.1.val,ZMod.val_lt _⟩,v.val.2,by rw [ZMod.natCast_zmod_val]; exact v.property⟩
  invFun z := ⟨((z.1.val:ZMod (m:ℕ)),z.2.val),z.2.property⟩
  left_inv v := Subtype.ext (Prod.ext (ZMod.natCast_zmod_val _) rfl)
  right_inv z := by
    rcases z with ⟨i,y,hy⟩
    dsimp
    congr 1
    exact Fin.ext (ZMod.val_natCast_of_lt i.isLt)

/-- The entire arithmetic product distribution on ℤ/mℤ. Taking t=0
recovers the classical gcd-sum function at m. -/
theorem nodalFiber_count (m : ℕ+) (t : ℕ) :
    Nat.card (nodalFiber m t) =
      ∑ d ∈ (m:ℕ).divisors, if d ∣ t then ((m:ℕ)/d).totient*d else 0 := by
  rw [Nat.card_congr (nodalRows m t),Nat.card_sigma]
  simp_rw [nodal_row_card]
  rw [Fin.sum_univ_eq_sum_range]
  have h := SuccessorShellArithmetic.sum_range_gcd_profile m.property
    (fun d => if d ∣ t then (d:ℝ) else 0)
  have he (d : ℕ) : (((m:ℕ)/d).totient:ℝ)*(if d ∣ t then (d:ℝ) else 0) =
      (if d ∣ t then ((((m:ℕ)/d).totient*d:ℕ):ℝ) else 0) := by split_ifs <;> simp
  simp_rw [he] at h
  exact_mod_cast h

private theorem pow_quot {p k j : ℕ} (hp : 0 < p) (hj : j ≤ k) : p^k/p^j = p^(k-j) := by
  rw [show p^k = p^(k-j)*p^j by rw [← pow_add,Nat.sub_add_cancel hj],Nat.mul_div_cancel _ (pow_pos hp _)]

/-- Each nonterminal valuation stratum contributes the same mass in the
singular fiber. The top stratum contributes the entire remaining axis. -/
theorem node_primePower (p : Nat.Primes) (k : ℕ) :
    Nat.card (nodalFiber (p.val^(k+1)) 0) = p.val^(k+1)+(k+1)*p.val^k*(p.val-1) := by
  have h := nodalFiber_count (⟨p.val^(k+1),pow_pos p.property.pos _⟩ : ℕ+) 0
  simp only [dvd_zero,if_true] at h
  rw [h,Nat.divisors_prime_pow p.property,sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [sum_range_succ,Nat.div_self (pow_pos p.property.pos _),Nat.totient_one,one_mul]
  have he (i : ℕ) (hi : i ∈ range (k+1)) : (p.val^(k+1)/p.val^i).totient*p.val^i =
      p.val^k*(p.val-1) := by
    have hi' := mem_range.mp hi
    rw [pow_quot p.property.pos hi'.le,show k+1-i=(k-i)+1 by omega,
      Nat.totient_prime_pow_succ p.property,mul_right_comm,← pow_add,Nat.sub_add_cancel (by omega)]
  rw [sum_congr rfl he,sum_const,card_range,nsmul_eq_mul]
  ring

/-- Parallel nodal equations give the integral model of the cross-polytope
Stanley--Reisner locus. Independent deformations of the nodes also factor. -/
theorem parallelNode_count {ι : Type*} [Fintype ι] (m : ℕ+) (t : ι → ℕ) :
    Nat.card {v : ι → ZMod (m:ℕ) × ZMod (m:ℕ) // ∀ i, (v i).1*(v i).2=t i} =
      ∏ i, ∑ d ∈ (m:ℕ).divisors, if d ∣ t i then ((m:ℕ)/d).totient*d else 0 := by
  let e : {v : ι → ZMod (m:ℕ) × ZMod (m:ℕ) // ∀ i, (v i).1*(v i).2=t i} ≃
      ∀ i, nodalFiber m (t i) :=
    {toFun := fun v i => ⟨v.val i,v.property i⟩
     invFun := fun w => ⟨fun i => (w i).val,fun i => (w i).property⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  rw [Nat.card_congr e,Nat.card_pi]
  simp only [nodalFiber_count]

/-- The actual affine coordinate algebra of independently deformed nodes. -/
abbrev nodeAlgebra {ι : Type*} (R : Type*) [CommRing R] (t : ι → R) :=
  MvPolynomial (ι × Bool) R ⧸ Ideal.span (Set.range fun i : ι =>
    X (i,false)*X (i,true)-C (t i))

/-- A character is precisely a collection of solutions of the prescribed
product equations, over arbitrary coefficient rings. -/
def nodeCharacterEquiv {ι R : Type*} [CommRing R] (t : ι → R) :
    (nodeAlgebra R t →ₐ[R] R) ≃ ∀ i, {v : R × R // v.1*v.2=t i} := by
  let I := Ideal.span (Set.range fun i : ι => X (i,false)*X (i,true)-C (t i))
  let Q := Ideal.Quotient.mkₐ R I
  let mk (x : ∀ i, {v : R × R // v.1*v.2=t i}) (v : ι × Bool) :=
    if v.2 then (x v.1).val.2 else (x v.1).val.1
  have hI (x : ∀ i, {v : R × R // v.1*v.2=t i}) : I ≤ RingHom.ker (aeval (mk x)).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simpa [RingHom.mem_ker,mk] using sub_eq_zero.mpr (x i).property
  let L (x : ∀ i, {v : R × R // v.1*v.2=t i}) :=
    Ideal.Quotient.liftₐ I (aeval (mk x)) fun f hf => hI x hf
  refine {toFun := fun f i => ⟨(f (Q (X (i,false))),f (Q (X (i,true)))),?_⟩
          invFun := L
          left_inv := ?_
          right_inv := ?_}
  · have he : Q (X (i,false)*X (i,true)-C (t i)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
    have hh := congrArg f he
    apply sub_eq_zero.mp
    simpa [map_sub,map_mul,Q] using hh
  · intro f
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro ⟨i,b⟩
    cases b <;> simp [L,mk,Q,Ideal.Quotient.liftₐ_apply]
  · intro x
    funext i
    apply Subtype.ext
    apply Prod.ext <;> simp [L,mk,Q,Ideal.Quotient.liftₐ_apply]

/-- Character count of the nodal algebra over every residue ring, including
nonreduced bases. -/
theorem nodeCharacter_card {ι : Type*} [Fintype ι] (m : ℕ+) (t : ι → ℕ) :
    Nat.card (nodeAlgebra (ZMod (m:ℕ)) (fun i => (t i:ZMod (m:ℕ))) →ₐ[ZMod (m:ℕ)] ZMod (m:ℕ)) =
      ∏ i, ∑ d ∈ (m:ℕ).divisors, if d ∣ t i then ((m:ℕ)/d).totient*d else 0 := by
  rw [Nat.card_congr (nodeCharacterEquiv _),Nat.card_pi]
  exact prod_congr rfl fun i _ => nodalFiber_count m (t i)

/-- Poincaré series of actual solutions along the prime-power tower. -/
def nodeSeries (p : Nat.Primes) : PowerSeries ℤ :=
  PowerSeries.mk fun k => (Nat.card (nodalFiber (p.val^k) 0):ℤ)

private theorem nodeSeries_zero (p : Nat.Primes) : PowerSeries.coeff 0 (nodeSeries p) = 1 := by
  simp only [nodeSeries,PowerSeries.coeff_mk,pow_zero]
  have h := nodalFiber_count (1:ℕ+) 0
  exact_mod_cast (show Nat.card (nodalFiber 1 0) = 1 by simpa using h)

private theorem nodeSeries_succ (p : Nat.Primes) (k : ℕ) :
    PowerSeries.coeff (k+1) (nodeSeries p) =
      (p.val:ℤ)^(k+1)+(k+1:ℕ)*(p.val:ℤ)^k*((p.val:ℤ)-1) := by
  rw [nodeSeries,PowerSeries.coeff_mk,node_primePower]
  push_cast [Nat.cast_sub p.property.one_le]
  ring

private theorem coeff_linear (p : ℤ) (f : PowerSeries ℤ) (k : ℕ) :
    PowerSeries.coeff (k+1) ((1-PowerSeries.C p*PowerSeries.X)*f) =
      PowerSeries.coeff (k+1) f-p*PowerSeries.coeff k f := by
  rw [sub_mul,one_mul,mul_assoc,map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_X_mul]

/-- The singular nodal tower has a double pole, with numerator exactly
1-T. The identity is integral before specialization to any analytic disk. -/
theorem nodeSeries_rational (p : Nat.Primes) :
    (1-PowerSeries.C (p.val:ℤ)*PowerSeries.X)^2*nodeSeries p = 1-PowerSeries.X := by
  rw [pow_two,mul_assoc]
  ext k
  cases k with
  | zero =>
    simp only [PowerSeries.coeff_zero_eq_constantCoeff,map_mul,map_sub,map_one,
      PowerSeries.constantCoeff_X,mul_zero,sub_zero,one_mul]
    exact nodeSeries_zero p
  | succ k =>
    rw [coeff_linear]
    cases k with
    | zero =>
      rw [coeff_linear,nodeSeries_succ,nodeSeries_zero]
      change _ - _*PowerSeries.constantCoeff _ = _
      simp [nodeSeries_zero,pow_succ]
    | succ k =>
      rw [coeff_linear,coeff_linear,nodeSeries_succ,nodeSeries_succ]
      cases k with
      | zero => simp [nodeSeries_zero,pow_succ]; ring
      | succ k => rw [nodeSeries_succ]; simp [pow_succ]; ring
end
end GaloisForLFunctions.HTGeometry.NormalCrossings
