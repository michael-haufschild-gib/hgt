import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.SquareTowerPolarForm
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Integral radical of the square-tower polar form

Recording the forward reading A and the congruence coordinate k gives
a surjective linear map onto ℤ². Its kernel consists precisely of the
translations preserving the arithmetic polar form at every coefficient
vector. Each endpoint fiber is a coset of this free integral radical.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SquareTower

def endpointReadings (b : Base) (n : ℕ) : Coeff n →+ ℤ × ℤ where
  toFun x := (forward b.val x,backward b.val x)
  map_zero' := by simp [forward,backward]
  map_add' x y := by
    apply Prod.ext <;> simp [forward,backward,add_mul,sum_add_distrib]

private theorem multiplier_nonzero (b : Base) : 1-(b.val:ℤ)^2≠0 := by
  have h : (1:ℤ)<b.val := by exact_mod_cast (show 1<b.val from b.property)
  exact sub_ne_zero.mpr (one_lt_pow₀ h (by decide : 2≠0)).ne

private def encode (b : Base) (d : ℕ) : ℤ × ℤ →+ ℤ × ℤ where
  toFun z := (z.1,z.1*(b.val:ℤ)^d+(1-(b.val:ℤ)^2)*z.2)
  map_zero' := by simp
  map_add' x y := Prod.ext rfl (by
    change (x.1+y.1)*(b.val:ℤ)^d+(1-(b.val:ℤ)^2)*(x.2+y.2)=
      (x.1*(b.val:ℤ)^d+(1-(b.val:ℤ)^2)*x.2)+(y.1*(b.val:ℤ)^d+(1-(b.val:ℤ)^2)*y.2)
    ring)

private theorem encode_injective (b : Base) (d : ℕ) : Function.Injective (encode b d) := by
  rintro ⟨a,k⟩ ⟨c,j⟩ eq
  have h : a=c := congrArg Prod.fst eq
  subst c
  have t := congrArg Prod.snd eq
  change a*(b.val:ℤ)^d+(1-(b.val:ℤ)^2)*k=a*(b.val:ℤ)^d+(1-(b.val:ℤ)^2)*j at t
  exact Prod.ext rfl (mul_left_cancel₀ (multiplier_nonzero b) (add_left_cancel t))

private def firstTwo (b : Base) (n : ℕ) (x : Coeff (n+2)) : ℤ × ℤ :=
  let z := coordinates b.val n x
  (z.1,z.2.1)

private theorem encode_firstTwo (b : Base) (n : ℕ) (x : Coeff (n+2)) :
    encode b (n+1) (firstTwo b n x)=endpointReadings b (n+2) x := by
  obtain ⟨f,g⟩ := coordinates_readings b.val n x
  exact Prod.ext f.symm g.symm

/-- A and (C−bᵈA)/(1−b²) are integral linear coordinates on the quotient. -/
def normalizedEndpoints (b : Base) (n : ℕ) : Coeff (n+2) →ₗ[ℤ] ℤ × ℤ :=
  AddMonoidHom.toIntLinearMap {
    toFun := firstTwo b n
    map_zero' := encode_injective b (n+1) (by simp only [encode_firstTwo,map_zero])
    map_add' := fun x y => encode_injective b (n+1) (by simp only [encode_firstTwo,map_add]) }

theorem normalizedEndpoints_surjective (b : Base) (n : ℕ) : Function.Surjective (normalizedEndpoints b n) := by
  rintro ⟨a,k⟩
  let e := coordinates (b.val:ℤ) n
  refine ⟨e.symm (a,k,0),?_⟩
  change ((e (e.symm (a,k,0))).1,(e (e.symm (a,k,0))).2.1)=(a,k)
  rw [e.apply_symm_apply]

/-- The integral submodule of translations invisible in both endpoint readings. -/
def radical (b : Base) (n : ℕ) : Submodule ℤ (Coeff (n+2)) := (normalizedEndpoints b n).ker

theorem mem_radical (b : Base) (n : ℕ) (x : Coeff (n+2)) :
    x∈radical b n ↔ endpointReadings b (n+2) x=0 := by
  change firstTwo b n x=0 ↔ _
  rw [←(encode_injective b (n+1)).eq_iff,encode_firstTwo,map_zero]

/-- A nonempty endpoint fiber is exactly the translate of the radical
through any one of its integer vectors. -/
theorem endpoint_fiber_coset (b : Base) (n : ℕ) (x y : Coeff (n+2)) :
    endpointReadings b (n+2) x=endpointReadings b (n+2) y ↔ x-y∈radical b n := by
  rw [mem_radical,map_sub,sub_eq_zero]

private theorem polar_eq_iff (b : Base) {d : ℕ} (x y : Coeff (d+1)) :
    polar b x=polar b y ↔ forward b.val x*backward b.val x=forward b.val y*backward b.val y := by
  let N := forward b.val y*backward b.val y
  have hy := (normalized_level_iff b y N).mpr rfl
  have hx := normalized_level_iff b x N
  have hb : 0<(b.val:ℝ) := by exact_mod_cast (show 0<b.val from lt_of_lt_of_le (by decide : 0<2) b.property)
  rwa [←hy,mul_right_inj' (pow_ne_zero d hb.ne')] at hx

/-- Preserving the true polar energy under every translation test detects
exactly the integral radical. Two attainable endpoint pairs, together
with the origin, suffice to prove necessity. -/
theorem polar_translation_iff (b : Base) (n : ℕ) (x : Coeff (n+2)) :
    (∀ y : Coeff (n+2), polar b (x+y)=polar b y) ↔ x∈radical b n := by
  let F := endpointReadings b (n+2)
  have criterion (y : Coeff (n+2)) : polar b (x+y)=polar b y ↔
      ((F x).1+(F y).1)*((F x).2+(F y).2)=(F y).1*(F y).2 := by
    rw [polar_eq_iff]
    change (F (x+y)).1*(F (x+y)).2=(F y).1*(F y).2 ↔ _
    simp only [map_add,Prod.fst_add,Prod.snd_add]
  rw [mem_radical]
  change _ ↔ F x=0
  constructor
  · intro h
    have prod := (criterion 0).mp (h 0)
    simp only [map_zero,Prod.fst_zero,Prod.snd_zero,add_zero,zero_mul] at prod
    have orth (y : Coeff (n+2)) : (F x).1*(F y).2+(F y).1*(F x).2=0 := by
      have hy := (criterion y).mp (h y)
      linear_combination hy - prod
    obtain ⟨u,hu,ku⟩ := (attainable_pair b.val n 0 (1-(b.val:ℤ)^2)).mpr ⟨1,by ring⟩
    change (F u).1=0 at hu
    change (F u).2=1-(b.val:ℤ)^2 at ku
    have test := orth u
    rw [hu,ku,zero_mul,add_zero] at test
    have hz := (mul_eq_zero.mp test).resolve_right (multiplier_nonzero b)
    obtain ⟨v,hv,_⟩ := (attainable_pair b.val n 1 ((b.val:ℤ)^(n+1))).mpr ⟨0,by ring⟩
    change (F v).1=1 at hv
    have last := orth v
    rw [hz,hv,zero_mul,one_mul,zero_add] at last
    exact Prod.ext hz last
  · intro h y
    apply (criterion y).mpr
    simp [h]

/-- Two measured directions exhaust the rank of the integral quotient. -/
theorem radical_rank (b : Base) (n : ℕ) : Module.finrank ℤ (radical b n)=n := by
  let f := normalizedEndpoints b n
  have quot := (f.quotKerEquivOfSurjective (normalizedEndpoints_surjective b n)).finrank_eq
  have rank := f.ker.finrank_quotient_add_finrank
  rw [quot,Module.finrank_prod,Module.finrank_self,Module.finrank_fin_fun] at rank
  change Module.finrank ℤ f.ker=n
  omega

/-- Linear identification of the translations preserving every energy with ℤⁿ. -/
def radicalCoordinates (b : Base) (n : ℕ) : radical b n ≃ₗ[ℤ] Coeff n :=
  LinearEquiv.ofFinrankEq _ _ ((radical_rank b n).trans (Module.finrank_fin_fun ℤ).symm)

#print axioms normalizedEndpoints_surjective
#print axioms endpoint_fiber_coset
#print axioms polar_translation_iff
#print axioms radical_rank
#print axioms radicalCoordinates
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SquareTower
