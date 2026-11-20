import GaloisForLFunctions.RepresentationLifting.Probability.TheSplitProbabilityOfAPadicQuadratic
import Mathlib.NumberTheory.Padics.Hensel

/-!
# Irreducibility on thin p-adic coefficient boxes

Consider X²+bX+yc with independent uniform b,c in Z_p. When y is
multiplied by p², a unit b gives a simple root modulo p, which lifts.
On b in pZ_p, scaling the variable by p recovers the original problem.
Thus each pair of extra constant-coefficient digits divides the
irreducibility probability by p. The two initial densities are
determined by the integral and maximal-ideal cases of Lemma C.1.
-/

namespace GaloisForLFunctions.RepresentationLifting
open MeasureTheory Polynomial RHTower
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "𝒪" => ℤ_[p]
private instance coordProbability : IsProbabilityMeasure (fieldOnePadicIntNormalizedHaar p) :=
  ⟨fieldOnePadicIntNormalizedHaar_univ p⟩

/-- The coefficient pairs for which the scaled quadratic has no factor over Q_p. -/
def scaledQuadraticIrreducible (y : 𝒪) : Set (𝒪×𝒪) :=
  {z | Irreducible (X^2+C (z.1:ℚ_[p])*X+C ((y*z.2:𝒪):ℚ_[p]))}

/-- On the integral coefficient box, a field factor is detected by an integral root. -/
theorem mem_scaledQuadraticIrreducible (y : 𝒪) (z : 𝒪×𝒪) :
    z∈scaledQuadraticIrreducible p y ↔ ¬∃ x : 𝒪, x*(z.1-x)=y*z.2 :=
  (irreducible_quadratic_iff _ _).trans (not_congr (quadratic_root_integral p _ _))

theorem measurableSet_scaledQuadraticIrreducible (y : 𝒪) : MeasurableSet (scaledQuadraticIrreducible p y) := by
  let f (z : 𝒪×𝒪) := (z.1,y*z.2)
  have hf : Continuous f := continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have he : scaledQuadraticIrreducible p y=f ⁻¹' {b : 𝒪×𝒪 | ∃ x : 𝒪, x*(b.1-x)=b.2}ᶜ :=
    Set.ext fun z => mem_scaledQuadraticIrreducible p y z
  rw [he]
  exact hf.measurable (measurableSet_padic_quadratic_split p).compl

/-- Joint measurability when the scale itself is sampled with Haar measure. -/
theorem measurableSet_scaledQuadraticIrreducible_family :
    MeasurableSet {q : 𝒪×(𝒪×𝒪) | q.2∈scaledQuadraticIrreducible p q.1} := by
  let f (q : 𝒪×(𝒪×𝒪)) := (q.2.1,q.1*q.2.2)
  have hf : Continuous f := (continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.mul (continuous_snd.comp continuous_snd))
  have he : {q : 𝒪×(𝒪×𝒪) | q.2∈scaledQuadraticIrreducible p q.1} =
      f ⁻¹' {b : 𝒪×𝒪 | ∃ x : 𝒪, x*(b.1-x)=b.2}ᶜ :=
    Set.ext fun q => mem_scaledQuadraticIrreducible p q.1 q.2
  rw [he]
  exact hf.measurable (measurableSet_padic_quadratic_split p).compl

/-- Scaling the first coordinate multiplies product Haar measure by 1/p,
even when membership couples both coordinates. -/
theorem product_haar_prime_first_image (S : Set (𝒪×𝒪)) (hS : MeasurableSet S) :
    let μ := fieldOnePadicIntNormalizedHaar p
    (μ.prod μ).real ((fun z : 𝒪×𝒪 => ((p:𝒪)*z.1,z.2)) '' S) =
      (μ.prod μ).real S/(p:ℝ) := by
  let μ := fieldOnePadicIntNormalizedHaar p
  let f (z : 𝒪×𝒪) := ((p:𝒪)*z.1,z.2)
  have hp : (p:𝒪)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hf : Continuous f := (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hin : Function.Injective f := by
    intro a b he
    change ((p:𝒪)*a.1,a.2)=((p:𝒪)*b.1,b.2) at he
    exact Prod.ext ((mul_right_inj' hp).mp (Prod.mk.inj he).1) (Prod.mk.inj he).2
  have ht := (hf.isClosedEmbedding hin).measurableEmbedding.measurableSet_image.mpr hS
  have slices (c : 𝒪) : (fun b : 𝒪 => (b,c)) ⁻¹' (f '' S) =
      (fun b : 𝒪 => (p:𝒪)*b) '' ((fun b : 𝒪 => (b,c)) ⁻¹' S) := by
    ext b
    constructor
    · rintro ⟨⟨u,v⟩,h,he⟩
      obtain rfl : v=c := congrArg Prod.snd he
      exact ⟨u,h,congrArg Prod.fst he⟩
    · rintro ⟨u,h,rfl⟩
      exact ⟨(u,c),h,rfl⟩
  have he : (μ.prod μ) (f '' S)=(p:ENNReal)⁻¹*(μ.prod μ) S := by
    rw [Measure.prod_apply_symm ht,Measure.prod_apply_symm hS]
    calc
      _ = ∫⁻ c, (p:ENNReal)⁻¹*μ ((fun b : 𝒪 => (b,c)) ⁻¹' S) ∂μ :=
        lintegral_congr fun c => (congrArg μ (slices c)).trans (padic_integral_haar_prime_image p _)
      _ = _ := lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr
        (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    div_eq_mul_inv,mul_comm (p:ℝ)⁻¹] using congrArg ENNReal.toReal he

/-- When b is a unit, the simple root zero modulo p lifts for every c. -/
theorem padic_quadratic_root_of_unit_linear (b c : 𝒪) (hb : ¬(p:𝒪)∣b) :
    ∃ x : 𝒪, x*(b-x)=p*c := by
  let F : 𝒪[X] := X^2-C b*X+C ((p:𝒪)*c)
  have hn : ‖b‖=1 := le_antisymm (PadicInt.norm_le_one b)
    (le_of_not_gt fun h => hb ((PadicInt.norm_lt_one_iff_dvd b).mp h))
  have hc : ‖(p:𝒪)*c‖<1 := (PadicInt.norm_lt_one_iff_dvd _).mpr (dvd_mul_right _ _)
  have hd : F.derivative.aeval (0:𝒪)= -b := by simp [F,derivative_sub,derivative_mul]
  have hF : F.aeval (0:𝒪)=(p:𝒪)*c := by simp [F]
  obtain ⟨x,hx,_⟩ := hensels_lemma (F:=F) (a:=(0:𝒪)) (by rwa [hd,hF,norm_neg,hn,one_pow])
  simp only [F,map_add,map_sub,map_mul,map_pow,aeval_X,aeval_C,Algebra.algebraMap_self_apply] at hx
  exact ⟨x,by linear_combination -hx⟩

/-- Dividing the variable by p removes two powers of p in the constant
coefficient and one in the linear coefficient, preserving field splitting. -/
theorem padic_quadratic_scaled_roots_iff (b d : 𝒪) :
    (∃ x : 𝒪, x*((p:𝒪)*b-x)=(p:𝒪)^2*d) ↔ ∃ x : 𝒪, x*(b-x)=d := by
  constructor
  · rintro ⟨x,hx⟩
    apply (quadratic_root_integral p b d).mp
    refine ⟨(x:ℚ_[p])/(p:ℚ_[p]),?_⟩
    have he := congrArg (fun z : 𝒪 => (z:ℚ_[p])) hx
    push_cast at he
    have hp : (p:ℚ_[p])≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    field_simp [hp]
    linear_combination he
  · rintro ⟨x,hx⟩
    exact ⟨p*x,by linear_combination (p:𝒪)^2*hx⟩

/-- The actual irreducible locus after a two-digit shrink is the
one-coordinate dilation of the previous locus, for every scale y. -/
theorem scaledQuadraticIrreducible_two_digits (y : 𝒪) :
    scaledQuadraticIrreducible p ((p:𝒪)^2*y) =
      (fun z : 𝒪×𝒪 => ((p:𝒪)*z.1,z.2)) '' scaledQuadraticIrreducible p y := by
  ext z
  obtain ⟨b,c⟩ := z
  rw [mem_scaledQuadraticIrreducible]
  constructor
  · intro h
    have hd : (p:𝒪)∣b := by
      by_contra hn
      apply h
      simpa only [sq,mul_assoc] using padic_quadratic_root_of_unit_linear p b ((p:𝒪)*(y*c)) hn
    obtain ⟨s,rfl⟩ := hd
    refine ⟨(s,c),(mem_scaledQuadraticIrreducible p y _).mpr (fun hr => h ?_),rfl⟩
    simpa only [mul_assoc] using (padic_quadratic_scaled_roots_iff p s (y*c)).mpr hr
  · rintro ⟨⟨s,v⟩,hs,he⟩
    obtain rfl : (p:𝒪)*s=b := congrArg Prod.fst he
    obtain rfl : v=c := congrArg Prod.snd he
    exact fun hr => (mem_scaledQuadraticIrreducible p y _).mp hs ((padic_quadratic_scaled_roots_iff p s (y*v)).mp
      (by simpa only [mul_assoc] using hr))

/-- Irreducibility probability when the independent constant coefficient
has been multiplied by a fixed integral scale y. -/
def scaledIrreducibleMass (y : 𝒪) : ℝ :=
  let μ := fieldOnePadicIntNormalizedHaar p
  (μ.prod μ).real (scaledQuadraticIrreducible p y)

theorem scaledIrreducibleMass_two_digits (y : 𝒪) :
    scaledIrreducibleMass p ((p:𝒪)^2*y)=scaledIrreducibleMass p y/(p:ℝ) := by
  unfold scaledIrreducibleMass
  rw [scaledQuadraticIrreducible_two_digits]
  exact product_haar_prime_first_image p _ (measurableSet_scaledQuadraticIrreducible p y)

/-- Unrestricted constant coefficient. -/
theorem scaledIrreducibleMass_one : scaledIrreducibleMass p 1=((p:ℝ)+2)/(2*((p:ℝ)+1)) := by
  simpa only [scaledIrreducibleMass,scaledQuadraticIrreducible,one_mul] using
    padic_monic_quadratic_irreducible_probability p

/-- The first thin box has a unit linear coefficient on its entire automatically split part. -/
theorem scaledIrreducibleMass_prime : scaledIrreducibleMass p p=(2*(p:ℝ)+1)/(2*((p:ℝ)+1)*(p:ℝ)) := by
  let μ := fieldOnePadicIntNormalizedHaar p
  let S := {z : 𝒪×𝒪 | ¬∃ x : 𝒪, x*(p*z.1-x)=p*z.2}
  have hS : MeasurableSet S := by
    have he : S=(fun z : 𝒪×𝒪 => ((p:𝒪)*z.1,z.2)) ⁻¹' scaledQuadraticIrreducible p p :=
      Set.ext fun z => (mem_scaledQuadraticIrreducible p p ((p:𝒪)*z.1,z.2)).symm
    rw [he]
    exact (measurableSet_scaledQuadraticIrreducible p p).preimage
      (((continuous_const.mul continuous_fst).prodMk continuous_snd :
        Continuous (fun z : 𝒪×𝒪 => ((p:𝒪)*z.1,z.2))).measurable)
  have hT : scaledQuadraticIrreducible p p=(fun z : 𝒪×𝒪 => ((p:𝒪)*z.1,z.2)) '' S := by
    ext z
    obtain ⟨b,c⟩ := z
    rw [mem_scaledQuadraticIrreducible]
    constructor
    · intro h
      have hd : (p:𝒪)∣b := by
        by_contra hn
        exact h (padic_quadratic_root_of_unit_linear p b c hn)
      obtain ⟨v,rfl⟩ := hd
      exact ⟨(v,c),h,rfl⟩
    · rintro ⟨⟨v,w⟩,hv,he⟩
      obtain rfl : (p:𝒪)*v=b := congrArg Prod.fst he
      obtain rfl : w=c := congrArg Prod.snd he
      exact hv
  have he : S={z : 𝒪×𝒪 | Irreducible
      (X^2+C (((p:𝒪)*z.1:𝒪):ℚ_[p])*X+C (((p:𝒪)*z.2:𝒪):ℚ_[p]))} := by
    ext z
    exact ((irreducible_quadratic_iff _ _).trans (not_congr (quadratic_root_integral p _ _))).symm
  unfold scaledIrreducibleMass
  rw [hT,product_haar_prime_first_image p S hS,he,padic_ramified_quadratic_irreducible_probability,div_div]

/-- Even and odd constant-coefficient valuations give different
irreducibility densities at every depth, including p=2. -/
theorem thin_coefficient_quadratic_irreducibility (k : ℕ) :
    scaledIrreducibleMass p ((p:𝒪)^(2*k))=((p:ℝ)+2)/(2*((p:ℝ)+1)*(p:ℝ)^k) ∧
    scaledIrreducibleMass p ((p:𝒪)^(2*k+1))=(2*(p:ℝ)+1)/(2*((p:ℝ)+1)*(p:ℝ)^(k+1)) := by
  induction k with
  | zero => simpa only [mul_zero,zero_add,pow_zero,pow_one,mul_one] using And.intro (scaledIrreducibleMass_one p) (scaledIrreducibleMass_prime p)
  | succ k ih =>
    obtain ⟨he,ho⟩ := ih
    constructor
    · rw [show 2*(k+1)=2+2*k by omega,pow_add,scaledIrreducibleMass_two_digits,he,div_div,pow_succ,mul_assoc]
    · rw [show 2*(k+1)+1=2+(2*k+1) by omega,pow_add,scaledIrreducibleMass_two_digits,ho,div_div,
        pow_succ (p:ℝ) (k+1),mul_assoc]

#print axioms padic_quadratic_root_of_unit_linear
#print axioms scaledQuadraticIrreducible_two_digits
#print axioms scaledIrreducibleMass_two_digits
#print axioms thin_coefficient_quadratic_irreducibility
end
end GaloisForLFunctions.RepresentationLifting
