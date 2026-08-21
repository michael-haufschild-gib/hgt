import GaloisForLFunctions.HTGeometry.PlaceGrading
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-!
# The value at a place

`TopLim m f a` — the value of `f` at infinity in the coordinate `m` — becomes, at a place of an
algebraic extension, the statement that `f − a` has valuation strictly below the unit level.  The
accuracy is a parameter here rather than the fixed `−1` of the coordinate model: at a place of
ramification index `e` one step of the base coordinate is `e` steps of the place.

Everything the peel consumes about values at infinity is reproduced: the algebra of limits, their
uniqueness against a subring on which the place is trivial, and the entrywise passage to
determinants.  The last theorem is what makes the transport from the coordinate model automatic —
a place trivial on a subfield is trivial on every element algebraic over it, so coordinate-free
elements stay coordinate-free after the algebraic extension.

* `PlaceLim`, `placeLim_self`, `PlaceLim.add/neg/sub/mul`;
* `placeLim_sum`, `placeLim_prod`, `placeLim_det`;
* `PlaceTrivialOn`, `eq_zero_of_mem_of_placeDegLE_lt`, `placeLim_unique`;
* `one_le_valuation_of_isIntegral`, `placeFree_of_isIntegral`.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- `f` has value `a` at the place, to accuracy `γ`. -/
def PlaceLim (γ : ℤᵐ⁰) (f a : K) : Prop := PlaceDegLE v γ (f - a)

theorem placeLim_self (γ : ℤᵐ⁰) (a : K) : PlaceLim v γ a a := by
  rw [PlaceLim, sub_self]
  exact placeDegLE_zero v γ

theorem PlaceLim.add {γ : ℤᵐ⁰} {f g a b : K} (hf : PlaceLim v γ f a) (hg : PlaceLim v γ g b) :
    PlaceLim v γ (f + g) (a + b) := by
  have h := PlaceDegLE.add v hf hg
  have heq : f - a + (g - b) = f + g - (a + b) := by ring
  rwa [heq] at h

theorem PlaceLim.neg {γ : ℤᵐ⁰} {f a : K} (hf : PlaceLim v γ f a) : PlaceLim v γ (-f) (-a) := by
  have h := PlaceDegLE.neg v hf
  have heq : -(f - a) = -f - -a := by ring
  rwa [heq] at h

theorem PlaceLim.sub {γ : ℤᵐ⁰} {f g a b : K} (hf : PlaceLim v γ f a) (hg : PlaceLim v γ g b) :
    PlaceLim v γ (f - g) (a - b) := by
  have h := PlaceDegLE.sub v hf hg
  have heq : f - a - (g - b) = f - g - (a - b) := by ring
  rwa [heq] at h

/-- A limit of unit size is itself of unit size. -/
theorem PlaceLim.placeDegLE_one {γ : ℤᵐ⁰} (hγ : γ ≤ 1) {f a : K} (ha : PlaceDegLE v 1 a)
    (hf : PlaceLim v γ f a) : PlaceDegLE v 1 f := by
  have h := PlaceDegLE.add v (PlaceDegLE.mono v hγ hf) ha
  have heq : f - a + a = f := by ring
  rwa [heq] at h

theorem PlaceLim.mul {γ : ℤᵐ⁰} (hγ : γ ≤ 1) {f g a b : K}
    (ha : PlaceDegLE v 1 a) (hb : PlaceDegLE v 1 b)
    (hf : PlaceLim v γ f a) (hg : PlaceLim v γ g b) :
    PlaceLim v γ (f * g) (a * b) := by
  have hg1 : PlaceDegLE v 1 g := PlaceLim.placeDegLE_one v hγ hb hg
  have h1 : PlaceDegLE v γ ((f - a) * g) := by
    have := PlaceDegLE.mul v hf hg1
    rwa [mul_one] at this
  have h2 : PlaceDegLE v γ (a * (g - b)) := by
    have := PlaceDegLE.mul v ha hg
    rwa [one_mul] at this
  have h := PlaceDegLE.add v h1 h2
  have heq : (f - a) * g + a * (g - b) = f * g - a * b := by ring
  rwa [heq] at h

theorem placeDegLE_one_prod {ι : Type*} (s : Finset ι) (L : ι → K)
    (hL : ∀ i ∈ s, PlaceDegLE v 1 (L i)) : PlaceDegLE v 1 (∏ i ∈ s, L i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using placeDegLE_one v
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have := PlaceDegLE.mul v (hL a (Finset.mem_insert_self a s))
        (ih fun i hi => hL i (Finset.mem_insert_of_mem hi))
      rwa [one_mul] at this

theorem placeLim_sum {γ : ℤᵐ⁰} {ι : Type*} (s : Finset ι) (F L : ι → K)
    (h : ∀ i ∈ s, PlaceLim v γ (F i) (L i)) :
    PlaceLim v γ (∑ i ∈ s, F i) (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using placeLim_self v γ (0 : K)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact PlaceLim.add v (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem placeLim_prod {γ : ℤᵐ⁰} (hγ : γ ≤ 1) {ι : Type*} (s : Finset ι) (F L : ι → K)
    (hL : ∀ i ∈ s, PlaceDegLE v 1 (L i)) (h : ∀ i ∈ s, PlaceLim v γ (F i) (L i)) :
    PlaceLim v γ (∏ i ∈ s, F i) (∏ i ∈ s, L i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using placeLim_self v γ (1 : K)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact PlaceLim.mul v hγ (hL a (Finset.mem_insert_self a s))
        (placeDegLE_one_prod v s L fun i hi => hL i (Finset.mem_insert_of_mem hi))
        (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => hL i (Finset.mem_insert_of_mem hi))
          fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **A matrix of limits has the limit determinant.** -/
theorem placeLim_det {γ : ℤᵐ⁰} (hγ : γ ≤ 1) {n : ℕ} (A L : Matrix (Fin n) (Fin n) K)
    (hL : ∀ i j, PlaceDegLE v 1 (L i j)) (h : ∀ i j, PlaceLim v γ (A i j) (L i j)) :
    PlaceLim v γ A.det L.det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply]
  refine placeLim_sum v _ _ _ fun σ _ => ?_
  have hprod : PlaceLim v γ (∏ i, A (σ i) i) (∏ i, L (σ i) i) :=
    placeLim_prod v hγ _ _ _ (fun i _ => hL (σ i) i) fun i _ => h (σ i) i
  have hsign : ((Equiv.Perm.sign σ : ℤ) : K) = 1 ∨ ((Equiv.Perm.sign σ : ℤ) : K) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] <;> simp
  rcases hsign with hs | hs <;>
    simp only [Units.smul_def, zsmul_eq_mul, hs, one_mul, neg_mul] <;>
    [exact hprod; exact PlaceLim.neg v hprod]

/-! ### Triviality on a subfield -/

/-- The place is trivial on `F`: every nonzero element of `F` is a unit there. -/
def PlaceTrivialOn (F : Subfield K) : Prop := ∀ x ∈ F, x ≠ 0 → v.valuation K x = 1

theorem PlaceTrivialOn.placeDegLE_one {F : Subfield K} (hF : PlaceTrivialOn v F)
    {x : K} (hx : x ∈ F) : PlaceDegLE v 1 x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact placeDegLE_zero v 1
  · exact le_of_eq (hF x hx hx0)

/-- **An element of a trivially valued subfield with strictly small valuation vanishes.** -/
theorem eq_zero_of_mem_of_placeDegLE_lt {F : Subfield K} (hF : PlaceTrivialOn v F)
    {γ : ℤᵐ⁰} (hγ : γ < 1) {f : K} (hf : f ∈ F) (hd : PlaceDegLE v γ f) : f = 0 := by
  by_contra h0
  have h1 : (1 : ℤᵐ⁰) ≤ γ := le_trans (le_of_eq (hF f hf h0).symm) hd
  exact absurd (lt_of_le_of_lt h1 hγ) (lt_irrefl 1)

/-- **The value at the place is unique.** -/
theorem placeLim_unique {F : Subfield K} (hF : PlaceTrivialOn v F)
    {γ : ℤᵐ⁰} (hγ : γ < 1) {f a b : K} (ha : a ∈ F) (hb : b ∈ F)
    (h1 : PlaceLim v γ f a) (h2 : PlaceLim v γ f b) : a = b := by
  have hsub : PlaceDegLE v γ (b - a) := by
    have hd := PlaceDegLE.sub v h1 h2
    have heq : f - a - (f - b) = b - a := by ring
    rwa [heq] at hd
  have hmem : b - a ∈ F := F.sub_mem hb ha
  have := eq_zero_of_mem_of_placeDegLE_lt v hF hγ hmem hsub
  linear_combination -this

/-- **A place trivial on a subfield admits no algebraic element of strictly small valuation.**
The constant term of the minimal equation is a unit while every other term is strictly small, so
the equation could not vanish. -/
theorem one_le_valuation_of_isIntegral {F : Subfield K} (hF : PlaceTrivialOn v F)
    {x : K} (hx : IsIntegral F x) (hx0 : x ≠ 0) : 1 ≤ v.valuation K x := by
  classical
  by_contra hlt
  push Not at hlt
  set p : Polynomial F := minpoly F x with hp
  have hc0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hx hx0
  have hcmem : ∀ i, (algebraMap F K (p.coeff i)) ∈ F := fun i => (p.coeff i).2
  have hcle : ∀ i, PlaceDegLE v 1 (algebraMap F K (p.coeff i)) := fun i =>
    hF.placeDegLE_one v (hcmem i)
  have hzero : (0 : K) = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • x ^ i := by
    rw [← Polynomial.aeval_eq_sum_range]
    exact (minpoly.aeval F x).symm
  rw [Finset.sum_range_succ'] at hzero
  simp only [Algebra.smul_def, pow_zero, mul_one] at hzero
  have htail : v.valuation K (∑ i ∈ Finset.range p.natDegree,
      algebraMap F K (p.coeff (i + 1)) * x ^ (i + 1)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [Valuation.map_mul, Valuation.map_pow]
    have hpow : v.valuation K x ^ (i + 1) ≤ v.valuation K x := by
      calc v.valuation K x ^ (i + 1) = v.valuation K x ^ i * v.valuation K x := pow_succ _ i
        _ ≤ 1 * v.valuation K x :=
            mul_le_mul' (pow_le_one' (le_of_lt hlt) i) le_rfl
        _ = v.valuation K x := one_mul _
    calc v.valuation K (algebraMap F K (p.coeff (i + 1))) * v.valuation K x ^ (i + 1)
        ≤ 1 * v.valuation K x ^ (i + 1) := mul_le_mul' (hcle (i + 1)) le_rfl
      _ = v.valuation K x ^ (i + 1) := one_mul _
      _ ≤ v.valuation K x := hpow
      _ < 1 := hlt
  have hhead : v.valuation K (algebraMap F K (p.coeff 0)) = 1 := by
    refine hF _ (hcmem 0) ?_
    simpa using (FaithfulSMul.algebraMap_injective F K).ne_iff.mpr hc0
  have hsum := valuation_add_of_lt v hhead htail
  rw [add_comm] at hsum
  rw [← hzero, Valuation.map_zero] at hsum
  exact zero_ne_one hsum

/-- **A place trivial on a subfield is trivial on every element algebraic over it.**  This is what
carries coordinate-freeness through an algebraic extension. -/
theorem placeFree_of_isIntegral {F : Subfield K} (hF : PlaceTrivialOn v F)
    {x : K} (hx : IsIntegral F x) (hxinv : IsIntegral F x⁻¹) (hx0 : x ≠ 0) :
    PlaceFree v x := by
  have h1 : 1 ≤ v.valuation K x := one_le_valuation_of_isIntegral v hF hx hx0
  have h2 : 1 ≤ v.valuation K x⁻¹ :=
    one_le_valuation_of_isIntegral v hF hxinv (inv_ne_zero hx0)
  have hmul : v.valuation K x * v.valuation K x⁻¹ = 1 := by
    rw [← Valuation.map_mul, mul_inv_cancel₀ hx0, Valuation.map_one]
  have hle : v.valuation K x ≤ 1 := by
    calc v.valuation K x = v.valuation K x * 1 := (mul_one _).symm
      _ ≤ v.valuation K x * v.valuation K x⁻¹ := mul_le_mul' le_rfl h2
      _ = 1 := hmul
  exact le_antisymm hle h1

end GaloisForLFunctions.HTGeometry
