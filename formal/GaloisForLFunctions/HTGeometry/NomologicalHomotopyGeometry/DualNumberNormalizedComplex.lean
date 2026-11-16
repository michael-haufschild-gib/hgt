import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw
import GaloisForLFunctions.HTGeometry.CochainComplexCohomology
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!+# The normalized dual-number Hochschild complex in every degree

The augmentation ideal of the dual numbers is the line spanned by ε,
with zero product. Thus a normalized cochain is determined by its value
on `(ε,…,ε)`. The Hochschild differential alternates between zero and
`(a,b) ↦ (0,2a)`. Every positive even class has a unique scalar-valued
representative; every odd class has a unique ε-valued representative.

The cup product and Euler action specialize the operations in Abbaspour,
arXiv:1302.6534, §1. The Euler weights extend the deformation-weight
mechanism of Lopatkin, arXiv:2611.04022, Proposition 11.4, to all degrees.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent

namespace NormalizedComplex

noncomputable section

/-- Cochains on the augmentation ideal, identified with its ε-coordinate. -/
abbrev ReducedCochain (n : ℕ) := MultilinearMap ℝ (fun _ : Fin n => ℝ) Dual

/-- A reduced cochain with prescribed value on the tensor of ε-generators. -/
def cochain (n : ℕ) (u : Dual) : ReducedCochain n := MultilinearMap.mkPiRing ℝ (Fin n) u

/-- This identification includes every reduced cochain, in every degree. -/
theorem cochain_exhaustive (n : ℕ) (F : ReducedCochain n) :
    F = cochain n (F fun _ => 1) := by
  apply DFunLike.ext
  intro x
  simpa only [smul_eq_mul, mul_one, cochain, MultilinearMap.mkPiRing_apply] using
    F.map_smul_univ x (fun _ => 1)

/-- The full normalized cochain is obtained by projecting each argument onto the augmentation ideal. -/
def normalizedCochain (n : ℕ) (u : Dual) : MultilinearMap ℝ (fun _ : Fin n => Dual) Dual :=
  (cochain n u).compLinearMap (fun _ => LinearMap.snd ℝ ℝ ℝ)

theorem normalizedCochain_unit (n : ℕ) (u : Dual) (x : Fin n → Dual) (i : Fin n) :
    normalizedCochain n u (Function.update x i one) = 0 := by
  apply (cochain n u).map_coord_zero i
  simp [one]

/-- Every normalized multilinear cochain on the full algebra is captured by the reduced model. -/
theorem normalizedCochain_exhaustive (n : ℕ)
    (F : MultilinearMap ℝ (fun _ : Fin n => Dual) Dual) :
    (∀ x i, F (Function.update x i one) = 0) ↔
      F = normalizedCochain n (F fun _ => eps) := by
  constructor
  · intro hn
    have strip (y : Fin n → Dual) (i : Fin n) :
        F y = F (Function.update y i ((y i).2 • eps)) := by
      have hc : y i = (y i).1 • one + (y i).2 • eps := by
        ext <;> simp [one, eps]
      calc
        F y = F (Function.update y i (y i)) :=
          congrArg F (Function.update_eq_self i y).symm
        _ = F (Function.update y i ((y i).1 • one + (y i).2 • eps)) :=
          congrArg (fun z => F (Function.update y i z)) hc
        _ = F (Function.update y i ((y i).1 • one)) +
            F (Function.update y i ((y i).2 • eps)) := F.map_update_add _ _ _ _
        _ = F (Function.update y i ((y i).2 • eps)) := by
          rw [F.map_update_smul, hn, smul_zero, zero_add]
    apply DFunLike.ext
    intro x
    let stripped (s : Finset (Fin n)) (i : Fin n) : Dual :=
      if i ∈ s then (x i).2 • eps else x i
    have hs (s : Finset (Fin n)) : F (stripped s) = F x := by
      induction s using Finset.induction_on with
      | empty => simp [stripped]
      | @insert i s hi ih =>
        have hupdate : stripped (insert i s) = Function.update (stripped s) i ((x i).2 • eps) := by
          funext j
          by_cases hj : j = i <;> simp [stripped, Function.update, hj]
        rw [hupdate]
        calc
          F (Function.update (stripped s) i ((x i).2 • eps)) = F (stripped s) := by
            simpa [stripped, hi] using (strip (stripped s) i).symm
          _ = F x := ih
    have hall : F (fun i => (x i).2 • eps) = F x := by
      simpa [stripped] using hs Finset.univ
    rw [← hall, F.map_smul_univ]
    rfl
  · intro h x i
    rw [h]
    exact normalizedCochain_unit _ _ _ _

/-- On ε-generators all interior Hochschild faces contain the zero product ε². -/
def generatorCoboundary (n : ℕ) (F : ReducedCochain n) : Dual :=
  product 0 eps (F fun _ => 1) +
    ∑ i : Fin n, (-1 : ℝ) ^ (i.val + 1) • F (Function.update (fun _ => 1) i 0) +
    (-1 : ℝ) ^ (n + 1) • product 0 (F fun _ => 1) eps

/-- The actual normalized Hochschild differential in coefficient coordinates. -/
def differential (n : ℕ) : Dual →ₗ[ℝ] Dual where
  toFun u := (0, (1 + (-1 : ℝ) ^ (n + 1)) * u.1)
  map_add' u v := by ext <;> dsimp <;> ring
  map_smul' a u := by ext <;> dsimp <;> ring

/-- The coefficient differential is the Hochschild alternating-face formula. -/
theorem generatorCoboundary_eq (n : ℕ) (F : ReducedCochain n) :
    generatorCoboundary n F = differential n (F fun _ => 1) := by
  have hz (i : Fin n) : F (Function.update (fun _ => 1) i 0) = 0 :=
    F.map_coord_zero i (by simp)
  simp only [generatorCoboundary, hz, smul_zero, Finset.sum_const_zero, add_zero]
  ext <;> dsimp [product, eps, differential] <;> ring

/-- Every interior reduced bar face vanishes because the augmentation ideal has square zero. -/
theorem augmentation_product_zero (a b : ℝ) : product 0 (a • eps) (b • eps) = 0 := by
  simp [product, eps]

/-- On arbitrary reduced inputs, the coefficient differential is the full remaining bar formula. -/
theorem differential_on_inputs (n : ℕ) (F : ReducedCochain n) (x : Fin (n + 1) → ℝ) :
    cochain (n + 1) (differential n (F fun _ => 1)) x =
      product 0 (x 0 • eps) (F fun i => x i.succ) +
        (-1 : ℝ) ^ (n + 1) • product 0 (F fun i => x i.castSucc) (x (Fin.last n) • eps) := by
  have ht := congrArg (fun G : ReducedCochain n => G (fun i => x i.succ))
    (cochain_exhaustive n F)
  have hi := congrArg (fun G : ReducedCochain n => G (fun i => x i.castSucc))
    (cochain_exhaustive n F)
  rw [ht, hi]
  have hfirst := Fin.prod_univ_succ x
  have hlast := Fin.prod_univ_castSucc x
  ext
  · simp [cochain, differential, product, eps, MultilinearMap.mkPiRing_apply]
  · simp only [cochain, MultilinearMap.mkPiRing_apply, Prod.snd_add]
    dsimp [differential, product, eps]
    linear_combination (F (fun _ => 1)).1 * hfirst +
      ((-1 : ℝ) ^ (n + 1) * (F (fun _ => 1)).1) * hlast

theorem differential_even (n : ℕ) (u : Dual) : differential (2 * n) u = 0 := by
  ext <;> simp [differential, pow_add, pow_mul]

theorem differential_odd (n : ℕ) (u : Dual) :
    differential (2 * n + 1) u = (0, 2 * u.1) := by
  ext <;> norm_num [differential, pow_add, pow_mul]

/-- The normalized coefficient complex, with the square-zero identity proved explicitly. -/
def complex : HTGeometry.DeningerCochainComplex ℝ (fun _ => Dual) where
  d := differential
  d_comp_d n := by
    apply LinearMap.ext
    intro u
    ext <;> simp [differential]

/-- Cup multiplication is the product of the values on ε-generators. -/
def cup (u v : Dual) : Dual := product 0 u v

/-- Hochschild's differential satisfies the graded Leibniz rule for the cup product. -/
theorem differential_cup (m n : ℕ) (u v : Dual) :
    differential (m + n) (cup u v) =
      cup (differential m u) v + (-1 : ℝ) ^ m • cup u (differential n v) := by
  ext <;> dsimp [differential, cup, product]
  · ring
  · simp only [pow_add, pow_one]
    ring

theorem cup_assoc (u v w : Dual) : cup (cup u v) w = cup u (cup v w) :=
  product_assoc 0 u v w

theorem odd_generator_cup_square : cup eps eps = 0 := by simp [cup, product, eps]

/-- Multiplication by the degree-two scalar generator gives the positive-degree periodicity. -/
theorem cup_scalar_generator (u : Dual) : cup one u = u ∧ cup u one = u :=
  ⟨product_one_left 0 u, product_one_right 0 u⟩

/-- Euler's Gerstenhaber action subtracts the total input weight from the output weight. -/
def eulerAction (n : ℕ) (u : Dual) : Dual := (-(n : ℝ) * u.1, (1 - n) * u.2)

/-- The unary Euler insertion fixes each ε-input and acts by its weight on the output. -/
theorem eulerAction_eq_insertions (n : ℕ) (u : Dual) :
    eulerAction n u = (0, u.2) - ∑ _ : Fin n, u := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ext <;> simp [eulerAction, nsmul_eq_mul, sub_mul]

theorem eulerAction_differential (n : ℕ) (u : Dual) :
    eulerAction (n + 1) (differential n u) = differential n (eulerAction n u) := by
  ext <;> simp only [eulerAction, differential, LinearMap.coe_mk, AddHom.coe_mk,
    Nat.cast_add, Nat.cast_one] <;> ring

theorem eulerAction_cup (m n : ℕ) (u v : Dual) :
    eulerAction (m + n) (cup u v) = cup (eulerAction m u) v + cup u (eulerAction n v) := by
  ext <;> dsimp [eulerAction, cup, product] <;> push_cast <;> ring

theorem odd_cocycle_iff (n : ℕ) (u : Dual) :
    u ∈ complex.cocycles (2 * n + 1) ↔ u.1 = 0 := by
  change differential (2 * n + 1) u = 0 ↔ _
  rw [differential_odd]
  simp

theorem odd_boundary_iff (n : ℕ) (u : Dual) :
    u ∈ complex.coboundaries (2 * n + 1) ↔ u = 0 := by
  change (∃ v, differential (2 * n) v = u) ↔ _
  simp only [differential_even]
  constructor
  · rintro ⟨_, h⟩; exact h.symm
  · rintro rfl; exact ⟨0, rfl⟩

theorem even_boundary_iff (n : ℕ) (u : Dual) :
    u ∈ complex.coboundaries (2 * (n + 1)) ↔ u.1 = 0 := by
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
  change (∃ v, differential (2 * n + 1) v = u) ↔ _
  simp only [differential_odd]
  constructor
  · rintro ⟨v, hv⟩
    exact (congrArg Prod.fst hv).symm
  · intro hu
    refine ⟨(u.2 / 2, 0), ?_⟩
    ext <;> dsimp
    · exact hu.symm
    · ring

/-- The degree-zero nilpotent annihilates every positive even scalar class. -/
theorem nilpotent_cup_even_is_boundary (n : ℕ) (a : ℝ) :
    cup eps (a, 0) ∈ complex.coboundaries (2 * (n + 1)) := by
  rw [even_boundary_iff]
  simp [cup, eps, product]

/-- Degree-zero classes are the two-dimensional center of the dual-number algebra. -/
def zeroClass (u : Dual) : complex.cohomology 0 :=
  complex.cohomologyMk ⟨u, differential_even 0 u⟩

theorem zeroClass_eq_iff (u v : Dual) : zeroClass u = zeroClass v ↔ u = v := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ ↔ _
  rw [Submodule.Quotient.eq]
  change u - v ∈ (⊥ : Submodule ℝ Dual) ↔ _
  rw [Submodule.mem_bot]
  exact sub_eq_zero

theorem zero_classification (q : complex.cohomology 0) : ∃! u : Dual, zeroClass u = q := by
  obtain ⟨x, rfl⟩ := complex.cohomologyMk_surjective 0 q
  have hx : zeroClass x.val = complex.cohomologyMk x := rfl
  exact ⟨x.val, hx, fun u hu => (zeroClass_eq_iff u x.val).mp (hu.trans hx.symm)⟩

/-- Canonical scalar representative of a positive even cohomology class. -/
def evenClass (n : ℕ) (a : ℝ) : complex.cohomology (2 * (n + 1)) :=
  complex.cohomologyMk ⟨(a, 0), differential_even (n + 1) (a, 0)⟩

/-- Canonical ε-valued representative of an odd cohomology class. -/
def oddClass (n : ℕ) (a : ℝ) : complex.cohomology (2 * n + 1) :=
  complex.cohomologyMk ⟨(0, a), (odd_cocycle_iff n _).mpr rfl⟩

theorem evenClass_eq_iff (n : ℕ) (a b : ℝ) : evenClass n a = evenClass n b ↔ a = b := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ ↔ _
  rw [Submodule.Quotient.eq]
  change ((a, 0) - (b, 0) : Dual) ∈ complex.coboundaries (2 * (n + 1)) ↔ _
  rw [even_boundary_iff]
  exact sub_eq_zero

theorem oddClass_eq_iff (n : ℕ) (a b : ℝ) : oddClass n a = oddClass n b ↔ a = b := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ ↔ _
  rw [Submodule.Quotient.eq]
  change ((0, a) - (0, b) : Dual) ∈ complex.coboundaries (2 * n + 1) ↔ _
  rw [odd_boundary_iff]
  simp [sub_eq_zero]

/-- Complete classification in every positive even degree. -/
theorem even_classification (n : ℕ) (q : complex.cohomology (2 * (n + 1))) :
    ∃! a : ℝ, evenClass n a = q := by
  obtain ⟨x, rfl⟩ := complex.cohomologyMk_surjective _ q
  have hx : evenClass n x.val.1 = complex.cohomologyMk x := by
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    change ((x.val.1, 0) - x.val : Dual) ∈ complex.coboundaries (2 * (n + 1))
    rw [even_boundary_iff]
    exact sub_self _
  refine ⟨x.val.1, hx, fun a ha => (evenClass_eq_iff n a x.val.1).mp (ha.trans hx.symm)⟩

/-- Complete classification in every odd degree. -/
theorem odd_classification (n : ℕ) (q : complex.cohomology (2 * n + 1)) :
    ∃! a : ℝ, oddClass n a = q := by
  obtain ⟨x, rfl⟩ := complex.cohomologyMk_surjective _ q
  have hfst : x.val.1 = 0 := (odd_cocycle_iff n x.val).mp x.property
  have hx : oddClass n x.val.2 = complex.cohomologyMk x := by
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    change ((0, x.val.2) - x.val : Dual) ∈ complex.coboundaries (2 * n + 1)
    rw [odd_boundary_iff]
    ext <;> simp [hfst]
  refine ⟨x.val.2, hx, fun a ha => (oddClass_eq_iff n a x.val.2).mp (ha.trans hx.symm)⟩

/-! The Frobenius transpose of cyclic rotation, and its derived Euler bracket. -/

/-- Signed multiplicity of the cyclic rotations of an ε-tensor. -/
def cyclicMultiplicity (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ (i * (n - 1))

private theorem alternating_sum_even (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), (-1 : ℝ) ^ i = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp [pow_add, pow_mul]

theorem cyclicMultiplicity_even (n : ℕ) : cyclicMultiplicity (2 * n) = 0 := by
  cases n with
  | zero => simp [cyclicMultiplicity]
  | succ n =>
      have hsign (i : ℕ) : (-1 : ℝ) ^ (i * (2 * (n + 1) - 1)) = (-1) ^ i := by
        rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, Nat.mul_comm i, pow_mul]
        simp [pow_add, pow_mul]
      simp only [cyclicMultiplicity, hsign]
      exact alternating_sum_even (n + 1)

theorem cyclicMultiplicity_odd (n : ℕ) : cyclicMultiplicity (2 * n + 1) = 2 * n + 1 := by
  have hsign (i : ℕ) : (-1 : ℝ) ^ (i * ((2 * n + 1) - 1)) = 1 := by
    rw [Nat.add_sub_cancel, Nat.mul_comm i, pow_mul]
    simp [pow_mul]
  simp only [cyclicMultiplicity, hsign]
  simp

/-- Frobenius transpose of the normalized cyclic operator; it lowers cochain degree by one. -/
def bv (n : ℕ) (u : Dual) : Dual := (cyclicMultiplicity n * u.2, 0)

/-- The ε-test of the transpose is exactly the signed cyclic trace sum. -/
theorem bv_pairing_generator (n : ℕ) (u : Dual) :
    pairing (bv n u) eps =
      ∑ i ∈ Finset.range n, (-1 : ℝ) ^ (i * (n - 1)) * trace u := by
  rw [← Finset.sum_mul]
  simp [pairing, bv, product, eps, trace, cyclicMultiplicity]

theorem bv_pairing_unit (n : ℕ) (u : Dual) : pairing (bv n u) one = 0 := by
  simp [pairing, bv, product, one, trace]

/-- The cyclic trace tests uniquely characterize the Frobenius transpose. -/
theorem bv_characterization (n : ℕ) (u v : Dual) :
    (pairing v eps = ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ (i * (n - 1)) * trace u) ∧ pairing v one = 0 ↔ v = bv n u := by
  constructor
  · rintro ⟨he, ho⟩
    have hε := he.trans (bv_pairing_generator n u).symm
    have h1 := ho.trans (bv_pairing_unit n u).symm
    apply Prod.ext
    · simpa [pairing, product, eps, trace] using hε
    · simpa [pairing, product, one, trace] using h1
  · rintro rfl
    exact ⟨bv_pairing_generator n u, bv_pairing_unit n u⟩

theorem bv_even (n : ℕ) (u : Dual) : bv (2 * n) u = 0 := by
  simp [bv, cyclicMultiplicity_even]

theorem bv_odd (n : ℕ) (u : Dual) : bv (2 * n + 1) u = ((2 * n + 1) * u.2, 0) := by
  rw [bv, cyclicMultiplicity_odd]

theorem bv_square_zero (m n : ℕ) (u : Dual) : bv m (bv n u) = 0 := by simp [bv]

/-- The cyclic transpose anticommutes with the Hochschild differential. -/
theorem bv_differential (n : ℕ) (u : Dual) :
    differential n (bv (n + 1) u) + bv (n + 2) (differential (n + 1) u) = 0 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hn : n = 2 * k := by omega
    rw [hn]
    rw [differential_even, show 2 * k + 2 = 2 * (k + 1) by omega, bv_even]
    simp
  · have hn : n = 2 * k + 1 := by omega
    rw [hn]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, bv_even, differential_even]
    simp [differential, bv]

/-- Abbaspour's BV-derived bracket with the degree-one Euler class. -/
def bvEulerBracket (n : ℕ) (u : Dual) : Dual :=
  -bv (n + 1) (cup eps u) + cup (bv 1 eps) u - cup eps (bv n u)

theorem bvEulerBracket_zero (u : Dual) : bvEulerBracket 0 u = eulerAction 0 u := by
  simp [bvEulerBracket, bv_odd 0, bv_even 0, cup, eps, product, eulerAction]
  ext <;> simp

/-- On positive even classes the BV-derived bracket equals the Euler insertion bracket. -/
theorem bvEulerBracket_even (n : ℕ) (a : ℝ) :
    bvEulerBracket (2 * n) (a, 0) = eulerAction (2 * n) (a, 0) := by
  have h1 : bv 1 eps = one := by simpa [eps, one] using bv_odd 0 eps
  rw [bvEulerBracket, bv_odd, bv_even, h1]
  ext <;> dsimp [cup, product, eps, one, eulerAction] <;> push_cast <;> ring

/-- On odd classes the same formula gives weight minus twice the periodicity exponent. -/
theorem bvEulerBracket_odd (n : ℕ) (a : ℝ) :
    bvEulerBracket (2 * n + 1) (0, a) = eulerAction (2 * n + 1) (0, a) := by
  have h1 : bv 1 eps = one := by simpa [eps, one] using bv_odd 0 eps
  rw [bvEulerBracket, show 2 * n + 1 + 1 = 2 * (n + 1) by omega, bv_even, bv_odd, h1]
  ext <;> dsimp [cup, product, eps, one, eulerAction] <;> push_cast <;> ring

end

end NormalizedComplex

end HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent

#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.NormalizedComplex.even_classification
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.NormalizedComplex.odd_classification
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.NormalizedComplex.differential_cup
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.NormalizedComplex.normalizedCochain_exhaustive
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.NormalizedComplex.generatorCoboundary_eq
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.NormalizedComplex.differential_on_inputs
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.NormalizedComplex.bv_differential
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.NormalizedComplex.bvEulerBracket_even
#print axioms HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw.DualNumberEvent.NormalizedComplex.bvEulerBracket_odd
