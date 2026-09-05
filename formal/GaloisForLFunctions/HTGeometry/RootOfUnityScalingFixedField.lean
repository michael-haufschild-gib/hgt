import GaloisForLFunctions.HTGeometry.TorusInvariantMonomials
import GaloisForLFunctions.HTGeometry.DifferentialHorizonInterface

/-!
# The invariant field of a root-of-unity scaling on a free differential field

On a freely differentially generated field with one generator `v`, the scaling deck transformation
by a root of unity of exact order `n` has invariant field exactly the differential field of the
`n`-th power `v ^ n`: the torus invariant theorem identifies the invariants with the velocity
field extended by the monomials of exponent divisible by `n`, and both the velocity `v′/v` and
those monomials are differential rational functions of `v ^ n`.

This is the rotation layer of every parabolic orbifold deck group: the cone orders
`n ∈ {2, 3, 4, 6}` of the compact Euclidean signatures, and the order-two inversion of the
dihedral signature acting on the Maurer–Cartan current by sign.

* `logDeriv_mem_differentialAdjoin_pow`;
* `mem_differentialAdjoin_pow_of_rootOfUnity_invariant`;
* `differentialAdjoin_pow_fixed_of_rootOfUnity`;
* `setOf_rootOfUnity_invariant_eq_differentialAdjoin_pow`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped Differential

noncomputable section

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero C] [CharZero E]

omit [CharZero C] in
/-- The logarithmic derivative of the generator is a differential rational function of any fixed
positive power: `v′/v = (v^n)′/(n·v^n)`. -/
theorem logDeriv_mem_differentialAdjoin_pow {v : E} (hv0 : v ≠ 0) {n : ℕ} (hn : 0 < n) :
    Differential.logDeriv v ∈ differentialAdjoin C ({v ^ n} : Set E) := by
  have hvn0 : v ^ n ≠ 0 := pow_ne_zero n hv0
  have hpow : (v ^ n)′ = (n : E) * v ^ (n - 1) * v′ := by
    have h := Differential.deriv.leibniz_pow (a := v) n
    simp only [nsmul_eq_mul, smul_eq_mul] at h
    rw [h]
    ring
  have hn0 : (n : E) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hn.ne'
  have hpred : v ^ (n - 1) * v = v ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hkey : (v ^ n)′ / ((n : E) * v ^ n) = v′ / v := by
    rw [hpow, div_eq_div_iff (mul_ne_zero hn0 hvn0) hv0]
    linear_combination ((n : E) * v′) * hpred
  rw [Differential.logDeriv, ← hkey]
  have hmem : v ^ n ∈ differentialAdjoin C ({v ^ n} : Set E) :=
    subset_differentialAdjoin C _ rfl
  have hderiv : (v ^ n)′ ∈ differentialAdjoin C ({v ^ n} : Set E) :=
    derivationClosed_differentialAdjoin C _ hmem
  have hnat : ((n : E)) ∈ differentialAdjoin C ({v ^ n} : Set E) := by
    exact_mod_cast (differentialAdjoin C ({v ^ n} : Set E)).natCast_mem n
  exact (differentialAdjoin C ({v ^ n} : Set E)).div_mem hderiv
    ((differentialAdjoin C ({v ^ n} : Set E)).mul_mem hnat hmem)

/-- **Invariance under a root-of-unity scaling forces membership in the power field.**  An element
of a freely generated rank-one differential field fixed by the scaling automorphism of a root of
unity of exact order `n` is a differential rational function of `v ^ n`. -/
theorem mem_differentialAdjoin_pow_of_rootOfUnity_invariant
    (hconst : ∀ c : C, c′ = 0)
    {v : E} (hv : DifferentialIndependent C (fun _ : Fin 1 ↦ v))
    (hgen : differentialAdjoin C (Set.range (fun _ : Fin 1 ↦ v)) = ⊤)
    (hv0 : v ≠ 0)
    {ζ : Cˣ} {n : ℕ} (hn : 0 < n) (hord : orderOf ζ = n)
    {z : E} (hz : torusScaleEquiv hv hgen (fun _ ↦ ζ) z = z) :
    z ∈ differentialAdjoin C ({v ^ n} : Set E) := by
  classical
  set N : IntermediateField C E := differentialAdjoin C ({v ^ n} : Set E) with hN
  have hbase : v ^ n ∈ N := subset_differentialAdjoin C ({v ^ n} : Set E) rfl
  have hzS : ∀ u ∈ ({fun _ ↦ ζ} : Set (Fin 1 → Cˣ)), torusScaleEquiv hv hgen u z = z := by
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact hz
  have hzmem := (torusScale_invariant_iff_mem_torusInvariantMonomialField hv hgen hconst
    (S := ({fun _ ↦ ζ} : Set (Fin 1 → Cˣ)))).mp hzS
  -- the velocity field lies in the power field
  have hvelle : torusVelocityField C (fun _ : Fin 1 ↦ v) ≤ N := by
    refine differentialAdjoin_le C ?_ (derivationClosed_differentialAdjoin C _)
    rintro w' ⟨i, rfl⟩
    exact logDeriv_mem_differentialAdjoin_pow hv0 hn
  -- every annihilating monomial lies in the power field
  have hmono : laurentMonomial (fun _ : Fin 1 ↦ v) '' scaleAnnihilator C
      ({fun _ ↦ ζ} : Set (Fin 1 → Cˣ)) ⊆ (N : Set E) := by
    rintro w ⟨a, ha, rfl⟩
    have ha' : ∀ u ∈ ({fun _ ↦ ζ} : Set (Fin 1 → Cˣ)), (∏ k, ((u k : C)) ^ (a k)) = 1 := ha
    have hchar : ((ζ : C)) ^ (a 0) = 1 := by
      have h1 := ha' (fun _ ↦ ζ) (Set.mem_singleton _)
      simpa [Fin.prod_univ_one] using h1
    have hunit : ζ ^ (a 0) = 1 := by
      ext
      rw [Units.val_zpow_eq_zpow_val, hchar]
      rfl
    have hdvd : ((n : ℤ)) ∣ a 0 := by
      rw [← hord]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hunit
    obtain ⟨k, hk⟩ := hdvd
    have hml : laurentMonomial (fun _ : Fin 1 ↦ v) a = v ^ (a 0) := by
      rw [laurentMonomial, Fin.prod_univ_one]
    rw [hml, hk, zpow_mul, zpow_natCast]
    obtain ⟨m, rfl | rfl⟩ := k.eq_nat_or_neg
    · rw [zpow_natCast]
      exact pow_mem hbase m
    · rw [zpow_neg, zpow_natCast]
      exact N.inv_mem (pow_mem hbase m)
  -- collapse the adjunction over the velocity field through scalar extension
  have hle : torusInvariantMonomialField C (fun _ : Fin 1 ↦ v)
      ({fun _ ↦ ζ} : Set (Fin 1 → Cˣ)) ≤ IntermediateField.extendScalars hvelle := by
    rw [torusInvariantMonomialField]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro w hw
    have hwN : w ∈ (N : Set E) := hmono hw
    rw [SetLike.mem_coe, IntermediateField.mem_extendScalars]
    exact hwN
  have hzN : z ∈ IntermediateField.extendScalars hvelle := hle hzmem
  rwa [IntermediateField.mem_extendScalars] at hzN

omit [CharZero C] [CharZero E] in
/-- **The power field is invariant.**  The scaling automorphism of a root of unity of order `n`
fixes every differential rational function of `v ^ n`. -/
theorem differentialAdjoin_pow_fixed_of_rootOfUnity
    {v : E} (hv : DifferentialIndependent C (fun _ : Fin 1 ↦ v))
    (hgen : differentialAdjoin C (Set.range (fun _ : Fin 1 ↦ v)) = ⊤)
    {ζ : Cˣ} {n : ℕ} (hord : orderOf ζ = n)
    {z : E} (hz : z ∈ differentialAdjoin C ({v ^ n} : Set E)) :
    torusScaleEquiv hv hgen (fun _ ↦ ζ) z = z := by
  have hfix : torusScaleEquiv hv hgen (fun _ ↦ ζ) (v ^ n) = v ^ n := by
    rw [map_pow, torusScaleEquiv_apply hv hgen (fun _ ↦ ζ) 0, mul_pow, ← map_pow]
    have hpow : ((ζ : C)) ^ n = 1 := by
      have h1 := pow_orderOf_eq_one ζ
      rw [hord] at h1
      calc ((ζ : C)) ^ n = ((ζ ^ n : Cˣ) : C) := (Units.val_pow_eq_pow_val ζ n).symm
        _ = ((1 : Cˣ) : C) := by rw [h1]
        _ = 1 := Units.val_one
    rw [hpow, map_one, one_mul]
  have hrange : ({v ^ n} : Set E) = Set.range (fun _ : Unit ↦ v ^ n) :=
    (Set.range_const).symm
  rw [hrange] at hz
  exact DifferentialAlgEquiv.fixed_on_differentialAdjoin
    (⟨torusScaleEquiv hv hgen (fun _ ↦ ζ),
      fun w ↦ torusScaleEquiv_deriv hv hgen (fun _ ↦ ζ) w⟩ : DifferentialAlgEquiv C E)
    (fun _ : Unit ↦ v ^ n) (fun _ ↦ hfix) hz

/-- **The invariant field of a root-of-unity scaling is exactly the power field.**  This is the
rotation layer of a parabolic orbifold deck group on the free rank-one cover field. -/
theorem setOf_rootOfUnity_invariant_eq_differentialAdjoin_pow
    (hconst : ∀ c : C, c′ = 0)
    {v : E} (hv : DifferentialIndependent C (fun _ : Fin 1 ↦ v))
    (hgen : differentialAdjoin C (Set.range (fun _ : Fin 1 ↦ v)) = ⊤)
    (hv0 : v ≠ 0)
    {ζ : Cˣ} {n : ℕ} (hn : 0 < n) (hord : orderOf ζ = n) :
    {z : E | torusScaleEquiv hv hgen (fun _ ↦ ζ) z = z}
      = (differentialAdjoin C ({v ^ n} : Set E) : Set E) := by
  ext z
  constructor
  · intro hz
    exact mem_differentialAdjoin_pow_of_rootOfUnity_invariant hconst hv hgen hv0 hn hord hz
  · intro hz
    exact differentialAdjoin_pow_fixed_of_rootOfUnity hv hgen hord hz

end

end GaloisForLFunctions.HTGeometry
