import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction
import GaloisForLFunctions.HTGeometry.RatFuncScaleFixedField
import GaloisForLFunctions.HTGeometry.DifferentialIndependentTopEquiv
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence

/-!
# The scalar differential torsor over its logarithmic-current field

Let `q` be a nonzero hypertranscendental element generating a differential field `T` over a
constant field `F`, and put `J = q'/q`, `L = F<J>`.  The reconstruction theorem says that
`T = L(q)` as an ordinary field.  This file proves the missing exact transport:

* `q` is transcendental over `L`, so `T` is canonically the rational function field `L(X)`;
* constant rescaling of `q` gives every derivation-preserving `L`-automorphism of `T`;
* the automorphism group is exactly `Fˣ`;
* finite and infinite cyclic scalar fixed fields transport from the exact `L(X)` computation.

This is the rank-one Picard--Vessiot torsor statement for `Y' = JY`, expressed entirely through
the concrete differential field, its constants, and its automorphism group.
-/

open scoped Differential Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F T : Type*} [Field F] [Field T] [Algebra F T]
  [Differential F] [Differential T] [DifferentialAlgebra F T]
  [CharZero T]

/-- The logarithmic-current differential field of a scalar amplitude. -/
def scalarLogCurrentField (F : Type*) {T : Type*} [Field F] [Field T]
    [Algebra F T] [Differential T] (q : T) : IntermediateField F T :=
  differentialAdjoin F ({Differential.logDeriv q} : Set T)

/-- Multiplying a differential generator by a nonzero base scalar does not change its generated
differential field. -/
theorem differentialAdjoin_mul_algebraMap_eq (q : T) (u : Fˣ) :
    differentialAdjoin F ({q * algebraMap F T (u : F)} : Set T) =
      differentialAdjoin F ({q} : Set T) := by
  apply le_antisymm
  · apply differentialAdjoin_le F
    · intro z hz
      have hzq : z = q * algebraMap F T (u : F) := Set.mem_singleton_iff.mp hz
      rw [hzq]
      exact (differentialAdjoin F ({q} : Set T)).mul_mem
        (subset_differentialAdjoin F ({q} : Set T) rfl)
        ((differentialAdjoin F ({q} : Set T)).algebraMap_mem (u : F))
    · exact derivationClosed_differentialAdjoin F ({q} : Set T)
  · apply differentialAdjoin_le F
    · intro z hz
      have hzq : z = q := Set.mem_singleton_iff.mp hz
      rw [hzq]
      have hscaled : q * algebraMap F T (u : F) ∈
          differentialAdjoin F ({q * algebraMap F T (u : F)} : Set T) :=
        subset_differentialAdjoin F _ rfl
      have huInv : algebraMap F T ((u⁻¹ : Fˣ) : F) ∈
          differentialAdjoin F ({q * algebraMap F T (u : F)} : Set T) :=
        (differentialAdjoin F _).algebraMap_mem ((u⁻¹ : Fˣ) : F)
      have hmul := (differentialAdjoin F
        ({q * algebraMap F T (u : F)} : Set T)).mul_mem hscaled huInv
      simpa [mul_assoc] using hmul
    · exact derivationClosed_differentialAdjoin F
        ({q * algebraMap F T (u : F)} : Set T)

private def scalarDifferentialScaleEquivRaw (q : T) (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) : T ≃ₐ[F] T := by
  let x : Unit → T := fun _ => q
  let y : Unit → T := fun _ => q * algebraMap F T (u : F)
  have hx : DifferentialIndependent F x := by
    simpa [x] using
      (GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton F q).mp hq
  have hyHT : HypertranscendentalOver F (q * algebraMap F T (u : F)) :=
    (hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_algebraMap (F := F) (E := T) (u : F))
      (by simpa using (algebraMap F T).injective.ne u.ne_zero)).2 hq
  have hy : DifferentialIndependent F y := by
    simpa [y] using
      (GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton F
        (q * algebraMap F T (u : F))).mp hyHT
  have hxtop : differentialAdjoin F (Set.range x) = ⊤ := by
    simpa [x] using hgen
  have hytop : differentialAdjoin F (Set.range y) = ⊤ := by
    simpa [y, differentialAdjoin_mul_algebraMap_eq q u] using hgen
  exact GaloisForLFunctions.differentialIndependentTopAlgEquiv
    x y hx hy hxtop hytop

private theorem scalarDifferentialScaleEquivRaw_apply_q (q : T)
    (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) :
    scalarDifferentialScaleEquivRaw q hq hgen u q =
      q * algebraMap F T (u : F) := by
  let x : Unit → T := fun _ => q
  let y : Unit → T := fun _ => q * algebraMap F T (u : F)
  have hx : DifferentialIndependent F x := by
    simpa [x] using
      (GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton F q).mp hq
  have hyHT : HypertranscendentalOver F (q * algebraMap F T (u : F)) :=
    (hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_algebraMap (F := F) (E := T) (u : F))
      (by simpa using (algebraMap F T).injective.ne u.ne_zero)).2 hq
  have hy : DifferentialIndependent F y := by
    simpa [y] using
      (GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton F
        (q * algebraMap F T (u : F))).mp hyHT
  have hxtop : differentialAdjoin F (Set.range x) = ⊤ := by
    simpa [x] using hgen
  have hytop : differentialAdjoin F (Set.range y) = ⊤ := by
    simpa [y, differentialAdjoin_mul_algebraMap_eq q u] using hgen
  exact GaloisForLFunctions.differentialIndependentTopAlgEquiv_apply
    x y hx hy hxtop hytop Unit.unit

private theorem scalarDifferentialScaleEquivRaw_deriv (q : T)
    (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) (z : T) :
    scalarDifferentialScaleEquivRaw q hq hgen u z′ =
      (scalarDifferentialScaleEquivRaw q hq hgen u z)′ := by
  let x : Unit → T := fun _ => q
  let y : Unit → T := fun _ => q * algebraMap F T (u : F)
  have hx : DifferentialIndependent F x := by
    simpa [x] using
      (GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton F q).mp hq
  have hyHT : HypertranscendentalOver F (q * algebraMap F T (u : F)) :=
    (hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_algebraMap (F := F) (E := T) (u : F))
      (by simpa using (algebraMap F T).injective.ne u.ne_zero)).2 hq
  have hy : DifferentialIndependent F y := by
    simpa [y] using
      (GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton F
        (q * algebraMap F T (u : F))).mp hyHT
  have hxtop : differentialAdjoin F (Set.range x) = ⊤ := by
    simpa [x] using hgen
  have hytop : differentialAdjoin F (Set.range y) = ⊤ := by
    simpa [y, differentialAdjoin_mul_algebraMap_eq q u] using hgen
  exact GaloisForLFunctions.differentialIndependentTopAlgEquiv_deriv
    x y hx hy hxtop hytop z

/-- Constant scalar rescaling exists on a freely generated differential field and commutes with
the derivation.  Packaging the large universal-property construction as an existence theorem keeps
downstream elaboration small. -/
theorem exists_scalarDifferentialScaleEquiv (q : T)
    (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) :
    ∃ sigma : T ≃ₐ[F] T,
      sigma q = q * algebraMap F T (u : F) ∧
        ∀ z : T, sigma z′ = (sigma z)′ :=
  ⟨scalarDifferentialScaleEquivRaw q hq hgen u,
    scalarDifferentialScaleEquivRaw_apply_q q hq hgen u,
    scalarDifferentialScaleEquivRaw_deriv q hq hgen u⟩

/-- Constant scalar rescaling on a freely generated differential field. -/
def scalarDifferentialScaleEquiv (q : T) (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) : T ≃ₐ[F] T :=
  (exists_scalarDifferentialScaleEquiv q hq hgen u).choose

@[simp]
theorem scalarDifferentialScaleEquiv_apply_q (q : T)
    (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) :
    scalarDifferentialScaleEquiv q hq hgen u q =
      q * algebraMap F T (u : F) :=
  (exists_scalarDifferentialScaleEquiv q hq hgen u).choose_spec.1

/-- The canonical scalar equivalence commutes with the derivation. -/
theorem scalarDifferentialScaleEquiv_deriv (q : T)
    (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) (z : T) :
    scalarDifferentialScaleEquiv q hq hgen u z′ =
      (scalarDifferentialScaleEquiv q hq hgen u z)′ :=
  (exists_scalarDifferentialScaleEquiv q hq hgen u).choose_spec.2 z

/-- The scalar differential field is generated as an ordinary field by its logarithmic-current
field and the one amplitude coordinate. -/
theorem scalarLogCurrentField_adjoin_amplitude_eq_top (q : T) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) :
    IntermediateField.adjoin (scalarLogCurrentField F q) ({q} : Set T) = ⊤ := by
  let L : IntermediateField F T := scalarLogCurrentField F q
  let A : IntermediateField F T := logCurrentOrdinaryExtension F q
  have hA : A = ⊤ := by
    change logCurrentOrdinaryExtension F q = ⊤
    rw [← differentialAdjoin_eq_logCurrentOrdinaryExtension hq0, hgen]
  apply top_unique
  intro z _
  have hzA : z ∈ A := by rw [hA]; trivial
  apply IntermediateField.adjoin_induction F
    (s := ((L : Set T) ∪ {q}))
    (p := fun w _ => w ∈ IntermediateField.adjoin L ({q} : Set T))
  · intro w hw
    rcases hw with hwL | hwq
    · exact (IntermediateField.adjoin L ({q} : Set T)).algebraMap_mem ⟨w, hwL⟩
    · have hwq' : w = q := Set.mem_singleton_iff.mp hwq
      subst w
      exact IntermediateField.subset_adjoin L ({q} : Set T) rfl
  · intro c
    exact (IntermediateField.adjoin L ({q} : Set T)).algebraMap_mem
      ⟨algebraMap F T c, L.algebraMap_mem c⟩
  · intro a b _ _ ha hb
    exact (IntermediateField.adjoin L ({q} : Set T)).add_mem ha hb
  · intro a _ ha
    exact (IntermediateField.adjoin L ({q} : Set T)).inv_mem ha
  · intro a b _ _ ha hb
    exact (IntermediateField.adjoin L ({q} : Set T)).mul_mem ha hb
  · exact hzA

/-- Constant rescaling fixes the logarithmic current. -/
theorem scalarDifferentialScaleEquiv_logDeriv (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) (u : Fˣ) :
    scalarDifferentialScaleEquiv q hq hgen u (Differential.logDeriv q) =
      Differential.logDeriv q := by
  have hu0 : algebraMap F T (u : F) ≠ 0 := by
    simpa using (algebraMap F T).injective.ne u.ne_zero
  have hu' : (algebraMap F T (u : F))′ = 0 := by
    rw [deriv_algebraMap, hconst]
    exact map_zero (algebraMap F T)
  rw [Differential.logDeriv, map_div₀,
    scalarDifferentialScaleEquiv_deriv,
    scalarDifferentialScaleEquiv_apply_q]
  rw [Derivation.leibniz, hu']
  simp only [smul_eq_mul, mul_zero, add_zero]
  field_simp [hu0, hq0]
  ring

/-- Constant rescaling fixes the whole differential field generated by the logarithmic current. -/
theorem scalarDifferentialScaleEquiv_fixed_on_currentField (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) (u : Fˣ)
    (z : scalarLogCurrentField F q) :
    scalarDifferentialScaleEquiv q hq hgen u z.1 = z.1 := by
  let sigma := scalarDifferentialScaleEquiv q hq hgen u
  have hJ : sigma (Differential.logDeriv q) = Differential.logDeriv q :=
    scalarDifferentialScaleEquiv_logDeriv
    q hq hq0 hgen hconst u
  have hjet : ∀ n : ℕ,
      sigma (differentialJet n (Differential.logDeriv q)) =
        differentialJet n (Differential.logDeriv q) := by
    intro n
    induction n with
    | zero => simpa using hJ
    | succ n ih =>
        rw [differentialJet_succ, scalarDifferentialScaleEquiv_deriv]
        exact congrArg Differential.deriv ih
  change sigma z.1 = z.1
  rw [scalarLogCurrentField, differentialAdjoin] at z
  apply IntermediateField.adjoin_induction F
    (s := differentialJetSet ({Differential.logDeriv q} : Set T))
    (p := fun w _ => sigma w = w)
  · rintro w ⟨v, hv, n, rfl⟩
    have hvJ : v = Differential.logDeriv q := Set.mem_singleton_iff.mp hv
    simpa [hvJ] using hjet n
  · intro c
    exact sigma.commutes c
  · intro a b _ _ ha hb
    rw [map_add, ha, hb]
  · intro a _ ha
    rw [map_inv₀, ha]
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb]
  · simpa using z.2

/-- The scalar action, re-based over the logarithmic-current field. -/
def scalarDifferentialScaleEquivCurrent (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) (u : Fˣ) :
    T ≃ₐ[scalarLogCurrentField F q] T where
  toRingEquiv := (scalarDifferentialScaleEquiv q hq hgen u).toRingEquiv
  commutes' z := scalarDifferentialScaleEquiv_fixed_on_currentField
    q hq hq0 hgen hconst u z

@[simp]
theorem scalarDifferentialScaleEquivCurrent_apply_q (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) (u : Fˣ) :
    scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u q =
      q * algebraMap F T (u : F) :=
  scalarDifferentialScaleEquiv_apply_q q hq hgen u

/-- Two current-field automorphisms of `T = L(q)` are equal as soon as they agree on `q`. -/
theorem scalarCurrentAlgEquiv_ext (q : T) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    {sigma tau : T ≃ₐ[scalarLogCurrentField F q] T}
    (hqeq : sigma q = tau q) : sigma = tau := by
  let L : IntermediateField F T := scalarLogCurrentField F q
  have htop : IntermediateField.adjoin L ({q} : Set T) = ⊤ :=
    scalarLogCurrentField_adjoin_amplitude_eq_top q hq0 hgen
  apply AlgEquiv.ext
  intro z
  have hz : z ∈ IntermediateField.adjoin L ({q} : Set T) := by
    rw [htop]
    trivial
  apply IntermediateField.adjoin_induction L
    (s := ({q} : Set T)) (p := fun w _ => sigma w = tau w)
  · intro w hw
    have hwq : w = q := Set.mem_singleton_iff.mp hw
    simpa [hwq] using hqeq
  · intro c
    exact (sigma.commutes c).trans (tau.commutes c).symm
  · intro a b _ _ ha hb
    rw [map_add, map_add, ha, hb]
  · intro a _ ha
    rw [map_inv₀, map_inv₀, ha]
  · intro a b _ _ ha hb
    rw [map_mul, map_mul, ha, hb]
  · exact hz

/-- Derivation-preserving automorphisms over a differential subfield. -/
def derivationPreservingAut (L : Type*) (T : Type*)
    [Field L] [Field T] [Algebra L T] [Differential T] :
    Subgroup (T ≃ₐ[L] T) where
  carrier := {sigma | ∀ z : T,
    sigma (Differential.deriv z) = Differential.deriv (sigma z)}
  one_mem' := by intro z; rfl
  mul_mem' := by
    intro sigma tau hsigma htau z
    change sigma (tau (Differential.deriv z)) =
      Differential.deriv (sigma (tau z))
    rw [htau, hsigma]
  inv_mem' := by
    intro sigma hsigma z
    apply sigma.injective
    simpa using (hsigma (sigma⁻¹ z)).symm

theorem scalarDifferentialScaleEquivCurrent_one (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) :
    scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst 1 = 1 := by
  apply scalarCurrentAlgEquiv_ext q hq0 hgen
  rw [scalarDifferentialScaleEquivCurrent_apply_q]
  simp

theorem scalarDifferentialScaleEquivCurrent_mul (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) (u v : Fˣ) :
    scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst (u * v) =
      scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u *
        scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst v := by
  apply scalarCurrentAlgEquiv_ext q hq0 hgen
  simp only [AlgEquiv.mul_apply, scalarDifferentialScaleEquivCurrent_apply_q]
  have hvL : algebraMap F T (v : F) ∈ scalarLogCurrentField F q :=
    (scalarLogCurrentField F q).algebraMap_mem (v : F)
  have hfixv : scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u
      (algebraMap F T (v : F)) = algebraMap F T (v : F) := by
    exact (scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u).commutes
      ⟨algebraMap F T (v : F), hvL⟩
  rw [map_mul, scalarDifferentialScaleEquivCurrent_apply_q, hfixv]
  simp only [Units.val_mul, map_mul]
  ring

/-- Constant rescaling as a multiplicative action by derivation-preserving automorphisms of the
current-field extension. -/
def scalarDifferentialScaleAction (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) :
    Fˣ →* derivationPreservingAut (scalarLogCurrentField F q) T where
  toFun u := ⟨scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u,
    scalarDifferentialScaleEquiv_deriv q hq hgen u⟩
  map_one' := Subtype.ext (scalarDifferentialScaleEquivCurrent_one q hq hq0 hgen hconst)
  map_mul' u v := Subtype.ext
    (scalarDifferentialScaleEquivCurrent_mul q hq hq0 hgen hconst u v)

@[simp]
theorem scalarDifferentialScaleAction_apply (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) (u : Fˣ) (z : T) :
    ((scalarDifferentialScaleAction q hq hq0 hgen hconst u).1 : T → T) z =
      scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u z := rfl

/-- The constant-scalar action on a free differential amplitude is faithful. -/
theorem scalarDifferentialScaleAction_injective (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) :
    Function.Injective (scalarDifferentialScaleAction q hq hq0 hgen hconst) := by
  intro u v huv
  have hqeq := congrArg
    (fun sigma : derivationPreservingAut (scalarLogCurrentField F q) T => sigma.1 q) huv
  have hqeq' : q * algebraMap F T (u : F) = q * algebraMap F T (v : F) := by
    simpa only [scalarDifferentialScaleAction_apply,
      scalarDifferentialScaleEquivCurrent_apply_q] using hqeq
  have hcoeff : algebraMap F T (u : F) = algebraMap F T (v : F) :=
    mul_left_cancel₀ hq0 hqeq'
  exact Units.ext ((algebraMap F T).injective hcoeff)

/-- The amplitude coordinate is algebraically transcendental over its logarithmic-current
field.  Its infinitely many constant rescalings give infinitely many roots of any hypothetical
minimal polynomial. -/
theorem scalar_amplitude_transcendental_over_currentField (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [CharZero F] :
    Transcendental (scalarLogCurrentField F q) q := by
  intro hqalg
  let L : IntermediateField F T := scalarLogCurrentField F q
  let p : L[X] := minpoly L q
  let P : T[X] := p.map (algebraMap L T)
  have hp0 : p ≠ 0 := minpoly.ne_zero hqalg.isIntegral
  have hP0 : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap L T).injective).mpr hp0
  let u : ℕ → Fˣ := fun n => Units.mk0 (n + 1 : F)
    (Nat.cast_add_one_ne_zero n)
  let r : ℕ → T := fun n => q * algebraMap F T (u n : F)
  have hrinj : Function.Injective r := by
    intro m n hmn
    have hcoeff : algebraMap F T (u m : F) = algebraMap F T (u n : F) :=
      mul_left_cancel₀ hq0 hmn
    have huval : (u m : F) = (u n : F) := (algebraMap F T).injective hcoeff
    have hcast : (m + 1 : F) = (n + 1 : F) := by
      simpa [u] using huval
    have hcast' : (m.succ : F) = (n.succ : F) := by
      simpa only [Nat.cast_succ] using hcast
    exact Nat.succ.inj (Nat.cast_injective hcast')
  have hqroot : P.IsRoot q := by
    change (p.map (algebraMap L T)).IsRoot q
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval L q
  have hroot : Set.range r ⊆ {z : T | P.IsRoot z} := by
    rintro z ⟨n, rfl⟩
    let sigma := scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst (u n)
    have hsroot : (P.map sigma.toRingEquiv.toRingHom).IsRoot (sigma q) :=
      hqroot.map
    have hmap : P.map sigma.toRingEquiv.toRingHom = P := by
      ext k
      simp only [P, Polynomial.coeff_map, Function.comp_apply]
      exact sigma.commutes (p.coeff k)
    rw [hmap] at hsroot
    simpa [r, sigma] using hsroot
  exact hP0 (Polynomial.eq_zero_of_infinite_isRoot P
    ((Set.infinite_range_of_injective hrinj).mono hroot))

/-- The exact rational coordinate on the scalar torsor: `X` is sent to the amplitude `q`. -/
def scalarTorsorRatFuncEquiv (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [CharZero F] :
    RatFunc (scalarLogCurrentField F q) ≃ₐ[scalarLogCurrentField F q] T :=
  (RatFunc.algEquivOfTranscendental q
      (scalar_amplitude_transcendental_over_currentField q hq hq0 hgen hconst)).trans
    ((IntermediateField.equivOfEq
      (scalarLogCurrentField_adjoin_amplitude_eq_top q hq0 hgen)).trans
        IntermediateField.topEquiv)

@[simp]
theorem scalarTorsorRatFuncEquiv_X (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [CharZero F] :
    scalarTorsorRatFuncEquiv q hq hq0 hgen hconst RatFunc.X = q := by
  simp [scalarTorsorRatFuncEquiv]

/-- Two algebra maps out of a rational function field agree when they agree on `X`. -/
theorem ratFunc_algHom_ext {K E : Type*} [Field K] [Field E] [Algebra K E]
    {f g : RatFunc K →ₐ[K] E} (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  apply AlgHom.ext
  intro z
  have hring : f.toRingHom = g.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := K[X])
    intro p
    have hpoly :
        f.toRingHom.comp (algebraMap K[X] (RatFunc K)) =
          g.toRingHom.comp (algebraMap K[X] (RatFunc K)) := by
      apply Polynomial.ringHom_ext
      · intro c
        change f (algebraMap K (RatFunc K) c) =
          g (algebraMap K (RatFunc K) c)
        rw [f.commutes, g.commutes]
      · simpa [RatFunc.algebraMap_X] using hX
    exact DFunLike.congr_fun hpoly p
  exact DFunLike.congr_fun hring z

/-- A constant unit viewed in the logarithmic-current field. -/
def scalarLogCurrentUnit (q : T) : Fˣ →* (scalarLogCurrentField F q)ˣ :=
  Units.map (algebraMap F (scalarLogCurrentField F q)).toMonoidHom

theorem scalarLogCurrentUnit_injective (q : T) :
    Function.Injective (scalarLogCurrentUnit (F := F) q) :=
  Units.map_injective (algebraMap F (scalarLogCurrentField F q)).injective

theorem orderOf_scalarLogCurrentUnit (q : T) (u : Fˣ) :
    orderOf (scalarLogCurrentUnit (F := F) q u) = orderOf u :=
  orderOf_injective (scalarLogCurrentUnit (F := F) q)
    (scalarLogCurrentUnit_injective q) u

/-- The rational-coordinate scale action and the differential scalar action are conjugate through
the exact coordinate equivalence `L(X) ≃ T`. -/
theorem scalarTorsorRatFuncEquiv_scale (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [CharZero F] (u : Fˣ) (z : RatFunc
      (scalarLogCurrentField F q)) :
    scalarTorsorRatFuncEquiv q hq hq0 hgen hconst
        (ratFuncUnitScaleAction (scalarLogCurrentUnit (F := F) q u) z) =
      scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u
        (scalarTorsorRatFuncEquiv q hq hq0 hgen hconst z) := by
  let e := scalarTorsorRatFuncEquiv q hq hq0 hgen hconst
  let sigma := scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u
  have heq : e.toAlgHom.comp
      (ratFuncUnitScaleAction (scalarLogCurrentUnit (F := F) q u)).toAlgHom =
        sigma.toAlgHom.comp e.toAlgHom := by
    apply ratFunc_algHom_ext
    change e (ratFuncUnitScaleAction (scalarLogCurrentUnit (F := F) q u) RatFunc.X) =
      sigma (e RatFunc.X)
    rw [ratFuncUnitScaleAction_apply_X, map_mul,
      scalarTorsorRatFuncEquiv_X, scalarDifferentialScaleEquivCurrent_apply_q,
      e.commutes]
    change
      algebraMap (scalarLogCurrentField F q) T
        (algebraMap F (scalarLogCurrentField F q) (u : F)) * q =
          q * algebraMap F T (u : F)
    rw [IsScalarTower.algebraMap_apply F (scalarLogCurrentField F q) T]
    ring
  exact DFunLike.congr_fun heq z

/-- The amplitude solves the rank-one linear equation `Y' = JY`. -/
theorem deriv_eq_logDeriv_mul (q : T) (hq0 : q ≠ 0) :
    q′ = Differential.logDeriv q * q := by
  simp only [Differential.logDeriv]
  field_simp [hq0]

/-- Every derivation-preserving current-field automorphism is one unique constant rescaling. -/
theorem scalarDifferentialScaleAction_surjective (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [Differential.ContainConstants F T] :
    Function.Surjective (scalarDifferentialScaleAction q hq hq0 hgen hconst) := by
  intro sigma
  let J : T := Differential.logDeriv q
  have hJmem : J ∈ scalarLogCurrentField F q :=
    subset_differentialAdjoin F ({J} : Set T) rfl
  have hfixJ : sigma.1 J = J := by
    exact sigma.1.commutes ⟨J, hJmem⟩
  have hsigmaq0 : sigma.1 q ≠ 0 :=
    (map_ne_zero_iff sigma.1 sigma.1.injective).2 hq0
  have hqderiv : q′ = J * q := deriv_eq_logDeriv_mul q hq0
  have hsigmaq_deriv : (sigma.1 q)′ = J * sigma.1 q := by
    calc
      (sigma.1 q)′ = sigma.1 q′ := (sigma.2 q).symm
      _ = sigma.1 (J * q) := by rw [hqderiv]
      _ = J * sigma.1 q := by rw [map_mul, hfixJ]
  have hratio_deriv : (sigma.1 q / q)′ = 0 := by
    rw [Derivation.leibniz_div, hsigmaq_deriv, hqderiv]
    field_simp [hq0]
    ring
  obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero F hratio_deriv
  have hc0 : c ≠ 0 := by
    intro hc0
    subst c
    simp only [map_zero] at hc
    have : sigma.1 q / q ≠ 0 := div_ne_zero hsigmaq0 hq0
    exact this hc.symm
  let u : Fˣ := Units.mk0 c hc0
  refine ⟨u, ?_⟩
  apply Subtype.ext
  apply scalarCurrentAlgEquiv_ext q hq0 hgen
  simp only [scalarDifferentialScaleAction_apply,
    scalarDifferentialScaleEquivCurrent_apply_q]
  change q * algebraMap F T c = sigma.1 q
  rw [hc]
  field_simp [hq0]

/-- **Full scalar differential Galois group.**  The derivation-preserving automorphism group of
`T/L`, where `L` is the logarithmic-current field, is exactly the multiplicative constant group. -/
def scalarDifferentialGaloisGroupEquiv (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [Differential.ContainConstants F T] :
    Fˣ ≃* derivationPreservingAut (scalarLogCurrentField F q) T :=
  MulEquiv.ofBijective (scalarDifferentialScaleAction q hq hq0 hgen hconst)
    ⟨scalarDifferentialScaleAction_injective q hq hq0 hgen hconst,
      scalarDifferentialScaleAction_surjective q hq hq0 hgen hconst⟩

/-- Membership in a cyclic fixed field is equivalent to fixedness under its generator. -/
theorem mem_fixedField_zpowers_iff {K E : Type*} [Field K] [Field E] [Algebra K E]
    (sigma : E ≃ₐ[K] E) (z : E) :
    z ∈ IntermediateField.fixedField (Subgroup.zpowers sigma) ↔ sigma z = z := by
  constructor
  · intro hz
    rw [IntermediateField.mem_fixedField_iff] at hz
    exact hz sigma (Subgroup.mem_zpowers sigma)
  · intro hz
    rw [IntermediateField.mem_fixedField_iff]
    let S : Subgroup (E ≃ₐ[K] E) :=
      { carrier := {tau : E ≃ₐ[K] E | tau z = z}
        one_mem' := rfl
        mul_mem' := by
          intro a b ha hb
          change a (b z) = z
          rw [hb, ha]
        inv_mem' := by
          intro a ha
          apply a.injective
          simpa using ha.symm }
    have hle : Subgroup.zpowers sigma ≤ S :=
      (Subgroup.zpowers_le).mpr hz
    intro tau htau
    exact hle htau

/-- Membership transports exactly through the image of an intermediate field under an algebra
equivalence. -/
theorem mem_map_algEquiv_iff {K E E' : Type*} [Field K] [Field E] [Field E']
    [Algebra K E] [Algebra K E'] (e : E ≃ₐ[K] E')
    (S : IntermediateField K E) (z : E') :
    z ∈ S.map e.toAlgHom ↔ e.symm z ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hz
    exact ⟨e.symm z, hz, e.apply_symm_apply z⟩

/-- The cyclic fixed field of a finite-order constant scalar on the differential torsor is the
power-coordinate field `L(q^N)`. -/
theorem fixedField_zpowers_scalarDifferentialScaleAction
    (q : T) (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [CharZero F]
    (u : Fˣ) {N : ℕ} (hN : 0 < N) (hu : orderOf u = N) :
    IntermediateField.fixedField
        (Subgroup.zpowers
          (scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u)) =
      IntermediateField.adjoin (scalarLogCurrentField F q) ({q ^ N} : Set T) := by
  let L : IntermediateField F T := scalarLogCurrentField F q
  let e : RatFunc L ≃ₐ[L] T := scalarTorsorRatFuncEquiv q hq hq0 hgen hconst
  let uL : Lˣ := scalarLogCurrentUnit (F := F) q u
  let sigmaX : RatFunc L ≃ₐ[L] RatFunc L := ratFuncUnitScaleAction uL
  let sigmaT : T ≃ₐ[L] T :=
    scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u
  have huL : orderOf uL = N := by
    exact (orderOf_scalarLogCurrentUnit q u).trans hu
  have hfixedX : IntermediateField.fixedField (Subgroup.zpowers sigmaX) =
      ratFuncPowerField L N := by
    exact fixedField_zpowers_ratFuncUnitScaleAction uL hN huL
  have hmapPower : (ratFuncPowerField L N).map e.toAlgHom =
      IntermediateField.adjoin L ({q ^ N} : Set T) := by
    rw [ratFuncPowerField, IntermediateField.adjoin_map]
    rw [Set.image_singleton]
    rw [map_pow]
    change IntermediateField.adjoin L ({e.toAlgHom RatFunc.X ^ N} : Set T) =
      IntermediateField.adjoin L ({q ^ N} : Set T)
    have heX : e.toAlgHom RatFunc.X = q := by
      exact scalarTorsorRatFuncEquiv_X q hq hq0 hgen hconst
    rw [heX]
  ext z
  have hconj : sigmaT z = z ↔ sigmaX (e.symm z) = e.symm z := by
    have heq := scalarTorsorRatFuncEquiv_scale q hq hq0 hgen hconst u (e.symm z)
    change e (sigmaX (e.symm z)) = sigmaT (e (e.symm z)) at heq
    rw [e.apply_symm_apply] at heq
    constructor
    · intro hz
      apply e.injective
      rw [heq, hz, e.apply_symm_apply]
    · intro hz
      rw [← heq, hz, e.apply_symm_apply]
  rw [mem_fixedField_zpowers_iff, hconj, ← mem_fixedField_zpowers_iff,
    hfixedX, ← hmapPower, mem_map_algEquiv_iff]

/-- An infinite-order constant scalar fixes exactly the logarithmic-current field. -/
theorem fixedField_zpowers_scalarDifferentialScaleAction_of_infinite_order
    (q : T) (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [CharZero F]
    (u : Fˣ) (hu : orderOf u = 0) :
    IntermediateField.fixedField
        (Subgroup.zpowers
          (scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u)) = ⊥ := by
  let L : IntermediateField F T := scalarLogCurrentField F q
  let e : RatFunc L ≃ₐ[L] T := scalarTorsorRatFuncEquiv q hq hq0 hgen hconst
  let uL : Lˣ := scalarLogCurrentUnit (F := F) q u
  let sigmaX : RatFunc L ≃ₐ[L] RatFunc L := ratFuncUnitScaleAction uL
  let sigmaT : T ≃ₐ[L] T :=
    scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u
  have huL : orderOf uL = 0 := by
    exact (orderOf_scalarLogCurrentUnit q u).trans hu
  have hfixedX : IntermediateField.fixedField (Subgroup.zpowers sigmaX) = ⊥ :=
    fixedField_zpowers_ratFuncUnitScaleAction_of_infinite_order uL huL
  have hmapBot : (⊥ : IntermediateField L (RatFunc L)).map e.toAlgHom = ⊥ := by
    simp
  ext z
  have hconj : sigmaT z = z ↔ sigmaX (e.symm z) = e.symm z := by
    have heq := scalarTorsorRatFuncEquiv_scale q hq hq0 hgen hconst u (e.symm z)
    change e (sigmaX (e.symm z)) = sigmaT (e (e.symm z)) at heq
    rw [e.apply_symm_apply] at heq
    constructor
    · intro hz
      apply e.injective
      rw [heq, hz, e.apply_symm_apply]
    · intro hz
      rw [← heq, hz, e.apply_symm_apply]
  rw [mem_fixedField_zpowers_iff, hconj, ← mem_fixedField_zpowers_iff,
    hfixedX, ← hmapBot, mem_map_algEquiv_iff]

/-- The power-coordinate field is also exactly the differential field generated by `q^N`, after
restricting scalars from the current field back to the constant field. -/
theorem scalarLogCurrentField_adjoin_power_restrictScalars
    (q : T) (hq0 : q ≠ 0) {N : ℕ} (hN : 0 < N) :
    (IntermediateField.adjoin (scalarLogCurrentField F q)
      ({q ^ N} : Set T)).restrictScalars F =
        differentialAdjoin F ({q ^ N} : Set T) := by
  rw [IntermediateField.restrictScalars_adjoin]
  simpa [scalarLogCurrentField] using
    (differentialAdjoin_pow_eq_logCurrentOrdinaryExtension
      (F := F) hq0 hN).symm

/-- A derivation-preserving current-field automorphism with multiplier `u` is the canonical
scalar action by `u`. -/
theorem derivationPreservingAut_eq_scaleAction_of_apply_q
    (q : T) (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0)
    (sigma : derivationPreservingAut (scalarLogCurrentField F q) T) (u : Fˣ)
    (hsigma : sigma.1 q = q * algebraMap F T (u : F)) :
    sigma = scalarDifferentialScaleAction q hq hq0 hgen hconst u := by
  apply Subtype.ext
  apply scalarCurrentAlgEquiv_ext q hq0 hgen
  simpa [hsigma]

/-- Finite-order fixed field for an arbitrary differential automorphism satisfying
`sigma(q) = u q`. -/
theorem fixedField_zpowers_derivationPreservingAut_of_finite_order
    (q : T) (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [CharZero F]
    (sigma : derivationPreservingAut (scalarLogCurrentField F q) T) (u : Fˣ)
    (hsigma : sigma.1 q = q * algebraMap F T (u : F))
    {N : ℕ} (hN : 0 < N) (hu : orderOf u = N) :
    IntermediateField.fixedField (Subgroup.zpowers sigma.1) =
      IntermediateField.adjoin (scalarLogCurrentField F q) ({q ^ N} : Set T) := by
  rw [derivationPreservingAut_eq_scaleAction_of_apply_q
    q hq hq0 hgen hconst sigma u hsigma]
  exact fixedField_zpowers_scalarDifferentialScaleAction
    q hq hq0 hgen hconst u hN hu

/-- Infinite-order fixed field for an arbitrary differential automorphism satisfying
`sigma(q) = u q`. -/
theorem fixedField_zpowers_derivationPreservingAut_of_infinite_order
    (q : T) (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [CharZero F]
    (sigma : derivationPreservingAut (scalarLogCurrentField F q) T) (u : Fˣ)
    (hsigma : sigma.1 q = q * algebraMap F T (u : F))
    (hu : orderOf u = 0) :
    IntermediateField.fixedField (Subgroup.zpowers sigma.1) = ⊥ := by
  rw [derivationPreservingAut_eq_scaleAction_of_apply_q
    q hq hq0 hgen hconst sigma u hsigma]
  exact fixedField_zpowers_scalarDifferentialScaleAction_of_infinite_order
    q hq hq0 hgen hconst u hu

end

end GaloisForLFunctions.HTGeometry
