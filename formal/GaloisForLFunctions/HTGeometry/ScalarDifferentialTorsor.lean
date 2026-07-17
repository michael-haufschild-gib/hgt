import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction
import GaloisForLFunctions.HTGeometry.RatFuncScaleFixedField
import GaloisForLFunctions.HTGeometry.DifferentialIndependentFieldUniversality
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.StableCoreFunctoriality

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

open scoped Differential

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

/-- Constant scalar rescaling on a freely generated differential field. -/
def scalarDifferentialScaleEquiv (q : T) (hq : HypertranscendentalOver F q)
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
  let exy := GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv x y hx hy
  let ex : differentialAdjoin F (Set.range x) ≃ₐ[F] T :=
    (IntermediateField.equivOfEq hxtop).trans IntermediateField.topEquiv
  let ey : differentialAdjoin F (Set.range y) ≃ₐ[F] T :=
    (IntermediateField.equivOfEq hytop).trans IntermediateField.topEquiv
  exact ex.symm.trans (exy.trans ey)

@[simp]
theorem scalarDifferentialScaleEquiv_apply_q (q : T)
    (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) :
    scalarDifferentialScaleEquiv q hq hgen u q =
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
  have hjet := GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv_jet
    x y hx hy Unit.unit 0
  change ((GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv x y hx hy) ⟨q, _⟩).1 = _
  simpa [x, y] using congrArg Subtype.val hjet

/-- The canonical scalar equivalence commutes with the derivation. -/
theorem scalarDifferentialScaleEquiv_deriv (q : T)
    (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) (z : T) :
    scalarDifferentialScaleEquiv q hq hgen u z′ =
      (scalarDifferentialScaleEquiv q hq hgen u z)′ := by
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
  let exy := GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv x y hx hy
  let ex : differentialAdjoin F (Set.range x) ≃ₐ[F] T :=
    (IntermediateField.equivOfEq hxtop).trans IntermediateField.topEquiv
  let ey : differentialAdjoin F (Set.range y) ≃ₐ[F] T :=
    (IntermediateField.equivOfEq hytop).trans IntermediateField.topEquiv
  let zx : differentialAdjoin F (Set.range x) := ex.symm z
  have hzx : ex.symm z′ = zx′ := by
    apply Subtype.ext
    rfl
  have hxy := GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv_deriv
    x y hx hy zx
  change ey (exy (ex.symm z′)) = Differential.deriv (ey (exy (ex.symm z)))
  rw [hzx]
  exact congrArg Subtype.val hxy

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
  carrier := {sigma | ∀ z : T, sigma z′ = (sigma z)′}
  one_mem' := by intro z; rfl
  mul_mem' := by
    intro sigma tau hsigma htau z
    change sigma (tau z′) = (sigma (tau z))′
    rw [htau, hsigma]
  inv_mem' := by
    intro sigma hsigma z
    apply sigma.injective
    rw [sigma.apply_symm_apply]
    calc
      sigma ((sigma.symm z)′) = (sigma (sigma.symm z))′ := hsigma (sigma.symm z)
      _ = z′ := by rw [sigma.apply_symm_apply]

/-- Constant rescaling as a multiplicative action by derivation-preserving automorphisms of the
current-field extension. -/
def scalarDifferentialScaleAction (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) :
    Fˣ →* derivationPreservingAut (scalarLogCurrentField F q) T where
  toFun u := ⟨scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u,
    scalarDifferentialScaleEquiv_deriv q hq hgen u⟩
  map_one' := by
    apply Subtype.ext
    apply scalarCurrentAlgEquiv_ext q hq0 hgen
    simp
  map_mul' u v := by
    apply Subtype.ext
    apply scalarCurrentAlgEquiv_ext q hq0 hgen
    simp only [Subgroup.coe_mul, AlgEquiv.mul_apply,
      scalarDifferentialScaleEquivCurrent_apply_q]
    have hvL : algebraMap F T (v : F) ∈ scalarLogCurrentField F q :=
      (scalarLogCurrentField F q).algebraMap_mem (v : F)
    have hfixv : scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u
        (algebraMap F T (v : F)) = algebraMap F T (v : F) := by
      exact (scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u).commutes
        ⟨algebraMap F T (v : F), hvL⟩
    rw [map_mul, scalarDifferentialScaleEquivCurrent_apply_q, hfixv]
    simp only [Units.val_mul, map_mul]
    ring

/-- The constant-scalar action on a free differential amplitude is faithful. -/
theorem scalarDifferentialScaleAction_injective (q : T)
    (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) :
    Function.Injective (scalarDifferentialScaleAction q hq hq0 hgen hconst) := by
  intro u v huv
  have hqeq := congrArg
    (fun sigma : derivationPreservingAut (scalarLogCurrentField F q) T => sigma.1 q) huv
  simp only [scalarDifferentialScaleAction,
    scalarDifferentialScaleEquivCurrent_apply_q] at hqeq
  have hcoeff : algebraMap F T (u : F) = algebraMap F T (v : F) :=
    mul_left_cancel₀ hq0 hqeq
  exact Units.ext ((algebraMap F T).injective hcoeff)

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
  have hsigmaq0 : sigma.1 q ≠ 0 := map_ne_zero_iff sigma.1.injective |>.2 hq0
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
    exact this hc
  let u : Fˣ := Units.mk0 c hc0
  refine ⟨u, ?_⟩
  apply Subtype.ext
  apply scalarCurrentAlgEquiv_ext q hq0 hgen
  have hscale := scalarDifferentialScaleEquivCurrent_apply_q
    q hq hq0 hgen hconst u
  rw [hscale]
  change sigma.1 q = q * algebraMap F T c
  rw [← hc]
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

end

end GaloisForLFunctions.HTGeometry
